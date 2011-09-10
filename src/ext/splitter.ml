open Pretty
open Cil
open Splitter_utils
module E = Errormsg
module C = Cil
module RD = Reachingdefs
module H = Hashtbl

(* command-line options *)
let splitwidth  = ref 1
let splitsize   = ref 100
let splitrmtmps = ref false;

exception TryStmtNotSupported

(* () -> () -> int *)
(* create a incrementing counter function *)
let genNextCounter = function () ->
  let ni = ref 0 in
    function () -> ni := (!ni + 1); !ni

class dereferenceVars (map, seen) = object (self)
  inherit Cil.nopCilVisitor

  method vlval l = match l with
  | Var (v) , o -> 
      if v.vglob then DoChildren else
      (match v.vtype with 
          | TNamed({ tname="va_list"}, a) -> 
              H.add seen v.vname 1;
              DoChildren
          | _ -> (try let vi = H.find map v.vname in
     H.add seen v.vname 1;
     ChangeTo(Mem(Lval(Var(vi), NoOffset)), visitCilOffset (new dereferenceVars(map, seen)) o);
    with Not_found -> DoChildren))
  | _ -> DoChildren
end

let addrofVar v = match v.vtype with
  | TNamed({ tname="va_list"}, a) -> v
  | _ -> { v with vtype = TPtr(v.vtype, []);}

let fixupTArray map seen t = match t with
  | TPtr( TArray( ty, Some(ex), at), at2) -> 
      let nex = visitCilExpr (new dereferenceVars(map, seen)) ex in
      TPtr(TArray(ty, Some(nex), at), at2)
  | _ -> t

let fixupTArrayVar map seen v = { v with vtype = fixupTArray map seen v.vtype; }

(* build a GFun from a fundec, i generator, loc, and block *)
exception Not_A_GFun_NEVER_GET_HERE

(* stmt -> skind -> stmt *)
(* makes a new statement from a previous stmt and a new statement kind(statement) *)
let instr2stmt2 stlabels stkind = {labels = stlabels; skind = stkind; sid = 0; succs = []; preds = []}
let instr2plain_stmt stkind = instr2stmt2 [] stkind
let instr2stmt  stmt stkind = instr2stmt2 stmt.labels stkind
let empty_stmt = {labels = []; skind = Instr([]); sid = 0; succs = []; preds = []}

let func2call_stmt fnvar args labels loc =
  {labels = labels; 
  skind = Instr [Call(None, Lval( Var(fnvar), NoOffset), args, loc)]; 
  sid = 0; 
  succs = []; 
  preds = []}

let filter_case s = { s with
  labels = List.filter (function x -> match x with 
                          | Case(e, l) -> false 
                          | _ -> true) s.labels; }

let dump_stmt d s =
  Printf.fprintf stderr "*** %s *** " d;
  (dumpStmt defaultCilPrinter stderr 2 s);
  Printf.fprintf stderr "\n"


let stmt_text_len (s : stmt) : int =
  let len = String.length (Pretty.sprint 80 (printStmt defaultCilPrinter () s)) in 
  len

let split_list l =
  let isl = List.length l in
  let rec slw l l1 lc =
    match lc with
    | 0 -> (List.rev l1), l
    | _ -> slw (List.tl l) ((List.hd l) :: l1) (lc - 1)
    in
  slw l [] (isl / 2)
(* func_creator : stmts list -> location -> (stmt, global)) *)

let haslabel h = match h with
  | { labels = [] } -> false
  | _ -> true

let ht_merge (a : (string, int) H.t)  (b : (string, int) H.t) : (string, int) H.t =
  (H.iter (fun k v -> (H.add b k v)) a);
  b

let splitFuncs file =
  let globalsN = 
    Cil.foldGlobals file (fun fns func -> match func with
    Cil.GFun(fd, loc) ->
      Printf.fprintf stderr "============== %s ==============\n" fd.svar.vname;
      let nexti = (genNextCounter ()) in 
      let localvars = (List.append fd.sformals fd.slocals) in

      let rec split_block localvars width (body : block) =

        (* generates a callstmt and function definition from a stmt list *)
        let func_creator localvars stmts loc =
          let b = {battrs = fd.sbody.battrs; bstmts = stmts} in
          let newlv = (List.map addrofVar localvars) in
          let seen : (string, int) H.t = H.create 113 in
          let map : (string, varinfo) H.t = H.create 113 in
          List.iter (fun x -> H.add map x.vname x) newlv;
          let dV = (new dereferenceVars(map, seen)) in
          let newb = (visitCilBlock dV b) in

          let filter_func = (fun v -> try (H.find seen v.vname); true with Not_found -> false ) in
          let min_localvars = List.filter filter_func localvars in 

          (* set up parameters for function body *)
          let params = match min_localvars with
          | [] -> None
          | _  -> Some(List.map (fun x -> x.vname, (fixupTArray map seen (TPtr(x.vtype, []))), []) min_localvars) in
          let appendVarName v = { v with
          vname       = v.vname ^ "_" ^ (string_of_int (nexti ()));
          vtype       = TFun(voidType,params,false,[]);
          vstorage    = Static; } in
          let nnewlv = List.map (fixupTArrayVar map seen) (List.filter filter_func newlv) in
          let blockfunc = 
            GFun({ fd with
            svar       = appendVarName fd.svar;
            sformals   = nnewlv;
            slocals    = [];
            sbody      = newb;
          }, loc) in
           (match blockfunc with
           | GFun(fn, floc) -> 
               let args = (List.map (fun x -> (match x.vtype with
               | TNamed({ tname="va_list"}, a) -> Lval((Var x), NoOffset)
               | _ -> (Cil.mkAddrOrStartOf ((Var x), NoOffset)))) min_localvars) in
               let callstmt = func2call_stmt fn.svar args (List.hd stmts).labels floc in
                 (callstmt, blockfunc, seen)
           | _ -> raise Not_A_GFun_NEVER_GET_HERE) in
 

          let rec split_stmt s loc =
            match s.skind with
            | Block(b) -> 
                let nb, nf, nseen = split_block localvars width b  in
                let st = instr2stmt s (Block(nb)) in
                st, nf, nseen
            | Loop(b, loc, s1, s2) -> 
                (* dump_stmt "Loop" h; *)
                let nb, nf, nseen = split_block localvars width b in
                let st = instr2stmt s (Loop(nb, loc, s1, s2)) in
                st, nf, nseen
            | Switch(exp1, b, stmts, loc) ->
                let nb, nf, nseen = split_block localvars width b in
                let st = instr2stmt s (Switch(exp1, nb, stmts, loc)) in
                st, nf, nseen
            | Instr(is) ->
                let l1, l2 = split_list is in
                let c1, f1, s1 = func_creator localvars [ (instr2stmt s (Instr(l1))) ] loc in
                let c2, f2, s2 = func_creator localvars [ (instr2stmt s (Instr(l2))) ] loc in
                let nb = {battrs = []; bstmts = [c1; c2]} in
                let nst = instr2stmt s (Block(nb)) in
                let nfuncs = [f1; f2] in
                nst, nfuncs, (ht_merge s1 s1) 
            | If(expr, _then, _else, loc) ->
              (* dump_stmt "If" h; *)
              let tnew_body, tnfuncs, s1 = split_block localvars width _then in
              let enew_body, enfuncs, s2 = split_block localvars width _else in

              let st = instr2stmt s (If(expr, tnew_body, enew_body, loc)) in
                st, (List.append tnfuncs enfuncs), (ht_merge s1 s2)
            | Break(loc)    -> s, [], H.create 1
            | Continue(loc) -> s, [], H.create 1
            | Goto(a, b)    -> s, [], H.create 1
            | Return(a, b)  -> s, [], H.create 1
            | TryFinally(b, b2, loc) -> raise TryStmtNotSupported; s, [], H.create 1
            | TryExcept(b, ilexpp, b2, loc) -> raise TryStmtNotSupported; s, [], H.create 1 in

          (* block-worker (bw) *)
          let rec bw (stmts : stmt list) (newstmts : stmt list) (oldstmts : stmt
          list) (left : int) (funcs : global list) (seen : (string, int) H.t) (*: Cil.block Cil.global list (string, int) H.t *) =
        (*    (List.iter (dump_stmt "LL") stmts); *)
            let chunk_size = !splitsize in
            match stmts with 
            (* base case, empty list  *)
            | [] -> 
               (match newstmts with
                | [] -> { battrs = body.battrs; bstmts = (List.rev oldstmts)}, funcs, seen
                | _  -> let newcall, func, nseen = func_creator localvars (List.rev newstmts) loc in 
                          { battrs = body.battrs; bstmts = (List.rev (newcall :: oldstmts))}, ( func :: funcs), (ht_merge nseen seen))

            (* statement has label, make noop stmt with label *)
            | h :: t when (haslabel h) -> 
        (*      dump_stmt "hasLabel" h;  *)

              let mknooplabel s = 
                 {labels = s.labels; 
                 skind = Instr [];
                 sid = 0; 
                 succs = []; 
                 preds = []},
                 {labels = []; 
                 skind = s.skind;
                 sid = 0; 
                 succs = []; 
                 preds = []} in
              let noop, ns = mknooplabel h in
              (match newstmts with
              | [] -> bw (ns::t) [] ( noop :: oldstmts) width funcs seen
              | _  -> 
               let newcall, func, nseen = func_creator localvars (List.rev newstmts) loc in 
               bw (ns::t) [] (noop :: (newcall :: oldstmts)) width (func :: funcs) (ht_merge nseen seen))


            (* current statement is splittable *)
            | h :: t when not (hasUnsplittable h) ->
        (*      dump_stmt "splittable" h; *)
               (match left with
                | 0 -> 
                  let newcall, func, nseen = func_creator localvars (List.rev newstmts) loc in 
                  bw (h :: t) [] (newcall :: oldstmts) width (func :: funcs) (ht_merge nseen seen)
                | _ -> 
                  begin
                  if (stmt_text_len h) > chunk_size  then 
                    (* cant split a Instr containing only a single instruction *)
                    (match h.skind with
                    | Instr(is) when ((List.length is) == 1) ->
                      bw t (h :: newstmts) oldstmts (left - 1) funcs seen
                    | _ -> 
                      let newstmt , nfuncs, nseen  = split_stmt h loc in
                      bw t (newstmt :: newstmts) oldstmts width (List.append nfuncs funcs) (ht_merge nseen seen))
                  else
                    bw t (h :: newstmts) oldstmts (left - 1) funcs seen
                  end)

            (* current statement is NOT splittable *)
            | h :: t -> 
        (*      dump_stmt "unsplittable" h; *)
               (match newstmts with
                | [] -> bw t [] (h :: oldstmts) width funcs seen
                | _  -> 
                  let newcall, func, nseen = func_creator localvars (List.rev newstmts) loc in 
                  bw t [] (h :: (newcall :: oldstmts)) width (func :: funcs) (ht_merge nseen seen)) in

            bw body.bstmts [] [] width [] (H.create 13) in

        let new_body, funcs, seens = split_block localvars !splitwidth fd.sbody in
        let labels = find_labels new_body.bstmts [] in

        fixup_labels new_body.bstmts labels;
        let funcN = GFun({ 
          svar       = fd.svar;
          sformals   = fd.sformals;
          slocals    = fd.slocals;
          smaxid     = fd.smaxid;
          sbody      = {battrs = new_body.battrs; bstmts = new_body.bstmts};
          smaxstmtid = fd.smaxstmtid;
          sallstmts  = fd.sallstmts; }, loc) in
        (List.concat [ fns; [GVarDecl(fd.svar, loc)]; (List.rev funcs); [funcN] ])

      | _ -> (List.concat [ fns; [func] ])) [] in
    file.globals <- globalsN

let dosplitter file =
  ignore (Partial.calls_end_basic_blocks file) ; 
  ignore (Partial.globally_unique_vids file) ; 
  splitFuncs file;
  Rmtmps.removeUnusedTemps file

let feature : featureDescr =
  { fd_name = "splitter";
    fd_enabled = Cilutil.logWrites;
    fd_description = "Split functions";
    fd_extraopt = [];
    fd_doit = dosplitter;
    fd_post_check = true;
  }

