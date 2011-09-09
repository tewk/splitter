open Pretty
open Cil
open Splitter_utils
module E = Errormsg
module C = Cil
module RD = Reachingdefs
module H = Hashtbl

(* command-line options *)
let splitwidth  = ref 4
let splitsize   = ref 300
let splitrmtmps = ref false;

exception TryStmtNotSupported
exception AEXN
exception BEXN
exception Oops

(* () -> () -> int *)
(* create a incrementing counter function *)
let genNextCounter = function () ->
  let ni = ref 0 in
    function () -> ni := (!ni + 1); !ni

class dereferenceVars (map) = object (self)
  inherit Cil.nopCilVisitor

  method vlval l = match l with
  | Var (v) , o -> 
      if v.vglob then DoChildren else
    (try
     ChangeTo(Mem(Lval(Var(H.find map v.vname), NoOffset)),
     visitCilOffset (new dereferenceVars(map)) o)
    with Not_found -> DoChildren)
  | _ -> DoChildren
end

let addrofVar v = match v.vtype with
  | TNamed({ tname="va_list"}, a) -> v
  | _ -> { v with vtype = TPtr(v.vtype, []);}

let fixupTArray map t = match t with
  | TPtr( TArray( ty, Some(ex), at), at2) -> 
      (*
       Printf.fprintf stderr "--- TArray ---";
       fprint stderr 80 (defaultCilPrinter#pExp () ex);
       Printf.fprintf stderr "\n";
      *)
      let nex = visitCilExpr (new dereferenceVars(map)) ex in
      (*
       Printf.fprintf stderr "--- TArray ---";
       fprint stderr 80 (defaultCilPrinter#pExp () nex);
       Printf.fprintf stderr "\n";
      *)
      TPtr(TArray(ty, Some(nex), at), at2)
  | _ -> t

let fixupTArrayVar map v = { v with vtype = fixupTArray map v.vtype; }

let change_out_vars b map =
  visitCilBlock (new dereferenceVars(map)) b

(* build a GFun from a fundec, i generator, loc, and block *)
let buildGFun (fd : fundec) localvars nexti (loc : location) (b : block) : global =
  let newlv = (List.map addrofVar localvars) in
  let map : (string, varinfo) H.t = H.create 113 in
  List.iter (fun x -> (match x.vtype with 
    | TNamed({ tname="va_list"}, a) -> ()
    | _  -> (H.add map x.vname x))) newlv;
  let params = match localvars with
  | [] -> None
  | _  -> Some (List.map (fun x -> x.vname, (fixupTArray map (TPtr(x.vtype, []))), []) localvars) in
  let appendVarName v = { v with
    vname       = v.vname ^ "_" ^ (string_of_int (nexti ()));
    vtype       = TFun(voidType,params,false,[]);
    vstorage    = Static; } in
  let newb = change_out_vars b map in
  let nnewlv = (List.map (fixupTArrayVar map) newlv) in
  
  GFun({ fd with
        svar       = appendVarName fd.svar;
        sformals   = nnewlv;
        slocals    = [];
        sbody      = newb;
        }, loc)

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

(* generates a callstmt and function definition from a stmt list *)
let gen_func_creator fd nexti =
  (fun localvars stmts loc ->
    let blockfunc = (buildGFun fd localvars nexti loc {battrs = fd.sbody.battrs; bstmts = stmts} ) in
     (match blockfunc with
     | GFun(fn, floc) -> 
         let args = (List.map (fun x -> (match x.vtype with
         | TNamed({ tname="va_list"}, a) -> Lval((Var x), NoOffset)
         | _ -> (Cil.mkAddrOrStartOf ((Var x), NoOffset)))) localvars) in
         let callstmt = func2call_stmt fn.svar args (List.hd stmts).labels floc in
           (callstmt, blockfunc)
     | _ -> raise Not_A_GFun_NEVER_GET_HERE))

let stmt_text_len (s : stmt) : int =
  let len = String.length (Pretty.sprint 80 (printStmt defaultCilPrinter () s)) in 
(*
  Printf.fprintf stderr "&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&& %i\n" len;
  Printf.fprintf stderr "%s" (Pretty.sprint 80 (printStmt defaultCilPrinter () s));
  Printf.fprintf stderr "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$ %i\n" len;
*)
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

let rec split_block localvars width (body : block) (loc : location) func_creator fd nexti =
  let rec split_stmt s loc func_creator =
    match s.skind with
    | Block(b) -> 
        let nb, nf = split_block localvars width b loc func_creator fd nexti in
        let st = instr2stmt s (Block(nb)) in
        st, nf
    | Loop(b, loc, s1, s2) -> 
        (* dump_stmt "Loop" h; *)
        let nb, nf = split_block localvars width b loc func_creator fd nexti in
        let st = instr2stmt s (Loop(nb, loc, s1, s2)) in
        st, nf
    | Switch(exp1, b, stmts, loc) ->
        let nb, nf = split_block localvars width b loc func_creator fd nexti in
        let st = instr2stmt s (Switch(exp1, nb, stmts, loc)) in
        st, nf
    | Instr(is) ->
        let l1, l2 = split_list is in
        let c1, f1 = func_creator localvars [ (instr2stmt s (Instr(l1))) ] loc in
        let c2, f2 = func_creator localvars [ (instr2stmt s (Instr(l2))) ] loc in
        let nb = {battrs = []; bstmts = [c1; c2]} in
        let nst = instr2stmt s (Block(nb)) in
        let nfuncs = [f1; f2] in
        nst, nfuncs
    | If(expr, _then, _else, loc) ->
      (* dump_stmt "If" h; *)
      let tnew_body, tnfuncs = split_block localvars width _then loc func_creator fd nexti in
      let enew_body, enfuncs = split_block localvars width _else loc func_creator fd nexti in

      let st = instr2stmt s (If(expr, tnew_body, enew_body, loc)) in
        st, (List.append tnfuncs enfuncs)
    | Break(loc)    -> s, []
    | Continue(loc) -> s, []
    | Goto(a, b)    -> s, []
    | Return(a, b)  -> s, []
    | TryFinally(b, b2, loc) -> raise TryStmtNotSupported; s, []
    | TryExcept(b, ilexpp, b2, loc) -> raise TryStmtNotSupported; s, [] in

  (* block-worker (bw) *)
  let rec bw (stmts : stmt list) (newstmts : stmt list) (oldstmts : stmt list) (left : int) (funcs : global list) =
(*    (List.iter (dump_stmt "LL") stmts); *)
    let chunk_size = !splitsize in
    match stmts with 
    (* base case, empty list  *)
    | [] -> 
       (match newstmts with
        | [] -> { battrs = body.battrs; bstmts = (List.rev oldstmts)}, funcs
        | _  -> let newcall, func = func_creator localvars (List.rev newstmts) loc in 
                  { battrs = body.battrs; bstmts = (List.rev (newcall :: oldstmts))}, ( func :: funcs))

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
      | [] -> bw (ns::t) [] ( noop :: oldstmts) width funcs
      | _  -> 
       let newcall, func = func_creator localvars (List.rev newstmts) loc in 
       bw (ns::t) [] (noop :: (newcall :: oldstmts)) width (func :: funcs))


    (* current statement is splittable *)
    | h :: t when not (hasUnsplittable h) ->
(*      dump_stmt "splittable" h; *)
       (match left with
        | 0 -> 
          let newcall, func = func_creator localvars (List.rev newstmts) loc in 
          bw (h :: t) [] (newcall :: oldstmts) width (func :: funcs)
        | _ -> 
          begin
          if (stmt_text_len h) > chunk_size  then 
            (* cant split a Instr containing only a single instruction *)
            (match h.skind with
            | Instr(is) when ((List.length is) == 1) ->
              bw t (h :: newstmts) oldstmts (left - 1) funcs
            | _ -> 
              let newstmt , nfuncs = split_stmt h loc func_creator in
              bw t (newstmt :: newstmts) oldstmts width (List.append nfuncs funcs))
          else
            bw t (h :: newstmts) oldstmts (left - 1) funcs
          end)

    (* current statement is NOT splittable *)
    | h :: t -> 
(*      dump_stmt "unsplittable" h; *)
       (match newstmts with
        | [] -> bw t [] (h :: oldstmts) width funcs
        | _  -> 
          let newcall, func = func_creator localvars (List.rev newstmts) loc in 
          bw t [] (h :: (newcall :: oldstmts)) width (func :: funcs)) in

    bw body.bstmts [] [] width []

let dump_func_to_file funcN fileN =
(*
  let channel = open_out (fileN.fileName ^ "NORMTMPS") in
    (* remove unuseds except for root funcN which may be static *)
    dumpFile defaultCilPrinter channel (fileN.fileName ^ "NORMTMPS") fileN;
    close_out channel;
*)
  let channel = open_out fileN.fileName in
    (* remove unuseds except for root funcN which may be static *)
    if !splitrmtmps then 
      Rmtmps.removeUnusedTemps ~isRoot:(fun x -> (Rmtmps.isExportedRoot x) || x == funcN) fileN;
    dumpFile defaultCilPrinter channel fileN.fileName fileN;
    close_out channel;
    fileN.fileName


(* Split functions into their own translation units *)
let splitFuncsToTU file =
  let channel = open_out (file.fileName ^ "_CILOUT.DUMP") in
    dumpFile defaultCilPrinter channel (file.fileName ^ "_CILOUT.DUMP") file;
    close_out channel;
  let globalsN = 
    Cil.foldGlobals file (fun fns func -> match func with
      Cil.GFun(fd, loc) ->
        Printf.fprintf stderr "============== %s ==============\n" fd.svar.vname;
        let nexti = (genNextCounter ()) in 
        let fun_creator = (gen_func_creator fd nexti) in
        let new_body, funcs = (split_block (List.append fd.sformals fd.slocals) !splitwidth fd.sbody loc fun_creator fd nexti) in
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
    let fileN = { fileName = file.fileName ^ "_split.c";
                  globals = globalsN;
                  globinit = None; 
                  globinitcalled = false; } in
      let channel = open_out fileN.fileName in
        if !splitrmtmps then 
          Rmtmps.removeUnusedTemps ~isRoot:(fun x -> (Rmtmps.isExportedRoot x)) fileN;
        dumpFile defaultCilPrinter channel fileN.fileName fileN;
        close_out channel

let dosplitter file =
  ignore (Partial.calls_end_basic_blocks file) ; 
  ignore (Partial.globally_unique_vids file) ; 
  splitFuncsToTU file

let feature : featureDescr =
  { fd_name = "splitter";
    fd_enabled = Cilutil.logWrites;
    fd_description = "Split functions";
    fd_extraopt = [];
    fd_doit = dosplitter;
    fd_post_check = true;
  }

