open Pretty
open Cil
open Splitter_utils
module C = Cil
module RD = Reachingdefs

exception TryStmtNotSupported
exception AEXN
exception BEXN

(* () -> () -> int *)
(* create a incrementing counter function *)
let genNextCounter = function () ->
  let ni = ref 0 in
    function () -> ni := (!ni + 1); !ni


(* print list of strings to stderr *)
let make_make_file lst =
  let rec w o lst = match lst with
  | [] -> ()
  | h :: t -> (fprintf o "%s\n" h); w o t in
    w stderr lst

let prepend_type_ t = match t with
  | TFun (tt, Some ats, b, attrs) ->
    let rec ptw ats nats =
      (match ats with
      | [] -> List.rev nats
      | (s, ty, at) :: tl -> ptw tl (( "_UnIqUe_" ^ s, ty, at) :: nats)) in
    let xnats = ptw ats [] in
    TFun(tt, Some xnats, b, attrs)
  | TFun(tt, None, b, attrs) -> t
  | TFun(a, b, c, d) ->       Printf.fprintf stderr "***Oops1 ***"; raise AEXN
  | TInt(a,b) ->              Printf.fprintf stderr "***Oops3 ***"; raise AEXN
  | TFloat(a,b) ->            Printf.fprintf stderr "***Oops4 ***"; raise AEXN
  | TPtr(a,b) ->              Printf.fprintf stderr "***Oops5 ***"; raise AEXN
  | TArray(a,b,c) ->          Printf.fprintf stderr "***Oops6 ***"; raise AEXN
  | TVoid(a) ->               Printf.fprintf stderr "***Oops7 ***"; raise AEXN
  | TNamed(a,b) ->            Printf.fprintf stderr "***Oops8 ***"; raise AEXN
  | TComp(a,b) ->             Printf.fprintf stderr "***Oops9 ***"; raise AEXN
  | TEnum(a,b) ->             Printf.fprintf stderr "***Oops10***"; raise AEXN
  | TBuiltin_va_list(a) ->    Printf.fprintf stderr "***Oops11***"; raise AEXN
  | _ -> raise BEXN


let remove_static v = {
  vname       = v.vname;
  vtype       = prepend_type_ v.vtype;
  vstorage    = (match v.vstorage with
                  | Static ->   NoStorage
                  | _ -> v.vstorage);
  vglob       = v.vglob;
  vinline     = v.vinline;
  vattr       = v.vattr;
  vdecl       = v.vdecl;
  vid         = v.vid;
  vaddrof     = v.vaddrof;
  vreferenced = v.vreferenced;
  vdescr      = v.vdescr;
  vdescrpure  = v.vdescrpure;}

let make_static v = {
  vname       = v.vname;
  vtype       = v.vtype;
  vstorage    = Static;
  vglob       = v.vglob;
  vinline     = v.vinline;
  vattr       = v.vattr;
  vdecl       = v.vdecl;
  vid         = v.vid;
  vaddrof     = v.vaddrof;
  vreferenced = v.vreferenced;
  vdescr      = v.vdescr;
  vdescrpure  = v.vdescrpure;}

let prepend_ v = {
  vname       = "_UnIqUe_" ^ v.vname;
  vtype       = v.vtype;
  vstorage    = v.vstorage;
  vglob       = v.vglob;
  vinline     = v.vinline;
  vattr       = v.vattr;
  vdecl       = v.vdecl;
  vid         = v.vid;
  vaddrof     = v.vaddrof;
  vreferenced = v.vreferenced;
  vdescr      = v.vdescr;
  vdescrpure  = v.vdescrpure;}

(* build a GFun from a fundec, i generator, loc, and block *)
let buildGFun (fd : fundec) nexti (loc : location) (b : block) : global =
  let appendVarName v = {
    vname       = v.vname ^ "_" ^ (string_of_int (nexti ()));
    vtype       = TFun(voidType,None,false,[]);
    vstorage    = Static;
    vglob       = v.vglob;
    vinline     = v.vinline;
    vattr       = v.vattr;
    vdecl       = v.vdecl;
    vid         = v.vid;
    vaddrof     = v.vaddrof;
    vreferenced = v.vreferenced;
    vdescr      = v.vdescr;
    vdescrpure  = v.vdescrpure;} in
  
  GFun({ 
        svar       = appendVarName fd.svar;
        sformals   = [];
        slocals    = [];
        smaxid     = fd.smaxid;
        sbody      = b;
        smaxstmtid = fd.smaxstmtid;
        sallstmts  = fd.sallstmts; }, loc)

exception Not_A_GFun_NEVER_GET_HERE

(* stmt -> skind -> stmt *)
(* makes a new statement from a previous stmt and a new statement kind(statement) *)
let instr2stmt2 stlabels stkind = {labels = stlabels; skind = stkind; sid = 0; succs = []; preds = []}
let instr2plain_stmt stkind = instr2stmt2 [] stkind
let instr2stmt  stmt stkind = instr2stmt2 stmt.labels stkind
let empty_stmt = {labels = []; skind = Instr([]); sid = 0; succs = []; preds = []}

let func2call_stmt fnvar labels loc =
  {labels = labels; 
  skind = Instr [Call(None, Lval( Var(fnvar), NoOffset), [], loc)]; 
  sid = 0; 
  succs = []; 
  preds = []}

let filter_case s = {
  labels = List.filter (function x -> match x with 
                          | Case(e, l) -> false 
                          | _ -> true) s.labels;
  skind  = s.skind; 
  sid    = s.sid;
  succs  = s.succs; 
  preds  = s.preds}


let dump_stmt d s =
  Printf.fprintf stderr "*** %s *** " d;
  (dumpStmt defaultCilPrinter stderr 2 s);
  Printf.fprintf stderr "\n"

(* generates a callstmt and function definition from a stmt list *)
let gen_func_creator fd nexti =
  (fun stmts loc ->
    let blockfunc = (buildGFun fd nexti loc {battrs = fd.sbody.battrs; bstmts = stmts} ) in
     (match blockfunc with
     | GFun(fn, floc) -> 
         let callstmt = func2call_stmt fn.svar (List.hd stmts).labels floc in
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

let move_condition_to_func expr loc fd nexti =  
  let make_unique_function_name_for_expr v = {
    vname       = v.vname ^ "_" ^ (string_of_int (nexti ()));
    vtype       = TInt(IInt, []);
    vstorage    = Static;
    vglob       = v.vglob;
    vinline     = v.vinline;
    vattr       = v.vattr;
    vdecl       = v.vdecl;
    vid         = v.vid;
    vaddrof     = v.vaddrof;
    vreferenced = v.vreferenced;
    vdescr      = v.vdescr;
    vdescrpure  = v.vdescrpure;} in
  (func2call_stmt fd.svar [] loc), 
  GFun({ 
        svar       = make_unique_function_name_for_expr fd.svar;
        sformals   = [];
        slocals    = [];
        smaxid     = fd.smaxid;
        sbody      = {battrs = fd.sbody.battrs; bstmts = [ (instr2plain_stmt (Return( Some expr, loc)))]};
        smaxstmtid = fd.smaxstmtid;
        sallstmts  = fd.sallstmts; }, loc)

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

let rec split_block width (body : block) (loc : location) func_creator fd nexti =
  let rec split_stmt s loc func_creator =
    match s.skind with
    | Block(b) -> 
        let nb, nf = split_block width b loc func_creator fd nexti in
        let st = instr2stmt s (Block(nb)) in
        st, nf
    | Loop(b, loc, s1, s2) -> 
      (* dump_stmt "Loop" h; *)
      let new_body, nfuncs = split_block width b loc func_creator fd nexti in
      let st = instr2stmt s (Loop(new_body, loc, s1, s2)) in
      st, nfuncs
    | Switch(exp1, b, stmts, loc) ->
        s, []
    | Instr(is) ->
        let l1, l2 = split_list is in
        let c1, f1 = func_creator [ (instr2stmt s (Instr(l1))) ] loc in
        let c2, f2 = func_creator [ (instr2stmt s (Instr(l2))) ] loc in
        let nb = {battrs = []; bstmts = [c1; c2]} in
        let nst = instr2stmt s (Block(nb)) in
        let nfuncs = [f1; f2] in
        nst, nfuncs
    | If(expr, _then, _else, loc) ->
      (* dump_stmt "If" h; *)
      let tnew_body, tnfuncs = split_block width _then loc func_creator fd nexti in
      let enew_body, enfuncs = split_block width _else loc func_creator fd nexti in
(*
      let nexpr, nstmt, efunc = move_condition_to_func expr loc fd nexti in 
      let assign_instr = instr2stmt s (
*)
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
    let chunk_size = 200 in
    match stmts with 
    (* base case, empty list  *)
    | [] -> 
       (match newstmts with
        | [] -> { battrs = body.battrs; bstmts = (List.rev oldstmts)}, (List.rev funcs)
        | _  -> let newcall, func = func_creator (List.rev newstmts) loc in 
                  { battrs = body.battrs; bstmts = (List.rev (newcall :: oldstmts))}, (List.rev ( func :: funcs)))

    (* statement has label, make noop stmt with label *)
    | h :: t when (haslabel h) -> 
   (*   dump_stmt "hasLabel" h; *)

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
      | [] -> bw t [ns] ( noop :: oldstmts) width funcs
      | _  -> 
       let newcall, func = func_creator (List.rev newstmts) loc in 
       bw t [ns] (noop :: (newcall :: oldstmts)) width (func :: funcs))


    (* current statement is splittable *)
    | h :: t when not (hasUnsplittable h) ->
(*      dump_stmt "splittable" h; *)
       (match left with
        | 0 -> 
          let newcall, func = func_creator (List.rev newstmts) loc in 
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
        let ns, nf = (if (stmt_text_len h) > chunk_size  then
          split_stmt h loc func_creator
        else
          h, []) in 
       (match newstmts with
        | [] -> bw t [] (ns :: oldstmts) width (List.append nf funcs)
        | _  -> 
          let newcall, func = func_creator (List.rev newstmts) loc in 
          bw t [] (ns :: (newcall :: oldstmts)) width (List.append nf (func :: funcs))) in

    bw body.bstmts [] [] width []

let dump_func_to_file funcN fileN =
  let channel = open_out fileN.fileName in
    (* remove unuseds except for root funcN which may be static *)
(*
    Rmtmps.removeUnusedTemps ~isRoot:(fun x -> (Rmtmps.isExportedRoot x) || x == funcN) fileN;
*)
    dumpFile defaultCilPrinter channel fileN.fileName fileN;
    close_out channel;
    fileN.fileName

let make_formal_assigns fs =
  let rec mkfa fs nfs = match fs with
  | [] -> Instr (List.rev nfs)
  | h :: t ->
    let nh = Set(((Var(h)), NoOffset), (Lval((Var(prepend_ h)), NoOffset)), h.vdecl) in
    mkfa t (nh :: nfs) in
  mkfa fs []

(* Split functions into their own translation units *)
let splitFuncsToTU file =
  let channel = open_out "CILOUT.DUMP" in
    dumpFile defaultCilPrinter channel "CILOUT.DUMP" file;
    close_out channel;
  let otherGlobals = List.filter (fun x -> match x with
      Cil.GFun(fd ,_) -> false
      | a -> true) 
    file.globals in 
  Cil.foldGlobals file (fun fns func -> match func with
    Cil.GFun(fd, loc) ->
      Printf.fprintf stderr "============== %s ==============\n" fd.svar.vname;
        let nexti = (genNextCounter ()) in 
        let fun_creator = (gen_func_creator fd nexti) in
        let new_body, funcs = (split_block 2 fd.sbody loc fun_creator fd nexti) in
        let formals_assigns = (instr2stmt2 [] (make_formal_assigns fd.sformals)) in
        (* build new Cil.GFun for func *)
        let funcN = GFun({ 
          svar       = remove_static fd.svar;
          sformals   = [];
          slocals    = [];
          smaxid     = fd.smaxid;
          sbody      = {battrs = new_body.battrs; bstmts = ( formals_assigns :: new_body.bstmts)};
          smaxstmtid = fd.smaxstmtid;
          sallstmts  = fd.sallstmts; }, loc)
        and varinfos2GVarDecls vs = List.map (fun x -> GVarDecl((make_static x), loc)) vs in
        (* build new Cil.file for func *)
          let fileN = { fileName = file.fileName ^ "_" ^ fd.C.svar.C.vname ^ ".c";
                        globals = (List.append (List.append (List.append (List.append
                          otherGlobals 
                          (varinfos2GVarDecls fd.sformals)) 
                          (varinfos2GVarDecls fd.slocals)) 
                          (List.rev funcs))
                          [funcN]);
                        globinit = None; 
                        globinitcalled = false; } in
            dump_func_to_file funcN fileN ;
            fileN.fileName :: fns
    | _ -> fns) []



let dosplitter file =
  ignore (Partial.calls_end_basic_blocks file) ; 
  ignore (Partial.globally_unique_vids file) ; 
  make_make_file (splitFuncsToTU file)

(*
  Cil.iterGlobals file (fun glob -> match glob with
    Cil.GFun(fd ,_) ->
      Cil.prepareCFG fd ;
      (* jc: blockinggraph depends on this "true" arg *)
      ignore (Cil.computeCFGInfo fd true);
      ignore (Cfg.printCfgFilename (Printf.sprintf "CFG_%s.dot" fd.C.svar.C.vname) fd);
      ignore (RD.computeRDs fd)
      
    | _ -> ())
    *)

let feature : featureDescr =
  { fd_name = "splitter";
    fd_enabled = Cilutil.logWrites;
    fd_description = "Split function CFGs";
    fd_extraopt = [];
    fd_doit = dosplitter;
    fd_post_check = true;
  }

