open Pretty
open Cil
open Splitter_utils
module C = Cil
module RD = Reachingdefs

exception TryStmtNotSupported

let genNextCounter = function () ->
  let ni = ref 0 in
    function () -> ni := (!ni + 1); !ni


(* print list of strings to stderr *)
let make_make_file lst =
  let rec w o lst = match lst with
  | [] -> ()
  | h :: t -> (fprintf o "%s\n" h); w o t in
    w stderr lst

let remove_static v = {
  vname       = v.vname;
  vtype       = v.vtype;
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

(* build a GFun from a fundec, i generator, loc stmt list *)
let buildGFun (fd : fundec) nexti (loc : location) (b : block) : global =
  let appendVarName v = {
    vname       = v.vname ^ "_" ^ (string_of_int (nexti ()));
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

let instr2stmt stmt x = {labels = stmt.labels; skind = x; sid = 0; succs = []; preds = []}
let empty_stmt = {labels = []; skind = Instr([]); sid = 0; succs = []; preds = []}


let filter_case s = {
  labels = List.filter (function x -> match x with 
                          | Case(e, l) -> false 
                          | _ -> true) s.labels;
  skind  = s.skind; 
  sid    = s.sid;
  succs  = s.succs; 
  preds  = s.preds}

(* generates a callstmt and function definition from a block node *)
let block2callsite_and_func fd nexti loc stmt b =
  (* build a stmt from a call node *)
  let call2stmt call = instr2stmt stmt (Instr [call]) in
  let blockfunc = (buildGFun fd nexti loc b) in
   match blockfunc with
   | GFun(fn, ln) -> let callstmt = call2stmt (Call( None, Lval( Var(fn.svar), NoOffset), [], ln)) in
         (callstmt, blockfunc)
   | _ -> raise Not_A_GFun_NEVER_GET_HERE

let dump_stmt d s =
  Printf.fprintf stderr "*** %s *** " d;
  (dumpStmt defaultCilPrinter stderr 2 s);
  Printf.fprintf stderr "\n"

let gen_func_creator fd nexti =
  (fun stmts loc ->
    let call2stmt call = instr2stmt (List.hd stmts) (Instr [call]) in
    let blockfunc = (buildGFun fd nexti loc {battrs = fd.sbody.battrs; bstmts = stmts} ) in
     (match blockfunc with
     | GFun(fn, ln) -> let callstmt = call2stmt (Call( None, Lval( Var(fn.svar), NoOffset), [], ln)) in
           (callstmt, blockfunc)
     | _ -> raise Not_A_GFun_NEVER_GET_HERE))

let stmt_text_len (s : stmt) : int =
  String.length (Pretty.sprint 80 (printStmt defaultCilPrinter () s))

let rec split_block width (body : block) (loc : location) func_creator =
  let rec split_stmt s loc func_creator =
    match s.skind with
    | Block(b) -> 
        let nb, nf = split_block width b loc func_creator in
        let st = instr2stmt s (Block(nb)) in
        st, nf
    | Loop(b, loc, s1, s2) -> 
      (* dump_stmt "Loop" h; *)
      let new_body, nfuncs = split_block width b loc func_creator in
      let st = instr2stmt s (Loop(new_body, loc, s1, s2)) in
      st, nfuncs
    | Switch(exp1, b, stmts, loc) ->
        s, []
    | Instr(is) ->
      (* dump_stmt "Instr" h; *)
        let nb, nf = split_block width { battrs = []; bstmts = [ (filter_case s) ] } loc func_creator in
        let st = instr2stmt s (Block(nb)) in
        st, nf
    | If(expr, _then, _else, loc) ->
      (* dump_stmt "If" h; *)
      let tnew_body, tnfuncs = split_block width _then loc func_creator in
      let enew_body, enfuncs = split_block width _else loc func_creator in
      let st = instr2stmt s (If(expr, tnew_body, enew_body, loc)) in
        st, (List.append tnfuncs enfuncs)
    | Break(loc)    -> s, []
    | Continue(loc) -> s, []
    | Goto(a, b)    -> s, []
    | Return(a, b)  -> s, []
    | TryFinally(b, b2, loc) -> raise TryStmtNotSupported; s, []
    | TryExcept(b, ilexpp, b2, loc) -> raise TryStmtNotSupported; s, [] in

  let rec bw (stmts : stmt list) (newstmts : stmt list) (oldstmts : stmt list) (left : int) (funcs : global list) =
    let chunk_size = 300 in
    match stmts with 
    | [] -> 
       (match newstmts with
        | [] -> { battrs = body.battrs; bstmts = (List.rev oldstmts)}, (List.rev funcs)
        | _  -> let newcall, func = func_creator newstmts loc in 
                  { battrs = body.battrs; bstmts = (List.rev (newcall :: oldstmts))}, (List.rev ( func :: funcs)))
    | h :: t when not (hasUnsplittable h) ->
       (match left with
        | 0 -> 
          let newcall, func = func_creator newstmts loc in 
          bw (h :: t) [] (newcall :: oldstmts) width (func :: funcs)
        | _ -> 
          begin
          if (stmt_text_len h) > chunk_size  then 
            let newstmt , nfuncs = split_stmt h loc func_creator in
            bw t [] (newstmt :: oldstmts) width (List.append nfuncs funcs)
          else
            bw t (h :: newstmts) oldstmts (left - 1) funcs
          end)
    | h :: t -> 
        let ns, nf = (if (stmt_text_len h) > chunk_size  then
          split_stmt h loc func_creator
        else
          h, []) in 
       (match newstmts with
        | [] -> bw t [] (ns :: oldstmts) width (List.append nf funcs)
        | _  -> 
          let newcall, func = func_creator newstmts loc in 
          bw t [] (ns :: (newcall :: oldstmts)) width (List.append nf (func :: funcs))) in

    bw body.bstmts [] [] width []

let dump_func_to_file funcN fileN =
  let channel = open_out fileN.fileName in
    (* remove unuseds except for root funcN which may be static *)
    Rmtmps.removeUnusedTemps ~isRoot:(fun x -> (Rmtmps.isExportedRoot x) || x == funcN) fileN;
    dumpFile defaultCilPrinter channel fileN.fileName fileN;
    close_out channel;
    fileN.fileName


(*
class hasInputGoto file = object (self)
  inherit nopCilVisitor
  
  val bool mutable present;

  method vstmt s = match s with | Goto(sr, loc) -> match !ref with
    {labels = ls;} when (List.fold (function a x -> a || match x with | Label(_,_,b) -> b) false ls)
    present := true;
    
  | _ -> DoChildren
end
*)
let rec hasGoto lst f =
  match lst with
    | [] -> f
    | h :: t -> 
      match h with 
        | Label(_,_,true) -> true
        | _ -> hasGoto t f

let rec hasBCorG (bodyb : block) : bool =
  let rec dbw (stmts : stmt list) : bool = match stmts with
  | [] -> false
  | h :: t -> match h.skind with
    | Block(b)                    -> hasBCorG b || dbw t
    | Loop(b, loc, s1, s2)        -> hasBCorG b || dbw t
    | Switch(expr, b, stmts, loc) -> hasBCorG b || dbw t
    | Instr(is)                   -> dbw t
    | If(expr, _then, _else, loc) -> hasBCorG _then || hasBCorG _else|| dbw t
    | Break(loc)                  -> true
    | Continue(loc)               -> true
    | Return(expr,loc)            -> dbw t
    | Goto(stmtref, loc)          -> (match !stmtref with
      | {labels = ls;} when (hasGoto ls false) -> true
      | _ -> dbw t)
    | TryFinally(b, b2, loc)        -> dump_stmt "Other"  h; dbw t
    | TryExcept(b, ilexpp, b2, loc) -> dump_stmt "Other"  h; dbw t  in
    dbw bodyb.bstmts

(* Split functions into their own translation units *)
let splitFuncsToTU file =
  let otherGlobals = List.filter (fun x -> match x with
      Cil.GFun(fd ,_) -> false
      | a -> true) 
    file.globals in 
  Cil.foldGlobals file (fun fns func -> match func with
    Cil.GFun(fd, loc) ->
      Printf.fprintf stderr "============== %s ==============\n" fd.svar.vname;
      let new_body, funcs = match (hasBCorG fd.sbody) with
      | true -> 
          (* Printf.fprintf stderr "^^^^^^^^^^^^^^ has BCorG  ^^^^^^^^^^^^^^\n";
           *)
          fd.sbody, [] 
      | false -> (split_block 2 fd.sbody loc (gen_func_creator fd (genNextCounter ()))) in
        (* build new Cil.GFun for func *)
        let funcN = GFun({ 
          svar       = remove_static fd.svar;
          sformals   = [];
          slocals    = [];
          smaxid     = fd.smaxid;
          sbody      = new_body;
          smaxstmtid = fd.smaxstmtid;
          sallstmts  = fd.sallstmts; }, loc)
        and varinfos2GVarDecls vs = List.map (fun x -> GVarDecl(x, loc)) vs in
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

