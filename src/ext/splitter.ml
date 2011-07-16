open Pretty
open Cil
open Splitter_utils
module C = Cil
module RD = Reachingdefs

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


let rec split_block width (body : block) (loc : location) func_creator =
  let rec bw (stmts : stmt list) (newstmts : stmt list) (oldstmts : stmt list) (left : int) (funcs : global list) =
    match stmts with 
    | [] -> ({ battrs = body.battrs; bstmts = (List.rev newstmts)}, (List.rev funcs)) 
    | h :: t when not (stmtHasReturn h) ->
        bw t (h :: newstmts) oldstmts (left - 1) funcs
    | h :: t -> 
        (match newstmts with
        | [] -> bw t (h :: oldstmts) [] width funcs
        | nb -> 
          let newcall, func = func_creator newstmts loc in 
            bw t (h :: (newcall :: oldstmts)) [] width (func :: funcs)) in

    bw body.bstmts [] [] width []

let rec split_block2 fd body loc nexti =
  (* split_block2 worker *)
  let rec dbw (stmts : stmt list) (funcs : global list)  (nstmts : stmt list) = match stmts with
  | [] -> ({ battrs = fd.sbody.battrs; bstmts = (List.rev nstmts)}, (List.rev funcs))
  | h :: t -> match h.skind with
  | Block(b) -> 
      dump_stmt "Block" h;
      let callstmt, func = block2callsite_and_func fd nexti loc h b in
        dbw t (func :: funcs) (callstmt :: nstmts)
  | Loop(b, loc, s1, s2) -> 
      dump_stmt "Loop" h;
      let new_body, nfuncs = split_block2 fd b loc nexti in
      let st = instr2stmt h (Loop(new_body, loc, s1, s2)) in
        dbw t (List.append nfuncs funcs) (st :: nstmts)
  | Switch(exp1, b, stmts, loc) ->
      dump_stmt "Switch" h;
      let new_body, nfuncs = split_block2 fd b loc nexti in
      let st = instr2stmt h (Switch(exp1, new_body, stmts, loc)) in
        dbw t (List.append nfuncs funcs) (st :: nstmts)
  | Instr(is) ->
      dump_stmt "Instr" h ;
      let callstmt, func = block2callsite_and_func fd nexti loc h { battrs = []; bstmts = [ (filter_case h) ] } in
        dbw t (func :: funcs) (callstmt :: nstmts)
  | If(expr, _then, _else, loc) ->
      dump_stmt "If" h;
      let tnew_body, tnfuncs = split_block2 fd _then loc nexti in
      let enew_body, enfuncs = split_block2 fd _else loc nexti in
      let st = instr2stmt h (If(expr, tnew_body, enew_body, loc)) in
        dbw t (List.append (List.append tnfuncs enfuncs) funcs) (st :: nstmts)
  | Break(loc)    -> dump_stmt "Break"    h; dbw t funcs (h :: nstmts)
  | Continue(loc) -> dump_stmt "Continue" h; dbw t funcs (h :: nstmts)
  | Goto(a, b)    -> dump_stmt "Goto"     h; dbw t funcs (h :: nstmts)
  | Return(a, b)  -> dump_stmt "Return"   h; dbw t funcs (h :: nstmts)
  | TryFinally(b, b2, loc) -> dump_stmt "TryFinally"    h; dbw t funcs (h :: nstmts)
  | TryExcept(b, ilexpp, b2, loc) -> dump_stmt "TryExcept"    h; dbw t funcs (h :: nstmts) in
    dbw body.bstmts [] []

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
      | false -> (split_block 4 fd.sbody loc (gen_func_creator fd (genNextCounter ()))) in
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

