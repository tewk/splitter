open Pretty
open Cil
module C = Cil
module RD = Reachingdefs

let genNextCounter = function () ->
  let ni = ref 0 in
    function () -> ni := (!ni + 1); !ni


(* print list of strings to stderr *)
let make_make_file lst =
  let rec w o lst = match lst with
  | [] -> ()
  | h :: t -> (fprintf o "%s\n" h); w o t; () in
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

(* build a GFun from a fundec, name suffix (txt), loc stmt list *)
let buildGFun (fd : fundec) (txt : string) (loc : location) (b : block) : global =

  let appendVarName v txt = {
    vname       = v.vname ^ txt;
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
        svar       = appendVarName fd.svar txt;
        sformals   = [];
        slocals    = [];
        smaxid     = fd.smaxid;
        sbody      = b;
        smaxstmtid = fd.smaxstmtid;
        sallstmts  = fd.sallstmts; }, loc)

exception Not_A_GFun_NEVER_GET_HERE
exception GOTOS_NOT_ALLOWED_YET

let instr2stmt stmt x = {labels = stmt.labels; skind = x; sid = 0; succs = []; preds = []}


let filter_case s = {
  labels = List.filter (function x -> match x with 
                          | Case(e, l) -> false 
                          | _ -> true) s.labels;
  skind  = s.skind; 
  sid    = s.sid;
  succs  = s.succs; 
  preds  = s.preds}

(* generates a callstmt and function definition from a block node *)
let block2callsite_and_func fd txt loc stmt b =
  (* build a stmt from a call node *)
  let call2stmt call = instr2stmt stmt (Instr [call]) in
  let blockfunc = (buildGFun fd txt loc b) in
   match blockfunc with
   | GFun(fn, ln) -> let callstmt = call2stmt (Call( None, Lval( Var(fn.svar), NoOffset), [], ln)) in
         (callstmt, blockfunc)
   | _ -> raise Not_A_GFun_NEVER_GET_HERE


let rec deblockify fd body loc nexti =
  (* dump statement nodes *)
  let dumps d s =
    Printf.fprintf stderr "\n*** %s ***\n" d;
    (dumpStmt defaultCilPrinter stderr 2 s);
    Printf.fprintf stderr "\n"
   in
  (* deblockify worker *)
  let rec dbw (stmts : stmt list) (funcs : global list)  (nstmts : stmt list) = match stmts with
  | [] -> ({ battrs = fd.sbody.battrs; bstmts = (List.rev nstmts)}, (List.rev funcs))
  | ({skind  = Block(b) } as stmt) :: t -> 
      dumps "Block" stmt;
      let txt = ("_" ^ (string_of_int (nexti ()))) in
      let callstmt, func = block2callsite_and_func fd txt loc stmt b in
        dbw t (func :: funcs) (callstmt :: nstmts)
  | ({skind  = Loop(b, loc, s1, s2) } as h) :: t -> 
      dumps "Loop" h;
      let new_body, nfuncs = deblockify fd b loc nexti in
      let st = instr2stmt h (Loop(new_body, loc, s1, s2)) in
        dbw t (List.append nfuncs funcs) (st :: nstmts)
  | ({skind  = Switch(exp1, b, stmts, loc) } as h) :: t ->
      dumps "Switch" h;
      let new_body, nfuncs = deblockify fd b loc nexti in
      let st = instr2stmt h (Switch(exp1, new_body, stmts, loc)) in
        dbw t (List.append nfuncs funcs) (st :: nstmts)
  | ({skind  = Instr(is)} as stmt) :: t ->
      dumps "Instr" stmt;
      let txt = ("_" ^ (string_of_int (nexti ()))) in
      let callstmt, func = block2callsite_and_func fd txt loc stmt { battrs = []; bstmts = [ (filter_case stmt) ] } in
        dbw t (func :: funcs) (callstmt :: nstmts)
  | ({skind  = If(expr, _then, _else, loc) } as h) :: t ->
      dumps "If" h;
      let tnew_body, tnfuncs = deblockify fd _then loc nexti in
      let enew_body, enfuncs = deblockify fd _else loc nexti in
      let st = instr2stmt h (If(expr, tnew_body, enew_body, loc)) in
        dbw t (List.append (List.append tnfuncs enfuncs) funcs) (st :: nstmts)
  | ({skind  = Break(loc) }     as h) :: t -> dumps "Break"    h; dbw t funcs (h :: nstmts)
  | ({skind  = Continue(loc) }  as h) :: t -> dumps "Continue" h; dbw t funcs (h :: nstmts)
  | ({skind  = Goto(a, b) }     as h) :: t -> dumps "Goto"     h; dbw t funcs (h :: nstmts)
  | ({skind  = Return(a, b) }   as h) :: t -> dumps "Return"   h; dbw t funcs (h :: nstmts)
  | ({skind  = TryFinally(b, b2, loc)} as h) :: t -> dumps "Other"    h; dbw t funcs (h :: nstmts)
  | ({skind  = TryExcept(b, ilexpp, b2, loc)} as h) :: t -> dumps "Other"    h; dbw t funcs (h :: nstmts) in
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

let dump_stmt d s =
  Printf.fprintf stderr "*** %s *** " d;
  (dumpStmt defaultCilPrinter stderr 2 s);
  Printf.fprintf stderr "\n"

let rec findGotos fd body loc nexti =
  let rec dbw (stmts : stmt list)  = match stmts with
  | [] -> ({ battrs = fd.sbody.battrs; bstmts = []}, [])
  | ({skind = Block(b) }                    as h) :: t -> findGotos fd b loc nexti ; dbw t
  | ({skind = Loop(b, loc, s1, s2) }        as h) :: t -> findGotos fd b loc nexti ; dbw t
  | ({skind = Switch(expr, b, stmts, loc) } as h) :: t -> findGotos fd b loc nexti ; dbw t
  | ({skind = Instr(is)}                    as h) :: t -> dbw t
  | ({skind = If(expr, _then, _else, loc) } as h) :: t -> findGotos fd _then loc nexti ;
                                                          findGotos fd _else loc nexti ; dbw t
  | ({skind = Break(loc) }                  as h) :: t -> dump_stmt "Break" h; dbw t
  | ({skind = Continue(loc) }               as h) :: t -> dump_stmt "Continue" h; dbw t
  | ({skind = Return(expr,loc) }            as h) :: t -> dump_stmt "Return" h; dbw t
  | ({skind = Goto(stmtref, loc) }          as h) :: t -> (match !stmtref with
    | {labels = ls;} when (hasGoto ls false) -> dump_stmt "Goto" h; dbw t
    | _ -> dbw t)
  | ({skind = TryFinally(b, b2, loc)} as h) :: t -> dump_stmt "Other"    h; dbw t
  | ({skind = TryExcept(b, ilexpp, b2, loc)} as h) :: t -> dump_stmt "Other"    h; dbw t  in
    dbw body.bstmts

let rec hasBCorG (bodyb : block) : bool =
  let rec dbw (stmts : stmt list) : bool = match stmts with
  | [] -> false
  | h :: t -> match h.skind with
    | Block(b)                    -> hasBCorG b ; dbw t
    | Loop(b, loc, s1, s2)        -> hasBCorG b ; dbw t
    | Switch(expr, b, stmts, loc) -> hasBCorG b ; dbw t
    | Instr(is)                   -> dbw t
    | If(expr, _then, _else, loc) -> hasBCorG _then ; hasBCorG _else ; dbw t
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
      let new_body, funcs = match hasBCorG fd.sbody with
      | true -> 
          Printf.fprintf stderr "^^^^^^^^^^^^^^ has BCorG  ^^^^^^^^^^^^^^\n";
          fd.sbody, [] 
      | _ -> (deblockify fd fd.sbody loc (genNextCounter () )) in
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

