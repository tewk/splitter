open Pretty
open Cil
module C = Cil
module RD = Reachingdefs

(* print list of strings to stderr *)
let make_make_file lst =
  let rec w o lst = match lst with
  | [] -> ()
  | h :: t -> fprintf o "%s\n" h; w o t in
    w stderr lst

let remove_static v = {
  vname       = v.vname;
  vtype       = v.vtype;
  vstorage    = (match v.vstorage with
                  | Static -> (Printf.fprintf stderr "%s is STATIC\n" v.vname) ; NoStorage
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

(* build a GFun from a fundec, name suffix (txt), loc stmt list *)
let buildGFun (fd : fundec) (txt : string) (loc : location) (b : stmt list) : global =

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
        sbody      = { battrs = fd.sbody.battrs; bstmts = b };
        smaxstmtid = fd.smaxstmtid;
        sallstmts  = fd.sallstmts; }, loc)


exception Not_A_GFun_NEVER_GET_HERE;;
exception GOTOS_NOT_ALLOWED_YET;;

let instr2stmt x = {labels = []; skind = x; sid = 0; succs = []; preds = []};;

(* generates a callstmt and function definition from a block node *)
let block2callsite_and_func fd txt loc lofstmts =
  (* build a stmt from a call node *)
  let call2stmt call = instr2stmt (Instr [call]) in
  let blockfunc = (buildGFun fd txt loc lofstmts) in
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
      let callstmt, func = block2callsite_and_func fd txt loc [stmt] in
        dbw t (func :: funcs) (callstmt :: nstmts)
  | ({skind  = Loop(b, loc, s1, s2) } as h) :: t -> 
      dumps "Loop" h;
      let new_body, nfuncs = deblockify fd b loc nexti in
      let st = instr2stmt (Loop(new_body, loc, s1, s2)) in
        dbw t (List.append nfuncs funcs) (st :: nstmts)
  | ({skind  = Switch(exp1, b, stmts, loc) } as h) :: t ->
      dumps "Switch" h;
      let new_body, nfuncs = deblockify fd b loc nexti in
      let st = instr2stmt (Switch(exp1, new_body, stmts, loc)) in
        dbw t (List.append nfuncs funcs) (st :: nstmts)
  | ({skind  = Instr(is)} as stmt) :: t ->
      dumps "Instr" stmt;
      let txt = ("_" ^ (string_of_int (nexti ()))) in
      let callstmt, func = block2callsite_and_func fd txt loc [stmt] in
        dbw t (func :: funcs) (callstmt :: nstmts)
  | ({skind  = Break(loc) }     as h) :: t -> dumps "Break"    h; dbw t funcs (h :: nstmts)
  | ({skind  = Continue(loc) }  as h) :: t -> dumps "Continue" h; dbw t funcs (h :: nstmts)
  | ({skind  = If(a, b, c, d) } as h) :: t -> dumps "If"       h; dbw t funcs (h :: nstmts)
  | ({skind  = Goto(a, b) }     as h) :: t -> dumps "Goto"     h; raise GOTOS_NOT_ALLOWED_YET ; dbw t funcs (h :: nstmts)
  | ({skind  = Return(a, b) }   as h) :: t -> dumps "Return"   h; dbw t funcs (h :: nstmts)
  | h :: t                                 -> dumps "Other"    h; dbw t funcs (h :: nstmts) in
    dbw body.bstmts [] []

(* Split functions into their own translation units *)
let splitFuncsToTU file =
  let otherGlobals = List.filter (fun x -> match x with
      Cil.GFun(fd ,_) -> false
      | a -> true) 
    file.globals in 
  Cil.foldGlobals file (fun fns func -> match func with
    Cil.GFun(fd, loc) ->
      let ni = ref 0 in
      let nexti = function () -> (ni := (!ni + 1)); !ni in 

      Printf.fprintf stderr "\n\n==============\n%s\n==============\n\n" fd.svar.vname;
      let new_body, funcs = deblockify fd fd.sbody loc nexti in
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
        let oldname = (String.sub file.fileName 2 ((String.length file.fileName) - 2)) in
        let fileN = { fileName = fd.C.svar.C.vname ^ "_" ^ oldname ^ ".c"; 
                      globals = (List.append (List.append (List.append (List.append
                        otherGlobals 
                        (varinfos2GVarDecls fd.sformals)) 
                        (varinfos2GVarDecls fd.slocals)) 
                        funcs) 
                        [funcN]);
                      globinit = None; 
                      globinitcalled = false; } in
          let channel = open_out fileN.fileName in
             (* remove unuseds except for root funcN which may be static *)
             Rmtmps.removeUnusedTemps ~isRoot:(fun x -> (Rmtmps.isExportedRoot x) || x == funcN) fileN;
             dumpFile defaultCilPrinter channel fileN.fileName fileN;
             close_out channel;
             fileN.fileName :: fns
    | _ -> fns) []

let dosplitter file =
  ignore (Partial.calls_end_basic_blocks file) ; 
  ignore (Partial.globally_unique_vids file) ; 
  make_make_file (splitFuncsToTU file);
  Cil.iterGlobals file (fun glob -> match glob with
    Cil.GFun(fd ,_) ->
      Cil.prepareCFG fd ;
      (* jc: blockinggraph depends on this "true" arg *)
      ignore (Cil.computeCFGInfo fd true);
      ignore (Cfg.printCfgFilename (Printf.sprintf "CFG_%s.dot" fd.C.svar.C.vname) fd);
      ignore (RD.computeRDs fd)
    | _ -> ())

let feature : featureDescr =
  { fd_name = "splitter";
    fd_enabled = Cilutil.logWrites;
    fd_description = "Split function CFGs";
    fd_extraopt = [];
    fd_doit = dosplitter;
    fd_post_check = true;
  }

