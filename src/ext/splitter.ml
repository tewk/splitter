open Pretty
open Cil
module C = Cil
module RD = Reachingdefs

let block_depth = ref 0

class dumpGlobalsVisitor file = object (self)
  inherit nopCilVisitor

(*
  method vinst i = kklog "ST %t" (function (m : unit) -> d_instr () i); DoChildren
  method vstmt s = kklog "ST %t" (function (m : unit) -> d_stmt  () s); DoChildren
*)

  method vinst i =
    match i with
      | Set(lval, expr, loc) -> DoChildren
      | Call(lval, Lval(Var(vi), io), args, loc) -> DoChildren
      | _ -> DoChildren

(*
  method vattr a =
    match a with
      Attr(n, ps) -> kklog "ATTR %a\n" d_attr a; SkipChildren
*)

  method vblock b = block_depth := !block_depth + 1; (* kklog "BLOCK %i\n" !block_depth;  *)
    let bpost children = block_depth := !block_depth - 1; children
      in ChangeDoChildrenPost(b, bpost);
(*
  method vfunc f = kklog "FUNC %s\n" f.svar.vname; DoChildren
*)

  method vglob g =
    match g with
      (*  GVarDecl(vi, loc) -> dumpgvarinfo "d" g vi loc *)
      (* | GVar(vi, b, loc) -> dumpgvarinfo "v" g vi loc *)
      (* | GFun(f, loc) -> kklog "FUNC "; kklogvarinfo f.svar loc; kklog "\n"; DoChildren *)
      | _ -> DoChildren
end

let dosplitter file =
  ignore (Partial.calls_end_basic_blocks file) ; 
  ignore (Partial.globally_unique_vids file) ; 
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

