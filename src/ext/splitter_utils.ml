open Pretty
open Cil

(* split block until break, continue; *)
(* split case statements out *)
exception TryStmtNotSupported

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

let rec hasGotos (bodyb : block) : bool =
  let rec dbw (stmts : stmt list) : bool = match stmts with
  | [] -> false
  | h :: t -> match h.skind with
    | Block(b)                    -> hasGotos b || dbw t
    | Loop(b, loc, s1, s2)        -> hasGotos b || dbw t
    | Switch(expr, b, stmts, loc) -> hasGotos b || dbw t
    | Instr(is)                   -> dbw t
    | If(expr, _then, _else, loc) -> hasGotos _then || hasGotos _else|| dbw t
    | Break(loc)                  -> dbw t
    | Continue(loc)               -> dbw t
    | Return(expr,loc)            -> dbw t
    | Goto(stmtref, loc)          -> (match !stmtref with
      | {labels = ls;} when (hasGoto ls false) -> true
      | _ -> dbw t)
    | TryFinally(b, b2, loc)        -> dump_stmt "TryFinally" h; raise TryStmtNotSupported; dbw t
    | TryExcept(b, ilexpp, b2, loc) -> dump_stmt "TryExcept"  h; raise TryStmtNotSupported; dbw t  in
    dbw bodyb.bstmts

let rec loopHasC (bodyb : block) : bool =
  let rec dbw (stmts : stmt list) : bool = match stmts with
  | [] -> false
  | h :: t -> match h.skind with
    | Block(b)                    -> loopHasC b || dbw t
    | Loop(b, loc, s1, s2)        -> dbw t
    | Switch(expr, b, stmts, loc) -> loopHasC b || dbw t
    | Instr(is)                   -> dbw t
    | If(expr, _then, _else, loc) -> loopHasC _then || loopHasC _else|| dbw t
    | Break(loc)                  -> dbw t
    | Continue(loc)               -> true
    | Return(expr,loc)            -> dbw t
    | Goto(stmtref, loc)          -> dbw t
    | TryFinally(b, b2, loc)        -> dump_stmt "TryFinally" h; raise TryStmtNotSupported; dbw t
    | TryExcept(b, ilexpp, b2, loc) -> dump_stmt "TryExcept"  h; raise TryStmtNotSupported; dbw t  in
    dbw bodyb.bstmts

let rec loopHasBorC (bodyb : block) : bool =
  let rec dbw (stmts : stmt list) : bool = match stmts with
  | [] -> false
  | h :: t -> match h.skind with
    | Block(b)                    -> loopHasBorC b || dbw t
    | Loop(b, loc, s1, s2)        -> dbw t
    | Switch(expr, b, stmts, loc) -> loopHasC b || dbw t
    | Instr(is)                   -> dbw t
    | If(expr, _then, _else, loc) -> loopHasBorC _then || loopHasBorC _else|| dbw t
    | Break(loc)                  -> true
    | Continue(loc)               -> true
    | Return(expr,loc)            -> dbw t
    | Goto(stmtref, loc)          -> dbw t
    | TryFinally(b, b2, loc)        -> dump_stmt "TryFinally" h; raise TryStmtNotSupported; dbw t
    | TryExcept(b, ilexpp, b2, loc) -> dump_stmt "TryExcept"  h; raise TryStmtNotSupported; dbw t  in
    dbw bodyb.bstmts

let rec hasReturn (bodyb : block) : bool =
  let rec dbw (stmts : stmt list) : bool = match stmts with
  | [] -> false
  | h :: t -> match h.skind with
    | Block(b)                    -> loopHasC b || dbw t
    | Loop(b, loc, s1, s2)        -> dbw t
    | Switch(expr, b, stmts, loc) -> loopHasC b || dbw t
    | Instr(is)                   -> dbw t
    | If(expr, _then, _else, loc) -> loopHasC _then || loopHasC _else|| dbw t
    | Break(loc)                  -> dbw t
    | Continue(loc)               -> dbw t
    | Return(expr,loc)            -> true
    | Goto(stmtref, loc)          -> dbw t
    | TryFinally(b, b2, loc)        -> dump_stmt "TryFinally" h; raise TryStmtNotSupported; dbw t
    | TryExcept(b, ilexpp, b2, loc) -> dump_stmt "TryExcept"  h; raise TryStmtNotSupported; dbw t  in
    dbw bodyb.bstmts

let rec stmtsHaveReturns (stmts : stmt list) : bool =
  let rec dbw (stmts : stmt list) : bool = match stmts with
  | [] -> false
  | h :: t -> match h.skind with
    | Block(b)                    -> stmtsHaveReturns b.bstmts || dbw t
    | Loop(b, loc, s1, s2)        -> stmtsHaveReturns b.bstmts || dbw t
    | Switch(expr, b, stmts, loc) -> stmtsHaveReturns b.bstmts || dbw t
    | Instr(is)                   -> dbw t
    | If(expr, _then, _else, loc) -> stmtsHaveReturns _then.bstmts || stmtsHaveReturns _else.bstmts || dbw t
    | Break(loc)                  -> dbw t
    | Continue(loc)               -> dbw t
    | Return(expr,loc)            -> true
    | Goto(stmtref, loc)          -> dbw t
    | TryFinally(b, b2, loc)        -> dump_stmt "TryFinally" h; raise TryStmtNotSupported; dbw t
    | TryExcept(b, ilexpp, b2, loc) -> dump_stmt "TryExcept"  h; raise TryStmtNotSupported; dbw t  in
    dbw stmts

let stmtHasReturn (s : stmt) : bool = stmtsHaveReturns [s]

let rec countReturns (bodyb : block) : int =
  let rec dbw (stmts : stmt list) (cnt : int) : int = match stmts with
  | [] -> cnt
  | h :: t -> match h.skind with
    | Block(b)                    -> dbw t (dbw b.bstmts cnt)
    | Loop(b, loc, s1, s2)        -> dbw t (dbw b.bstmts cnt)
    | Switch(expr, b, stmts, loc) -> dbw t (dbw b.bstmts cnt)
    | Instr(is)                   -> dbw t cnt
    | If(expr, _then, _else, loc) -> dbw t (dbw _else.bstmts (dbw _then.bstmts cnt))
    | Break(loc)                  -> dbw t cnt
    | Continue(loc)               -> dbw t cnt
    | Return(expr,loc)            -> dbw t (cnt + 1)
    | Goto(stmtref, loc)          -> dbw t cnt
    | TryFinally(b, b2, loc)        -> dump_stmt "TryFinally" h; raise TryStmtNotSupported; dbw t cnt
    | TryExcept(b, ilexpp, b2, loc) -> dump_stmt "TryExcept"  h; raise TryStmtNotSupported; dbw t cnt  in
    dbw bodyb.bstmts 0
