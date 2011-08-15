open Cil

(* split block until break, continue; *)
(* split case statements out *)
exception TryStmtNotSupported
exception LabelNotFound
exception FirstLabelDoesntMatch

let rec hasGoto lst f =
  match lst with
    | [] -> f
    | h :: t ->
      match h with
        | Label(_,_,true) -> true
        | _ -> hasGoto t f
let hasPrefix s p =
  let pl = String.length p in
  let sl = String.length s in
  if ((sl >= pl) && (String.compare p (String.sub s 0 pl)) == 0) then true
  else false

let hasLabel s =
  let rec hasRealLabel lst =
    match lst with
      | [] -> false
      | h :: t ->
        match h with
          | Label(name,_,true) -> not (hasPrefix name "_cont")
          | Label(name,_,_) -> not (hasPrefix name "case ")
          | _ -> hasRealLabel t in
  hasRealLabel s.labels

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
      | _ -> true (*dbw t*))
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

let rec hasRGs (stmts : stmt list ) : bool =
  let rec dbw (stmts : stmt list) : bool = match stmts with
  | [] -> false
  | h :: t ->
      (hasLabel h) ||
      match h.skind with
    | Block(b)                    -> hasRGs b.bstmts || dbw t
    | Loop(b, loc, s1, s2)        -> hasRGs b.bstmts || dbw t
    | Switch(expr, b, stmts, loc) -> hasRGs b.bstmts || dbw t
    | Instr(is)                   -> dbw t
    | If(expr, _then, _else, loc) -> hasRGs _then.bstmts || hasRGs _else.bstmts || dbw t
    | Break(loc)                  -> dbw t
    | Continue(loc)               -> dbw t
    | Return(expr,loc)            -> true
    | Goto(stmtref, loc)          -> (match !stmtref with
      | {labels = ls;} when (hasGoto ls false) -> true
      | _ -> true (*dbw t*))
    | TryFinally(b, b2, loc)        -> dump_stmt "TryFinally" h; raise TryStmtNotSupported; dbw t
    | TryExcept(b, ilexpp, b2, loc) -> dump_stmt "TryExcept"  h; raise TryStmtNotSupported; dbw t  in
    dbw stmts

let rec hasRGCs (stmts : stmt list) : bool =
  let rec dbw (stmts : stmt list) : bool = match stmts with
  | [] -> false
  | h :: t ->
      (hasLabel h) ||
      match h.skind with
    | Block(b)                    -> hasRGCs b.bstmts || dbw t
    | Loop(b, loc, s1, s2)        -> hasRGs  b.bstmts || dbw t
    | Switch(expr, b, stmts, loc) -> hasRGCs b.bstmts || dbw t
    | Instr(is)                   -> dbw t
    | If(expr, _then, _else, loc) -> hasRGCs _then.bstmts || hasRGCs _else.bstmts || dbw t
    | Break(loc)                  -> dbw t
    | Continue(loc)               -> true
    | Return(expr,loc)            -> true
    | Goto(stmtref, loc)          -> (match !stmtref with
      | {labels = ls;} when (hasGoto ls false) -> true
      | _ -> true (*dbw t*))
    | TryFinally(b, b2, loc)        -> dump_stmt "TryFinally" h; raise TryStmtNotSupported; dbw t
    | TryExcept(b, ilexpp, b2, loc) -> dump_stmt "TryExcept"  h; raise TryStmtNotSupported; dbw t  in
    dbw stmts

let rec hasUnsplittables (stmts : stmt list) : bool =
  let rec dbw (stmts : stmt list) : bool = match stmts with
  | [] -> false
  | h :: t -> 
      (hasLabel h) ||
      match h.skind with
    | Block(b)                    -> hasUnsplittables b.bstmts || dbw t
    | Loop(b, loc, s1, s2)        -> hasRGs b.bstmts  || dbw t
    | Switch(expr, b, stmts, loc) -> hasRGCs b.bstmts || dbw t
    | Instr(is)                   -> dbw t
    | If(expr, _then, _else, loc) -> hasUnsplittables _then.bstmts || hasUnsplittables _else.bstmts || dbw t
    | Break(loc)                  -> true
    | Continue(loc)               -> true
    | Return(expr,loc)            -> true
    | Goto(stmtref, loc)          -> (match !stmtref with
      | {labels = ls;} when (hasGoto ls false) -> true
      | _ -> true (*dbw t*))
    | TryFinally(b, b2, loc)        -> dump_stmt "TryFinally" h; raise TryStmtNotSupported; dbw t
    | TryExcept(b, ilexpp, b2, loc) -> dump_stmt "TryExcept"  h; raise TryStmtNotSupported; dbw t  in
    dbw stmts

let hasUnsplittable (s : stmt) : bool = hasUnsplittables [s]

let rec find_labels (stmts : stmt list) (lbls: stmt list) : stmt list =
  let labeled_stmt_lst s =
    match s.labels with
    | [] -> []
    | _  -> [ s ]  in
  let rec dbw (stmts : stmt list) (lbls: stmt list) : stmt list = match stmts with
  | [] -> lbls
  | h :: t -> 
      let hl = (labeled_stmt_lst h) in 
      match h.skind with
    | Block(b)                    -> dbw t (List.append (find_labels b.bstmts hl) lbls)
    | Loop(b, loc, s1, s2)        -> dbw t (List.append (find_labels b.bstmts hl) lbls)
    | Switch(expr, b, stmts, loc) -> dbw t (List.append (find_labels b.bstmts hl) lbls) 
    | Instr(is)                   -> dbw t (List.append hl lbls)
    | If(expr, _then, _else, loc) -> dbw t (List.append (List.append (find_labels _then.bstmts hl) (find_labels _else.bstmts [])) lbls)
    | Break(loc)                  -> dbw t (List.append hl lbls)
    | Continue(loc)               -> dbw t (List.append hl lbls)
    | Return(expr,loc)            -> dbw t (List.append hl lbls)
    | Goto(stmtref, loc)          -> dbw t (List.append hl lbls)
    | TryFinally(b, b2, loc)        -> dump_stmt "TryFinally" h; raise TryStmtNotSupported; dbw t []
    | TryExcept(b, ilexpp, b2, loc) -> dump_stmt "TryExcept"  h; raise TryStmtNotSupported; dbw t []  in

  dbw stmts []

let rec fixup_labels (stmts : stmt list) (lbls: stmt list) : stmt list =
  let rec find_labeled_statement s ls =
    match ls with
    | [] -> (Printf.fprintf stderr "%s\n" s); raise LabelNotFound
    | h :: t ->
        let rec find_label lls = match lls with
        | [] -> find_labeled_statement s t 
        | Label(str, _, _ ) :: lt when str = s -> h
        | lh :: lt -> find_label lt in 
        find_label h.labels in
  let rec dbw (stmts : stmt list) : stmt list = match stmts with
  | [] -> []
  | h :: t -> 
      match h.skind with
    | Block(b)                    -> (fixup_labels b.bstmts); dbw t
    | Loop(b, loc, s1, s2)        -> (fixup_labels b.bstmts); dbw t
    | Switch(expr, b, stmts, loc) -> (fixup_labels b.bstmts); dbw t
    | Instr(is)                   -> dbw t
    | If(expr, _then, _else, loc) -> fixup_labels _then.bstmts; fixup_labels _else.bstmts; dbw t
    | Break(loc)                  -> dbw t
    | Continue(loc)               -> dbw t
    | Return(expr,loc)            -> dbw t
    | Goto(stmtref,loc)           ->
        (match List.hd( (!stmtref).labels) with
        | Label(s, l, b) -> h.skind <- Goto( ref (find_labeled_statement s lbls), loc); dbw t
        | _ -> raise FirstLabelDoesntMatch)
    | TryFinally(b, b2, loc)        -> dump_stmt "TryFinally" h; raise TryStmtNotSupported; dbw t
    | TryExcept(b, ilexpp, b2, loc) -> dump_stmt "TryExcept"  h; raise TryStmtNotSupported; dbw t in

  dbw stmts
