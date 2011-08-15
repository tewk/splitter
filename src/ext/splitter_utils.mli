open Pretty
open Cil

(* split block until break, continue; *)
(* split case statements out *)
(* exception TryStmtNotSupported *)

val hasGotos: block -> bool

val loopHasC: block -> bool

val loopHasBorC: block -> bool

val hasReturn: block -> bool

val stmtsHaveReturns: stmt list -> bool

val stmtHasReturn: stmt -> bool

val countReturns: block -> int

val hasUnsplittable: stmt -> bool

val find_labels: stmt list -> stmt list -> stmt list

val fixup_labels: stmt list -> stmt list -> stmt list
