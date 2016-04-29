
(* This file is free software, part of dolmen. See file "LICENSE" formore information *)

(** Dimacs language input *)

module type Term = Ast_dimacs.Term
module type Statement = Ast_dimacs.Statement

module Make
    (L : ParseLocation.S)
    (T : Term with type location := L.t)
    (S : Statement with type location := L.t and type term := T.t) :
  Language_intf.S with type statement = S.t
