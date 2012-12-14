(** Because we do not use the Coq standard library at all, we have
    to start from scratch. *)

Require Export Notations.
Require Export Logic.
Require Export Datatypes.
Require Export Coq.Init.Tactics.
Require Export Specif.

Add Search Blacklist "_admitted" "_subproof" "Private_".
