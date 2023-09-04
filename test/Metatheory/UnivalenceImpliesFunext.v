From HoTT Require Import Basics.
From HoTT.Metatheory Require Import Core FunextVarieties UnivalenceImpliesFunext.

(** Note that only the codomain universe of [NaiveNondepFunext] is required to be univalent. *)
Check @Univalence_implies_FunextNondep@{j jplusone i max j max}
  : Univalence_type@{j jplusone} -> NaiveNondepFunext@{i j max}.
