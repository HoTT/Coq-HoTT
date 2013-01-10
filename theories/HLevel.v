(** * H-Levels *)

Require Import Overture Funext Contractible Equivalences types.Paths.
Local Open Scope equiv_scope.

Generalizable Variable A.

(** A contractible space has h-level zero, of course. *)
Instance Contr_hlevel_0 (A : Type) : is_hlevel 0 A -> Contr A
  := idmap.
  
(** H-levels are cummulative. *)
Lemma hlevel_succ (n : nat) :
  forall A : Type, is_hlevel n A -> is_hlevel (S n) A.
Proof.
  induction n as [| n I].
  - intros A H x y.
    unfold is_hlevel in H.
    apply contr_paths_contr.
  - intros A H x y p q.
    apply I.
    apply H.
Qed.

(** Equivalence preserves h-levels (this is, of course, trivial with univalence). *)
Theorem hlevel_equiv (n : nat) : forall (A B : Type), (A <~> B) -> is_hlevel n A -> is_hlevel n B.
Proof.
  induction n as [| n I].
  - apply Contr_equiv_contr.
  - intros A B e H x y.
    fold is_hlevel.
    apply I with (A := (e^-1 x = e^-1 y)).
    + apply equiv_inverse.
      apply @equiv_ap.
      apply @isequiv_inverse.
    + apply H.
Qed.
