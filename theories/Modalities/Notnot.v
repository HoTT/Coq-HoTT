Require Import HoTT.Basics HoTT.Types Universes.HProp.
Require Import Modality.

Local Open Scope path_scope.

(** * The double negation modality *)

(** The operation sending [X] to [~~X] is a modality.  This is Exercise 7.12 in the book.  Note that it is (apparently) *not* accessible unless we assume propositional resizing. *)
Definition NotNot `{Funext} : Modality.
Proof.
  snrapply easy_modality.
  - intros X; exact (~~X).
  - exact @not_not_unit.
  - cbn beta; intros A B f z nBz.
    apply z; intros a.
    exact (f a (transport (fun x => ~ (B x))
                          (path_ishprop _ _)
                          nBz)).
  - cbn beta; intros A B f a.
    apply path_ishprop.
  - cbn beta; intros A z z'.
    refine (isequiv_iff_hprop _ _).
    intros; apply path_ishprop.
Defined.

(** By definition, the local types for this modality are the types such that [not_not_unit : P -> ~~P] is an equivalence.  These are exactly the stable propositions, i.e. those propositions [P] such that [~~P -> P]. *)
Definition inO_notnot `{Funext} (P : Type)
  : In NotNot P <~> (Stable P * IsHProp P)
  := equiv_isequiv_not_not_unit_stable_hprop P.
