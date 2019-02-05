(** Conjugation operation that was put into [Paths] by Assia and Cyril.
   It is useful in group theory, but it is not so clear what it is for
   in HoTT. So we store it away here, in case someone needs it later. *)

Require Import HoTT.Basics.
Local Open Scope path_scope.

(** We shall use a conjugation-like operation which is not present in the standard library. *)
Definition conjp {A B : Type} {f g : A -> B} {x y : A} (r : forall x, f x = g x) (p : f x = f y) :
  g x = g y
  :=
  (r x)^ @ p @ r y.

(** Several lemmas about conjugation. Does this actually get used? *)

Definition conjp_concat {A : Type} (f g : A -> A) (r : forall x, f x = g x) {x y z : A}
  (p : f x = f y) (q : f y = f z) :
  conjp r (p @ q) = conjp r p @ (conjp r q).
Proof.
  unfold conjp.
  try repeat (rewrite concat_p_pp).
  rewrite concat_pp_V.
  reflexivity.
Qed.

Lemma ap_to_conjp {A B : Type} {f g : A -> B} (p : forall x, f x = g x) {x y : A} (q : x = y) :
  ap g q = conjp p (ap f q).
Proof.
  destruct q.  unfold conjp.  simpl.
  transitivity ((p x)^ @ p x).
  - symmetry; apply concat_Vp.
  - apply whiskerR.  symmetry; apply concat_p1.
Qed.

Lemma conjp_ap {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  conjp p (ap f q) = q.
Proof.
  destruct q.  unfold conjp.  simpl.
  transitivity ((p x)^ @ p x).
  - apply whiskerR.  apply concat_p1.
  - apply concat_Vp.
Qed.

Lemma ap1_to_conjp {A : Type} {f : A -> A} (p : forall x, idmap x = f x) {x y : A} (q : x = y) :
  ap f q = conjp p q.
Proof.
  transitivity (conjp p (ap idmap q)).
  - apply ap_to_conjp.
  - apply ap; apply ap_idmap.
Defined.

(* TEMPORARILY COMMENTED OUT.
Lemma conjp_ap_cancel {A B : Type} {f : A -> B} {g : B -> A}
                (p : forall x, g (f x) = x) {x y : A} (q : x = y) :
      conjp p (ap g (ap f q)) = q.
Proof.
  transitivity (conjp p (ap (compose g f) q)).
  apply ap.  symmetry.  apply (ap_compose f g q).
  (* Todo: give, for here, a lemma that [conjp] preserves homotopy. *)
Defined.

(* Was not in the original file ? *)
Lemma conj_canV {A B : Type} {f : A -> B} {g : B -> A} (p : forall x, x = g (f x))
      {x y : A} (q : x = y) :
      ap g (ap f q) = conjp p q.
Proof.
  destruct q.
  symmetry; apply concat_Vp.
Defined.
*)
