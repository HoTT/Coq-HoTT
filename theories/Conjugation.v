(** Conjugation operation that was put into [Paths] by Assia and Cyril.
   It is useful in group theory, but it is not so clear what it is for
   in HoTT. So we store it away here, in case someone needs it later. *)

Require Import Paths.

Import PathNotations.
Open Scope path_scope.

(** We shall use a conjugation-like operation which is not present in the standard library. *)
Definition conjp {A B : Type} {f g : A -> B} {x y : A} (r : forall x, f x = g x) (p : f x = f y) :
  g x = g y
  :=
  (r x)^-1 @ p @ r y.

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

Lemma pmap_to_conjp {A B : Type} {f g : A -> B} (p : forall x, f x = g x) {x y : A} (q : x = y) :
  pmap g q = conjp p (pmap f q).
Proof.
  destruct q.
  symmetry; apply concat_Vp.
Qed.

Lemma conjp_pmap {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  conjp p (pmap f q) = q.
Proof.
  destruct q.
  apply concat_Vp.
Qed.

Lemma pmap1_to_conjp {A : Type} {f : A -> A} (p : forall x, idmap x = f x) {x y : A} (q : x = y) :
  pmap f q = conjp p q.
Proof.
  destruct q.
  symmetry; apply concat_Vp.
Defined.

Lemma conjp_pmap_cancel {A B : Type} {f : A -> B} {g : B -> A}
                (p : forall x, g (f x) = x) {x y : A} (q : x = y) :
      conjp p (pmap g (pmap f q)) = q.
Proof.
  destruct q.
  apply concat_Vp.
Defined.

(* Was not in the original file ? *)
Lemma conj_canV {A B : Type} {f : A -> B} {g : B -> A} (p : forall x, x = g (f x))
      {x y : A} (q : x = y) :
      pmap g (pmap f q) = conjp p q.
Proof.
  destruct q.
  symmetry; apply concat_Vp.
Defined.
