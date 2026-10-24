From HoTT Require Import Basics Truncations.Core.

(** * Tests for [strip_truncations] *)

(** Hypotheses that are not truncations are skipped, and truncations hidden behind definitions such as [merely], [hexists], [hor] and [Tr] are stripped. *)
Goal forall (A B C : Type) (P : A -> Type),
    IsHProp B -> merely A -> hexists P -> hor A B -> Tr (-1) C -> Tr (-1) (A * sig P * (A + B) * C).
Proof.
  intros A B C P HB a p ab c.
  strip_truncations.
  (* All four truncated hypotheses keep their names and have been replaced by their underlying types. *)
  match type of a with A => idtac end.
  match type of p with sig P => idtac end.
  match type of ab with (A + B)%type => idtac end.
  match type of c with C => idtac end.
  (* The other hypotheses are untouched. *)
  match type of HB with IsHProp B => idtac end.
  exact (tr (a, p, ab, c)).
Defined.

(** A truncated hypothesis on which the goal depends is stripped using dependent elimination. *)
Goal forall (A : Type) (P : merely A -> Type), (forall x, IsHProp (P x))
  -> (forall a, P (tr a)) -> forall x, P x.
Proof.
  intros A P ? f x.
  strip_truncations.
  exact (f x).
Defined.

(** Truncations behind local definitions are stripped too. *)
Section Local.
  Context (A : Type).
  Let mA := merely A.

  Goal mA -> merely A.
  Proof.
    intro a.
    strip_truncations.
    exact (tr a).
  Defined.
End Local.

(** Let-bound hypotheses are not stripped. *)
Goal forall (A : Type), A -> merely A.
Proof.
  intros A a.
  pose (b := tr a : merely A).
  Fail strip_truncations.
Abort.

(** Nothing is stripped if the goal is not appropriately truncated. *)
Goal forall (A : Type), merely A -> Tr 0 A.
Proof.
  intros A a.
  Fail strip_truncations.
Abort.

Goal forall (A : Type), merely A -> A.
Proof.
  intros A a.
  Fail strip_truncations.
Abort.

(** A truncation of a higher level than the goal is not stripped, but the others are. *)
Goal forall (A B : Type) (n : trunc_index), Tr n A -> merely B -> merely B.
Proof.
  intros A B n a b.
  strip_truncations.
  let T := type of a in unify T (Tr n A).
  match type of b with B => idtac end.
  exact (tr b).
Defined.
