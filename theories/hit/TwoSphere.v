(* -*- mode: coq; mode: visual-line -*- *)

(** * Theorems about the 2-sphere [S²]. *)

Require Import HoTT.Basics HSet.
Require Import types.Paths types.Forall types.Arrow types.Universe types.Empty types.Unit.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

(* ** Definition of the circle. *)

Module Export TwoSphere.

Private Inductive S2 : Type0 :=
| base : S2.

Axiom surf : idpath base = idpath base.

Definition S2_rect (P : S2 -> Type) (b : P base) (l : transport2 P surf b = idpath b)
  : forall (x:S2), P x
  := fun x => match x with base => fun _ => b end l.

Axiom S2_rect_beta_loop
  : forall (P : S2 -> Type) (b : P base) (l : transport2 P surf b = idpath b),
      apD02 (S2_rect P b l) surf = l^ @ (concat_p1 _)^.

End TwoSphere.

(* ** The non-dependent eliminator *)

Definition S2_rectnd (P : Type) (b : P) (l : idpath b = idpath b)
  : S2 -> P
  := S2_rect (fun _ => P) b ((concat_p1 _)^ @ (transport2_const surf b)^ @ l).

(** TODO: Write the non-dependent eliminator.  It's probably something like
<<
Definition S1_rectnd_beta_loop (P : Type) (b : P) (l : idpath b = idpath b)
: ap02 (S2_rectnd P b l) surf = l^ @ (concat_p1 _)^.
Proof.
  unfold S2_rectnd.
  refine (cancelL (transport2_const surf b)^ _ _ _).
  refine (cancelL ((concat_p1 (transport2 (fun _ : S2 => P) surf b))^) _ _ _).
...
>>
*)
