(* -*- mode: coq; mode: visual-line -*- *)

Require Import Basics Types.
Require Import TruncType.
Require Import Truncations.Core Modalities.Modality Modalities.Descent.

(** ** Separatedness and path-spaces of truncations *)

Section SeparatedTrunc.

Local Open Scope subuniverse_scope.

(** The [n.+1]-truncation modality consists of the separated types for the [n]-truncation modality. *)
Global Instance O_eq_Tr (n : trunc_index)
  : Tr n.+1 <=> Sep (Tr n).
Proof.
  split; intros A A_inO.
  - intros x y; exact _.
  - exact _.
Defined.

(** It follows that [Tr n <<< Tr n.+1].  However, it is easier to prove this directly than to go through separatedness. *)
Global Instance O_leq_Tr (n : trunc_index)
  : Tr n <= Tr n.+1.
Proof.
  intros A ?; exact _.
Defined.

Global Instance O_strong_leq_Tr (n : trunc_index)
  : Tr n << Tr n.+1.
Proof.
  srapply O_strong_leq_trans_l.
Defined.

(** For some reason, this causes typeclass search to spin. *)
Local Instance O_lex_leq_Tr `{Univalence} (n : trunc_index)
  : Tr n <<< Tr n.+1.
Proof.
  intros A; unshelve econstructor; intros P' P_inO;
    pose (P := fun x => Build_TruncType n (P' x)).
  - refine (Trunc_rec P).
  - intros; simpl; exact _.
  - intros; cbn. reflexivity.
Defined.

Definition path_Tr {n A} (x y : A)
  : Tr n (x = y) -> (tr x = tr y :> Tr n.+1 A)
  := path_OO (Tr n.+1) (Tr n) x y.

Definition equiv_path_Tr@{u v} `{Univalence} {n} {A : Type@{u}} (x y : A)
  : Tr n (x = y) <~> (tr x = tr y :> Tr n.+1 A)
  := @equiv_path_OO@{u u u u u u u u v} (Tr n.+1) (Tr n) _
       (O_lex_leq_Tr@{v u} n) _ _ x y.

End SeparatedTrunc.

