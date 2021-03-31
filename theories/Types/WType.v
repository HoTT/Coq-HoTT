(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics.
Require Import Types.Forall Types.Sigma.

(** * Theorems about W-types (well-founded trees) *)

Inductive W (A : Type) (B : A -> Type) : Type :=
  w_sup (x : A) : (B x -> W A B) -> W A B.

Definition w_label {A B} (w : W A B) : A :=
  match w with
  | w_sup x y => x
  end.

Definition w_arg {A B} (w : W A B) : B (w_label w) -> W A B :=
  match w with
  | w_sup x y => y
  end.

Definition issig_W (A : Type) (B : A -> Type)
  : _ <~> W A B := ltac:(issig).

(** ** Paths *)

Definition equiv_path_wtype {A B} (z z' : W A B)
  : (w_label z;w_arg z) = (w_label z';w_arg z') :> {a : _ & B a -> W A B} <~> z = z'
  := (equiv_ap' (issig_W A B)^-1%equiv z z')^-1%equiv.

Definition equiv_path_wtype' {A B} (z z' : W A B)
  : {p : w_label z = w_label z' & w_arg z = w_arg z' o transport B p}
    <~> z = z'.
Proof.
  refine (equiv_path_wtype _ _ oE equiv_path_sigma _ _ _ oE _).
  apply equiv_functor_sigma_id.
  destruct z as [z1 z2], z' as [z1' z2'].
  cbn; intros p.
  destruct p.
  reflexivity.
Defined.

(** ** W-types preserve truncation *)

Global Instance istrunc_wtype `{Funext} {A B} {n : trunc_index} `{IsTrunc n.+1 A}
: IsTrunc n.+1 (W A B) | 100.
Proof.
  intros z; induction z as [a w].
  intro y; destruct y as [a0 w0].
  nrefine (trunc_equiv' _ (equiv_path_wtype' _ _)).
  rapply trunc_sigma.
  cbn; intro p.
  destruct p.
  apply (trunc_equiv' _ (equiv_path_forall _ _)).
Defined.
