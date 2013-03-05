(* -*- mode: coq; mode: visual-line -*- *)

(** * Theorems about the circle S^1 *)

Require Import Overture PathGroupoids Equivalences Trunc.
Require Import Paths Forall Arrow Universe.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

(* *** Definition of the circle. *)

Module Circle.

(* Local *)
Inductive S1 : Type :=
| base : S1.

Axiom loop : base = base.

Definition S1_rech (P : S1 -> Type) (b : P base) (l : loop # b = b)
  : forall (x:S1), P x
  := fun x => match x with base => b end.

Axiom S1_rech_beta_loop
  : forall (P : S1 -> Type) (b : P base) (l : loop # b = b),
  apD (S1_rech P b l) loop = l.

End Circle.

Import Circle.

(* *** The non-dependent eliminator *)

Definition S1_rechnd (P : Type) (b : P) (l : b = b)
  : S1 -> P
  := S1_rech (fun _ => P) b (transport_const _ _ @ l).

Definition S1_rechnd_beta_loop (P : Type) (b : P) (l : b = b)
  : ap (S1_rechnd P b l) loop = l.
Proof.
  unfold S1_rechnd.
  set (l' := transport_const loop b @ l).
  path_via ((transport_const loop _)^
    @ apD (S1_rech (fun _ => P) b l') loop).
  apply moveL_Vp.  apply symmetry, apD_const.
  apply moveR_Vp.  simpl.  fold l'.
  refine (S1_rech_beta_loop (fun _ => P) _ _).
Defined.

(* *** The loop space of the circle is the Integers. *)

Inductive Pos : Type :=
| one : Pos
| psucc : Pos -> Pos.

Inductive Int : Type :=
| neg : Pos -> Int
| zero : Int
| pos : Pos -> Int.

Definition succ_int (z : Int) : Int
  := match z with
       | neg (psucc n) => neg n
       | neg one => zero
       | zero => pos one
       | pos n => pos (psucc n)
     end.

Definition pred_int (z : Int) : Int
  := match z with
       | neg n => neg (psucc n)
       | zero => neg one
       | pos one => zero
       | pos (psucc n) => pos n
     end.

Instance isequiv_succ_int : IsEquiv succ_int
  := isequiv_adjointify succ_int pred_int _ _.
Proof.
  intros [[|n] | | [|n]]; reflexivity.
  intros [[|n] | | [|n]]; reflexivity.
Defined.

Section AssumeUnivalence.

Context `{Univalence} `{Funext}.

Definition S1_code : S1 -> Type
  := S1_rechnd Type Int (path_universe succ_int).

Definition S1_encode (x:S1) : (base = x) -> S1_code x
  := fun p => p # zero.

Fixpoint loopexp {A : Type} {x : A} (p : x = x) (n : Pos) : (x = x)
  := match n with
       | one => p
       | psucc n => loopexp p n @ p
     end.

Definition looptothe (z : Int) : (base = base)
  := match z with
       | neg n => loopexp (loop^) n
       | zero => 1
       | pos n => loopexp (loop) n
     end.

Definition S1_decode (x:S1) : S1_code x -> (base = x).
Proof.
  refine (S1_rech (fun x => S1_code x -> base = x) looptothe _ x).
  apply path_forall; intros z; simpl in z.
  refine (transport_arrow _ _ _ @ _).
  refine (transport_paths_r loop _ @ _).
  refine (whiskerR (ap _ (transport_compose idmap S1_code loop^ z)) loop @ _).
  rewrite ap_V.
  unfold S1_code; rewrite S1_rechnd_beta_loop.
  rewrite path_universe_inverse.
  rewrite transport_path_universe.
  destruct z as [[|n] | | [|n]]; simpl.
  by apply concat_pV_p.
  by apply concat_pV_p.
  by apply concat_Vp.
  by apply concat_1p.
  reflexivity.
Defined.

End AssumeUnivalence.
