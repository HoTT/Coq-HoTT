(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the natural numbers *)

Require Export Coq.Init.Peano.
Require Import HoTT.Basics.
Require Import HoTT.Types.Empty.
Require Import HoTT.Types.Unit.
Require Import HoTT.Types.Bool.

(** We reopen these scopes so they take precedence over nat_scope; otherwise, now that we have [Coq.Init.Peano], we'd get [* : nat -> nat -> nat] rather than [* : Type -> Type -> Type]. *)
Global Open Scope type_scope.
Global Open Scope core_scope.

(** But in this file, we want to be able to use the usual symbols for natural number arithmetic. *)
Local Open Scope nat_scope.



Scheme nat_ind := Induction for nat Sort Type.
Scheme nat_rec := Minimality for nat Sort Type.

(** ** Arithmetic *)

Lemma nat_plus_n_O : forall n:nat, n = n + 0.
Proof.
  induction n.
  - reflexivity.
  - simpl; apply ap; assumption.
Qed.

Lemma nat_plus_n_Sm : forall n m:nat, (n + m).+1 = n + m.+1.
Proof.
  intros n m; induction n; simpl.
  - reflexivity.
  - apply ap; assumption.
Qed.

Definition nat_plus_comm (n m : nat) : n + m = m + n.
Proof.
  revert m; induction n as [|n IH]; intros m; simpl.
  - refine (nat_plus_n_O m).
  - transitivity (m + n).+1.
    + apply ap, IH.
    + apply nat_plus_n_Sm.
Qed.

(** ** Exponentiation *)

Fixpoint nat_exp (n m : nat) : nat
  := match m with
       | 0 => 1
       | S m => nat_exp n m * n
     end.

(** ** Factorials *)

Fixpoint factorial (n : nat) : nat
  := match n with
       | 0 => 1
       | S n => S n * factorial n
     end.

(** ** proof of [HSet nat] using the encode-decode method *)

Fixpoint code (m n : nat) : Type :=
  match m, n with
  | O, O => Unit
  | O, S _ => Empty
  | S _, O => Empty
  | S m', S n' => code m' n'
  end.

Definition r (n : nat) : code n n.
induction n.
* simpl. exact tt.
* simpl. exact IHn.
Defined.

(*  Empty_Is_HProp : IsTrunc -1 Empty.  *)

Lemma code_Is_HProp : forall (m n : nat), IsTrunc -1 (code m n).
Proof.
  induction m, n.
  * exact (hprop_allpath Unit path_unit).
  * exact hprop_Empty.
  * exact hprop_Empty.
  * simpl. apply IHm.
Defined.

Definition encode (m n : nat): m = n -> code m n.
intro p.
  exact (transport (code m) p (r m)). (* @transport nat (code m) m n p (r m). *)
Defined.

Fixpoint decode (m n : nat) : code m n -> m = n.
intro u.
induction m, n.
* exact idpath.
* elim u.
* elim u.
* apply (ap S). exact (decode m n u). (* @ap nat nat S m n *)
Defined.

Lemma decode_encode_diag : forall (n : nat), decode n n (encode n n idpath) = idpath.
Proof.
  induction n.
  * trivial.
  * simpl. rewrite IHn. trivial.
Defined.

Lemma decode_encode : forall (m n : nat) (p : m = n), decode m n (encode m n p) = p.
Proof.
  apply paths_ind'.
  induction a.
  * trivial.
  * simpl. apply decode_encode_diag.
Defined.

Lemma encode_decode : forall (m n : nat) (u : code m n), encode m n (decode m n u) = u.
Proof.
  intros.
  apply hprop_allpath.
  apply code_Is_HProp.
Qed.

(* by the way *)
Lemma O_is_not_a_successor : forall (m : nat), ~ (S m = O).
Proof.
  intros.
  unfold not.
  exact (encode (S m) O).
Qed.

Lemma S_is_injective : forall (m n : nat), (S m = S n) -> m = n.
Proof.
  intros.
  apply decode.
  apply (encode (S m) (S n)).
  exact H.
Qed.

Proposition equiv_types : forall (m n : nat), Equiv (code m n) (m = n).
Proof.
  intros.
  refine (equiv_adjointify (decode m n) (encode m n) _ _).
    unfold Sect. apply decode_encode.
    unfold Sect. apply encode_decode.
Qed.

Lemma idmn_Is_HProp : forall (m n : nat), IsTrunc -1 (m = n).
Proof.
  intros.
  exact (@trunc_equiv' (code m n) (m = n) (equiv_types m n) -1 (code_Is_HProp m n)).
Qed.

Proposition N_is_HSet : IsHSet nat.
Proof.
  repeat intro.
  apply idmn_Is_HProp.
Qed.





