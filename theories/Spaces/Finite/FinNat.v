Require Import Basics.Overture Basics.Tactics Basics.Trunc Basics.PathGroupoids
  Basics.Equivalences Basics.Decidable Basics.Classes.
Require Import Types.Empty Types.Sigma Types.Sum Types.Prod Types.Equiv.
Require Import Spaces.Nat.Core.
Require Import Finite.Fin.

Local Open Scope nat_scope.

Set Universe Minimization ToSet.

Definition FinNat@{} (n : nat) : Type0 := {x : nat | x < n}.

Definition zero_finnat@{} (n : nat) : FinNat n.+1
  := (0; _ : 0 < n.+1).

Definition succ_finnat@{} {n : nat} (u : FinNat n) : FinNat n.+1
  := (u.1.+1; leq_succ u.2).

Definition path_succ_finnat {n : nat} (x : nat) (h : x.+1 < n.+1)
  : succ_finnat (x; leq_pred' h) = (x.+1; h).
Proof.
  by apply path_sigma_hprop.
Defined.

Definition last_finnat@{} (n : nat) : FinNat n.+1
  := exist (fun x => x < n.+1) n (leq_refl n.+1).

Definition incl_finnat@{} {n : nat} (u : FinNat n) : FinNat n.+1
  := (u.1; leq_trans u.2 (leq_succ_r (leq_refl n))).

Definition finnat_ind@{u} (P : forall n : nat, FinNat n -> Type@{u})
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n), P n u -> P n.+1 (succ_finnat u))
  {n : nat} (u : FinNat n)
  : P n u.
Proof.
  simple_induction n n IHn; intro u.
  - elim (not_lt_zero_r u.1 u.2).
  - destruct u as [x h].
    destruct x as [| x].
    + nrefine (transport (P n.+1) _ (z _)).
      by apply path_sigma_hprop.
    + refine (transport (P n.+1) (path_succ_finnat _ _) _).
      apply s. apply IHn.
Defined.

Definition finnat_ind_beta_zero@{u} (P : forall n : nat, FinNat n -> Type@{u})
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n), P n u -> P n.+1 (succ_finnat u))
  (n : nat)
  : finnat_ind P z s (zero_finnat n) = z n.
Proof.
  snrapply (transport2 _ (q:=idpath@{Set})).
  rapply path_ishprop.
Defined.

Definition finnat_ind_beta_succ@{u} (P : forall n : nat, FinNat n -> Type@{u})
  (z : forall n : nat, P n.+1 (zero_finnat n))
  (s : forall (n : nat) (u : FinNat n),
       P n u -> P n.+1 (succ_finnat u))
  {n : nat} (u : FinNat n)
  : finnat_ind P z s (succ_finnat u) = s n u (finnat_ind P z s u).
Proof.
  destruct u as [u1 u2]; simpl; unfold path_succ_finnat.
  destruct (path_ishprop u2 (leq_pred' (leq_succ u2))).
  refine (transport2 _ (q:=idpath@{Set}) _ _).
  rapply path_ishprop.
Defined.

Definition is_bounded_fin_to_nat@{} {n} (k : Fin n)
  : fin_to_nat k < n.
Proof.
  induction n as [| n IHn].
  - elim k.
  - destruct k as [k | []]; exact _.
Defined.

Definition fin_to_finnat {n} (k : Fin n) : FinNat n
  := (fin_to_nat k; is_bounded_fin_to_nat k).

Fixpoint finnat_to_fin@{} {n : nat} : FinNat n -> Fin n
  := match n with
     | 0 => fun u => Empty_rec (not_lt_zero_r _ u.2)
     | n.+1 => fun u =>
        match u with
        | (0; _) => fin_zero
        | (x.+1; h) => fsucc (finnat_to_fin (x; leq_pred' h))
        end
     end.

Definition path_fin_to_finnat_fsucc@{} {n : nat} (k : Fin n)
  : fin_to_finnat (fsucc k) = succ_finnat (fin_to_finnat k).
Proof.
  apply path_sigma_hprop.
  apply path_nat_fsucc.
Defined.

Definition path_fin_to_finnat_fin_zero@{} (n : nat)
  : fin_to_finnat (@fin_zero n) = zero_finnat n.
Proof.
  apply path_sigma_hprop.
  apply path_nat_fin_zero.
Defined.

Definition path_finnat_to_fin_succ@{} {n : nat} (u : FinNat n)
  : finnat_to_fin (succ_finnat u) = fsucc (finnat_to_fin u).
Proof.
  cbn. do 2 f_ap. by apply path_sigma_hprop.
Defined.

Definition path_finnat_to_fin_incl@{} {n : nat} (u : FinNat n)
  : finnat_to_fin (incl_finnat u) = fin_incl (finnat_to_fin u).
Proof.
  revert n u.
  snrapply finnat_ind.
  1: reflexivity.
  intros n u; cbn beta; intros p.
  lhs nrapply (path_finnat_to_fin_succ (incl_finnat u)).
  lhs nrapply (ap fsucc p).
  exact (ap fin_incl (path_finnat_to_fin_succ _))^.
Defined.

Definition path_finnat_to_fin_last@{} (n : nat)
  : finnat_to_fin (last_finnat n) = fin_last.
Proof.
  induction n as [| n IHn].
  - reflexivity.
  - exact (ap fsucc IHn).
Defined.

Definition path_finnat_to_fin_to_finnat@{} {n : nat} (u : FinNat n)
  : fin_to_finnat (finnat_to_fin u) = u.
Proof.
  induction n as [| n IHn].
  - elim (not_lt_zero_r _ u.2).
  - destruct u as [x h].
    apply path_sigma_hprop.
    destruct x as [| x].
    + exact (ap pr1 (path_fin_to_finnat_fin_zero n)).
    + refine ((path_fin_to_finnat_fsucc _)..1 @ _).
      exact (ap S (IHn (x; leq_pred' h))..1).
Defined.

Definition path_fin_to_finnat_to_fin@{} {n : nat} (k : Fin n)
  : finnat_to_fin (fin_to_finnat k) = k.
Proof.
  induction n as [| n IHn].
  - elim k.
  - destruct k as [k | []].
    + specialize (IHn k).
      refine (path_finnat_to_fin_incl (fin_to_finnat k) @ _).
      exact (ap fin_incl IHn).
    + apply path_finnat_to_fin_last.
Defined.

Definition equiv_fin_finnat@{} (n : nat) : Fin n <~> FinNat n
  := equiv_adjointify fin_to_finnat finnat_to_fin
      path_finnat_to_fin_to_finnat
      path_fin_to_finnat_to_fin.
