Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HSet
  HoTT.Spaces.Nat
  HoTT.Spaces.Finite.FinNat
  HoTT.Spaces.Finite.Fin.

Local Open Scope nat_scope.

Definition fin_ind (P : forall n : Nat, Fin n -> Type)
  (z : forall n : Nat, P n.+1 fin_zero)
  (s : forall (n : Nat) (k : Fin n), P n k -> P n.+1 (fsucc k))
  {n : Nat} (k : Fin n)
  : P n k.
Proof.
  refine (transport (P n) (path_fin_to_finnat_to_fin k) _).
  refine (finnat_ind (fun n u => P n (finnat_to_fin u)) _ _ _).
  - intro. apply z.
  - intros n' u c.
    refine ((path_finnat_to_fin_succ _)^ # _).
    by apply s.
Defined.

Lemma compute_fin_ind_fin_zero (P : forall n : Nat, Fin n -> Type)
  (z : forall n : Nat, P n.+1 fin_zero)
  (s : forall (n : Nat) (k : Fin n), P n k -> P n.+1 (fsucc k)) (n : Nat)
  : fin_ind P z s fin_zero = z n.
Proof.
  unfold fin_ind.
  generalize (path_fin_to_finnat_to_fin (@fin_zero n)).
  induction (path_fin_to_finnat_fin_zero n)^.
  intro p.
  destruct (hset_path2 1 p).
  cbn.
  by destruct (hset_path2 1 (path_zero_finnat n leq_1_Sn)).
Defined.

Lemma compute_fin_ind_fsucc (P : forall n : Nat, Fin n -> Type)
  (z : forall n : Nat, P n.+1 fin_zero)
  (s : forall (n : Nat) (k : Fin n), P n k -> P n.+1 (fsucc k))
  {n : Nat} (k : Fin n)
  : fin_ind P z s (fsucc k) = s n k (fin_ind P z s k).
Proof.
  unfold fin_ind.
  generalize (path_fin_to_finnat_to_fin (fsucc k)).
  induction (path_fin_to_finnat_fsucc k)^.
  intro p.
  refine (ap (transport (P n.+1) p) (compute_finnat_ind_succ _ _ _ _) @ _).
  generalize dependent p.
  induction (path_fin_to_finnat_to_fin k).
  induction (path_fin_to_finnat_to_fin k)^.
  intro p.
  induction (hset_path2 p (path_finnat_to_fin_succ (fin_to_finnat k))).
  apply transport_pV.
Defined.

Definition fin_rec (B : Nat -> Type)
  : (forall n : Nat, B n.+1) -> (forall (n : Nat), Fin n -> B n -> B n.+1) ->
    forall {n : Nat}, Fin n -> B n
  := fin_ind (fun n _ => B n).

Lemma compute_fin_rec_fin_zero (B : Nat -> Type)
  (z : forall n : Nat, B n.+1)
  (s : forall (n : Nat) (k : Fin n), B n -> B n.+1) (n : Nat)
  : fin_rec B z s fin_zero = z n.
Proof.
  apply (compute_fin_ind_fin_zero (fun n _ => B n)).
Defined.

Lemma compute_fin_rec_fsucc (B : Nat -> Type)
  (z : forall n : Nat, B n.+1)
  (s : forall (n : Nat) (k : Fin n), B n -> B n.+1)
  {n : Nat} (k : Fin n)
  : fin_rec B z s (fsucc k) = s n k (fin_rec B z s k).
Proof.
  apply (compute_fin_ind_fsucc (fun n _ => B n)).
Defined.

