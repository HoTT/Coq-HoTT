Require Import Basics.
Require Import Types.
Require Import HSet.
Require Import Spaces.Nat.

Local Open Scope path_scope.
Local Open Scope nat_scope.

(** * Definitions, properties and operations about finite sets. *)

(** ** Canonical finite sets *)

(** A *finite set* is a type that is merely equivalent to the canonical finite set determined by some natural number.  There are many equivalent ways to define the canonical finite sets, such as [{ k : nat & k < n}]; we instead choose a recursive one. *)
Fixpoint Fin (n : nat) : Type
  := match n with
       | 0 => Empty
       | S n => Fin n + Unit
     end.

(** Finite sets always either have an element or they don't. *)
Global Instance decidable_fin (n : nat)
  : Decidable (Fin n).
Proof.
  destruct n as [|n]; try exact _.
  exact (inl (inr tt)).
Defined.

(** Finite sets have decidable equality. Which means they are also sets. *)
Global Instance decidablepaths_fin (n : nat)
  : DecidablePaths (Fin n).
Proof.
  induction n as [|n IHn]; simpl; exact _.
Defined.

(** The 1 element finite set is contractible. *)
Global Instance contr_fin1 : Contr (Fin 1).
Proof.
  refine (contr_equiv' Unit (sum_empty_l Unit)^-1).
Defined.

(** If there is a map from an n element finite set into the empty type then n = 0. *)
Definition fin_empty (n : nat) (f : Fin n -> Empty) : n = 0.
Proof.
  destruct n; [ reflexivity | ].
  elim (f (inr tt)).
Defined.

(** The zero element in a non-empty finite set is the right most element. *)
Fixpoint fin_zero (n : nat)
  : Fin n.+1
  := match n with
      | O => inr tt
      | S n' => inl (fin_zero n')
      end.

(** There is an injection from the n element finite set into the n.+1 element finite set,
    mapping [i : Fin n] to the successor of [i] in [Fin n.+1]. *)
Fixpoint fin_succ_inject (n : nat)
  : Fin n -> Fin n.+1
  := match n with
      | O => Empty_rec
      | S n' =>
        fun i : Fin (S n') =>
          match i with
          | inl i' => inl (fin_succ_inject n' i')
          | inr tt => inr tt
          end
      end.

(** This actually is an embedding (by showing it is an injection). *)
Lemma isembedding_fin_succ_inject (n : nat)
  : IsEmbedding (fin_succ_inject n).
Proof.
  apply isembedding_isinj_hset.
  induction n.
  1: intros [].
  intros [] []; intro p.
  + f_ap. apply IHn. eapply path_sum_inl. exact p.
  + destruct u. elim (inl_ne_inr _ _ p).
  + destruct u. elim (inr_ne_inl _ _ p).
  + destruct u, u0; reflexivity.
Defined.

(** ** Tactics **)
Ltac FinIndOn X := repeat
  match type of X with
  | Fin 0 => destruct X
  | Empty => destruct X
  | Unit => destruct X
  | Fin ?n => destruct X as [X|X]
  | ?L + Unit => destruct X as [X|X]
  end.

(** A tactic that lets you eliminate from a given finite set. *)
Ltac FinInd := let X := fresh "X" in intro X; FinIndOn X.

(** Here is an example *)
Goal Fin 5 -> Type.
FinInd.
Abort.

(** ** Operations on Fin *)

(** Sucessor of an element of a finite set. This is a periodic function. *)
(** TODO: make this more readable? *)
Fixpoint fsucc {n : nat} : Fin n -> Fin n
  := match n with
      | 0 => Empty_rec : Fin 0 -> Fin 0
      | S n' => fun r =>
        match r with
        | inl r' =>
          match n' as n' return (Fin n' -> Fin n') -> Fin n' -> Fin n'.+1 with
          | 0 => fun _ => Empty_rec
          | S n'' =>
            fun F r'' =>
              match r'' with
                | inl r''' => inl (F (inl r'''))
                | inr tt => inr tt
              end
          end (@fsucc n') r'
        | inr _ => fin_zero n'
        end
      end.

(** The map from the natural numbers to a finite set. The modulo map. *)
Fixpoint fin_nat (n : nat) (m : nat) : Fin n.+1
  := match m with
      | 0 => fin_zero n
      | S m => fsucc (fin_nat _ m)
     end.

(** TODO: Use and put in scope *)
(** Here is a notation for a natural number in a finite set. It is suggestive of modulo classes. *)
(* Notation "[ n ]" := (fin_nat _ n). *)


(** ** Initial segments of [nat] *)

Definition nat_fin (n : nat) (k : Fin n) : nat.
Proof.
  induction n as [|n nf].
  - contradiction.
  - destruct k as [k|_].
    + exact (nf k).
    + exact n.
Defined.

Definition nat_fin_inl (n : nat) (k : Fin n)
  : nat_fin n.+1 (inl k) = nat_fin n k := 1.

Definition nat_fin_compl (n : nat) (k : Fin n) : nat.
Proof.
  induction n as [|n nfc].
  - contradiction.
  - destruct k as [k|_].
    + exact (nfc k).+1.
    + exact 0.
Defined.

Definition nat_fin_compl_compl n k
: (nat_fin n k + nat_fin_compl n k).+1 = n.
Proof.
  induction n as [|n IH].
  - contradiction.
  - destruct k as [k|?]; simpl.
    + rewrite nat_plus_comm.
      specialize (IH k).
      rewrite nat_plus_comm in IH.
      exact (ap S IH).
    + rewrite nat_plus_comm; reflexivity.
Qed.

(** TODO: finish *)
(** Turning an element of a finite set into a natural number then back into a finite set is homotopic to the identity map. *)
(*
Definition fin_nat_nat_fin (n : nat)
  : Sect (nat_fin n.+1) (@fin_nat n).
Proof.
(*   repeat (induction n; [by FinInd|]). *)
*)
