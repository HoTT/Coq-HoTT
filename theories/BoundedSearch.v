(** * Bounded Search *)

(** The main result of this file is [minimal_n], which say that if [P : nat -> Type] is a family such that each [P n] is decidable and [{n & P n}] is merely inhabited, then [{n & P n}] is inhabited.  Since [P n] is decidable, it is sufficient to prove [{n & merely (P n)}], and to do this, we prove the stronger claim that there is a *minimal* [n] satisfying [merely (P n)].  This stronger claim is a proposition, which is what makes the argument work.  Along the way, we also prove that [{ l : nat & (l <= n) * P l }] is decidable for each [n]. *)

Require Import Basics.Overture Basics.Decidable Basics.Trunc Basics.Tactics.
Require Import Types.Sigma Types.Prod.
Require Import Truncations.Core.
Require Import Spaces.Nat.Core.

Section bounded_search.

  Context (P : nat -> Type) (P_dec : forall n, Decidable (P n)).
  
  (** We open type_scope again after nat_scope in order to use the product type notation. *)
  Local Open Scope nat_scope.
  Local Open Scope type_scope.
  
  Local Definition minimal (n : nat) : Type := forall m : nat, P m -> n <= m.

  (** If we assume [Funext], then [minimal n] is a proposition.  But to avoid needing [Funext], we propositionally truncate it. *)
  Local Definition min_n_Type : Type := { n : nat & merely (P n) * merely (minimal n) }.

  Local Instance ishpropmin_n : IsHProp min_n_Type.
  Proof.
    apply ishprop_sigma_disjoint.
    intros n n' [p m] [p' m'].
    strip_truncations.
    apply leq_antisym.
    - exact (m n' p').
    - exact (m' n p).
  Defined.

  Local Definition smaller (n : nat) := { l : nat & P l * minimal l * (l <= n) }.

  Local Definition smaller_S (n : nat) (k : smaller n) : smaller (S n).
  Proof.
    destruct k as [l [[p m] z]].
    exists l.
    repeat split.
    1,2: assumption.
    exact _.
  Defined.

  Local Definition bounded_search (n : nat) : smaller n + forall l : nat, (l <= n) -> not (P l).
  Proof.
    induction n as [|n IHn].
    - destruct (dec (P 0)) as [h|n].
      + left.
        exact (0; (h, fun _ _ => _, _)).
      + right.
        intros l lleq0.
        by rewrite (leq_antisym lleq0 _ : l = 0).
    - destruct IHn as [s|n0].
      + left; by apply smaller_S.
      + destruct (dec (P n.+1)) as [h|nP].
        * left.
          refine (n.+1; (h, _, _)).
          intros m pm.
          apply leq_iff_not_gt.
          unfold gt, lt; intro leq_Sm_Sn.
          apply leq_pred' in leq_Sm_Sn.
          destruct (n0 m leq_Sm_Sn pm).
        * right.
          by apply leq_ind_l.
  Defined.

  Local Definition n_to_min_n (n : nat) (Pn : P n) : min_n_Type.
  Proof.
    destruct (bounded_search n) as [[l [[Pl ml] _]] | none].
    - exact (l; (tr Pl, tr ml)).
    - destruct (none n (leq_refl n) Pn).
  Defined.

  Local Definition prop_n_to_min_n (P_inhab : hexists P) : min_n_Type.
  Proof.
    strip_truncations.
    exact (n_to_min_n (P_inhab.1) (P_inhab.2)).
  Defined.

  Definition minimal_n (P_inhab : hexists P) : { n : nat & P n }.
  Proof.
    destruct (prop_n_to_min_n P_inhab) as [n [p _]].
    exact (n; fst merely_inhabited_iff_inhabited_stable p).
  Defined.

  (** As a consequence of [bounded_search] we deduce that bounded existence is decidable.  See also [decidable_exists_bounded_nat] in Spaces/Lists/Theory.v for a similar result with different dependencies. *)
  Definition decidable_search (n : nat) : Decidable { l : nat & (l <= n) * P l }.
  Proof.
    destruct (bounded_search n) as [s | no_l].
    - destruct s as [l [[Pl min] l_leq_n]].
      exact (inl (l; (l_leq_n, Pl))).
    - right.
      intros [l [l_leq_n Pl]].
      exact (no_l l l_leq_n Pl).
  Defined.

End bounded_search.

Section bounded_search_alt_type.

  Context (X : Type)
          (e : nat <~> X)
          (P : X -> Type)
          (P_dec : forall x, Decidable (P x))
          (P_inhab : hexists P).

  (** Bounded search works for types equivalent to the naturals even without full univalence. *)
  Definition minimal_n_alt_type : {x : X & P x}.
  Proof.
    pose (P' n := P (e n)).
    pose (P'_dec n := P_dec (e n) : Decidable (P' n)).
    assert (P'_inhab : hexists P').
    {
      strip_truncations. apply tr.
      destruct P_inhab as [x p].
      exists (e ^-1 x).
      unfold P'.
      rewrite (eisretr e). exact p.
    }
    destruct (minimal_n P' P'_dec P'_inhab) as [n p'].
    exact ((e n); p').
  Defined.

End bounded_search_alt_type.
