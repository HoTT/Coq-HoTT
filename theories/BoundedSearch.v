Require Import HoTT.Basics HoTT.Types.
Require Import HoTT.Truncations.
Require Import HoTT.HProp HoTT.DProp.
Require Import HoTT.Spaces.Nat.

Section bounded_search.

  Context (P : nat -> Type)
          {P_hprop : forall n, IsHProp (P n)}
          (P_dec : forall n, Decidable (P n))
          (P_inhab : hexists (fun n => P n)).
  
  (** We open type_scope again after nat_scope in order to use the product type notation. *)
  Local Open Scope nat_scope.
  Local Open Scope type_scope.
  
  Local Definition minimal (n : nat) : Type := forall m : nat, P m -> n <= m.

  (** If we assume [Funext], then [minimal n] is a proposition.  But to avoid needing [Funext], we propositionally truncate it. *)
  Local Definition min_n_Type : Type := { n : nat & (P n) * merely (minimal n) }.

  Local Definition ishpropmin_n : IsHProp min_n_Type.
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
    - assert (P 0 + not (P 0)) as X; [apply P_dec |].
      destruct X as [h|].
      + left.
        refine (0;(h,_,_)).
        * intros ? ?. exact _.
      + right.
        intros l lleq0.
        assert (l0 : l = 0) by rapply leq_antisym.
        rewrite l0; assumption.
    - destruct IHn as [|n0].
      + left. apply smaller_S. assumption.
      + assert (P (n.+1) + not (P (n.+1))) as X by apply P_dec.
        destruct X as [h|].
        * left.
          refine (n.+1;(h,_,_)).
          -- intros m pm.
             assert ((n.+1 <= m)+(n.+1>m)) as X by apply leq_dichot.
             destruct X as [leqSnm|ltmSn].
             ++ assumption.
             ++ unfold gt, lt in ltmSn.
                assert (m <= n) as X by rapply leq_S_n.
                destruct (n0 m X pm).
        * right. intros l q.
          assert ((l <= n) + (l > n)) as X by apply leq_dichot.
          destruct X as [h|h].
          -- exact (n0 l h).
          -- unfold lt in h.
             assert (eqlSn : l = n.+1) by (apply leq_antisym; assumption).
             rewrite eqlSn; assumption.
  Defined.

  Local Definition n_to_min_n (n : nat) (Pn : P n) : min_n_Type.
  Proof.
    assert (smaller n + forall l, (l <= n) -> not (P l)) as X by apply bounded_search.
    destruct X as [[l [[Pl ml] leqln]]|none].
    - exact (l;(Pl,tr ml)).
    - destruct (none n (leq_refl n) Pn).
  Defined.

  Local Definition prop_n_to_min_n : min_n_Type.
  Proof.
    refine (Trunc_rec _ P_inhab).
    - exact ishpropmin_n.
    - destruct 1 as [n Pn]. exact (n_to_min_n n Pn).
  Defined.

  Definition minimal_n : { n : nat & P n }.
  Proof.
    destruct prop_n_to_min_n as [n pl]. destruct pl as [p _].
    exact (n;p).
  Defined.

End bounded_search.

Section bounded_search_alt_type.

  Context (X : Type)
          (e : nat <~> X)
          (P : X -> Type)
          {P_hprop : forall x, IsHProp (P x)}
          (P_dec : forall x, Decidable (P x))
          (P_inhab : hexists (fun x => P x)).

  (** Bounded search works for types equivalent to the naturals even without full univalence. *)
  Definition minimal_n_alt_type : {x : X & P x}.
  Proof.
    set (P' n := P (e n)).
    assert (P'_hprop : forall n, IsHProp (P' n)) by apply _.
    assert (P'_dec : forall n, Decidable (P' n)) by apply _.
    assert (P'_inhab : hexists (fun n => P' n)).
    {
      strip_truncations. apply tr.
      destruct P_inhab as [x p].
      exists (e ^-1 x).
      unfold P'.
      rewrite (eisretr e). exact p.
    }
    destruct (minimal_n P' P'_dec P'_inhab) as [n p'].
    exists (e n). exact p'.
  Defined.

End bounded_search_alt_type.
