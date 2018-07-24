Require Import Coq.Init.Peano.
Require Import HoTT.Basics HoTT.HIT.Truncations HoTT.HProp HoTT.Types.Arrow HoTT.Types.Forall HoTT.Types.Sigma HoTT.Spaces.Nat HoTT.DProp.

Section bounded_search.

  Context `{Funext}.
  Context (P : nat -> Type)
          {P_hprop : forall n, IsHProp (P n)}
          (P_dec : forall n, Decidable (P n))
          (P_inhab : hexists (fun n => P n)).
  (** We reopen these scopes so they take precedence over nat_scope; otherwise, now that we have [Coq.Init.Peano], we'd get [* : nat -> nat -> nat] rather than [* : Type -> Type -> Type]. *)
  Global Open Scope type_scope.
  Global Open Scope core_scope.

  (** But in this file, we want to be able to use the usual symbols for natural number arithmetic. *)
  Local Open Scope nat_scope.

  Local Definition minimal (n : nat) : Type := forall m : nat, P m -> n <= m.
  Local Definition ishprop_minimal (n : nat) : IsHProp (minimal n).
  Proof.
    apply _.
  Qed.
  Local Definition min_n_Type : Type := { n : nat & ((P n) * (minimal n))%type}.

  Local Definition ishpropmin_n : IsHProp min_n_Type.
  Proof.
    apply ishprop_sigma_disjoint.
    intros n n' [p m] [p' m'].
    apply leq_antisym.
    - exact (m n' p').
    - exact (m' n p).
  Qed.

  (* Local Definition min_n : hProp := hProppair min_n_UU isapropmin_n. *)

  Local Definition smaller (n : nat) := { l : nat & (P l * minimal l * (l <= n))%type}.

  Local Definition smaller_S (n : nat) (k : smaller n) : smaller (S n).
  Proof.
    induction k as [l [[p m] z]].
    exists l.
    repeat split; try assumption.
    refine (leq_trans _ _ _ _ _).
    - exact z.
    - apply leqnSn.
  Qed.

  Local Definition bounded_search (n : nat) : smaller n + forall l : nat, (l <= n) -> not (P l).
  Proof.
    induction n as [|n IHn].
    - assert (P 0 + not (P 0)) as X; [apply P_dec |].
      induction X as [h|].
      + left.
        refine (0;(h,_,_)).
        * intros ? ?. apply leq0n.
        * reflexivity.
      + right.
        intros l lleq0.
        assert (l0 : l = 0).
        {
          apply leq_antisym; try assumption.
          apply leq0n.
        }
        rewrite l0; assumption.
    - induction IHn as [|n0].
      + left. apply smaller_S. assumption.
      + assert (P (n.+1) + not (P (n.+1))) as X by apply P_dec.
        induction X as [h|].
        * left.
          refine (n.+1;(h,_,_)).
          -- intros m pm.
             assert ((n.+1 <= m)+(n.+1>m))%type as X by apply leqdichot.
             destruct X as [leqSnm|ltmSn].
             ++ assumption.
             ++ unfold lt in ltmSn.
                assert (m <= n) as X by assumption.
                destruct (n0 m X pm).
          -- apply leq_refl.
        * right. intros l q.
          assert ((l <= n) + (l > n)) as X by apply leqdichot.
          induction X as [h|h].
          -- exact (n0 l h).
          -- unfold lt in h.
             assert (eqlSn : l = n.+1).
             {
               apply leq_antisym; assumption.
             }
             rewrite eqlSn; assumption.
  Qed.

  Local Definition n_to_min_n (n : nat) (Pn : P n) : min_n_Type.
  Proof.
    assert (smaller n + forall l, (l <= n) -> not (P l)) as X by apply bounded_search.
    induction X as [[l [[Pl ml] leqln]]|none].
    - exact (l;(Pl,ml)).
    - destruct (none n (leq_refl n) Pn).
  Defined.

  Local Definition prop_n_to_min_n : min_n_Type.
  Proof.
    SearchAbout (merely).
    refine (Trunc_rec _ P_inhab).
    - exact ishpropmin_n.
    - induction 1 as [n Pn]. exact (n_to_min_n n Pn).
  Defined.

  Definition minimal_n : { n : nat & P n }.
  Proof.
    induction prop_n_to_min_n as [n pl]. induction pl as [p _].
    exact (n;p).
  Defined.

End bounded_search.
