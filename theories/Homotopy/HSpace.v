Require Import Basics.
Require Import Types.
Require Import HIT.Truncations.
Require Import HIT.Connectedness.
Import TrM.

Section HSpace.

  Context `{Univalence}.

  Class HSpace (space : Type) := {
    id : space;
    mu : space -> space -> space;
    left_id : forall a, mu id a = a;
    right_id : forall a, mu a id = a
  }.

  Context 
    {A : Type}
   `{HSpace A}
   `{IsConnected 0 A}. (* Can we weaken this to ||X||_0 is a group? *)

  Lemma mu_l_equiv : forall (a : A), IsEquiv (mu a).
  Proof.
    refine (conn_map_elim -1 (unit_name id) _ _).
    + exact (conn_point_incl id).
    + apply Unit_ind.
      serapply (isequiv_homotopic idmap).
      exact (fun a => (left_id a)^).
  Defined.

  Lemma mu_r_equiv : forall (a : A), IsEquiv (fun x => mu x a).
  Proof.
    refine (conn_map_elim -1 (unit_name id) _ _).
    + exact (conn_point_incl id).
    + apply Unit_ind.
      serapply (isequiv_homotopic idmap).
      exact (fun a => (right_id a)^).
  Defined.

  Definition mu_l_equiv' (a : A) : A <~> A
    := BuildEquiv _ _ _ (mu_l_equiv a).

  Definition mu_r_equiv' (a : A) : A <~> A
    := BuildEquiv _ _ _ (mu_r_equiv a).

End HSpace.

Global Instance hspace_isequiv {A B} (e : A -> B)
  `{eq : IsEquiv _ _ e} `{hs : HSpace A} : HSpace B.
Proof.
  destruct hs as [id mu l r].
  serapply Build_HSpace.
  1: exact (e id).
  { intros a b.
    apply e.
    exact (mu (e^-1 a) (e^-1 b)). }
  1,2: intro; cbv; destruct eq as [e' p q _].
  1,2: (rewrite q,l || rewrite q,r).
  1,2: apply p.
Defined.

Global Instance hspace_equiv {A B} (e : A <~> B) `{HSpace A} : HSpace B.
Proof.
  apply (hspace_isequiv e).
Defined.
