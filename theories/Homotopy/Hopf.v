Require Import Types Basics Pointed Truncations.
Require Import HSpace Suspension ExactSequence HomotopyGroup.
Require Import WildCat Modalities.ReflectiveSubuniverse.
Require Import HSet Spaces.Nat.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.


(** * The Hopf construction *)

(** We define the Hopf construction associated to a left-invertible H-space, and use it to prove that H-spaces satisfy a strengthened version of Freudenthal's theorem (see [freudenthal_hspace] below).

We have not yet included various standard results about the Hopf construction, such as the total space being the join of the fibre. *)

(** The Hopf construction associated to a left-invertible H-space (Definition 8.5.6 in the HoTT book). *)
Definition hopf_construction `{Univalence} (X : pType)
  `{IsHSpace X} `{forall a, IsEquiv (a *.)}
  : pFam (psusp X).
Proof.
  srapply Build_pFam.
  - apply (Susp_rec (Y:=Type) X X).
    exact (fun x => path_universe (x *.)).
  - simpl. exact pt.
Defined.

Lemma transport_hopf_construction `{Univalence} {X : pType}
  `{IsHSpace X} `{forall a, IsEquiv (a *.)}
  : forall x y : X, transport (hopf_construction X) (merid x) y = x * y.
Proof.
  intros x y.
  transport_to_ap.
  refine (ap (fun z => transport idmap z y) _ @ _).
  1: apply Susp_rec_beta_merid.
  apply transport_path_universe.
Defined.

(** The connecting map associated to the Hopf construction of [X] is a retraction of [loop_susp_unit X] (Proposition 2.19 in https://arxiv.org/abs/2301.02636v1). *)
Proposition hopf_retraction `{Univalence} (X : pType)
  `{IsHSpace X} `{forall a, IsEquiv (a *.)}
  : connecting_map_family (hopf_construction X) o* loop_susp_unit X
    ==* pmap_idmap.
Proof.
  nrapply hspace_phomotopy_from_homotopy.
  1: assumption.
  intro x; cbn.
  refine (transport_pp _ _ _ _ @ _); unfold dpoint.
  apply moveR_transport_V.
  refine (transport_hopf_construction _ _
            @ _ @ (transport_hopf_construction _ _)^).
  exact (right_identity _ @ (left_identity _)^).
Defined.

(** It follows from [hopf_retraction] and Freudenthal's theorem that [loop_susp_unit] induces an equivalence on [Pi (2n+1)] for [n]-connected H-spaces (with n >= 0). *)
Proposition freudenthal_hspace `{Univalence}
  {n : nat} {X : pType} `{IsConnected n X}
  `{IsHSpace X} `{forall a, IsEquiv (a *.)}
  : IsEquiv (fmap (pPi (n + n).+1) (loop_susp_unit X)).
Proof.
  nrapply isequiv_surj_emb.
  - apply issurj_pi_connmap.
    destruct n.
    + by apply (conn_map_loop_susp_unit (-1)).
    + rewrite <- trunc_index_add_nat_add.
      by apply (conn_map_loop_susp_unit).
  - nrapply isembedding_pi_psect.
    apply hopf_retraction.
Defined.
