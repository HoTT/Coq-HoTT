From HoTT Require Import Basics Types Pointed Truncations.
Require Import HSpace Suspension ExactSequence HomotopyGroup.
Require Import WildCat.Core WildCat.Universe WildCat.Equiv Modalities.ReflectiveSubuniverse Modalities.Descent.
Require Import HSet Spaces.Nat.Core.
Require Import Homotopy.Join Colimits.Pushout.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.


(** * The Hopf construction *)

(** We define the Hopf construction associated to a left-invertible H-space, and use it to prove that H-spaces satisfy a strengthened version of Freudenthal's theorem (see [freudenthal_hspace] below). *)

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

(** *** Total space of the Hopf construction *)

(** The total space of the Hopf construction on [Susp X] is the join of [X] with itself. Note that we need both left and right multiplication to be equivalences. This is true when [X] is a 0-connected H-space for example. (This is lemma 8.5.7 in the HoTT book). *)
Definition pequiv_hopf_total_join `{Univalence} (X : pType)
  `{IsHSpace X} `{forall a, IsEquiv (a *.)} `{forall a, IsEquiv (.* a)}
  : psigma (hopf_construction X) <~>* pjoin X X.
Proof.
  snapply Build_pEquiv'.
  { refine (_ oE equiv_pod_flatten (f := const_tt X) (g := const_tt X)
    (@Build_poDescent _ _ _ (const_tt X) (const_tt X)
    (Unit_ind (pointed_type X)) (Unit_ind (pointed_type X))
    (fun x => Build_Equiv _ _ (x *.) (H1 x)))).
    snapply equiv_pushout.
    (* The equivalence [{x : X & X} <~> X * X] that we need sends [(x; y) to (y, x*y)]. *)
    { cbn. refine (equiv_sigma_prod0 _ _ oE _ oE equiv_sigma_symm0 _ _).
      snapply equiv_functor_sigma_id.
      intros x.
      exact (Build_Equiv _ _ (.* x) _). }
    1,2: exact (equiv_contr_sigma (Unit_ind (pointed_type X))).
    1,2: reflexivity. }
  reflexivity.
Defined.

(** ** Miscellaneous lemmas and corollaries about the Hopf construction *)

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
  napply hspace_phomotopy_from_homotopy.
  1: assumption.
  intro x; cbn.
  refine (transport_pp _ _ _ _ @ _); unfold dpoint.
  apply moveR_transport_V.
  refine (transport_hopf_construction _ _
            @ _ @ (transport_hopf_construction _ _)^).
  exact (right_identity _ @ (left_identity _)^).
Defined.

(** It follows from [hopf_retraction] and Freudenthal's theorem that [loop_susp_unit] induces an equivalence on [Pi (2n+1)] for [n]-connected H-spaces (with n >= 0). Note that [X] is automatically left-invertible. *)
Proposition isequiv_Pi_connected_hspace `{Univalence}
  {n : nat} (X : pType) `{IsConnected n X}
  `{IsHSpace X}
  : IsEquiv (fmap (pPi (n + n).+1) (loop_susp_unit X)).
Proof.
  napply isequiv_surj_emb.
  - apply issurj_pi_connmap.
    destruct n.
    + by apply (conn_map_loop_susp_unit (-1)).
    + rewrite <- trunc_index_add_nat_add.
      by apply (conn_map_loop_susp_unit).
  - pose (is0connected_isconnected n.-2 _).
    napply isembedding_pi_psect.
    apply hopf_retraction.
Defined.

(** By Freudenthal, [loop_susp_unit] induces an equivalence on lower homotopy groups as well, so it is a (2n+1)-equivalence.  We formalize it below with [m = n-1], and allow [n] to start at [-1].  We prove it using a more general result about reflective subuniverses, [OO_inverts_conn_map_factor_conn_map], but one could also use homotopy groups and the truncated Whitehead theorem. *)
Definition freudenthal_hspace' `{Univalence}
  {m : trunc_index} (X : pType) `{IsConnected m.+1 X}
  `{IsHSpace X} `{forall a, IsEquiv (a *.)}
  : O_inverts (Tr (m +2+ m).+1) (loop_susp_unit X).
Proof.
  set (r:=connecting_map_family (hopf_construction X)).
  napply (OO_inverts_conn_map_factor_conn_map _ (m +2+ m) _ r).
  2, 4: exact _.
  1: apply O_lex_leq_Tr.
  rapply (conn_map_homotopic _ equiv_idmap (r o loop_susp_unit X)).
  symmetry.
  napply hopf_retraction.
Defined.

(** Note that we don't really need the assumption that [X] is left-invertible in the previous result; for [m >= -1], it follows from connectivity.  And for [m = -2], the conclusion is trivial. Here we state the version for [m >= -1] without left-invertibility. *)
Definition freudenthal_hspace `{Univalence}
  {m : trunc_index} (X : pType) `{IsConnected m.+2 X}
  `{IsHSpace X}
  : O_inverts (Tr (m.+1 +2+ m.+1).+1) (loop_susp_unit X).
Proof.
  pose (is0connected_isconnected m _).
  exact (freudenthal_hspace' (m:=m.+1) X).
Defined.

(** Here we give a generalization of a result from Eilenberg-Mac Lane Spaces in Homotopy Type Theory, Dan Licata and Eric Finster.  Their version corresponds to [m = -2] in our version.  Their encode-decode proof was formalized in this library in EMSpace.v until this shorter and more general approach was found. *)
Definition licata_finster `{Univalence}
  {m : trunc_index} (X : pType) `{IsConnected m.+2 X}
  (k := (m.+1 +2+ m.+1).+1) `{IsHSpace X} `{IsTrunc k X}
  : X <~>* pTr k (loops (psusp X)).
Proof.
  refine (_ o*E pequiv_ptr (n:=k)).
  nrefine (pequiv_O_inverts k (loop_susp_unit X)).
  rapply freudenthal_hspace.
Defined.

(** Since [loops X] is an H-space, the Hopf construction provides a map [Join (loops X) (loops X) -> Susp (loops X)].  We show that this map is equivalent to the fiber of [loop_susp_counit X : Susp (loops X) -> X] over the base point, up to the automorphism of [Susp (loops X)] induced by inverting loops. *)
Definition pequiv_pfiber_loops_susp_counit_join `{Univalence} (X : pType)
  : pfiber (loop_susp_counit X) <~>* pjoin (loops X) (loops X).
Proof.
  snrefine (pequiv_hopf_total_join (loops X) o*E _).
  2: exact ishspace_loops.
  2,3: exact _.
  snapply Build_pEquiv'.
  { snapply equiv_functor_sigma'.
    1: exact (emap psusp (equiv_path_inverse _ _)).
    snapply Susp_ind; hnf.
    1,2: reflexivity.
    intros p.
    napply path_equiv.
    funext q.
    simpl.
    lhs rapply (transport_equiv (merid p) _ q).
    simpl.
    lhs napply ap.
    { lhs napply transport_paths_Fl.
      napply whiskerR.
      { lhs napply (ap inverse (ap_V _ _)).
        lhs rapply inv_V.
        apply Susp_rec_beta_merid. } }
    lhs napply (transport_idmap_ap _ (merid p)).
    lhs napply (transport2 idmap).
    { lhs napply ap_compose.
      lhs napply ap.
      1: apply functor_susp_beta_merid.
      apply Susp_rec_beta_merid. }
    lhs napply transport_path_universe.
    apply concat_V_pp. }
  reflexivity.
Defined.

(** As a corollary we get 2n-connectivity of [loop_susp_counit X] for an n-connected [X]. *)
Instance conn_map_loop_susp_counit `{Univalence}
  {n : trunc_index} (X : pType) `{IsConnected n.+1 X}
  : IsConnMap (n +2+ n) (loop_susp_counit X).
Proof.
  destruct n.
  - intro x; hnf; exact _.
  - snapply (conn_point_elim (-1)).
    + exact (isconnected_pred_add' n 0 _).
    + exact _.
    + napply (isconnected_equiv' _ _ (pequiv_pfiber_loops_susp_counit_join X)^-1).
      napply isconnected_join; exact _.
Defined.

(** In particular, we get the following result.  All we are really using is that [n.+2 <= n +2+ n], but because of the use of [isconnmap_pred_add], the proof is a bit more specific to this case. *)
Definition pequiv_ptr_psusp_loops `{Univalence} (X : pType) (n : nat) `{IsConnected n.+1 X}
  : pTr n.+2 (psusp (loops X)) <~>* pTr n.+2 X.
Proof.
  snapply Build_pEquiv.
  1: exact (fmap (pTr _) (loop_susp_counit _)).
  napply O_inverts_conn_map.
  napply (isconnmap_pred_add n.-2).
  rewrite 2 trunc_index_add_succ.
  exact (conn_map_loop_susp_counit X).
Defined.
