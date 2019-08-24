Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Cubical.
Require Import abstract_algebra.
Require Import TruncType.
Require Import HIT.Truncations.
Require Import HSpace.
Import TrM.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.

(* TODO: Generalise this to H-spaces?
  This however might require H-spaces to be more general than groups in the library. *)
(* Definition of Classifying Spaces of a Group *)
Module Export ClassifyingSpace.

  (* We define the classifying space of a group X as a HIT with the following
    constructors:
      * A point   bbase : B X
      * a path    bloop : forall x, bbase = bbase
      * a 2-path  bloop_pp : forall x y, bloop (x * y) = bloop x @ bloop y
      * a proof that B X is 1-truncated

    It can be proven that bloop e = idpath and bloop p^-1 = (bloop p)^. *)

  Private Inductive ClassifyingSpace (X : Type) `{Group X} :=
    | bbase : ClassifyingSpace X.

  Arguments bbase X {Aop Aunit Anegate H}.

  Axiom bloop : forall `{Group X}, X -> bbase X = bbase X.

  Axiom bloop_pp : forall `{Group X},
    forall x y, bloop (x & y) = bloop x @ bloop y.

  (* Faking truncation *)
  Global Instance istrunc_ClassifyingSpace `{Group X}
  : IsTrunc 1 (ClassifyingSpace X).
  Proof. Admitted.

Local Open Scope dpath_scope.

  (* The induction principle for the classifying space takes a
      - point bbase' from P(bbase X)
      - forall x, a dependent path from bbase' to bbase' called bloop'
      - forall x y, a dependent square that maps between bloop' (x & y)
        and (bloop' x) @D (bloop' y). *)

  Definition ClassifyingSpace_ind (X : Type) `{Group X}
    (P : ClassifyingSpace X -> Type) `{IsTrunc 1 (P (bbase X))}
    (bbase' : P (bbase X))
    (bloop' : forall x, DPath P (bloop x) bbase' bbase')
    (bloop_pp' : forall x y,  DSquare P (sq_G1 (bloop_pp x y))
      (bloop' (x & y)) ((bloop' x) @D (bloop' y)) 1 1) x : P x
    := match x return (_ -> P x) with
          bbase => (fun _ => bbase')
       end bloop.

  Axiom ClassifyingSpace_ind_beta_bloop : forall (X : Type) `{Group X}
    (P : ClassifyingSpace X -> Type) `(IsTrunc 1 (P (bbase X)))
    (bbase' : P (bbase X)) (bloop' : forall x, DPath P (bloop x) bbase' bbase')
    (bloop_pp' : forall x y,  DSquare P (sq_G1 (bloop_pp x y))
      (bloop' (x & y)) ((bloop' x) @D (bloop' y)) 1 1) (x : X),
    dp_apD (ClassifyingSpace_ind X P bbase' bloop' bloop_pp') (bloop x) = bloop' x.


  Definition ClassifyingSpace_rec (X : Type) `{Group X}
    (P : Type) `{IsTrunc 1 P} (bbase' : P) (bloop' : X -> bbase' = bbase')
    (bloop_pp' : forall x y : X, bloop' (x & y) = bloop' x @ bloop' y)
    : ClassifyingSpace X -> P.
  Proof.
    srefine (ClassifyingSpace_ind X (fun _ => P) bbase' _ _).
    1: intro; apply dp_const, bloop', x.
    intros x y.
    apply ds_const'.
    erapply sq_GGcc.
    2: refine (_ @ ap _ (dp_const_pp _ _)).
    1,2: symmetry; apply eissect.
    apply sq_G1.
    revert x y.
    assumption.
  Defined.

  Definition ClassifyingSpace_rec_beta_bloop (X : Type) `{Group X}
    (P : Type) `{IsTrunc 1 P} (bbase' : P) (bloop' : X -> bbase' = bbase')
    (bloop_pp' : forall x y : X, bloop' (x & y) = bloop' x @ bloop' y) (x : X)
    : ap (ClassifyingSpace_rec X P bbase' bloop' bloop_pp') (bloop x) = bloop' x.
  Proof.
    rewrite <- dp_apD_const'.
    unfold ClassifyingSpace_rec.
    rewrite ClassifyingSpace_ind_beta_bloop.
    apply eissect.
  Qed.

End ClassifyingSpace.

Global Instance ispointed_BG `{Group G} : IsPointed (ClassifyingSpace G).
Proof.
  exact (bbase G).
Defined.

Definition B (G : Type) `{Group G} := Build_pType (ClassifyingSpace G) _.

(* TODO: Move to "Group" file? *)
Lemma left_mult_equiv `{Group G} : G -> G <~> G.
Proof.
  intro x.
  serapply equiv_adjointify.
  + intro y; exact (x & y).
  + intro y; exact (Anegate x & y).
  + intro y.
    rewrite associativity.
    rewrite right_inverse.
    apply left_identity.
  + intro y.
    rewrite associativity.
    rewrite (left_inverse x).
    apply left_identity.
Defined.

(* TODO: move to Group *)
Lemma right_mult_equiv `{Group G} : G -> G <~> G.
Proof.
  intro x.
  serapply equiv_adjointify.
  + intro y; exact (y & x).
  + intro y; exact (y & Anegate x).
  + intro y.
    rewrite <- (associativity y _ x).
    rewrite (left_inverse x).
    apply right_identity.
  + intro y.
    rewrite <- (associativity y x).
    rewrite right_inverse.
    apply right_identity.
Defined.

Definition bloop_id `{Group G} : bloop mon_unit = idpath.
Proof.
  symmetry.
  apply (cancelL (bloop mon_unit)).
  refine (_ @ bloop_pp _ _).
  refine (_ @ ap _ (left_identity _)^).
  apply concat_p1.
Defined.

Definition bloop_inv `{Group G} : forall x, bloop (Anegate x) = (bloop x)^.
Proof.
  intro x.
  refine (_ @ concat_p1 _).
  apply moveL_Vp.
  refine (_ @ bloop_id).
  refine ((bloop_pp _ _)^ @ _).
  apply ap, right_inverse.
Defined.

Section EncodeDecode.

  Context `{Univalence}.

  Local Definition codes `{Group G} : B G -> 0 -Type.
  Proof.
    serapply ClassifyingSpace_rec.
    + serapply (BuildhSet G).
    + intro x.
      apply path_trunctype.
      apply (right_mult_equiv x).
    + intros x y.
      refine (_ @ path_trunctype_pp _ _).
      apply ap, path_equiv, path_forall.
      intro; cbn.
      apply associativity.
  Defined.

  Local Definition encode `{Group G} : forall z, bbase G = z -> codes z.
  Proof.
    intros z p.
    exact (transport codes p Aunit).
  Defined.

  Local Definition codes_transport `{Group G} : forall x y,
    transport codes (bloop x) y = y & x.
  Proof.
    intros x y.
    rewrite transport_idmap_ap.
    rewrite ap_compose.
    rewrite ClassifyingSpace_rec_beta_bloop.
    rewrite ap_trunctype.
    by rewrite transport_path_universe_uncurried.
  Qed.

  Local Definition decode `{Group G} : forall (z : B G), codes z -> bbase G = z.
  Proof.
    serapply ClassifyingSpace_ind.
    + exact bloop.
    + intro x.
      apply dp_arrow.
      intro y; cbn in *.
      apply dp_paths_r.
      refine ((bloop_pp _ _)^ @ _).
      symmetry.
      apply ap, codes_transport.
    + intros x y.
      simpl.
      apply ds_G1.
      apply dp_path_transport.
      serapply path_ishprop.
      rewrite <- (path_universe dp_path_transport).
      exact _.
  Defined.

  Local Lemma decode_encode `{Group} : forall z p, decode z (encode z p) = p.
  Proof.
    intros z p.
    destruct p.
    apply bloop_id.
  Defined.

  (* Universal property of BG *)
  Lemma equiv_loops_BG_G `{Group G} : loops (B G) <~> G.
  Proof.
    serapply equiv_adjointify.
    + exact (encode _).
    + exact bloop.
    + intro x.
      refine (codes_transport _ _ @ _).
      apply left_identity.
    + intro.
      apply (decode_encode (bbase G) x).
  Defined.

  Lemma pequiv_loops_BG_G `{Group G}
    : loops (B G) <~>* Build_pType G Aunit.
  Proof.
    serapply Build_pEquiv'.
    1: apply equiv_loops_BG_G.
    reflexivity.
  Defined.

End EncodeDecode.

Global Instance isconnected_BG `{Univalence} `{Group G}
  : IsConnected 0 (B G).
Proof.
  serapply BuildContr.
  { exact (tr (bbase G)). }
  serapply Trunc_ind.
  serapply ClassifyingSpace_ind; cbn.
  + reflexivity.
  + intro x.
    apply dp_paths_FlFr.
    apply path_ishprop.
  + intros.
    apply ds_G1.
    apply dp_path_transport.
    serapply path_ishprop.
    rewrite <- (path_universe dp_path_transport).
    exact _.
Defined.

Definition bg_mul `{Univalence} `{AbGroup G} : B G -> B G -> B G.
Proof.
  serapply ClassifyingSpace_rec.
  1: apply idmap.
  { intro x.
    apply path_forall.
    serapply ClassifyingSpace_ind.
    1: exact (bloop x).
    { intro y.
      cbn.
      apply dp_paths_lr.
      refine (concat_pp_p _ _ _ @ _).
      apply moveR_Vp.
      refine ((bloop_pp _ _)^ @ _ @ bloop_pp _ _).
      apply ap.
      apply commutativity. }
    intros.
    simpl.
    apply ds_G1.
    apply dp_path_transport.
    serapply path_ishprop.
    rewrite <- (path_universe dp_path_transport).
    exact _. }
  intros x y.
  simpl.
  rewrite <- path_forall_pp.
  apply ap.
  apply path_forall.
  serapply ClassifyingSpace_ind.
  1: apply bloop_pp.
  { intro z.
    simpl.
    serapply dp_paths_FlFr_D.
    serapply path_ishprop. }
  intros.
  simpl.
  apply ds_G1.
  apply dp_path_transport.
  serapply path_ishprop.
  rewrite <- (path_universe dp_path_transport).
  exact _.
Defined.

Global Instance hspace_BG `{Univalence} `{AbGroup G} : HSpace (B G).
Proof.
  serapply Build_HSpace.
  1: apply bg_mul.
  { serapply ClassifyingSpace_ind.
    { reflexivity. }
    { intro. cbn. apply dp_paths_lr.
      refine (concat_pp_p _ _ _ @ _).
      apply moveR_Vp.
      refine (concat_1p _ @ 1 @ (concat_p1 _)^). }
    intros.
    simpl.
    apply ds_G1.
    apply dp_path_transport.
    serapply path_ishprop.
    rewrite <- (path_universe dp_path_transport).
    exact _. }
  { serapply ClassifyingSpace_ind.
    1: reflexivity.
    { intro; cbn.
      apply dp_paths_FlFr.
      rewrite concat_p1.
      apply moveR_Vp.
      rewrite ap_idmap, concat_p1.
      unfold bg_mul.
      rewrite ClassifyingSpace_rec.
Admitted.

