Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Cubical.
Require Import abstract_algebra.
Require Import TruncType.
Require Import HIT.Truncations.
Import TrM.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.

(* TODO: Generalise this to H-spaces?
  This however might require H-spaces to be more general than groups in the library. *)
(* Definition of Classifying Spaces of a Group *)
Module Export ClassifyingSpace.

  (* We define the classifying space of a group X as a HIT with the following
    constructors:
      * A point   base : B X
      * a path    bloop : forall x, base = base
      * a 2-path  bloop_pp : forall x y, bloop (x * y) = bloop x @ bloop y
      * a proof that B X is 1-truncated

    It can be proven that bloop e = idpath and bloop p^-1 = (bloop p)^. *)

  Private Inductive ClassifyingSpace (X : Type) `{Group X} :=
    | base : ClassifyingSpace X.

  Arguments base X {Aop Aunit Anegate H}.

  Axiom bloop : forall `{Group X}, X -> base X = base X.

  Axiom bloop_pp : forall `{Group X},
    forall x y, bloop (x & y) = bloop x @ bloop y.

  (* Faking truncation *)
  Global Instance istrunc_ClassifyingSpace `{Group X}
  : IsTrunc 1 (ClassifyingSpace X).
  Proof. Admitted.
(*
  Definition ClassifyingSpace_ind' (X : Type) `{Group X}
    (P : ClassifyingSpace X -> Type) `{IsTrunc 1 (P (base X))}
    (base' : P (base X))
    (bloop' : forall x, (bloop x) # base' = base')
    (bloop_pp' : forall x y,
      change_path (bloop_pp x y) (bloop' (x & y))
      = concato (bloop' x) (bloop' y))
    : forall x, P x := fun x => (match x return (_ -> P x) with
        base => (fun _ => base') end) bloop. *)

Local Open Scope dpath_scope.

  (* The induction principle for the classifying space takes a
      - point base' from P(base X)
      - forall x, a dependent path from base' to base' called bloop'
      - forall x y, a dependent square that maps between bloop' (x & y)
        and (bloop' x) @D (bloop' y). *)

  Definition ClassifyingSpace_ind (X : Type) `{Group X}
    (P : ClassifyingSpace X -> Type) `{IsTrunc 1 (P (base X))}
    (base' : P (base X))
    (bloop' : forall x, DPath P (bloop x) base' base')
    (bloop_pp' : forall x y,  DSquare P (sq_G1 (bloop_pp x y))
      (bloop' (x & y)) ((bloop' x) @D (bloop' y)) 1 1) x : P x
    := match x return (_ -> P x) with
          base => (fun _ => base')
       end bloop.

  Axiom ClassifyingSpace_ind_beta_bloop : forall (X : Type) `{Group X}
    (P : ClassifyingSpace X -> Type) `(IsTrunc 1 (P (base X)))
    (base' : P (base X)) (bloop' : forall x, DPath P (bloop x) base' base')
    (bloop_pp' : forall x y,  DSquare P (sq_G1 (bloop_pp x y))
      (bloop' (x & y)) ((bloop' x) @D (bloop' y)) 1 1) (x : X),
    dp_apD (ClassifyingSpace_ind X P base' bloop' bloop_pp') (bloop x) = bloop' x.


  Definition ClassifyingSpace_rec (X : Type) `{Group X}
    (P : Type) `{IsTrunc 1 P} (base' : P) (bloop' : X -> base' = base')
    (bloop_pp' : forall x y : X, bloop' (x & y) = bloop' x @ bloop' y)
    : ClassifyingSpace X -> P.
  Proof.
    srefine (ClassifyingSpace_ind X (fun _ => P) base' _ _).
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
    (P : Type) `{IsTrunc 1 P} (base' : P) (bloop' : X -> base' = base')
    (bloop_pp' : forall x y : X, bloop' (x & y) = bloop' x @ bloop' y) (x : X)
    : ap (ClassifyingSpace_rec X P base' bloop' bloop_pp') (bloop x) = bloop' x.
  Proof.
    rewrite <- dp_apD_const'.
    unfold ClassifyingSpace_rec.
    rewrite ClassifyingSpace_ind_beta_bloop.
    apply eissect.
  Qed.

End ClassifyingSpace.

Global Instance ispointed_BG `{Group G} : IsPointed (ClassifyingSpace G).
Proof.
  exact (base G).
Defined.

Definition B (G : Type) `{Group G} := Build_pType (ClassifyingSpace G) _.

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

  Local Definition encode `{Group G} : forall z, base G = z -> codes z.
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

  Local Definition decode `{Group G} : forall (z : B G), codes z -> base G = z.
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
      apply (decode_encode (base G) x).
  Defined.

  (* We also give the pointed version for later *)
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
  { exact (tr (base G)). }
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
