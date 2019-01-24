(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics HoTT.Types.
Require Import Constant Factorization UnivalenceImpliesFunext.
Require Import Modalities.Modality HIT.Truncations HIT.Connectedness.
Import TrM.
Require Import Spaces.BAut.

Local Open Scope trunc_scope.
Local Open Scope path_scope.

(** * BAut(Bool) *)

Section AssumeUnivalence.
  Context `{Univalence}.

  (** ** Nontrivial central homotopy *)

  (** The equivalence [Bool <~> (Bool <~> Bool)], and particularly its consequence [abelian_aut_bool], implies that [BAut Bool] has a nontrivial center.  *)

  Definition negb_center_baut_bool
  : forall (Z:BAut Bool), Z = Z.
  Proof.
    apply center_baut; try exact _.
    exists equiv_negb.
    intros g; apply abelian_aut_bool.
  Defined.

  Definition nontrivial_negb_center_baut_bool
  : negb_center_baut_bool <> (fun Z => idpath Z).
  Proof.
    intros oops.
    pose (p := ap10_equiv
                 ((ap (center_baut Bool))^-1
                  (oops @ (id_center_baut Bool)^))..1 true).
    exact (false_ne_true p).
  Defined.

  (** In particular, every element of [BAut Bool] has a canonical flip automorphism.  *)
  Definition negb_baut_bool (Z : BAut Bool) : Z <~> Z
    := equiv_path Z Z (negb_center_baut_bool Z)..1.

  Definition negb_baut_bool_ne_idmap (Z : BAut Bool)
  : negb_baut_bool Z <> equiv_idmap Z.
  Proof.
    intros oops.
    apply nontrivial_negb_center_baut_bool.
    apply path_forall; intros Z'.
    pose (p := merely_path_baut Z Z').
    clearbody p. strip_truncations.
    destruct p.
    unfold negb_baut_bool in oops.
    apply moveL_equiv_V in oops.
    refine (_ @ ap (equiv_path_sigma_hprop _ _)
                   (oops @ path_universe_1) @ _).
    - symmetry.
      refine (eisretr (equiv_path_sigma_hprop Z Z) _).
    - apply moveR_equiv_M; reflexivity.
  Defined.

  (** If [Z] is [Bool], then the flip is the usual one. *)
  Definition negb_baut_bool_bool_negb
  : negb_baut_bool (point _) = equiv_negb.
  Proof.
    pose (c := aut_bool_idmap_or_negb (negb_baut_bool (point _))).
    destruct c.
    - pose (negb_baut_bool_ne_idmap (point _) p).
      contradiction.
    - assumption.
  Defined.

  Definition ap_pr1_negb_baut_bool_bool
  : (negb_center_baut_bool (point _))..1 = path_universe negb.
  Proof.
    apply moveL_equiv_V.
    apply negb_baut_bool_bool_negb.
  Defined.

  (** Moreover, we can show that every automorphism of a [Z : BAut Bool] must be either the flip or the identity. *)
  Definition aut_baut_bool_idmap_or_negb (Z : BAut Bool) (e : Z <~> Z)
  : (e = equiv_idmap Z) + (e = negb_baut_bool Z).
  Proof.
    assert (IsHProp ((e = equiv_idmap Z) + (e = negb_baut_bool Z))).
    { apply ishprop_sum; try exact _.
      intros p q; exact (negb_baut_bool_ne_idmap Z (q^ @ p)). }
    baut_reduce.
    case (aut_bool_idmap_or_negb e).
    - intros p; exact (inl p).
    - intros q; apply inr.
      exact (q @ negb_baut_bool_bool_negb^).
  Defined.

  (** ** Connectedness *)

  Global Instance isminusoneconnected_baut_bool `{Funext} (Z : BAut Bool)
  : IsConnected -1 Z.
  Proof.
    baut_reduce.
    apply contr_inhabited_hprop; try exact _.
    exact (tr true).
  Defined.

  Definition merely_inhab_baut_bool `{Funext} (Z : BAut Bool)
  : merely Z
    := center (merely Z).

  (** ** Equivalence types *)

  (** As soon as an element of [BAut Bool] is inhabited, it is (purely) equivalent to [Bool].  (Of course, every element of [BAut Bool] is *merely* inhabited, since [Bool] is.)  In fact, it is equivalent in two canonical ways.

First we define the function that will be the equivalence. *)
  Definition inhab_baut_bool_from_bool (t : Bool)
             (Z : BAut Bool) (z : Z)
  : Bool -> Z
    := fun b => if t then
                  if b then z else negb_baut_bool Z z
                else
                  if b then negb_baut_bool Z z else z.

  (** We compute this in the case when [Z] is [Bool]. *)
  Definition inhab_baut_bool_from_bool_bool (t : Bool)
  : inhab_baut_bool_from_bool t (point _) =
    fun (z : point (BAut Bool)) (b : Bool) =>
      if t then
        if b then z else negb z
      else
        if b then negb z else z.
  Proof.
    apply path_forall; intros z'; simpl in z'.
    apply path_forall; intros b.
    destruct z', b, t; simpl;
    try reflexivity;
    try apply (ap10_equiv negb_baut_bool_bool_negb).
  Defined.

  (** Now we show that it is an equivalence. *)
  Global Instance isequiv_inhab_baut_bool_from_bool (t : Bool)
         (Z : BAut Bool) (z : Z)
  : IsEquiv (inhab_baut_bool_from_bool t Z z).
  Proof.
    baut_reduce.
    refine (transport IsEquiv (ap10 (inhab_baut_bool_from_bool_bool t)^ z) _).
    simpl in z; destruct z, t; simpl.
    - refine (isequiv_homotopic idmap _); intros []; reflexivity.
    - apply isequiv_negb.
    - apply isequiv_negb.
    - refine (isequiv_homotopic idmap _); intros []; reflexivity.
  Defined.

  Definition equiv_inhab_baut_bool_bool (t : Bool)
             (Z : BAut Bool) (z : Z)
  : Bool <~> Z
    := BuildEquiv _ _ (inhab_baut_bool_from_bool t Z z) _.

  Definition path_baut_bool_inhab (Z : BAut Bool) (z : Z)
  : (point (BAut Bool)) = Z.
  Proof.
    apply path_baut.
    exact (equiv_inhab_baut_bool_bool true Z z). (** [true] is a choice! *)
  Defined.

  (** In fact, the map sending [z:Z] to this equivalence [Bool <~> Z] is also an equivalence.  To assist with computing the result when [Z] is [Bool], we prove it with an extra parameter first. *)
  Definition isequiv_equiv_inhab_baut_bool_bool_lemma
             (t : Bool) (Z : BAut Bool) (m : merely (point _ = Z))
  : IsEquiv (equiv_inhab_baut_bool_bool t Z).
  Proof.
    strip_truncations. destruct m.
    refine (isequiv_adjointify _ (fun (e : Bool <~> Bool) => e t) _ _).
    + intros e.
      apply path_equiv.
      refine (ap10 (inhab_baut_bool_from_bool_bool t) (e t) @ _).
      apply path_arrow; intros []; destruct t.
      * reflexivity.
      * refine (abelian_aut_bool equiv_negb e false).
      * refine (abelian_aut_bool equiv_negb e true).
      * reflexivity.
    + intros z.
      refine (ap10 (ap10 (inhab_baut_bool_from_bool_bool t) z) t @ _).
      destruct t; reflexivity.
  Defined.

  Global Instance isequiv_equiv_inhab_baut_bool_bool
         (t : Bool) (Z : BAut Bool)
  : IsEquiv (equiv_inhab_baut_bool_bool t Z).
  Proof.
    exact (isequiv_equiv_inhab_baut_bool_bool_lemma t Z
            (merely_path_baut _ _)).
  Defined.

  (** The names are getting pretty ridiculous; below we suggest a better name for this. *)
  Definition equiv_equiv_inhab_baut_bool_bool (t : Bool)
             (Z : BAut Bool)
  : Z <~> (Bool <~> Z)
    := BuildEquiv _ _ (equiv_inhab_baut_bool_bool t Z) _.

  (** We compute its inverse in the case of [Bool]. *)
  Definition equiv_equiv_inhab_baut_bool_bool_bool_inv (t : Bool)
             (e : Bool <~> Bool)
  : equiv_inverse (equiv_equiv_inhab_baut_bool_bool t (point _)) e = e t.
  Proof.
    pose (alt := BuildEquiv _ _ (equiv_inhab_baut_bool_bool t (point _))
                   (isequiv_equiv_inhab_baut_bool_bool_lemma
                      t (point _) (tr 1))).
    assert (p : equiv_equiv_inhab_baut_bool_bool t (point _) = alt).
    { apply (ap (fun i => BuildEquiv _ _ _ i)).
      apply (ap (isequiv_equiv_inhab_baut_bool_bool_lemma t (point _))).
      apply path_ishprop. }
    exact (ap10_equiv (ap equiv_inverse p) e).
  Defined.

  (** ** Group structure *)

  (** Homotopically, [BAut Bool] is a [K(Z/2,1)].  In particular, it has a (coherent) abelian group structure induced from that of [Z/2].  With our definition of [BAut Bool], we can construct this operation as follows. *)

  Definition baut_bool_pairing : BAut Bool -> BAut Bool -> BAut Bool.
  Proof.
    intros Z W.
    exists (Z <~> W).
    baut_reduce; simpl.
    apply tr, symmetry.
    exact (path_universe equiv_bool_aut_bool).
  Defined.

  Declare Scope baut_bool_scope.
  Notation "Z ** W" := (baut_bool_pairing Z W) : baut_bool_scope.
  Local Open Scope baut_bool_scope.

  Local Notation pt := (point (BAut Bool)).

  (** Now [equiv_equiv_inhab_baut_bool_bool] is revealed as simply the left unit law of this pairing. *)
  Definition baut_bool_pairing_1Z Z : pt ** Z = Z.
  Proof.
    apply path_baut, equiv_inverse, equiv_equiv_inhab_baut_bool_bool.
    exact true.                   (** This is a choice! *)
  Defined.

  (** The pairing is obviously symmetric. *)
  Definition baut_bool_pairing_symm Z W : Z ** W = W ** Z.
  Proof.
    apply path_baut, equiv_equiv_inverse.
  Defined.

  (** Whence we get the right unit law as well. *)
  Definition baut_bool_pairing_Z1 Z : Z ** pt = Z
    := baut_bool_pairing_symm Z pt @ baut_bool_pairing_1Z Z.

  (** Every element is its own inverse. *)
  Definition baut_bool_pairing_ZZ Z : Z ** Z = pt.
  Proof.
    apply symmetry, path_baut_bool_inhab.
    apply equiv_idmap.            (** A choice!  Could be the flip. *)
  Defined.

  (** Associativity is easiest to think about in terms of "curried 2-variable equivalences".  We start with some auxiliary lemmas. *)
  Definition baut_bool_pairing_ZZ_Z_symm_part1 {Y Z W}
             (e : Y ** (Z ** W)) (z : Z)
  : Y ** W.
  Proof.
    simple refine (equiv_adjointify _ _ _ _).
    + exact (fun y => e y z).
    + intros w.
      destruct (path_baut_bool_inhab W w).
      destruct (path_baut_bool_inhab Z z).
      (** It might be tempting to just say [e^-1 (equiv_idmap _)] here, but for the rest of the proof to work, we actually need to choose between [idmap] and [negb] based on whether [z] and [w] are equal or not. *)
      destruct (dec (z=w)).
      exact (e^-1 (equiv_idmap _)).
      exact (e^-1 equiv_negb).
    + intros w.
      destruct (path_baut_bool_inhab W w).
      destruct (path_baut_bool_inhab Z z).
      simpl.
      destruct z,w; simpl; refine (ap10_equiv (eisretr e _) _).
    + intros y.
      destruct (path_baut_bool_inhab Y y).
      destruct (path_baut_bool_inhab Z z).
      destruct (path_baut_bool_inhab W (e y z)).
      simpl.
      case (dec (z = e y z)); intros p; apply moveR_equiv_V;
      destruct (aut_bool_idmap_or_negb (e y)) as [q|q].
      * symmetry; assumption.
      * case (not_fixed_negb z (p @ ap10_equiv q z)^).
      * case (p (ap10_equiv q z)^).
      * symmetry; assumption.
  Defined.

  Definition baut_bool_pairing_ZZ_Z_symm_lemma {Y Z W}
             (e : Y ** (Z ** W)) (f : Y ** W)
  : merely Y -> Z.
  Proof.
    pose (k := (fun y => (e y)^-1 (f y))).
    refine (merely_rec_hset k); intros y1 y2.
    destruct (path_baut_bool_inhab Y y1).
    destruct (path_baut_bool_inhab W (f y1)).
    destruct (path_baut_bool_inhab Z (k y1)).
    destruct (aut_bool_idmap_or_negb f) as [p|p];
      refine (ap (e y1)^-1 (ap10_equiv p y1) @ _);
      refine (_ @ (ap (e y2)^-1 (ap10_equiv p y2))^);
      clear p f k; simpl.
    + destruct (dec (y1=y2)) as [p|p].
      { exact (ap (fun y => (e y)^-1 y) p). }
      destruct (aut_bool_idmap_or_negb (e y1)) as [q1|q1];
        destruct (aut_bool_idmap_or_negb (e y2)) as [q2|q2].
      * case (p ((ap e)^-1 (q1 @ q2^))).
      * rewrite q1, q2. exact (negb_ne p).
      * rewrite q1, q2. symmetry. exact (negb_ne (fun r => p r^)).
      * case (p ((ap e)^-1 (q1 @ q2^))).
    + destruct (dec (y1=y2)) as [p|p].
      { exact (ap (fun y => (e y)^-1 (negb y)) p). }
      destruct (aut_bool_idmap_or_negb (e y1)) as [q1|q1];
        destruct (aut_bool_idmap_or_negb (e y2)) as [q2|q2].
      * case (p ((ap e)^-1 (q1 @ q2^))).
      * rewrite q1, q2.
        exact (negb_ne (fun r => p ((ap negb)^-1 r))).
      * rewrite q1, q2. symmetry.
        exact (negb_ne (fun r => p ((ap negb)^-1 r)^)).
      * case (p ((ap e)^-1 (q1 @ q2^))).
  Defined.

  Definition baut_bool_pairing_ZZ_Z_symm_map Y Z W
  : Y ** (Z ** W) -> Z ** (Y ** W).
  Proof.
    intros e.
    simple refine (equiv_adjointify (baut_bool_pairing_ZZ_Z_symm_part1 e)
                             _ _ _).
    - intros f.
      exact (baut_bool_pairing_ZZ_Z_symm_lemma e f
               (merely_inhab_baut_bool Y)).
    - intros f.
      apply path_equiv, path_arrow; intros y.
      change ((e y)
                (baut_bool_pairing_ZZ_Z_symm_lemma e f
                  (merely_inhab_baut_bool Y)) = f y).
      refine (ap (e y o baut_bool_pairing_ZZ_Z_symm_lemma e f)
                 (path_ishprop _ (tr y)) @ _).
      simpl. apply eisretr.
    - intros z.
      assert (IsHSet Z) by exact _.
      refine (Trunc_rec _ (merely_inhab_baut_bool Y)); intros y.
      refine (ap (baut_bool_pairing_ZZ_Z_symm_lemma e _)
                 (path_ishprop _ (tr y)) @ _).
      simpl. refine (eissect _ _).
  Defined.

  Definition baut_bool_pairing_ZZ_Z_symm_inv Y Z W
  : baut_bool_pairing_ZZ_Z_symm_map Y Z W
    o baut_bool_pairing_ZZ_Z_symm_map Z Y W
    == idmap.
  Proof.
    intros e.
    apply path_equiv, path_arrow; intros z.
    apply path_equiv, path_arrow; intros y.
    reflexivity.
  Defined.

  Definition baut_bool_pairing_ZZ_Z_symm Y Z W
  : Y ** (Z ** W) <~> Z ** (Y ** W).
  Proof.
    refine (equiv_adjointify
              (baut_bool_pairing_ZZ_Z_symm_map Y Z W)
              (baut_bool_pairing_ZZ_Z_symm_map Z Y W)
              (baut_bool_pairing_ZZ_Z_symm_inv Y Z W)
              (baut_bool_pairing_ZZ_Z_symm_inv Z Y W)).
  Defined.

  (** Finally, we can prove associativity. *)
  Definition baut_bool_pairing_ZZ_Z Z W Y
  : (Z ** W) ** Y = Z ** (W ** Y).
  Proof.
    refine (baut_bool_pairing_symm (Z ** W) Y @ _).
    refine (_ @ ap (fun X => Z ** X) (baut_bool_pairing_symm Y W)).
    apply path_baut, baut_bool_pairing_ZZ_Z_symm.
  Defined.

  (** Since [BAut Bool] is not a set, we ought to have some coherence for these operations too, but we'll leave that for another time. *)

  (** ** Automorphisms of [BAut Bool] *)

  (** Interestingly, like [Bool] itself, [BAut Bool] is equivalent to its own automorphism group. *)

  (** An initial lemma: every automorphism of [BAut Bool] and its inverse are "adjoint" with respect to the pairing. *)
  Definition aut_baut_bool_moveR_pairing_V
             (e : BAut Bool <~> BAut Bool) (Z W : BAut Bool)
  : (e^-1 Z ** W) = (Z ** e W).
  Proof.
    apply path_baut; simpl.
    refine ((equiv_equiv_path _ _) oE _ oE (equiv_equiv_path _ _)^-1).
    refine (_ oE (@equiv_moveL_equiv_M _ _ e _ W Z) oE _).
    - apply equiv_inverse, equiv_path_sigma_hprop.
    - apply equiv_path_sigma_hprop.
  Defined.

  Definition equiv_baut_bool_aut_baut_bool
  : BAut Bool <~> (BAut Bool <~> BAut Bool).
  Proof.
    simple refine (equiv_adjointify _ _ _ _).
    - intros Z.
      refine (equiv_involution (fun W => Z ** W) _).
      intros W.
      refine ((baut_bool_pairing_ZZ_Z Z Z W)^ @ _).
      refine (_ @ baut_bool_pairing_1Z W).
      apply (ap (fun Y => Y ** W)).
      apply baut_bool_pairing_ZZ.
    - intros e.
      exact (e^-1 pt).
    - intros e.
      apply path_equiv, path_arrow; intros Z; simpl.
      refine (aut_baut_bool_moveR_pairing_V e pt Z @ _).
      apply baut_bool_pairing_1Z.
    - intros Z.
      apply baut_bool_pairing_Z1.
  Defined.

  (** ** [BAut (BAut Bool)]  *)

  (** Putting all of this together, we can construct a nontrivial 2-central element of [BAut (BAut Bool)]. *)

  Definition center_baut_bool_central
             (g : BAut Bool <~> BAut Bool) (W : BAut Bool)
  : ap g (negb_center_baut_bool W) = negb_center_baut_bool (g W).
  Proof.
    revert g; equiv_intro equiv_baut_bool_aut_baut_bool Z.
    simpl.
    baut_reduce.
    refine (_ @ apD negb_center_baut_bool (baut_bool_pairing_1Z pt)^).
    rewrite transport_paths_lr, inv_V.
    apply moveL_pV.
    exact (concat_A1p baut_bool_pairing_1Z (negb_center_baut_bool pt)).
  Qed.

  Definition negb_center2_baut_baut_bool
  : forall B : BAut (BAut Bool), (idpath B) = (idpath B).
  Proof.
    refine (center2_baut (BAut Bool) _).
    exists negb_center_baut_bool.
    apply center_baut_bool_central.
  Defined.

  Definition nontrivial_negb_center_baut_baut_bool
  : negb_center2_baut_baut_bool <> (fun Z => idpath (idpath Z)).
  Proof.
    intros oops.
    exact (nontrivial_negb_center_baut_bool
             (((ap (center2_baut (BAut Bool)))^-1
                (oops @ (id_center2_baut (BAut Bool))^))..1)).
  Defined.

End AssumeUnivalence.
