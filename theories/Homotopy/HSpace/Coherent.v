Require Import Basics HSpace.Core Pointed.Core Pointed.Loops.

Local Open Scope mc_mult_scope.
Local Open Scope pointed_scope.

(** ** Coherent H-space structures *)

(** An H-space is coherent when the left and right identities agree at the base point. *)

Class IsCoherent (X : pType) `{IsHSpace X} :=
  iscoherent : left_identity pt = right_identity pt.

Class IsCohHSpace (A : pType) := {
  ishspace_cohhspace :: IsHSpace A;
  iscoherent_cohhspace :: IsCoherent A;
}.

Definition issig_iscohhspace (A : pType)
  : { hspace_op : SgOp A
    & { hspace_left_identity : LeftIdentity hspace_op pt
    & { hspace_right_identity : RightIdentity hspace_op pt
    & hspace_left_identity pt = hspace_right_identity pt } } }
      <~> IsCohHSpace A.
Proof.
  transitivity { H : IsHSpace A & IsCoherent A }.
  2: issig.
  unfold IsCoherent.
  make_equiv.
Defined.

(** A type equivalent to a coherent H-space is a coherent H-space. *)
Definition iscohhspace_equiv_cohhspace {X Y : pType} `{IsCohHSpace Y} (f : X <~>* Y)
  : IsCohHSpace X.
Proof.
  snrapply Build_IsCohHSpace.
  - rapply (ishspace_equiv_hspace f).
  - unfold IsCoherent; cbn.
    refine (_ @@ 1).
    refine (ap (ap f^-1) _).
    pelim f.
    refine (1 @@ _).
    apply iscoherent.
Defined.

(** Every loop space is a coherent H-space. *)
Definition iscohhspace_loops {X : pType} : IsCohHSpace (loops X).
Proof.
  snrapply Build_IsCohHSpace.
  - apply ishspace_loops.
  - reflexivity.
Defined.

(** A 0-truncated H-space is a coherent H-space. *)
Global Instance iscoherent_hset (X : pType) `{IsHSpace X} `{IsHSet X}
  : IsCoherent X.
Proof.
  apply path_ishprop.
Defined.

(** A coherently associative H-space is a H-space in which the operation is associative together with an additional coherence. *)
Class IsCohAssociative (X : pType) `{IsHSpace X} := {
  associative_iscohassoc :: Associative (.*.);
  associative_iscohassoc_coh : simple_associativity pt pt pt
      = ap (pt *.) (left_identity pt) @ ap (.* pt) (left_identity pt)^;
}.

(** A 0-truncated H-space whose operation is associative is coherently associative. *)
Global Instance iscohassoc_hset (X : pType) `{IsHSpace X} `{!Associative (.*.)} `{IsHSet X}
  : IsCohAssociative X.
Proof.
  snrapply Build_IsCohAssociative.
  1: exact _.
  apply path_ishprop.
Defined.

(** A coherent H-monoid, also known as a coherent A_3-space, is a coherent H-space that is also coherently associative. *)
Class IsCohHMonoid (A : pType) := {
  iscohhspace_iscohhmonoid :: IsCohHSpace A;
  iscohassoc_cohassochspace :: IsCohAssociative A;
}.

(** A type equivalent to a coherent H-monoid is a coherent H-monoid. *)
Definition iscohhmonoid_equiv_cohmonoid {X Y : pType} `{IsCohHMonoid Y} (f : X <~>* Y)
  : IsCohHMonoid X.
Proof.
  snrapply Build_IsCohHMonoid.
  - rapply (iscohhspace_equiv_cohhspace f).
  - snrapply Build_IsCohAssociative.
    + intros x y z.
      nrefine (ap f^-1 _).
      lhs nrapply ap.
      1: apply eisretr.
      rhs nrapply (ap (.* _)).
      2: apply eisretr.
      apply associative_iscohassoc.
    + unfold simple_associativity; cbn.
      (** The path algebra is a little complicated but still straightforward. *)
      rhs nrapply (_ @@ _).
      2: { lhs nrefine (ap_compose (fun x => sg_op (f x) _) f^-1 _).
        nrapply ap.
        nrapply (ap_compose f (fun x => sg_op x _)). }
      2: { lhs nrefine (ap_compose (fun x => sg_op _ (f x)) f^-1 _).
        nrapply ap.
        nrapply (ap_compose f (sg_op _)). }
      rhs_V nrapply ap_pp.
      nrapply ap.
      rhs nrapply (ap _ _ @@ ap _ _).
      2: lhs nrapply ap; [nrapply inv_pp|].
      2,3: lhs nrapply ap_pp.
      2: nrefine (1 @@ _).
      3: nrefine (_ @@ 1).
      2: lhs_V nrapply ap; [ apply ap_V | ].
      2,3: lhs_V nrapply ap_compose.
      2,3: nrapply (ap_homotopic (eisretr f)).
      (** I gave up avoiding rewrite here. TODO: remove rewrite *)
      rewrite eisadj.
      rewrite 2 ap_idmap.
      rewrite ap_V.
      rewrite ? concat_pp_p.
      rewrite concat_Vp.
      rewrite ? concat_p_pp.
      rewrite concat_Vp.
      hott_simpl.
      (** This is finally simple enough that we can use [pelim]. *)
      pelim f.
      simpl.
      apply moveR_pV.
      apply moveR_Mp.
      lhs nrapply associative_iscohassoc_coh.
      rewrite concat_1p, concat_p1.
      apply moveL_Vp.
      rhs nrapply concat_pp_p.
      rewrite ap_pp.
      rhs nrapply concat_pp_p.
      f_ap. f_ap.
      rewrite ap_pp.
      rhs nrapply concat_pp_p.
      rewrite ap_V.
      apply moveL_Vp. 
      rewrite concat_pV.
      rewrite ap_V.
      symmetry.
      apply concat_Vp.
Defined.

Definition iscohhmonoid_loops {X : pType} : IsCohHMonoid (loops X).
Proof.
  snrapply Build_IsCohHMonoid.
  - apply iscohhspace_loops.
  - snrapply Build_IsCohAssociative.
    + intros p q r.
      apply concat_p_pp.
    + reflexivity.
Defined.

(** A coherently commutative H-space is a H-space in which the operation is commutative together with an additional coherence. *)
Class IsCohCommutative (X : pType) `{IsHSpace X} := {
  commutative_iscohcommutative :: Commutative (.*.);
  iscohcommutative : commutativity pt pt = 1;
}.

(** A 0-truncated H-space whose operation is commutative is coherently commutative. *)
Global Instance iscohcommutative_hset (X : pType) `{IsHSpace X} `{!Commutative (.*.)} `{IsHSet X}
  : IsCohCommutative X.
Proof.
  snrapply Build_IsCohCommutative.
  1: exact _.
  apply path_ishprop.
Defined.

(** A type equivalent to a H-space with a coherent commutative operation is a H-space with a coherent commutative operation. *)
Definition iscohcommutative_equiv_cohcommutative {X Y : pType} `{IsCohCommutative Y} (f : X <~>* Y)
  : @IsCohCommutative X (ishspace_equiv_hspace f).
Proof.
  snrapply Build_IsCohCommutative.
  - intros x y.
    nrefine (ap f^-1 _).
    apply commutativity.
  - unfold commutativity; cbn.
    pelim f.
    change (?x = _) with (x = ap f^-1 1).
    nrapply ap.
    apply iscohcommutative.
Defined.

Definition iscohcommutative_loops_loops {X : pType}
  : @IsCohCommutative (loops (loops X)) ishspace_loops.
Proof.
  snrapply Build_IsCohCommutative.
  - intros p q.
    apply eckmann_hilton.
  - reflexivity.
Defined.

(** A coherent H-commutative monoid is a coherent H-monoid that is also coherently commutative. This is not an E_3-space as it would also have to be an A_oo-space. *)
Class IsCohHCommutativeMonoid (A : pType) := {
  iscohhmonoid_iscohhcommutativemonoid :: IsCohHMonoid A;
  iscohcommutative_cohcommutativemonoid :: IsCohCommutative A;
}.

(** A type equivalent to a coherent H-commutative monoid is a coherent H-commutative monoid. *)
Definition iscohhcommutativemonoid_equiv_cohcommutativemonoid
  {X Y : pType} `{IsCohHCommutativeMonoid Y} (f : X <~>* Y)
  : IsCohHCommutativeMonoid X.
Proof.
  snrapply Build_IsCohHCommutativeMonoid.
  - rapply (iscohhmonoid_equiv_cohmonoid f).
  - rapply (iscohcommutative_equiv_cohcommutative f).
Defined.

Definition iscohcommutativemonoid_loops_loops {X : pType}
  : IsCohHCommutativeMonoid (loops (loops X)).
Proof.
  snrapply Build_IsCohHCommutativeMonoid.
  - apply iscohhmonoid_loops.
  - apply iscohcommutative_loops_loops.
Defined.

(** A coherent H-group is a coherent H-space in which every element has an inverse in a coherent way. *)
Class IsCohHGroup (A : pType) := {
  iscohhmonoid_iscohhgroup :: IsCohHMonoid A;
  negate_cohhgroup :: Negate A;
  negate_coh : negate pt = pt;
  left_inverse_cohhgroup :: LeftInverse (.*.) negate_cohhgroup pt;
  left_inverse_coh : left_inverse pt = ap (.* pt) negate_coh @ hspace_left_identity pt;
  right_inverse_cohhgroup :: RightInverse (.*.) negate_cohhgroup pt;
  right_inverse_coh : right_inverse pt = ap (pt *.) negate_coh @ hspace_left_identity pt;
}.

(** A type equivalent to a coherent H-group is a coherent H-group. *)
Definition iscohhgroup_equiv_cohhgroup {X Y : pType} `{IsCohHGroup Y} (f : X <~>* Y)
  : IsCohHGroup X.
Proof.
  snrapply Build_IsCohHGroup.
  - rapply (iscohhmonoid_equiv_cohmonoid f).
  - intros x.
    apply f^-1.
    apply negate.
    apply f.
    exact x.
  - unfold negate.
    apply moveR_equiv_V.
    refine (ap _ (point_eq f) @ _ @ (point_eq f)^).
    apply negate_coh.
  - intros x.
    simpl.
    unfold sg_op.
    apply moveR_equiv_V.
    lhs nrapply (ap (.* _)).
    1: apply eisretr.
    lhs apply left_inverse.
    symmetry.
    apply point_eq. 
  - simpl.
    (** TODO: Simplify this proof *) 
    unfold moveR_equiv_V.
    unfold left_inverse.
    rhs nrapply concat_p_pp.
    nrefine (_ @@ 1).
    apply moveL_pM.
    rewrite <- (ap_V f^-1).
    rewrite <- (ap_pp f^-1).
    unfold sg_op.
    simpl.
    symmetry.
    nrefine (ap_compose (fun x => sg_op (f x) _) f^-1 _ @ _).
    nrapply ap.
    lhs nrapply (ap_pp ((.* _) o f)).
    apply moveR_pM.
    lhs nrapply (ap_compose f (.* _)).
    lhs nrapply ap.
    { lhs_V nrapply (ap_compose f^-1 f).
      nrapply (ap_homotopic (eisretr f)). }
    rewrite ap_idmap.
    rewrite ap_pp.
    f_ap.
    { rewrite ap_pp.
      rhs nrapply concat_pp_p.
      f_ap.
      rewrite ap_pp.
      apply moveL_pV.
      pelim f.
      simpl.
      hott_simpl.
      symmetry.
      apply left_inverse_coh. }
    lhs nrapply (ap_V (.* _)).
    apply inverse2.
    rhs nrapply (ap_compose f (.* _)).
    apply ap.
    apply eisadj.
  - intros x.
    simpl.
    unfold sg_op.
    apply moveR_equiv_V.
    lhs nrapply (ap (_ *.)).
    1: apply eisretr.
    lhs apply right_inverse.
    symmetry.
    apply point_eq.
  - simpl.
    (** TODO: simplify proof *)
    unfold moveR_equiv_V.
    unfold right_inverse.
    rhs nrapply concat_p_pp.
    nrefine (_ @@ 1).
    apply moveL_pM.
    rewrite <- (ap_V f^-1).
    rewrite <- (ap_pp f^-1).
    unfold sg_op.
    simpl.
    symmetry.
    nrefine (ap_compose (fun x => sg_op _ (f x)) f^-1 _ @ _).
    nrapply ap.
    lhs nrapply (ap_pp (sg_op _ o f)).
    apply moveR_pM.
    lhs nrapply (ap_compose f (sg_op _)).
    lhs nrapply ap.
    { lhs_V nrapply (ap_compose f^-1 f).
      nrapply (ap_homotopic (eisretr f)). }
    rewrite ap_idmap.
    rewrite ap_pp.
    f_ap.
    { rewrite ap_pp.
      rhs nrapply concat_pp_p.
      f_ap.
      rewrite ap_pp.
      apply moveL_pV.
      pelim f.
      simpl.
      hott_simpl.
      symmetry.
      apply right_inverse_coh. }
    lhs nrapply (ap_V (_ *.)).
    apply inverse2.
    rhs nrapply (ap_compose f (sg_op _)).
    apply ap.
    apply eisadj.
Defined.

Definition iscohgroup_loops {X : pType} : IsCohHGroup (loops X).
Proof.
  snrapply Build_IsCohHGroup.
  - apply iscohhmonoid_loops.
  - intros p.
    exact p^.
  - reflexivity.
  - intros p.
    apply concat_Vp.
  - reflexivity.
  - intros p.
    apply concat_pV.
  - reflexivity.
Defined.

(** A coherent H-Abelian group is a coherent H-group in which the operation is commutative. *)
Class IsCohHAbGroup (A : pType) := {
  iscohgroup_cohabgroup :: IsCohHGroup A;
  commutative_cohabgroup :: IsCohCommutative A;
}.

(** A type equivalent to a coherent H-Abelian group is a coherent H-Abelian group. *)
Definition iscohhabgroup_equiv_cohhabgroup {X Y : pType} `{IsCohHAbGroup Y} (f : X <~>* Y)
  : IsCohHAbGroup X.
Proof.
  snrapply Build_IsCohHAbGroup.
  - rapply (iscohhgroup_equiv_cohhgroup f).
  - rapply (iscohcommutative_equiv_cohcommutative f).
Defined.

Definition iscohhabgroup_loops_loops {X : pType} : IsCohHAbGroup (loops (loops X)).
Proof.
  snrapply Build_IsCohHAbGroup.
  - apply iscohgroup_loops.
  - apply iscohcommutative_loops_loops.
Defined.
