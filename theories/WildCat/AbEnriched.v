Require Import WildCat.SetoidRewrite.
Import CMorphisms.ProperNotations.

Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.FunctorCat WildCat.ZeroGroupoid WildCat.Yoneda WildCat.UnitCat WildCat.Equiv WildCat.Products WildCat.Prod WildCat.Bifunctor WildCat.Monoidal.

(** See Groups/Group.v and AbGroups/AbelianGroup.v for additional things that it might be useful to export in the future. *)
Require Export Classes.interfaces.canonical_names (SgOp, sg_op,
    MonUnit, mon_unit, Inverse, inv).
Export canonical_names.BinOpNotations.

Local Open Scope mc_add_scope.

(** * Wild categories enriched in abelian groups *)

(** ** 0-groupoid abelian groups *)

(** Hom sets in wild categories are 0-groupoids, and we'd like to put an abelian group structure on these hom sets that satisfies the axioms up to 1-cells, to avoid needing function extensionality.  So we define the abstract idea of a 0-groupoid with an abelian group structure.  Because we use 1-cells, not paths, we can't reuse any of the work done in Algebra/Groups or Algebra/AbGroups. Note that our definition has redundant fields, which could be filled in using a "smart constructor":  [is0functor_inverse_0gpd], [mon_unit_r_0gpd], [inverse_r_0gpd] and the fact that [sgop_0gpd] is a 0-functor in the second variable. *)

Class IsAbGroup_0gpd (A : Type) `{Is0Gpd A} := {
    (* Data: *)
    sgop_0gpd :: SgOp A;
    mon_unit_0gpd :: MonUnit A;
    inverse_0gpd :: Inverse A;

    (* 0-functoriality: *)
    is0bifunctor_sgop_0gpd :: Is0Bifunctor sgop_0gpd;
    is0functor_inverse_0gpd :: Is0Functor inverse_0gpd;

    (* Axioms: *)
    assoc_0gpd : forall a b c, (a + b) + c $== a + (b + c);
    mon_unit_l_0gpd : forall a, 0 + a $== a;
    mon_unit_r_0gpd : forall a, a + 0 $== a;
    inverse_l_0gpd : forall a, (-a) + a $== 0;
    inverse_r_0gpd : forall a, a - a $== 0;
    comm_0gpd : forall a b, a + b $== b + a;
  }.

(** ** Setoid rewriting *)

(** [forall x y : A, x $== y -> forall x' y' : A, x' $== y' -> x + x' $== y + y']. *)
Instance IsProper_sgop_0gpd (A : Type) `{IsAbGroup_0gpd A}
  : CMorphisms.Proper (GpdHom ==> GpdHom ==> GpdHom) (sg_op (A:=A))
  := @fmap11 _ _ _ _ _ _ sg_op _.

(** [forall a x y : A, x $== y -> a + x $== a + y]. This is needed to rewrite on the RHS of a sum. LHS is handled by the two-argument version, but this isn't. *)
Instance IsProper_sgop_0gpd1 (A : Type) `{IsAbGroup_0gpd A} {a : A}
  : CMorphisms.Proper (GpdHom ==> GpdHom) (sg_op (A:=A) a)
  := @fmap01 _ _ _ _ _ _ sg_op _ a.

Instance IsProper_inverse_0gpd (A : Type) `{IsAbGroup_0gpd A}
  : CMorphisms.Proper (GpdHom ==> GpdHom) (inv (A:=A))
  := @fmap _ _ _ _ inv _.

(** ** A few lemmas about 0-groupoid abelian groups *)

(** We will try to parallel the naming in Group.v, when applicable. *)

Section Lemmas.

  Context {A : Type} `{IsAbGroup_0gpd A}.
  Context (x y : A).

  Definition inv_V_gg_0gpd : (-x) + (x + y) $== y
    := (assoc_0gpd _ _ _)^$ $@ fmap10 sg_op (inverse_l_0gpd x) y $@ mon_unit_l_0gpd _.

  Definition inv_g_Vg_0gpd : x + (-x + y) $== y
    := (assoc_0gpd _ _ _)^$ $@ fmap10 sg_op (inverse_r_0gpd x) y $@ mon_unit_l_0gpd _.

  Definition inv_gg_V_0gpd : (x + y) - y $== x
    := assoc_0gpd _ _ _ $@ fmap01 sg_op x (inverse_r_0gpd y) $@ mon_unit_r_0gpd _.

  Definition inv_gV_g_0gpd : (x - y) + y $== x
    := assoc_0gpd _ _ _ $@ fmap01 sg_op x (inverse_l_0gpd y) $@ mon_unit_r_0gpd _.

  Definition inv_inv_0gpd : - (-x) $== x.
  Proof.
    rhs_V' rapply mon_unit_l_0gpd.
    rewrite <- (inverse_l_0gpd (-x)).
    rhs' napply assoc_0gpd.
    rewrite inverse_l_0gpd.
    symmetry; apply mon_unit_r_0gpd.
  Defined.

End Lemmas.

(** ** We express the operations as maps of 0-groupoids *)

Definition zerogpd_0gpd (A : Type) `{IsAbGroup_0gpd A} : ZeroGpd
  := Build_ZeroGpd _ _ _ _.

Definition left_op_0gpd {A : Type} `{IsAbGroup_0gpd A} (a : A)
  : zerogpd_0gpd A $-> zerogpd_0gpd A
  := Build_Fun01' (fun b : A => a + b) (fun _ _ => fmap01 sg_op a).

Definition right_op_0gpd {A : Type} `{IsAbGroup_0gpd A} (a : A)
  : zerogpd_0gpd A $-> zerogpd_0gpd A
  := Build_Fun01' (fun b : A => b + a) (fun b b' p => fmap10 sg_op p a).

Definition inv_0gpd {A : Type} `{IsAbGroup_0gpd A}
  : zerogpd_0gpd A $-> zerogpd_0gpd A
  := Build_Fun01 inverse_0gpd.

(** ** The operations are equivalences *)

(** Addition on the left is biinvertible. *)
Instance cat_isbiinv_left_op_0gpd {A : Type} `{IsAbGroup_0gpd A} (a : A)
  : Cat_IsBiInv (left_op_0gpd a).
Proof.
  snapply Build_Cat_IsBiInv.
  1,3: exact (left_op_0gpd (-a)).
  all: intro b; simpl.
  - apply inv_g_Vg_0gpd.
  - apply inv_V_gg_0gpd.
Defined.

Definition left_op_0gpd' {A : Type} `{IsAbGroup_0gpd A} (a : A)
  := Build_Cat_BiInv _ _ _ _ _ _ _ (left_op_0gpd a) _.

(** Addition on the right is biinvertible. *)
Instance cat_isbiinv_right_op_0gpd {A : Type} `{IsAbGroup_0gpd A} (a : A)
  : Cat_IsBiInv (right_op_0gpd a).
Proof.
  snapply Build_Cat_IsBiInv.
  1,3: exact (right_op_0gpd (-a)).
  all: intro b; simpl.
  - apply inv_gV_g_0gpd.
  - apply inv_gg_V_0gpd.
Defined.

Definition right_op_0gpd' {A : Type} `{IsAbGroup_0gpd A} (a : A)
  := Build_Cat_BiInv _ _ _ _ _ _ _ (right_op_0gpd a) _.

(** Inversion is biinvertible. *)
Instance cat_isbiinv_inverse_0gpd {A : Type} `{IsAbGroup_0gpd A}
  : Cat_IsBiInv (inv_0gpd (A:=A)).
Proof.
  snapply Build_Cat_IsBiInv.
  1,3: exact inv_0gpd.
  all: intro b; simpl.
  all: apply inv_inv_0gpd.
Defined.

Definition inv_0gpd' {A : Type} `{IsAbGroup_0gpd A}
  := Build_Cat_BiInv _ _ _ _ _ _ _ (inv_0gpd (A:=A)) _.

(** ** General properties of a 0-groupoid abelian group *)

(** None of these use commutativity. *)

Section GroupProperties.

  Context {A : Type} `{IsAbGroup_0gpd A}.

  Definition cancelL_0gpd (a b c : A) (p : a + b $== a + c)
    : b $== c
    := isinj_equiv_0gpd (left_op_0gpd' a) p.

  Definition cancelR_0gpd (a b c : A) (p : b + a $== c + a)
    : b $== c
    := isinj_equiv_0gpd (right_op_0gpd' a) p.

  Definition inv_unit_0gpd : -0 $== 0
    := (mon_unit_l_0gpd (-0))^$ $@ inverse_r_0gpd 0.

  Definition moveL_gM_0gpd {a b c : A} (p : a - c $== b)
    : a $== b + c
    := moveL_equiv_M_0gpd (right_op_0gpd' c) p.

  Definition moveL_Mg_0gpd {a b c : A} (p : - b + a $== c)
    : a $== b + c
    := moveL_equiv_M_0gpd (left_op_0gpd' b) p.

  Definition moveR_gM_0gpd {a b c : A} (p : a $== c - b)
    : a + b $== c
    := moveR_equiv_M_0gpd (right_op_0gpd' b) p.

  Definition moveR_Mg_0gpd {a b c : A} (p : b $== - a + c)
    : a + b $== c
    := moveR_equiv_M_0gpd (left_op_0gpd' a) p.

  (** The next four are the inverses of the previous four. *)
  Definition moveR_gV_0gpd {a b c : A} (p : a $== c + b)
    : a - b $== c
    := moveR_equiv_V_0gpd (right_op_0gpd' b) p.

  Definition moveR_Vg_0gpd {a b c : A} (p : b $== a + c)
    : -a + b $== c
    := moveR_equiv_V_0gpd (left_op_0gpd' a) p.

  Definition moveL_gV_0gpd {a b c : A} (p : a + c $== b)
    : a $== b - c
    := moveL_equiv_V_0gpd (right_op_0gpd' c) p.

  Definition moveL_Vg_0gpd {a b c : A} (p : b + a $== c)
    : a $== -b + c
    := moveL_equiv_V_0gpd (left_op_0gpd' b) p.

  (** Versions of the above involving the unit. *)
  Definition moveL_0M_0gpd {a b : A} (p : a - b $== 0) : a $== b
    := moveL_gM_0gpd p $@ mon_unit_l_0gpd _.

  Definition moveL_M0_0gpd {a b : A} (p : -b + a $== 0) : a $== b
    := moveL_Mg_0gpd p $@ mon_unit_r_0gpd _.

  Definition moveL_0V_0gpd {a b : A} (p : a + b $== 0) : a $== -b
    := moveL_gV_0gpd p $@ mon_unit_l_0gpd _.

  Definition moveL_V0_0gpd {a b : A} (p : b + a $== 0) : a $== -b
    := moveL_Vg_0gpd p $@ mon_unit_r_0gpd _.

  Definition moveR_0M_0gpd {a b : A} (p : 0 $== b - a) : a $== b
    := (mon_unit_l_0gpd _)^$ $@ moveR_gM_0gpd p.

  Definition moveR_M0_0gpd {a b : A} (p : 0 $== -a + b) : a $== b
    := (mon_unit_r_0gpd _)^$ $@ moveR_Mg_0gpd p.

  Definition moveR_0V_0gpd {a b : A} (p : 0 $== b + a) : -a $== b
    := (mon_unit_l_0gpd _)^$ $@ moveR_gV_0gpd p.

  Definition moveR_V0_0gpd {a b : A} (p : 0 $== a + b) : -a $== b
    := (mon_unit_r_0gpd _)^$ $@ moveR_Vg_0gpd p.

  (** Equal things have zero difference. *)
  Definition inverse_r_homotopy_0gpd {a b : A} (p : a $== b)
    : a - b $== 0.
  Proof.
    rewrite p; apply inverse_r_0gpd.
  Defined.

  Definition inverse_l_homotopy_0gpd {a b : A} (p : a $== b)
    : -a + b $== 0.
  Proof.
    rewrite p; apply inverse_l_0gpd.
  Defined.

  (** Adding the inverse of the unit. *)
  Definition mon_unit_l_inv_0gpd {a : A} : a - 0 $== a.
  Proof.
    apply moveR_gV_0gpd.
    symmetry; apply mon_unit_r_0gpd.
  Defined.

  Definition mon_unit_r_inv_0gpd {a : A} : -0 + a $== a.
  Proof.
    apply moveR_Vg_0gpd.
    symmetry; apply mon_unit_l_0gpd.
  Defined.

End GroupProperties.

(** ** Homomorphisms between 0-groupoid abelian groups *)

Section Homomorphism.

  Context {A B : Type} `{IsAbGroup_0gpd A} `{IsAbGroup_0gpd B}.

  (** A homomorphism is a 0-functor that respects the operation up to 1-cells. *)
  Class IsGroupHom_0gpd (f : A -> B) `{!Is0Functor f} :=
      grp_homo_op_0gpd : forall (a a' : A), f (a + a') $== f a + f a'.

  (** It follows that it respects the unit and inversion. *)
  Definition grp_homo_unit_0gpd (f : A -> B) `{IsGroupHom_0gpd f}
    : f 0 $== 0.
  Proof.
    apply (cancelL_0gpd (f 0)).
    rhs' napply mon_unit_r_0gpd.
    rhs_V' rapply (fmap f (mon_unit_l_0gpd 0)).
    symmetry.
    apply grp_homo_op_0gpd.
  Defined.

  Definition grp_homo_inv_0gpd (f : A -> B) `{IsGroupHom_0gpd f} (a : A)
    : f (-a) $== -(f a).
  Proof.
    apply (cancelL_0gpd (f a)).
    lhs_V' rapply grp_homo_op_0gpd.
    lhs' rapply (fmap f (inverse_r_0gpd _)).
    rhs' rapply inverse_r_0gpd.
    rapply grp_homo_unit_0gpd.
  Defined.

  Definition grp_homo_op_inv_0gpd (f : A -> B) `{IsGroupHom_0gpd f} (a b : A)
    : f (a - b) $== f a - f b.
  Proof.
    lhs' rapply grp_homo_op_0gpd.
    apply (fmap (sgop_0gpd _)).
    rapply grp_homo_inv_0gpd.
  Defined.

End Homomorphism.

(** ** Definition of a wild category enriched in abelian groups *)

(** It is a 1-category with 0-groupoid abelian group structures on its hom types, such that pre- and post-composition are homomorphisms. *)
Class IsAbEnriched (A : Type) `{Is1Cat A} := {
    abgroup_abenriched :: forall (a b : A), IsAbGroup_0gpd (a $-> b);
    issgpreserving_postcomp_abenriched
      :: forall (a b c : A) (g : b $-> c), IsGroupHom_0gpd (cat_postcomp a g) ;
    issgpreserving_precomp_abenriched
      :: forall (a b c : A) (f : a $-> b), IsGroupHom_0gpd (cat_precomp c f) ;
  }.

(** ** Results involving pre- and post-composition *)

(** All of these except [precomp_zero] may not be needed, since Rocq is usually able to infer which homomorphism is involved, but we include them for completeness. *)

Section AbEnriched.

  Context {A : Type} `{IsAbEnriched A}.

  Definition postcomp_op {B C D : A} (f : C $-> D) (g h : B $-> C)
    : f $o (g + h) $== (f $o g) + (f $o h)
    := grp_homo_op_0gpd g h.

  Definition precomp_op {B C D : A} (f : B $-> C) (g h : C $-> D)
    : (g + h) $o f $== (g $o f) + (h $o f)
    := grp_homo_op_0gpd g h.

  Definition postcomp_zero {B C D : A} (f : C $-> D)
    : f $o 0 $== (0 : B $-> D)
    := grp_homo_unit_0gpd _.

  Definition precomp_zero {B C D : A} (f : B $-> C)
    : 0 $o f $== (0 : B $-> D)
    := grp_homo_unit_0gpd (cat_precomp _ _).

  Definition postcomp_inv {B C D : A} (f : C $-> D) (g : B $-> C)
    : f $o (-g) $== -(f $o g)
    := grp_homo_inv_0gpd _ g.

  Definition precomp_inv {B C D : A} (f : C $-> D) (g : B $-> C)
    : (-f) $o g $== -(f $o g)
    := grp_homo_inv_0gpd _ f.

  Definition postcomp_op_inv {B C D : A} (f : C $-> D) (g h : B $-> C)
    : f $o (g - h) $== (f $o g) - (f $o h)
    := grp_homo_op_inv_0gpd _ _ _.

  Definition precomp_op_inv {B C D : A} (f : B $-> C) (g h : C $-> D)
    : (g - h) $o f $== (g $o f) - (h $o f)
    := grp_homo_op_inv_0gpd _ g h.

End AbEnriched.
