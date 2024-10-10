Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core WildCat.Equiv WildCat.Monoidal WildCat.Bifunctor
  WildCat.NatTrans WildCat.Opposite WildCat.Products.
Require Import abstract_algebra.

(** * Monoids and Comonoids *)

(** Here we define a monoid internal to a monoidal category. Note that we don't actually need the full monoidal structure so we assume only the parts we need. This allows us to keep the definitions general between various flavours of monoidal category.

Many algebraic theories such as groups and rings may also be internalized, however these specifically require a cartesian monoidal structure. The theory of monoids however has no such requirement and can therefore be developed in much greater generality. This can be used to define a range of objects such as R-algebras, H-spaces, Hopf algebras and more. *)

(** * Monoid objects *)

Section MonoidObject.
  Context {A : Type} {tensor : A -> A -> A} {unit : A}
    `{HasEquivs A, !Is0Bifunctor tensor, !Is1Bifunctor tensor}
    `{!Associator tensor, !LeftUnitor tensor unit, !RightUnitor tensor unit}.

  (** An object [x] of [A] is a monoid object if it comes with the following data: *)
  Class IsMonoidObject (x : A) := {
    (** A multiplication map from the tensor product of [x] with itself to [x]. *)
    mo_mult : tensor x x $-> x;
    (** A unit of the multplication. *)
    mo_unit : unit $-> x;
    (** The multiplication map is associative. *)
    mo_assoc : mo_mult $o fmap10 tensor mo_mult x $o associator x x x
        $== mo_mult $o fmap01 tensor x mo_mult;
    (** The multiplication map is left unital. *)
    mo_left_unit : mo_mult $o fmap10 tensor mo_unit x $== left_unitor x;
    (** The multiplication map is right unital. *)
    mo_right_unit : mo_mult $o fmap01 tensor x mo_unit $== right_unitor x;
  }.

  Context `{!Braiding tensor}.

  (** An object [x] of [A] is a commutative monoid object if: *)
  Class IsCommutativeMonoidObject (x : A) := {
    (** It is a monoid object. *)
    cmo_mo :: IsMonoidObject x;
    (** The multiplication map is commutative. *)
    cmo_comm : mo_mult $o braid x x $== mo_mult;
  }.

End MonoidObject.

Arguments IsMonoidObject {A} tensor unit {_ _ _ _ _ _ _ _ _ _} x.
Arguments IsCommutativeMonoidObject {A} tensor unit {_ _ _ _ _ _ _ _ _ _ _} x.

Section ComonoidObject.
  Context {A : Type} (tensor : A -> A -> A) (unit : A)
    `{HasEquivs A, !Is0Bifunctor tensor, !Is1Bifunctor tensor}
    `{!Associator tensor, !LeftUnitor tensor unit, !RightUnitor tensor unit}.

  (** A comonoid object is a monoid object in the opposite category. *)
  Class IsComonoidObject (x : A)
    := ismonoid_comonoid_op :: IsMonoidObject (A:=A^op) tensor unit x.

  (** We can build comonoid objects from the following data: *)
  Definition Build_IsComonoidObject (x : A)
    (** A comultplication map. *)
    (co_comult : x $-> tensor x x)
    (** A counit. *)
    (co_counit : x $-> unit)
    (** The comultiplication is coassociative. *)
    (co_coassoc : associator x x x $o fmap01 tensor x co_comult $o co_comult
        $== fmap10 tensor co_comult x $o co_comult)
    (** The comultiplication is left counital. *)
    (co_left_counit : left_unitor x $o fmap10 tensor co_counit x $o co_comult $== Id x)
    (** The comultiplication is right counital. *)
    (co_right_counit : right_unitor x $o fmap01 tensor x co_counit $o co_comult $== Id x)
    : IsComonoidObject x.
  Proof.
    snrapply Build_IsMonoidObject.
    - exact co_comult.
    - exact co_counit.
    - nrapply cate_moveR_eV.
      symmetry.
      nrefine (cat_assoc _ _ _ $@ _).
      rapply co_coassoc.
    - simpl; nrefine (_ $@ cat_idr _).
      nrapply cate_moveL_Ve.
      nrefine (cat_assoc_opp _ _ _ $@ _).
      exact co_left_counit.
    - simpl; nrefine (_ $@ cat_idr _).
      nrapply cate_moveL_Ve.
      nrefine (cat_assoc_opp _ _ _ $@ _).
      exact co_right_counit.
  Defined.

  (** Comultiplication *)
  Definition co_comult {x : A} `{!IsComonoidObject x} : x $-> tensor x x
   := mo_mult (A:=A^op) (tensor:=tensor) (unit:=unit) (x:=x).

  (** Counit *)
  Definition co_counit {x : A} `{!IsComonoidObject x} : x $-> unit
    := mo_unit (A:=A^op) (tensor:=tensor) (unit:=unit) (x:=x).

  (** Coassociativity *)
  Definition co_coassoc {x : A} `{!IsComonoidObject x}
    : associator x x x $o fmap01 tensor x co_comult $o co_comult
        $== fmap10 tensor co_comult x $o co_comult.
  Proof.
    refine (cat_assoc _ _ _ $@ _).
    apply cate_moveR_Me.
    symmetry.
    exact (mo_assoc (A:=A^op) (tensor:=tensor) (unit:=unit) (x:=x)).
  Defined.

  (** Left counitality *)
  Definition co_left_counit {x : A} `{!IsComonoidObject x}
    : left_unitor x $o fmap10 tensor co_counit x $o co_comult $== Id x.
  Proof.
    refine (cat_assoc _ _ _ $@ _).
    apply cate_moveR_Me.
    refine (_ $@ (cat_idr _)^$).
    exact (mo_left_unit (A:=A^op) (tensor:=tensor) (unit:=unit) (x:=x)).
  Defined.

  (** Right counitality *)
  Definition co_right_counit {x : A} `{!IsComonoidObject x}
    : right_unitor x $o fmap01 tensor x co_counit $o co_comult $== Id x.
  Proof.
    refine (cat_assoc _ _ _ $@ _).
    apply cate_moveR_Me.
    refine (_ $@ (cat_idr _)^$).
    exact (mo_right_unit (A:=A^op) (tensor:=tensor) (unit:=unit) (x:=x)).
  Defined.

  Context `{!Braiding tensor}.

  (** A cocommutative comonoid objects is a commutative monoid object in the opposite category. *)
  Class IsCocommutativeComonoidObject (x : A)
    := iscommuatativemonoid_cocomutativemonoid_op
      :: IsCommutativeMonoidObject (A:=A^op) tensor unit x.

  (** We can build cocommutative comonoid objects from the following data: *)
  Definition Build_IsCocommutativeComonoidObject (x : A)
    (** A comonoid. *)
    `{!IsComonoidObject x}
    (** Together with a proof of cocommutativity. *)
    (cco_cocomm : braid x x $o co_comult $== co_comult)
    : IsCocommutativeComonoidObject x.
  Proof.
    snrapply Build_IsCommutativeMonoidObject.
    - exact _.
    - exact cco_cocomm.
  Defined.

  Global Instance co_cco {x : A} `{!IsCocommutativeComonoidObject x}
    : IsComonoidObject x.
  Proof.
    apply cmo_mo.
  Defined.

  (** Cocommutativity *)
  Definition cco_cocomm {x : A} `{!IsCocommutativeComonoidObject x}
    : braid x x $o co_comult $== co_comult.
  Proof.
    exact (cmo_comm (A:=A^op) (tensor:=tensor) (unit:=unit) (x:=x)).
  Defined.

End ComonoidObject.

(** A comonoid object in [A^op] is a monoid object in [A]. *)
Definition mo_co_op {A : Type} {tensor : A -> A -> A} {unit : A}
  `{HasEquivs A, !Is0Bifunctor tensor, !Is1Bifunctor tensor}
  `{!Associator tensor, !LeftUnitor tensor unit, !RightUnitor tensor unit}
  {x : A} `{C : !IsComonoidObject (A:=A^op) tensor unit x}
  : IsMonoidObject tensor unit x.
Proof.
  snrapply Build_IsMonoidObject.
  - exact (co_comult (A:=A^op) tensor unit).
  - exact (co_counit (A:=A^op) tensor unit).
  - apply cate_moveR_eM.
    symmetry.
    exact (cat_assoc _ _ _ $@ co_coassoc (A:=A^op) tensor unit (x:=x)).
  - simpl; nrefine (_ $@ cat_idl _).
    apply cate_moveL_eM.
    refine (cat_assoc _ _ _ $@ _).
    exact (co_left_counit (A:=A^op) tensor unit (x:=x)).
  - simpl; nrefine (_ $@ cat_idl _).
    apply cate_moveL_eM.
    refine (cat_assoc _ _ _ $@ _).
    exact (co_right_counit (A:=A^op) tensor unit (x:=x)).
Defined.

(** A cocommutative cocomonoid object in [A^op] is a commutative monoid object in [A]. *)
Definition cmo_coco_op {A : Type} {tensor : A -> A -> A} {unit : A}
  `{HasEquivs A, !Is0Bifunctor tensor, !Is1Bifunctor tensor}
  `{!Associator tensor, !LeftUnitor tensor unit, !RightUnitor tensor unit,
    !Braiding tensor}
  {x : A} `{C : !IsCocommutativeComonoidObject (A:=A^op) tensor unit x}
  : IsCommutativeMonoidObject tensor unit x.
Proof.
  snrapply Build_IsCommutativeMonoidObject.
  - nrapply mo_co_op.
    rapply co_cco.
  - exact (cco_cocomm (A:=A^op) tensor unit).
Defined.

(** ** Monoid enrichment *)

(** A hom [x $-> y] in a cartesian category where [y] is a monoid object has the structure of a monoid. Equivalently, a hom [x $-> y] in a cartesian category where [x] is a comonoid object has the structure of a monoid. *)

Section MonoidEnriched.
  Context {A : Type} `{HasEquivs A} `{!HasBinaryProducts A}
    (unit : A) `{!IsTerminal unit} {x y : A}
    `{!HasMorExt A} `{forall x y, IsHSet (x $-> y)}.

  Section Monoid.
    Context `{!IsMonoidObject _ _ y}.

    Local Instance sgop_hom : SgOp (x $-> y)
      := fun f g => mo_mult $o cat_binprod_corec f g.

    Local Instance monunit_hom : MonUnit (x $-> y) := mo_unit $o mor_terminal _ _.

    Local Instance associative_hom : Associative sgop_hom.
    Proof.
      intros f g h.
      unfold sgop_hom.
      rapply path_hom.
      refine ((_ $@L cat_binprod_fmap01_corec _ _ _)^$ $@ _).
      nrefine (cat_assoc_opp _ _ _ $@ _).
      refine ((mo_assoc $@R _)^$ $@ _).
      nrefine (_ $@ (_ $@L cat_binprod_fmap10_corec _ _ _)).
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ cat_assoc _ _ _).
      nrapply cat_binprod_associator_corec.
    Defined.

    Local Instance leftidentity_hom : LeftIdentity sgop_hom mon_unit.
    Proof.
      intros f.
      unfold sgop_hom, mon_unit.
      rapply path_hom.
      refine ((_ $@L (cat_binprod_fmap10_corec _ _ _)^$) $@ cat_assoc_opp _ _ _ $@ _).
      nrefine (((mo_left_unit $@ _) $@R _) $@ _).
      1: nrapply cate_buildequiv_fun.
      unfold trans_nattrans.
      nrefine ((((_ $@R _) $@ _) $@R _) $@ _).
      1: nrapply cate_buildequiv_fun.
      1: nrapply cat_binprod_beta_pr1.
      nrapply cat_binprod_beta_pr2.
    Defined.

    Local Instance rightidentity_hom : RightIdentity sgop_hom mon_unit.
    Proof.
      intros f.
      unfold sgop_hom, mon_unit.
      rapply path_hom.
      refine ((_ $@L (cat_binprod_fmap01_corec _ _ _)^$) $@ cat_assoc_opp _ _ _ $@ _).
      nrefine (((mo_right_unit $@ _) $@R _) $@ _).
      1: nrapply cate_buildequiv_fun.
      nrapply cat_binprod_beta_pr1.
    Defined.

    Local Instance issemigroup_hom : IsSemiGroup (x $-> y) := {}.
    Local Instance ismonoid_hom : IsMonoid (x $-> y) := {}.

  End Monoid.

  Context `{!IsCommutativeMonoidObject _ _ y}.
  Local Existing Instances sgop_hom monunit_hom ismonoid_hom.

  Local Instance commutative_hom : Commutative sgop_hom.
  Proof.
    intros f g.
    unfold sgop_hom.
    rapply path_hom.
    refine ((_ $@L _^$) $@ cat_assoc_opp _ _ _ $@ (cmo_comm $@R _)).
    nrapply cat_binprod_swap_corec. 
  Defined.

  Local Instance iscommutativemonoid_hom : IsCommutativeMonoid (x $-> y) := {}.

End MonoidEnriched.

(** ** Preservation of monoid objects by lax monoidal functors *)

Definition mo_preserved {A B : Type}
  {tensorA : A -> A -> A} {tensorB : B -> B -> B} {IA : A} {IB : B} 
  (F : A -> B) `{IsMonoidalFunctor A B tensorA tensorB IA IB F} (x : A)
  : IsMonoidObject tensorA IA x -> IsMonoidObject tensorB IB (F x).
Proof.
  intros mo_x.
  snrapply Build_IsMonoidObject.
  - exact (fmap F mo_mult $o fmap_tensor F (x, x)).
  - exact (fmap F mo_unit $o fmap_unit).
  - refine (((_ $@L (fmap10_comp tensorB _ _ _)) $@R _)
      $@ _ $@ (_ $@L (fmap01_comp tensorB _ _ _)^$)).
    refine (_ $@ (((_ $@L _^$) $@ cat_assoc_opp _ _ _) $@R _)
      $@ cat_assoc _ _ _).
    2: snrapply fmap_tensor_nat_r.
    refine (_ $@ ((fmap2 _ mo_assoc $@ fmap_comp _ _ _) $@R _)
      $@ cat_assoc_opp _ _ _ $@ (cat_assoc _ _ _ $@R _)).
    refine (_ $@ ((fmap_comp _ _ _ $@ (fmap_comp _ _ _ $@R _))^$ $@R _)).
    nrefine (cat_assoc _ _ _ $@ cat_assoc _ _ _ $@ (_ $@L _)
      $@ cat_assoc_opp _ _ _ $@ cat_assoc_opp _ _ _).
    refine (_ $@ (_ $@L (_^$ $@ cat_assoc _ _ _))).
    2: snrapply fmap_tensor_assoc.
    nrefine (cat_assoc_opp _ _ _ $@ (cat_assoc_opp _ _ _ $@R _)
      $@ (((_ $@R _) $@ cat_assoc _ _ _) $@R _) $@ cat_assoc _ _ _).
    snrapply fmap_tensor_nat_l.
  - refine ((_ $@L fmap10_comp _ _ _ _) $@ cat_assoc _ _ _
      $@ (_ $@L (cat_assoc_opp _ _ _ $@ (_ $@R _))) $@ _).
    1: snrapply fmap_tensor_nat_l.
    refine (cat_assoc_opp _ _ _ $@ ((cat_assoc_opp _ _ _ $@
      (((fmap_comp _ _ _)^$ $@ fmap2 _ mo_left_unit) $@R _)) $@R _) $@ _^$).
    snrapply fmap_tensor_left_unitor.
  - refine ((_ $@L fmap01_comp _ _ _ _) $@ cat_assoc _ _ _
      $@ (_ $@L (cat_assoc_opp _ _ _ $@ (_ $@R _))) $@ _).
    1: snrapply fmap_tensor_nat_r.
    refine (cat_assoc_opp _ _ _ $@ ((cat_assoc_opp _ _ _ $@
      (((fmap_comp _ _ _)^$ $@ fmap2 _ mo_right_unit) $@R _)) $@R _) $@ _^$).
    snrapply fmap_tensor_right_unitor.
Defined.
