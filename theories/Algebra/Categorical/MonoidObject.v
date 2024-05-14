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

End ComonoidObject.

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




