Require Import Basics Types.
Require Import WildCat.Core.
Require Import WildCat.NatTrans.
Require Import WildCat.FunctorCat.
Require Import WildCat.Adjoint.
Require Import WildCat.Equiv.
Require Import WildCat.Opposite.
Require Import WildCat.Yoneda.
Require Import WildCat.Type.

(** Limits and colimits *)


(** For any category [A] there is a functor [diagonal : A $-> Fun01 J A] *)

Section ConstantFunctor.

  Context (A J : Type) `{Is1Cat A, IsGraph J}.

  Definition diagonal : A -> Fun01 J A :=
    fun x : A => Build_Fun01 J A (fun _ => x).

  Global Instance is0functor_diagonal : Is0Functor diagonal.
  Proof.
    apply Build_Is0Functor.
    intros a b f.
    snrapply Build_NatTrans.
    - intros c.
      exact f.
    - intros x y g.
      exact (cat_idr _ $@ (cat_idl _)^$).
  Defined.

  Global Instance is1functor_diagonal : Is1Functor diagonal.
  Proof.
    apply Build_Is1Functor.
    - intros a b f g p j.
      exact p.
    - intros a j.
      reflexivity.
    - intros a b c f g j.
      reflexivity.
  Defined.

  (** The property of having a [J]-shaped limit. *)
  Class HasLimit := {
    cat_limit : Fun01 J A -> A ;
    is0functor_cat_limit : Is0Functor cat_limit ;
    is1functor_cat_limit : Is1Functor cat_limit ;
    adjunction_cat_limit : Adjunction diagonal cat_limit;
  }.

  Global Existing Instances
    is0functor_cat_limit
    is1functor_cat_limit.

End ConstantFunctor.

(** [C] having [J]-shaped colimits can be defined as [C^op] having [J]-shaped limits. *)
Definition HasColimit (A : Type) `{Is1Cat A} (J : Type) `{IsGraph J} : Type :=
  HasLimit A^op J.

(** Preservation of limits *)

(** Property of a functor preserving limits. *)
Class PreservesLimits (A B J : Type) `{Is1Cat A, IsGraph J, !HasLimit A J,
  HasEquivs B, !HasLimit B J} (F : Fun11 A B) :=
  equiv_preserveslimits (x : Fun01 J A)
    : F (cat_limit A J x) $<~> cat_limit B J (fun01_compose F x).




(** This seems to be too strong *)
(* 
(** Property of a functor preserving limits. *)
Class PreservesLimits (A B J : Type) `{Is1Cat A, IsGraph J, !HasLimit A J,
  HasEquivs B, !HasLimit B J} (F : Fun11 A B) :=
  natequiv_preserveslimits
    : NatEquiv (F o cat_limit A J) (cat_limit B J o fun01_compose F).
 *)

(** Properties of limits (and colimits) *)

(** Right adjoints preserve limits *)
Global Instance preserveslimits_right_adjoint `{Funext} (A B J : Type)
  `{Is1Cat A, !HasEquivs A, !Is1Cat_Strong A, Is01Cat J, !HasLimit A J,
    HasEquivs B, !HasMorExt B, !HasLimit B J}
  (L : Fun11 A B) (R : Fun11 B A) (adj : L ⊣ R)
  : PreservesLimits B A J R.
Proof.
  hnf.
  intros K.
  (** Uses yoneda *)
  srapply yon_equiv.
  refine (natequiv_compose (natequiv_adjunction_l
    (adjunction_cat_limit _ _) (fun11_fun01_postcomp R K)) _).
  refine (natequiv_compose (natequiv_prewhisker (natequiv_adjunction_l
    (adjunction_postcomp _ _ J L R adj) K) (diagonal A J)) _).
  refine (natequiv_compose _ (natequiv_inverse _ _
    (natequiv_adjunction_l adj (cat_limit B J K)))).
  refine (natequiv_compose _ (natequiv_inverse _ _ (natequiv_prewhisker
    (natequiv_adjunction_l (adjunction_cat_limit _ _) K) L))).
  refine (natequiv_compose (natequiv_inverse _ _ _) _).
  1: apply natequiv_functor_assoc_ff_f.
  refine (natequiv_compose _ _).
  2: apply natequiv_functor_assoc_ff_f.
  (** This is where morphism extensionality and funext is used. *)
  snrapply natequiv_postwhisker.
  (** Why can't typeclasses find this? *)
  4: rapply hasequivs_op.
  2: rapply is1functor_yon.
  (** Perhaps it's type for a natequiv_adjointify? *)
  snrapply Build_NatEquiv.
  { intros a. cbn.
    srapply cate_adjointify.
    - snrapply Build_NatTrans.
      1: intro j; exact (Id _).
      intros i j f.
      rapply cat_postwhisker.
      rapply fmap_id.
    - snrapply Build_NatTrans.
      1: intro j; exact (Id _).
      intros i j f.
      rapply cat_prewhisker.
      rapply gpd_rev.
      rapply fmap_id.
    - intros i.
      rapply cat_idl.
    - intros j.
      rapply cat_idr. }
  intros a a' f.
  unfold trans_comp.
  unfold cate_adjointify.
  refine ((cate_buildequiv_fun _ $@R _) $@ _).
  refine (_ $@ (_ $@L _)).
  2: symmetry; rapply cate_buildequiv_fun.
  intros j; exact (cat_idr _ $@ (cat_idl _)^$).
Defined.

(* (** Limits commute with functors which have a right adjoint. *)
(** This can be written down as a natural equivalence, but specifying the categories involved is a bit tricky, whilst still trying to keep the coherence low. *)
Theorem limits_commute_right_adjoint (A B J : Type) (F : A -> B)
  `{Is1Cat A, IsGraph J, !HasLimit A J, HasEquivs B, !HasLimit B J,
    !Is0Functor F, !Is1Functor F}
  (** Diagram *)
  (x : Fun01 J A)
  : F (cat_limit A J x)
    $<~> cat_limit B J (fun01_compose (Build_Fun01 _ _ F) x).
Proof.
  
 *)



