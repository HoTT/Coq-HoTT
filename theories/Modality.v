(* -*- mode: coq; mode: visual-line -*- *)

Require Import Overture PathGroupoids HProp Equivalences EquivalenceVarieties
        UnivalenceImpliesFunext.
Require Import types.Empty types.Unit types.Arrow types.Sigma types.Paths
        types.Forall types.Prod types.Universe ObjectClassifier.
Require Import ReflectiveSubuniverse.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Modalities *)

Section Modalities.
  Context `{Funext}.

  (** A modality consists of *)
  Class Modality :=
    {
      (** a UnitSubuniverse, whose types are called "modal", *)
      mod_usubu : UnitSubuniverse ;
      (** an induction principle into families of modal types *)
      O_rect : forall A (B : O A -> Type) (B_inO : forall oa, inO (B oa)),
        (forall a, B (O_unit A a)) -> forall a, B a ;
      (** with a computation rule *)
      O_rect_beta : forall A B B_inO (f : forall a : A, B (O_unit A a)) a,
        O_rect A B B_inO f (O_unit A a) = f a ;
      (** such that [O] maps into the subuniverse *)
      O_inO_modality : forall A, inO (O A) ;
      (** and which is closed under path spaces. *)
      inO_paths : forall A (A_inO : inO A) (z z' : A), inO (z = z')
    }.

  Arguments O_rect {Modality} {A} B {B_inO} f a.
  Arguments O_rect_beta {Modality} {A} B {B_inO} f a.
  
  (** See ReflectiveSubuniverse.v for explanation of how to use (and how not to use) [Modality] as a typeclass. *)

  Global Existing Instance mod_usubu.
  Coercion mod_usubu : Modality >-> UnitSubuniverse.
  Global Existing Instance O_inO_modality.
  Global Existing Instance inO_paths.

  (** Our definition of modality is slightly different from the one in the book, which requires an induction principle only into families of the form [fun oa => O (B oa)] and similarly only that path-spaces of types [O A] are modal.  This is "obviously" equivalent since every modal type is equivalent to one of the form [O A].  However, our definition is more convenient in formalized applications because in some examples, there is a naturally occurring [O_rect] into all modal types that is not judgmentally equal to the one that can be constructed by passing through [O] and back again.

     However, in other examples it is easier to construct the latter weaker induction principle, so we now show how to do this. *)

  Definition Build_Modality_easy `{Univalence}
    (mod_usubu : UnitSubuniverse)
    (O_rectO : forall A (B : O A -> Type),
      (forall a, O (B (O_unit A a))) -> forall z, O (B z))
    (O_rectO_beta : forall A B (f : forall a : A, O (B (O_unit A a))) a,
      O_rectO A B f (O_unit A a) = f a)
    (inO_pathsO : forall A (z z' : O A), inO (z = z'))
    : Modality.
  Proof.
    refine (Build_Modality mod_usubu _ _ _ _).
    - intros A B B_inO f oa.
      apply ((O_unit (B oa))^-1).
      apply O_rectO.
      intros a; apply O_unit. apply f.
    - intros A B B_inO f a; unfold O_rect.
      apply moveR_equiv_V.
      apply @O_rectO_beta with (f := fun x => O_unit _ (f x)).
    - intros A; apply inO_isequiv_O_unit.
      refine (isequiv_adjointify (O_unit (O A)) (O_rectO (O A) (fun _ => A) idmap) _ _).
      + intro x.
        apply ((O_unit _)^-1).
        generalize dependent x; apply O_rectO; intro a.
        apply O_unit. apply ap.
        apply (O_rectO_beta _ (fun _ : O (O A) => A) (fun u:O A => u) a).
      + exact (O_rectO_beta _ (fun _ : O (O A) => A) idmap).
    - intros A A_inO x y.
      refine (@transport Type inO (O_unit A x = O_unit A y) (x = y) _ _).
      symmetry; exact (path_universe (equiv_ap (O_unit A) _ _)).
  Defined.

  (** For the rest of this section, we work with an arbitrary modality. *)
  Context {mod : Modality}.

  (** The induction principle [O_rect], like most induction principles, is an equivalence. *)

  Section ORectEquiv.

    Context {A : Type} (B : O A -> Type) {B_inO : forall a, inO (B a)}.

    Global Instance isequiv_O_rect : IsEquiv (O_rect B).
    Proof.
      apply isequiv_adjointify with (g := fun h => h oD O_unit A).
      - intros h. apply path_forall.
        refine (O_rect (fun oa => O_rect B (h oD O_unit A) oa = h oa) _).
        exact (O_rect_beta B (h oD O_unit A)).
      - intros f. apply path_forall.
        exact (O_rect_beta B f).
    Defined.

    Definition equiv_O_rect
    : (forall a, B (O_unit A a)) <~> (forall oa, B oa)
    := BuildEquiv _ _ (O_rect B) _.

    (** Theorem 7.7.7 *)
    Definition isequiv_oD_O_unit
    : IsEquiv (fun (h : forall oa, B oa) => h oD O_unit A)
    := equiv_isequiv (equiv_inverse equiv_O_rect).

  End ORectEquiv.

  Local Definition isequiv_o_O_unit (A B : Type) (B_inO : inO B)
  : IsEquiv (fun (h : O A -> B) => h o O_unit A)
    := isequiv_oD_O_unit (fun _ => B).

  (** Corollary 7.7.8, part 1 *)
  Global Instance modality_to_reflective_subuniverse
  : ReflectiveSubuniverse
    := Build_ReflectiveSubuniverse _
         O_inO_modality
         isequiv_o_O_unit.

  (** Corollary 7.7.8, part 2 *)
  Global Instance inO_sigma (A:Type) (B:A -> Type)
    {A_inO : inO A} {B_inO : forall a, inO (B a)}
  : inO {x:A & B x}.
  Proof.
    generalize dependent A.
    refine (snd inO_sigma_iff _).
    intros A B ? g.
    exists (O_rect B g).
    apply O_rect_beta.
  Defined.

End Modalities.

Theorem reflective_subuniverse_to_modality `{fs : Funext}
  (subU : ReflectiveSubuniverse)
  (H : forall (A:Type) (B:A -> Type)
          {A_inO : inO A} {B_inO : forall a, inO (B a)},
     (inO ({x:A & B x})))
  : Modality.
Proof.
  pose (K := fst inO_sigma_iff H).
  exact (Build_Modality _
           (fun A B B_inO g => pr1 (K A B B_inO g))
           (fun A B B_inO g => pr2 (K A B B_inO g))
           _ _).
Defined.

(** Exercise 7.12 *)
Definition notnot_modality `{Univalence} : Modality.
Proof.
  refine (Build_Modality_easy
            (Build_UnitSubuniverse_easy
               (fun X => ~~X)
               (fun X x nx => nx x))
            (fun A B f z nBz =>
              z (fun a => f a (transport (fun x => ~B x)
                                          (allpath_hprop _ _)
                                          nBz)))
            _ _).
  - intros A B f a. apply allpath_hprop.
  - intros A z z'.
    refine (@transport Type inO Unit (z = z') _ _).
    * assert (f : Unit <~> (z = z')).
      { apply equiv_iff_hprop.
        + intros; apply allpath_hprop.
        + intros; exact tt. }
      apply (path_universe f).
    * exact (equiv_isequiv
               (@equiv_iff_hprop Unit _ (~~Unit) _
                                 (fun u nu => nu u) (fun _ => tt))).
Defined.
