Require Import Overture PathGroupoids HProp Equivalences EquivalenceVarieties
        UnivalenceImpliesFunext.
Require Import types.Empty types.Unit types.Arrow types.Sigma types.Paths
        types.Forall types.Prod types.Universe ObjectClassifier.
Require Import ReflectiveSubuniverse.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Modalities *)

Section Modalities.
  Context {ua : Univalence}.

  (** Quoting the HoTT Book: *)
  (** Definition 7.7.5. A _modality_ is an operation [○ : Type → Type] for which there are

    (i) functions [eta^○_A : A → ○(A)] for every type [A]

    (ii) for every [A : Type] and every type family [B : ○(A) → Type], a function

         [ind_○ : (∀ a : A, ○(B(eta^○_A(a)))) → (∀ z : ○(A), ○(B(z)))]

    (iii) A path [ind_○(f)(eta^○_A(a)) = f(a)] for each [f : ∀ a : A, ○(B(eta^○_A(a)))].

    (iv) For any [z z' : ○(A)], the function [eta^○_{z = z'} : (z = z') → ○(z = z')] is an equivalence. *)

  Class Modality :=
    {
      mod_usubu :> UnitSubuniverse ;
      O_rectO : forall A (B : O A -> Type),
                (forall a, O (B (O_unit A a))) -> forall z, O (B z) ;
      O_rectO_beta : forall A B (f : forall a : A, O (B (O_unit A a))) a,
                     O_rectO A B f (O_unit A a) = f a ;
      inO_pathsO : forall A (z z' : O A), inO (z = z')
    }.

  (** See ReflectiveSubuniverse.v for explanation of how to use (and how not to use) [Modality] as a typeclass. *)

  Global Existing Instance inO_pathsO.

  Context {mod : Modality}.

  (** The image of a type by [mod] is always modal *)
  Local Definition O_inO_modality (A:Type) : inO (O A).
  Proof.
    apply isequiv_adjointify with (g := O_rectO (O A) (fun _ => A) idmap).
    - intro x.
      apply ((O_unit _)^-1).
      generalize dependent x; apply O_rectO; intro a.
      apply O_unit.
      apply ap.
      apply (O_rectO_beta _ (fun _ : O (O A) => A) (fun u:O A => u) a).
    - exact (O_rectO_beta _ (fun _ : O (O A) => A) idmap).
  Qed.

  Local Instance inO_paths_modality (A:Type) {A_inO : inO A}
  : forall (x y:A), inO (x=y).
  Proof.
    intros x y.
    refine (inO_equiv_inO (O_unit A x = O_unit A y) _).
    apply equiv_inverse, equiv_ap, A_inO.
  Qed.

  (** A generalized induction principle into families of modal types. *)

  Section OInd.

    Context {A : Type} (B : O A -> Type) {B_inO : forall a, inO (B a)}
            (f : forall a, B (O_unit A a)).

    Definition O_rect : forall oa, B oa.
    Proof.
      intros oa.
      apply ((O_unit (B oa))^-1).
      apply O_rectO.
      intros a; apply O_unit. apply f.
    Defined.

    Definition O_rect_beta : forall a, O_rect (O_unit A a) = f a.
    Proof.
      intros a; unfold O_rect.
      apply moveR_VE.
      apply @O_rectO_beta with (f := fun x => O_unit _ (f x)).
    Defined.

  End OInd.

  (** The induction principle [O_rect], like most induction principles, is an equivalence. *)

  Section OIndEquiv.

    Context {A : Type} (B : O A -> Type) {B_inO : forall a, inO (B a)}.

    Instance isequiv_O_rect : IsEquiv (O_rect B).
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

  End OIndEquiv.

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

Theorem reflective_subuniverse_to_modality `{ua : Univalence}
  (subU : ReflectiveSubuniverse)
  (H : forall (A:Type) (B:A -> Type)
          {A_inO : inO A} {B_inO : forall a, inO (B a)},
     (inO ({x:A & B x})))
  : Modality.
Proof.
  pose (K := fst inO_sigma_iff H).
  exact (Build_Modality _
           (fun A B g => pr1 (K A (O oD B) _ g))
           (fun A B g => pr2 (K A (O oD B) _ g))
           _).
Defined.  

(** Exercise 7.12 *)
Definition notnot_modality `{Univalence} : Modality.
Proof.
  refine (Build_Modality
            (Build_UnitSubuniverse
               (fun X => ~~X)
               (fun X x nx => nx x))
            (fun A B f z nBz =>
              z (fun a => f a (transport (fun x => ~B x)
                                          (allpath_hprop _ _)
                                          nBz)))
            _ _).
  - intros A B f a. apply allpath_hprop.
  - intros A z z'.
    refine (inO_equiv_inO Unit _).
    * exact (equiv_isequiv
               (@equiv_iff_hprop Unit _ (~~Unit) _
                                 (fun u nu => nu u) (fun _ => tt))).
    * apply equiv_iff_hprop.
      + intros; apply allpath_hprop.
      + intros; exact tt.
Defined.
