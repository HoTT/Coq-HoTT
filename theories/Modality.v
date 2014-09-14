(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics.
Require Import types.Empty types.Unit types.Arrow types.Sigma types.Paths types.Forall types.Prod types.Universe.
Require Import HProp EquivalenceVarieties ObjectClassifier ReflectiveSubuniverse.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Modalities *)

Class Modality :=
  {
    mod_usubu : UnitSubuniverse ;
    mod_replete : Replete mod_usubu ;
    O_rect : forall A (B : O A -> Type) (B_inO : forall oa, inO (B oa)),
               (forall a, B (O_unit A a)) -> forall a, B a ;
    O_rect_beta : forall A B B_inO (f : forall a : A, B (O_unit A a)) a,
                    O_rect A B B_inO f (O_unit A a) = f a ;
    inO_paths : forall A (A_inO : inO A) (z z' : A), inO (z = z')
  }.

Arguments O_rect {Modality} {A} B {B_inO} f a.
Arguments O_rect_beta {Modality} {A} B {B_inO} f a.

(** See ReflectiveSubuniverse.v for explanation of how to use (and how not to use) [Modality] as a typeclass. *)

Global Existing Instance mod_usubu.
Coercion mod_usubu : Modality >-> UnitSubuniverse.
Global Existing Instance mod_replete.
Global Existing Instance inO_paths.

(** Our definition of modality is slightly different from the one in the book, which requires an induction principle only into families of the form [fun oa => O (B oa)], and similarly only that path-spaces of types [O A] are modal, where "modal" means that the unit is an equivalence.  This is equivalent, roughly since every modal type [A] (in this sense) is equivalent to [O A].  However, our definition is more convenient in formalized applications because in some examples (such as [Truncation] and closed modalities), there is a naturally occurring [O_rect] into all modal types that is not judgmentally equal to the one that can be constructed by passing through [O] and back again.

   However, in other examples (such as [~~] and open modalities) it is easier to construct the latter weaker induction principle.  Thus, we now show how to get from that to our definition of modality. *)

Section EasyModality.
  Context {fs : Funext}.

  Context (O : Type -> Type).

  Context (O_unit : forall T, T -> O T).

  Let inO' A := IsEquiv (O_unit A).

  Context (O_rectO : forall A (B : O A -> Type),
                       (forall a, O (B (O_unit A a)))
                       -> forall z, O (B z)).

  Context (O_rectO_beta : forall A B (f : forall a, O (B (O_unit A a))) a,
      O_rectO A B f (O_unit A a) = f a).

  Context (inO_pathsO : forall A (z z' : O A), inO' (z = z')).

  (** Here is the defined more general induction principle. *)

  Local Definition O_rect' A (B : O A -> Type)
        (B_inO : forall oa, inO' (B oa))
        (f : forall a, B (O_unit A a))
        (oa : O A) : B oa.
  Proof.
    pose (H := B_inO oa); unfold inO' in H.
    apply ((O_unit (B oa))^-1).
    apply O_rectO.
    intros a; apply O_unit, f.
  Defined.

  Local Definition O_rect_beta' A B {B_inO : forall oa, inO' (B oa)}
        (f : forall a : A, B (O_unit A a)) a
  : O_rect' A B B_inO f (O_unit A a) = f a.
  Proof.
    unfold O_rect'.
    apply moveR_equiv_V.
    apply @O_rectO_beta with (f := fun x => O_unit _ (f x)).
  Qed.

  (** We start by building a [UnitSubuniverse]. *)

  Local Definition O_inO' A : inO' (O A).
  Proof.
    refine (isequiv_adjointify (O_unit (O A))
             (O_rectO (O A) (const A) idmap) _ _).
    - intros x; pattern x; apply O_rect'.
      + intros oa; apply inO_pathsO.
      + intros a; apply ap.
        exact (O_rectO_beta (O A) (const A) idmap a).
    - intros a.
      exact (O_rectO_beta (O A) (const A) idmap a).
  Defined.

  Local Instance usubU : UnitSubuniverse
    := Build_UnitSubuniverse
         (fun T => hp (IsEquiv (O_unit T)) _)
         O O_inO' O_unit.

  (** However, it seems to be surprisingly hard to show (without univalence) that this [UnitSubuniverse] is replete.  We basically have to develop enough functoriality of [O] and naturality of [O_unit].  We could do that directly, but instead we piggyback by showing that it is a reflective subuniverse. *)

  Local Instance rsubU : ReflectiveSubuniverse.
  Proof.
    assert (H : forall P Q, inO' Q ->
             IsEquiv (fun f : O P -> Q => f o O_unit P)).
    { intros P Q Q_inO.
      refine (isequiv_adjointify _
               (O_rect' P (const Q) (const Q_inO)) _ _).
      - intros f.
        apply path_forall; intros x.
        apply O_rect_beta'.
      - intros f.
        refine (@equiv_inj _ _
                 (compose (O_unit Q))
                 (@isequiv_postcompose _ _ _ _ (O_unit Q) Q_inO) _ _ _).
        apply path_forall; intros x; pattern x.
        apply O_rect'.
        + intros oa; apply inO_pathsO. 
        + intros a; unfold compose.
          apply ap.
          apply (O_rect_beta' P (const Q)). }
    exact (Build_ReflectiveSubuniverse usubU H).
  Defined.

  (** It is now automatically replete, since in our case [inO] means by definition that [O_unit] is an equivalence. *)

  Local Instance replete_rsubU : Replete rsubU
    := replete_inO_isequiv_O_unit (fun _ H => H).

  (** Finally, we can build a modality. *)

  Definition Build_Modality_easy : Modality.
  Proof.
    refine (Build_Modality usubU _ O_rect' O_rect_beta' _); cbn.
    intros A A_inO x y.
    refine (inO_equiv_inO (O_unit A x = O_unit A y) (x = y)
                          (inO_pathsO A _ _)
                          (ap (O_unit A))^-1 _).
  Defined.

End EasyModality.

(** We now prove various useful things about a general modality. *)
Section Modalities.
  Context {fs : Funext}.
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

  (** We show that modalities have underlying reflective subuniverses.  It is important in some applications, such as [Truncation], that this construction uses the general [O_rect] given as part of the modality data, and not one constructed out of [O_rectO] as we did when proving [Build_Modality_easy].  For instance, this ensures that [O_functor] reduces to simply an application of [O_rect]. *)

  (** Corollary 7.7.8, part 1 *)
  Global Instance modality_to_reflective_subuniverse
  : ReflectiveSubuniverse
    := Build_ReflectiveSubuniverse _ isequiv_o_O_unit.

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

(** Conversely, if a reflective subuniverse is closed under sigmas, it is a modality. *)

Theorem reflective_subuniverse_to_modality `{fs : Funext}
  (subU : ReflectiveSubuniverse) {rep : Replete subU}
  (H : forall (A:Type) (B:A -> Type)
          {A_inO : inO A} {B_inO : forall a, inO (B a)},
     (inO ({x:A & B x})))
  : Modality.
Proof.
  pose (K := fst inO_sigma_iff H).
  exact (Build_Modality _ _
           (fun A B B_inO g => pr1 (K A B B_inO g))
           (fun A B B_inO g => pr2 (K A B B_inO g))
           _).
Defined.

(** Finally, we give one example of a modality.  This is Exercise 7.12 in the book. *)
Definition notnot_modality `{Funext} : Modality.
Proof.
  refine (Build_Modality_easy
            (fun X => ~~X)
            (fun X x nx => nx x)
            (fun A B f z nBz =>
              z (fun a => f a (transport (fun x => ~B x)
                                          (allpath_hprop _ _)
                                          nBz)))
            _ _).
  - intros; apply allpath_hprop.
  - intros; refine (isequiv_iff_hprop _ _).
    intros; apply allpath_hprop.
Defined.

(** For more examples of modalities, see hit/Truncations.v and hit/PropositionalFracture.v. *)
