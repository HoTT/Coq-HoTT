(* -*- mode: coq -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import CoReflectiveSubuniverse.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * CoModalities *)

Class CoModality :=
  {
    comod_usubu : CoUnitSubuniverse ;
    comod_replete : Replete comod_usubu ;
    (* The idea is that every element of A comes from O A.  So to show
    that every A is necessarily B, it suffices to show that every A
    which follows by necessity is necessarily B*)
    O_coind : forall A (B : A -> Type) (A_inO : inO A),
               (forall oa : O A, O (B (O_counit A oa))) -> forall a, O (B a) ;
    O_coind_beta : forall A B A_inO f oa,
                    (O_coind A B A_inO f (O_counit A oa)) = f oa ;
    inO_paths : forall A (A_inO : inO A) (z z' : A), inO (z = z')
  }.

Arguments O_coind {CoModality} {A} B {A_inO} f a.
Arguments O_coind_beta {CoModality} {A} B {A_inO} f oa.

(** See CoReflectiveSubuniverse.v for explanation of how to use (and how not to use) [CoModality] as a typeclass. *)

Global Existing Instance comod_usubu.
(* We don't declare this as a coercion, since soon we're going to declare a coercion from [CoModality] to [CoReflectiveSubuniverse]; then we'll get this coercion automatically as a composite. *)
(* Coercion comod_usubu : CoModality >-> CoUnitSubuniverse. *)
Global Existing Instance comod_replete.
Global Existing Instance inO_paths.


(*
Section EasyCoModality.

  Context (O : Type -> Type).

  Context (O_counit : forall T, O T -> T).

  Let inO' A := IsEquiv (O_counit A).

  Context (O_coindO : forall A (B : A -> Type),
                       (forall oa, O (B (O_counit A oa)))
                       -> forall a, O (B a)).

  Context (O_coindO_beta : forall A B f oa, 
                             O_coindO A B f (O_counit A oa) = f oa).

  Context (inO_pathsO : forall A (z z' : O A), inO' (z = z')).

  (** Here is the defined more general induction principle. *)

  Local Definition O_coind' A (B : A -> Type) (A_inO : inO' A)
        (f : forall oa, O (B (O_counit A oa))) (a : A) : O (B a).
  Proof.
    apply O_coindO.
    intros oa. apply f.
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
         (fun T => IsEquiv (O_unit T))
         O O_inO' O_unit _.

  (** However, it seems to be surprisingly hard to show (without univalence) that this [UnitSubuniverse] is replete.  We basically have to develop enough functoriality of [O] and naturality of [O_unit].  We could do that directly, but instead we piggyback by showing that it is a reflective subuniverse.  This is why we excluded repleteness from the basic definition of [ReflectiveSubuniverse] and the proofs of functoriality. *)

  Local Instance rsubU : ReflectiveSubuniverse.
  Proof.
    refine (Build_ReflectiveSubuniverse _ _ _ _ _);
      intros P Q ?.
    - intros f. exact (O_rect' P (fun _ => Q) (fun _ => Q_inO) f).
    - intros f x. exact (O_rect_beta' P (fun _ => Q) f x).
    - intros g h p x.
      cbn in Q_inO.
      refine ((ap (O_unit Q))^-1 _).
      refine (O_rect' P (fun y => O_unit Q (g y) = O_unit Q (h y)) _ _ x).
      + intros y. apply inO_pathsO.
      + intros a; apply ap, p.
    - intros g h p x; cbn.
      rewrite O_rect_beta'.
      rewrite concat_pp_p.
      apply moveR_Vp.
      rewrite <- ap_compose.
      exact (concat_A1p (eissect (O_unit Q)) (p x)).
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

(** The induction principle [O_rect], like most induction principles, is an equivalence. *)
Section ORectEquiv.
  Context {fs : Funext}.
  Context {mod : Modality}.

  Section ORectEquivData.

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

  End ORectEquivData.

  Local Definition isequiv_o_O_unit (A B : Type) (B_inO : inO B)
  : IsEquiv (fun (h : O A -> B) => h o O_unit A)
    := isequiv_oD_O_unit (fun _ => B).

End ORectEquiv.

(** We show that modalities have underlying reflective subuniverses.  It is important in some applications, such as [Trunc], that this construction uses the general [O_rect] given as part of the modality data, and not one constructed out of [O_rectO] as we did when proving [Build_Modality_easy].  For instance, this ensures that [O_functor] reduces to simply an application of [O_rect].

 Note also that our choice of how to define reflective subuniverses differently from the book enables us to prove this without using funext. *)

(** Corollary 7.7.8, part 1 *)
Global Instance modality_to_reflective_subuniverse (mod : Modality)
: ReflectiveSubuniverse
:= Build_ReflectiveSubuniverse _
     (fun P Q H => O_rect (fun _ => Q))
     (fun P Q H => O_rect_beta (fun _ => Q))
     (fun P Q H g h => O_rect (fun y => g y = h y))
     (fun P Q H g h => O_rect_beta (fun y => g y = h y)).

Coercion modality_to_reflective_subuniverse : Modality >-> ReflectiveSubuniverse.

(** Corollary 7.7.8, part 2 *)
Global Instance inO_sigma {mod : Modality} (A:Type) (B:A -> Type)
       {A_inO : inO A} {B_inO : forall a, inO (B a)}
: inO {x:A & B x}.
Proof.
  generalize dependent A.
  refine (snd inO_sigma_iff _).
  intros A B ? g.
  exists (O_rect B g).
  apply O_rect_beta.
Defined.

(** Conversely, if a reflective subuniverse is closed under sigmas, it is a modality. *)

Theorem reflective_subuniverse_to_modality
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

(** Finally, we give one nontrivial example of a modality.  This is Exercise 7.12 in the book. *)
Definition notnot_modality `{Funext} : Modality.
Proof.
  refine (Build_Modality_easy
            (fun X => ~~X)
            (fun X x nx => nx x)
            (fun A B f z nBz =>
              z (fun a => f a (transport (fun x => ~B x)
                                          (path_ishprop _ _)
                                          nBz)))
            _ _).
  - intros; apply path_ishprop.
  - intros; refine (isequiv_iff_hprop _ _).
    intros; apply path_ishprop.
Defined.

(** Of course, there is also the trivial example. *)
Definition identity_modality : Modality
  := Build_Modality
     (Build_UnitSubuniverse
        (fun _ => Unit)
        idmap
        (fun _ => tt)
        (fun T => idmap)
        _)
     (fun T U _ _ _ => tt)
     (fun A B _ f a => f a)
     (fun A B _ f a => 1)
     (fun A _ z z' => tt).
*)