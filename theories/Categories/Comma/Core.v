(** * Comma categories *)
Require Import Category.Core Functor.Core.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors.
Require Functor.Identity.
Require Import Category.Strict.
Require Import Types.Paths Types.Sigma Trunc HoTT.Tactics HProp.
Import Functor.Identity.FunctorIdentityNotations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.


Local Open Scope morphism_scope.
Local Open Scope category_scope.

(** Quoting Wikipedia:

    Suppose that [A], [B], and [C] are categories, and [S] and [T] are
    functors

    [S : A → C ← B : T]

    We can form the comma category [(S ↓ T)] as follows:

    - The objects are all triples [(α, β, f)] with [α] an object in
      [A], [β] an object in [B], and [f : S α -> T β] a morphism in
      [C].

    - The morphisms from [(α, β, f)] to [(α', β', f')] are all pairs
      [(g, h)] where [g : α → α'] and [h : β → β'] are morphisms in
      [A] and [B] respectively, such that the following diagram
      commutes:

<<
             S g
        S α -----> S α'
         |          |
       f |          | f'
         |          |
         ↓          ↓
        T β -----> T β'
             T h
>>

    Morphisms are composed by taking [(g, h) ∘ (g', h')] to be [(g ∘
    g', h ∘ h')], whenever the latter expression is defined.  The
    identity morphism on an object [(α, β, f)] is [(1_α, 1_β)].  *)

(** ** Comma category [(S / T)] *)
Module Import CommaCategory.
  Section comma_category_parts.
    Variables A B C : PreCategory.
    Variable S : Functor A C.
    Variable T : Functor B C.

    Record object :=
      {
        a : A;
        b : B;
        f : morphism C (S a) (T b)
      }.

    Global Arguments a _ / .
    Global Arguments b _ / .
    Global Arguments f _ / .

    Local Notation object_sig_T :=
      ({ a : A
       | { b : B
         | morphism C (S a) (T b) }}).

    Lemma issig_object
    : object_sig_T <~> object.
    Proof.
      issig.
    Defined.

    Global Instance trunc_object `{IsTrunc n A, IsTrunc n B}
           `{forall s d, IsTrunc n (morphism C s d)}
    : IsTrunc n object.
    Proof.
      eapply trunc_equiv';
      [ exact issig_object | ].
      typeclasses eauto.
    Qed.

    Lemma path_object' (x y : object)
    : forall (Ha : x.(a) = y.(a))
             (Hb : x.(b) = y.(b)),
        transport (fun X => morphism C (S X) _)
                  Ha
                  (transport (fun Y => morphism C _ (T Y))
                             Hb
                             x.(f))
        = y.(f)
        -> x = y.
    Proof.
      destruct x, y; simpl.
      intros; path_induction; reflexivity.
    Defined.

    Lemma ap_a_path_object' x y Ha Hb Hf
    : ap (@a) (@path_object' x y Ha Hb Hf) = Ha.
    Proof.
      destruct x, y; simpl in *.
      destruct Ha, Hb, Hf; simpl in *.
      reflexivity.
    Qed.

    Lemma ap_b_path_object' x y Ha Hb Hf
    : ap (@b) (@path_object' x y Ha Hb Hf) = Hb.
    Proof.
      destruct x, y; simpl in *.
      destruct Ha, Hb, Hf; simpl in *.
      reflexivity.
    Qed.

    Global Arguments path_object' : simpl never.

    Record morphism (abf a'b'f' : object) :=
      Build_morphism' {
          g : Category.Core.morphism A (abf.(a)) (a'b'f'.(a));
          h : Category.Core.morphism B (abf.(b)) (a'b'f'.(b));
          p : T _1 h o abf.(f) = a'b'f'.(f) o S _1 g;
          p_sym : a'b'f'.(f) o S _1 g = T _1 h o abf.(f)
        }.

    Definition Build_morphism abf a'b'f' g h p : morphism abf a'b'f'
      := @Build_morphism' abf a'b'f' g h p p^.

    Global Arguments Build_morphism / .
    Global Arguments g _ _ _ / .
    Global Arguments h _ _ _ / .
    Global Arguments p _ _ _ / .
    Global Arguments p_sym _ _ _ / .

    Local Notation morphism_sig_T abf a'b'f' :=
      ({ g : Category.Core.morphism A (abf.(a)) (a'b'f'.(a))
       | { h : Category.Core.morphism B (abf.(b)) (a'b'f'.(b))
         | T _1 h o abf.(f) = a'b'f'.(f) o S _1 g }}).

    Local Notation morphism_sig_T' abf a'b'f' :=
      ({ g : Category.Core.morphism A (abf.(a)) (a'b'f'.(a))
       | { h : Category.Core.morphism B (abf.(b)) (a'b'f'.(b))
         | { _ : T _1 h o abf.(f) = a'b'f'.(f) o S _1 g
           | a'b'f'.(f) o S _1 g = T _1 h o abf.(f) }}}).

    Lemma issig_morphism' abf a'b'f'
    : (morphism_sig_T' abf a'b'f')
        <~> morphism abf a'b'f'.
    Proof.
      issig.
    Defined.

    Lemma issig_morphism_helper {T0} `{IsHSet T0} (a b : T0) (pf : a = b)
    : Contr (b = a).
    Proof.
      destruct pf.
      apply contr_inhabited_hprop; try reflexivity.
      typeclasses eauto.
    Qed.


    Lemma issig_morphism abf a'b'f'
    : (morphism_sig_T abf a'b'f')
        <~> morphism abf a'b'f'.
    Proof.
      etransitivity; [ | exact (issig_morphism' abf a'b'f') ].
      repeat (apply equiv_functor_sigma_id; intro).
      symmetry; apply equiv_sigma_contr; intro.
      apply issig_morphism_helper; assumption.
    Defined.

    Global Instance trunc_morphism abf a'b'f'
           `{IsTrunc n (Category.Core.morphism A (abf.(a)) (a'b'f'.(a)))}
           `{IsTrunc n (Category.Core.morphism B (abf.(b)) (a'b'f'.(b)))}
           `{forall m1 m2,
               IsTrunc n (T _1 m2 o abf.(f) = a'b'f'.(f) o S _1 m1)}
    : IsTrunc n (morphism abf a'b'f').
    Proof.
      assert (forall m1 m2,
                IsTrunc n (a'b'f'.(f) o S _1 m1 = T _1 m2 o abf.(f)))
        by (intros; apply (trunc_equiv _ inverse)).
      eapply trunc_equiv';
      [ exact (issig_morphism _ _) | ].
      typeclasses eauto.
    Qed.

    Lemma path_morphism abf a'b'f'
          (gh g'h' : morphism abf a'b'f')
    : gh.(g) = g'h'.(g)
      -> gh.(h) = g'h'.(h)
      -> gh = g'h'.
    Proof.
      destruct gh, g'h'; simpl.
      intros; path_induction.
      f_ap.
      all:exact (center _).
    Qed.

    Definition compose s d d'
               (gh : morphism d d') (g'h' : morphism s d)
    : morphism s d'
      := Build_morphism'
           s d'
           (gh.(g) o g'h'.(g))
           (gh.(h) o g'h'.(h))
           ((ap (fun m => m o s.(f)) (composition_of T _ _ _ _ _))
              @ (associativity _ _ _ _ _ _ _ _)
              @ (ap (fun m => _ o m) g'h'.(p))
              @ (associativity_sym _ _ _ _ _ _ _ _)
              @ (ap (fun m => m o _) gh.(p))
              @ (associativity _ _ _ _ _ _ _ _)
              @ (ap (fun m => d'.(f) o m) (composition_of S _ _ _ _ _)^))%path
           ((ap (fun m => d'.(f) o m) (composition_of S _ _ _ _ _))
              @ (associativity_sym _ _ _ _ _ _ _ _)
              @ (ap (fun m => m o _) gh.(p_sym))
              @ (associativity _ _ _ _ _ _ _ _)
              @ (ap (fun m => _ o m) g'h'.(p_sym))
              @ (associativity_sym _ _ _ _ _ _ _ _)
              @ (ap (fun m => m o s.(f)) (composition_of T _ _ _ _ _)^))%path.

    Global Arguments compose _ _ _ _ _ / .

    Definition identity x : morphism x x
      := Build_morphism'
           x x
           (identity (x.(a)))
           (identity (x.(b)))
           ((ap (fun m => m o x.(f)) (identity_of T _))
              @ (left_identity _ _ _ _)
              @ ((right_identity _ _ _ _)^)
              @ (ap (fun m => x.(f) o m) (identity_of S _)^))
           ((ap (fun m => x.(f) o m) (identity_of S _))
              @ (right_identity _ _ _ _)
              @ ((left_identity _ _ _ _)^)
              @ (ap (fun m => m o x.(f)) (identity_of T _)^)).

    Global Arguments identity _ / .
  End comma_category_parts.
End CommaCategory.

Global Arguments CommaCategory.path_object' : simpl never.

Local Ltac path_comma_t :=
  intros;
  apply path_morphism;
  simpl;
  auto with morphism.

Definition comma_category A B C (S : Functor A C) (T : Functor B C)
: PreCategory.
Proof.
  refine (@Build_PreCategory
            (@object _ _ _ S T)
            (@morphism _ _ _ S T)
            (@identity _ _ _ S T)
            (@compose _ _ _ S T)
            _
            _
            _
            _
         );
  abstract path_comma_t.
Defined.

Global Instance isstrict_comma_category A B C S T
       `{IsStrictCategory A, IsStrictCategory B}
: IsStrictCategory (@comma_category A B C S T).
Proof.
  typeclasses eauto.
Qed.

(*  Section category.
    Context `{IsCategory A, IsCategory B}.
    (*Context `{Funext}. *)

    Definition comma_category_isotoid (x y : comma_category)
    : x ≅ y -> x = y.
    Proof.
      intro i.
      destruct i as [i [i' ? ?]].
      hnf in *.
      destruct i, i'.
      simpl in *.


    Global Instance comma_category_IsCategory `{IsCategory A, IsCategory B}
    : IsCategory comma_category.
    Proof.
      hnf.
      unfold IsStrictCategory in *.
      typeclasses eauto.
    Qed.
  End category.
*)

Hint Unfold compose identity : category.
Hint Constructors morphism object : category.

(** ** (co)slice category [(a / F)], [(F / a)] *)
Section slice_category.
  Variables A C : PreCategory.
  Variable a : C.
  Variable S : Functor A C.

  Definition slice_category := comma_category S (!a).
  Definition coslice_category := comma_category (!a) S.

  (** [x ↓ F] is a coslice category; [F ↓ x] is a slice category; [x ↓ F] deals with morphisms [x -> F y]; [F ↓ x] has morphisms [F y -> x] *)
End slice_category.

(** ** (co)slice category over [(a / C)], [(C / a)] *)
Section slice_category_over.
  Variable C : PreCategory.
  Variable a : C.

  Definition slice_category_over := slice_category a (Functor.Identity.identity C).
  Definition coslice_category_over := coslice_category a (Functor.Identity.identity C).
End slice_category_over.

(** ** category of arrows *)
Section arrow_category.
  Variable C : PreCategory.

  Definition arrow_category := comma_category (Functor.Identity.identity C) (Functor.Identity.identity C).
End arrow_category.

Definition CC_Functor' (C : PreCategory) (D : PreCategory) := Functor C D.
Coercion cc_functor_from_terminal' (C : PreCategory) (x : C) : CC_Functor' _ C
  := (!x)%functor.
Coercion cc_identity_functor' (C : PreCategory) : CC_Functor' C C
  := 1%functor.
Global Arguments CC_Functor' / .
Global Arguments cc_functor_from_terminal' / .
Global Arguments cc_identity_functor' / .

Local Set Warnings Append "-notation-overridden". (* work around bug #5567, https://coq.inria.fr/bugs/show_bug.cgi?id=5567, notation-overridden,parsing should not trigger for only printing notations *)
Module Export CommaCoreNotations.
  (** We really want to use infix [↓] for comma categories, but that's unicode.  Infix [,] might also be reasonable, but I can't seem to get it to work without destroying the [(_, _)] notation for ordered pairs.  So I settle for the ugly ASCII rendition [/] of [↓]. *)
  (** Set some notations for printing *)
  Notation "C / a" := (@slice_category_over C a) (only printing) : category_scope.
  Notation "a \ C" := (@coslice_category_over C a) : category_scope.
  Notation "a / C" := (@coslice_category_over C a) (only printing) : category_scope.
  Notation "x / F" := (coslice_category x F) (only printing) : category_scope.
  Notation "F / x" := (slice_category x F) (only printing) : category_scope.
  Notation "S / T" := (comma_category S T) (only printing) : category_scope.
  (** Set the notation for parsing; coercions will automatically decide which of the arguments are functors and which are objects, i.e., functors from the terminal category. *)
  Notation "S / T" := (comma_category (S : CC_Functor' _ _)
                                      (T : CC_Functor' _ _)) : category_scope.
End CommaCoreNotations.
