(** * Comma categories *)
Require Import Category.Core Functor.Core.
Require Import InitialTerminalCategory.Core InitialTerminalCategory.Functors.
Require Functor.Identity.
Require Import Category.Strict.
Require Import types.Record Trunc HoTT.Tactics.
Import Functor.Identity.FunctorIdentityNotations.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope equiv_scope.
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
    Variable A : PreCategory.
    Variable B : PreCategory.
    Variable C : PreCategory.
    Variable S : Functor A C.
    Variable T : Functor B C.

    Record object :=
      {
        a : A;
        b : B;
        f : morphism C (S a) (T b)
      }.

    Local Notation object_sig_T :=
      ({ a : A
       | { b : B
         | morphism C (S a) (T b) }}).

    Lemma issig_object
    : object_sig_T <~> object.
    Proof.
      issig (@Build_object)
            (@a)
            (@b)
            (@f).
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
        match Ha in _ = X, Hb in _ = Y return morphism C (S X) (T Y) with
          | idpath, idpath => x.(f)
        end = y.(f)
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
      {
        g : Category.Core.morphism A (abf.(a)) (a'b'f'.(a));
        h : Category.Core.morphism B (abf.(b)) (a'b'f'.(b));
        p : T _1 h o abf.(f) = a'b'f'.(f) o S _1 g
      }.

    Local Notation morphism_sig_T abf a'b'f' :=
      ({ g : Category.Core.morphism A (abf.(a)) (a'b'f'.(a))
       | { h : Category.Core.morphism B (abf.(b)) (a'b'f'.(b))
         | T _1 h o abf.(f) = a'b'f'.(f) o S _1 g }}).

    Lemma issig_morphism abf a'b'f'
    : (morphism_sig_T abf a'b'f')
        <~> morphism abf a'b'f'.
    Proof.
      issig (@Build_morphism abf a'b'f')
            (@g abf a'b'f')
            (@h abf a'b'f')
            (@p abf a'b'f').
    Defined.

    Global Instance trunc_morphism abf a'b'f'
           `{IsTrunc n (Category.Core.morphism A (abf.(a)) (a'b'f'.(a)))}
           `{IsTrunc n (Category.Core.morphism B (abf.(b)) (a'b'f'.(b)))}
           `{forall m1 m2,
               IsTrunc n (T _1 m2 o abf.(f) = a'b'f'.(f) o S _1 m1)}
    : IsTrunc n (morphism abf a'b'f').
    Proof.
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
      exact (center _).
    Qed.

    Definition compose s d d'
               (gh : morphism d d') (g'h' : morphism s d)
    : morphism s d'.
    Proof.
      exists (gh.(g) o g'h'.(g)) (gh.(h) o g'h'.(h)).
      hnf in *; simpl in *.
      abstract (
          destruct_head morphism;
          rewrite !composition_of;
            by repeat try_associativity_quick progress rewrite_rev_hyp
        ).
    Defined.

    Global Arguments compose _ _ _ _ _ / .

    Definition identity x : morphism x x.
    Proof.
      exists (identity (x.(a))) (identity (x.(b))).
      abstract (
          simpl; autorewrite with category; reflexivity
        ).
    Defined.

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
  Variable A : PreCategory.
  Variable C : PreCategory.
  Variable a : C.
  Variable S : Functor A C.

  Definition slice_category := comma_category S (Functors.from_terminal C a).
  Definition coslice_category := comma_category (Functors.from_terminal C a) S.

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
  := Functors.from_terminal C x.
Coercion cc_identity_functor' (C : PreCategory) : CC_Functor' C C
  := 1%functor.
Global Arguments CC_Functor' / .
Global Arguments cc_functor_from_terminal' / .
Global Arguments cc_identity_functor' / .

Module Export CommaCoreNotations.
  (** We really want to use infix [↓] for comma categories, but that's unicode.  Infix [,] might also be reasonable, but I can't seem to get it to work without destroying the [(_, _)] notation for ordered pairs.  So I settle for the ugly ASCII rendition [/] of [↓]. *)
  (** Set some notations for printing *)
  Notation "C / a" := (@slice_category_over C a) : category_scope.
  Notation "a \ C" := (@coslice_category_over C a) (at level 40, left associativity) : category_scope.
  Notation "a / C" := (@coslice_category_over C a) : category_scope.
  Notation "x / F" := (coslice_category x F) : category_scope.
  Notation "F / x" := (slice_category x F) : category_scope.
  Notation "S / T" := (comma_category S T) : category_scope.
  (** Set the notation for parsing; coercions will automatically decide which of the arguments are functors and which are objects, i.e., functors from the terminal category. *)
  Notation "S / T" := (comma_category (S : CC_Functor' _ _)
                                      (T : CC_Functor' _ _)) : category_scope.
End CommaCoreNotations.
