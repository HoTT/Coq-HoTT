(** * Lifting saturation from categories to sigma/subcategories *)
Require Import Category.Core Category.Morphisms.
Require Import Category.Univalent.
Require Import Category.Sigma.Core Category.Sigma.OnObjects Category.Sigma.OnMorphisms.
Require Import HoTT.Types.Sigma HoTT.Basics.Equivalences HoTT.Basics.Trunc HoTT.Basics.PathGroupoids HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation pr1_type := Overture.pr1 (only parsing).

Local Open Scope path_scope.
Local Open Scope morphism_scope.

Local Open Scope function_scope.

(** TODO: Following a comment from Mike Shulman
    (https://github.com/HoTT/HoTT/pull/670##issuecomment-68907833),
    much of this can probably be subsumed by a general theorem proving
    that univalence lifts along suitable pseudomonic functors
    (http://ncatlab.org/nlab/show/pseudomonic+functor). *)

(** ** Lift saturation to sigma on objects whenever the property is an hProp *)
Section onobjects.
  Variable A : PreCategory.
  Variable Pobj : A -> Type.

  Global Instance iscategory_sigT_obj `{forall a, IsHProp (Pobj a), A_cat : IsCategory A}
  : IsCategory (sigT_obj A Pobj).
  Proof.
    intros s d.
    refine (isequiv_homotopic
              ((issig_full_isomorphic (sigT_obj A Pobj) _ _ o (issig_full_isomorphic A _ _)^-1)
                 o (@idtoiso A s.1 d.1)
                 o pr1_path)
              _).
    intro x; destruct x.
    reflexivity.
  Defined.

  (** The converse is not true; consider [Pobj := fun _ => Empty]. *)
End onobjects.

(** ** Lift saturation to sigma on objects whenever the property is automatically and uniquely true of isomorphisms *)
Section onmorphisms.
  Variable A : PreCategory.
  Variable Pmor : forall s d, morphism A s d -> Type.

  Local Notation mor s d := { m : _ | Pmor s d m }%type.
  Context `(HPmor : forall s d, IsHSet (mor s d)).

  Variable Pidentity : forall x, @Pmor x x (@identity A _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 o m2).

  Local Notation identity x := (@identity A x; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 o m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Hypothesis P_associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).

  Hypothesis P_left_identity
  : forall a b (f : mor a b),
      compose (identity b) f = f.

  Hypothesis P_right_identity
  : forall a b (f : mor a b),
      compose f (identity a) = f.

  Local Notation A' := (@sigT_mor A Pmor HPmor Pidentity Pcompose P_associativity P_left_identity P_right_identity).

  (** To have any hope of relating [IsCategory A] with [IsCategory
      A'], we assume that [Pmor] is automatically and uniquely true on
      isomorphisms. *)
  Context `{forall s d m, IsIsomorphism m -> Contr (Pmor s d m)}.

  Definition iscategory_sigT_mor_helper {s d}
  : @Isomorphic A' s d -> @Isomorphic A s d.
  Proof.
    refine ((issig_full_isomorphic A _ _) o _ o (issig_full_isomorphic A' _ _)^-1).
    exact (functor_sigma
             pr1_type
             (fun _ =>
                functor_sigma
                  pr1_type
                  (fun _ =>
                     functor_sigma
                       pr1_path
                       (fun _ => pr1_path)))).
  Defined.

  Local Instance isequiv_iscategory_sigT_mor_helper s d
  : IsEquiv (@iscategory_sigT_mor_helper s d).
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    { intro e.
      exists (e : morphism _ _ _; center _).
      exists (e^-1%morphism; center _);
        simple refine (path_sigma _ _ _ _ _);
        first [ apply left_inverse
              | apply right_inverse
              | by apply path_ishprop ]. }
    { intro; by apply path_isomorphic. }
    { intros x; apply path_isomorphic.
      exact (path_sigma' _ 1 (contr _)). }
  Defined.

  Global Instance iscategory_sigT_mor `{A_cat : IsCategory A}
  : IsCategory A'.
  Proof.
    intros s d.
    refine (isequiv_homotopic
              (iscategory_sigT_mor_helper^-1 o @idtoiso _ _ _)
              _).
    intro x; apply path_isomorphic; cbn.
    destruct x; refine (path_sigma' _ 1 (contr _)).
  Defined.

  Definition iscategory_from_sigT_mor `{A'_cat : IsCategory A'}
  : IsCategory A.
  Proof.
    intros s d.
    refine (isequiv_homotopic
              (iscategory_sigT_mor_helper
                 o (@idtoiso A' _ _))
              _).
    intro x; apply path_isomorphic; cbn.
    destruct x; reflexivity.
  Defined.

  Global Instance isequiv_iscategory_sigT_mor `{Funext}
  : IsEquiv (@iscategory_sigT_mor).
  Proof.
    refine (isequiv_iff_hprop _ (@iscategory_from_sigT_mor)).
  Defined.
End onmorphisms.

(** ** Lift saturation to sigma on both objects and morphisms *)
Section on_both.
  Variable A : PreCategory.
  Variable Pobj : A -> Type.

  Local Notation obj := { x : _ | Pobj x }%type (only parsing).

  Variable Pmor : forall s d : obj, morphism A s.1 d.1 -> Type.

  Local Notation mor s d := { m : _ | Pmor s d m }%type (only parsing).
  Context `(HPmor : forall s d, IsHSet (mor s d)).

  Variable Pidentity : forall x, @Pmor x x (@identity A _).
  Variable Pcompose : forall s d d' m1 m2,
                        @Pmor d d' m1
                        -> @Pmor s d m2
                        -> @Pmor s d' (m1 o m2).

  Local Notation identity x := (@identity A x.1; @Pidentity x).
  Local Notation compose m1 m2 := (m1.1 o m2.1; @Pcompose _ _ _ m1.1 m2.1 m1.2 m2.2)%morphism.

  Hypothesis P_associativity
  : forall x1 x2 x3 x4 (m1 : mor x1 x2) (m2 : mor x2 x3) (m3 : mor x3 x4),
      compose (compose m3 m2) m1 = compose m3 (compose m2 m1).

  Hypothesis P_left_identity
  : forall a b (f : mor a b),
      compose (identity b) f = f.

  Hypothesis P_right_identity
  : forall a b (f : mor a b),
      compose f (identity a) = f.

  Local Notation A' := (@sigT A Pobj Pmor HPmor Pidentity Pcompose P_associativity P_left_identity P_right_identity).

  (** We must assume some relation on the properties; we assume that
      the path space of the extra data on objects is classified by
      isomorphisms of the extra data on objects. *)
  Local Definition Pmor_iso_T s d m m' left right :=
    ({ e : Pmor s d m
     | { e' : Pmor d s m'
       | { _ : transport (Pmor _ _) ((left : m' o m = 1)%morphism) (Pcompose e' e) = Pidentity _
         | transport (Pmor _ _) ((right : m o m' = 1)%morphism) (Pcompose e e') = Pidentity _ } } }).

  Global Arguments Pmor_iso_T / .

  Local Definition Pmor_iso_T' x (xp xp' : Pobj x)
    := { e : Pmor (x; xp) (x; xp') 1
       | { e' : Pmor (x; xp') (x; xp) 1
         | { _ : Pcompose e' e = Pcompose (Pidentity _) (Pidentity _)
           | Pcompose e e' = Pcompose (Pidentity _) (Pidentity _) } } }.

  Global Arguments Pmor_iso_T' / .

  Local Definition Pidtoiso x (xp xp' : Pobj x) (H : xp = xp')
  : Pmor_iso_T' xp xp'.
  Proof.
    destruct H.
    exists (Pidentity _).
    exists (Pidentity _).
    split; reflexivity.
  Defined.

  Global Arguments Pidtoiso / .

  (** TODO: generalize this to a theorem [forall A P, IsHSet A -> IsHSet { x : A | P x } -> forall x, IsHSet (P x)], [inO_unsigma] of ##672 *)
  Local Instance ishset_pmor {s d m} : IsHSet (Pmor s d m).
  Proof.
    intros p q.
    apply hprop_allpath.
    let H := constr:(_ : forall x y : mor s d, IsHProp (x = y)) in
    pose proof (@path_ishprop _ (H (m; p) (m; q))) as H'.
    intros x y.
    specialize (H' (path_sigma' _ 1 x) (path_sigma' _ 1 y)).
    unfold path_sigma', path_sigma in H'.
    apply (ap (path_sigma_uncurried (Pmor s d) (m; p) (m; q)))^-1 in H'.
    assert (H'' : H'..1 = idpath) by apply path_ishprop.
    exact (transport (fun H'1 => transport _ H'1 _ = _) H'' H'..2).
  Defined.

  Local Definition Pmor_iso_adjust x xp xp'
  : (Pmor_iso_T (x; xp) (x; xp') 1 1 (left_identity _ _ _ _) (right_identity _ _ _ _))
      <~> Pmor_iso_T' xp xp'.
  Proof.
    refine (equiv_functor_sigma' (equiv_idmap _) _); intro.
    refine (equiv_functor_sigma' (equiv_idmap _) _); intro.
    refine (equiv_functor_sigma' (equiv_iff_hprop _ _) (fun _ => equiv_iff_hprop _ _));
      cbn; intro H';
      first [ apply moveL_transport_V in H'
                | apply moveR_transport_p ];
      refine (H' @ _);
      first [ refine (_ @ ((P_left_identity (identity (x; _)))^)..2)
                | refine ((((P_left_identity (identity (x; _)))^)..2)^ @ _) ];
      refine (ap (fun p => transport _ p _) (path_ishprop _ _)).
  Defined.

  Global Arguments Pmor_iso_adjust / .

  Local Definition iso_A'_code {s d}
  : (@Isomorphic A' s d)
    -> { e : @Isomorphic A s.1 d.1
       | Pmor_iso_T s d e e^-1 (@left_inverse _ _ _ e e) right_inverse }.
  Proof.
    intro e.
    simple refine (_; _).
    { exists (e : morphism _ _ _).1.
      exists (e^-1%morphism).1.
      exact (@left_inverse _ _ _ e e)..1.
      exact (@right_inverse _ _ _ e e)..1. }
    { exists (e : morphism _ _ _).2.
      exists (e^-1%morphism).2; cbn.
      exists (((@left_inverse _ _ _ e e))..2).
      exact (@right_inverse _ _ _ e e)..2. }
  Defined.

  Local Definition iso_A'_decode_helper {s d}
        (e : { e : @Isomorphic A s.1 d.1
             | Pmor_iso_T s d e e^-1 (@left_inverse _ _ _ e e) right_inverse })
  : @IsIsomorphism A' _ _ (e.1:morphism A s.1 d.1; (e.2).1).
  Proof.
    eexists. Unshelve.
    3:exact (e.1^-1%morphism; e.2.2.1).
    { refine (path_sigma' _ left_inverse e.2.2.2.1). }
    { refine (path_sigma' _ right_inverse e.2.2.2.2). }
  Defined.

  Local Definition iso_A'_decode {s d}
  : { e : @Isomorphic A s.1 d.1
    | Pmor_iso_T s d e e^-1 (@left_inverse _ _ _ e e) right_inverse }
    -> (@Isomorphic A' s d).
  Proof.
    intro e.
    eexists. Unshelve.
    2:exact (e.1 : morphism _ _ _; e.2.1).
    apply iso_A'_decode_helper.
  Defined.

  Local Definition equiv_iso_A'_eisretr_helper {s d}
        (x : {e : @Isomorphic A s.1 d.1
             | Pmor_iso_T s d e e^-1 (@left_inverse _ _ _ e e) right_inverse }%type)
  : transport
      (fun e : @Isomorphic A s.1 d.1 =>
         Pmor_iso_T s d e e^-1 left_inverse right_inverse)
      (path_isomorphic (iso_A'_code (iso_A'_decode x)).1 x.1 1)
      (iso_A'_code (iso_A'_decode x)).2 = x.2.
  Proof.
    simple refine (path_sigma _ _ _ _ _); cycle 1.
    simple refine (path_sigma _ _ _ _ (path_ishprop _ _)).
    all:repeat match goal with
                 | [ |- (transport ?P ?p ?z).1 = _ ] => rewrite (@ap_transport _ P _ _ _ p (fun _ x => x.1))
                 | [ |- (transport ?P ?p ?z).2.1 = _ ] => rewrite (@ap_transport _ P _ _ _ p (fun _ x => x.2.1))
                 | [ |- transport (fun _ => ?x) _ _ = _ ] => rewrite transport_const
                 | [ |- transport (fun x => ?f (@morphism_inverse _ _ _ (@morphism_isomorphic _ _ _ x) _)) _ _ = _ ]
                   => rewrite (@transport_compose _ _ _ _ f (fun x => (@morphism_inverse _ _ _ (@morphism_isomorphic _ _ _ x) (@isisomorphism_isomorphic _ _ _ x))))
                 | [ |- transport (?f o ?g) _ _ = _ ] => rewrite (@transport_compose _ _ _ _ f g)
                 | [ |- transport (fun x => ?f (?g x)) _ _ = _ ] => rewrite (@transport_compose _ _ _ _ f g)
                 | [ |- context[ap (@morphism_isomorphic ?a ?b ?c) (path_isomorphic ?i ?j ?x)] ]
                   => change (ap (@morphism_isomorphic a b c)) with ((path_isomorphic i j)^-1%function);
                     rewrite (@eissect _ _ (path_isomorphic i j) _ x)
                 | [ |- context[ap (fun e : Isomorphic _ _ => @morphism_inverse ?C ?s ?d _ _) (path_isomorphic ?i ?j ?x)] ]
                   => rewrite (@ap_morphism_inverse_path_isomorphic C s d i j x 1)
                 | [ |- transport ?P 1 ?x = ?y ] => change (x = y)
                 | [ |- (((iso_A'_code (iso_A'_decode ?x)).2).2).1 = ((?x.2).2).1 ] => reflexivity
                 | [ |- (((iso_A'_code (iso_A'_decode ?x)).2).1) = ((?x.2).1) ] => reflexivity
               end.
  Qed.

  Local Definition equiv_iso_A' {s d}
  : (@Isomorphic A' s d)
      <~> { e : @Isomorphic A s.1 d.1
          | Pmor_iso_T s d e e^-1 (@left_inverse _ _ _ e e) right_inverse }.
  Proof.
    refine (equiv_adjointify iso_A'_code iso_A'_decode _ _).
    { intro.
      simple refine (path_sigma _ _ _ _ _).
      { apply path_isomorphic; reflexivity. }
      { apply equiv_iso_A'_eisretr_helper. }  }
    { intro.
      apply path_isomorphic.
      reflexivity. }
  Defined.

  Context `{Pisotoid : forall x xp xp', IsEquiv (@Pidtoiso x xp xp')}.

  Local Arguments Pmor_iso_T : simpl never.

  Global Instance iscategory_sigT `{A_cat : IsCategory A}
  : IsCategory A'.
  Proof.
    intros s d.
    simple refine (isequiv_homotopic
              ((equiv_iso_A'^-1)
                 o (functor_sigma _ _)
                 o (path_sigma_uncurried _ _ _)^-1)
              _); try exact _.
    { exact (@idtoiso A _ _). }
    1:revert Pisotoid; clear; intro Pisotoid.
    all:repeat (refine isequiv_compose; []).
    { destruct s as [s0 s1], d as [d0 d1]; cbn.
      intro p; destruct p; cbn.
      refine ((@Pmor_iso_adjust s0 s1 d1)^-1 o _).
      refine (@Pidtoiso _ _ _). }
    { refine isequiv_functor_sigma.
      destruct s, d.
      simpl Overture.pr1.
      intro p; destruct p.
      eapply @isequiv_compose.
      exact _.
      eapply @isequiv_inverse. }
    { intro p; apply path_isomorphic; destruct p.
      reflexivity. }
  Defined.
End on_both.
