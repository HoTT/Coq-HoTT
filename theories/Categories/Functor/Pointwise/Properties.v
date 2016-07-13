(** * Properties of pointwise functors *)
Require Import Category.Core Functor.Core Functor.Pointwise.Core NaturalTransformation.Core NaturalTransformation.Paths Functor.Composition.Core Functor.Identity Functor.Paths.
Require Import PathGroupoids Types.Forall HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope functor_scope.

Section parts.
  Context `{Funext}.

  (** We could do this all in a big [repeat match], but we split it
      up, to shave off about two seconds per proof. *)
  Local Ltac functor_pointwise_t helper_lem_match helper_lem :=
    repeat (apply path_forall; intro);
    rewrite !transport_forall_constant, !path_forall_2_beta;
    path_natural_transformation;
    repeat match goal with
             | [ |- context[components_of (transport ?P ?p ?z)] ]
               => simpl rewrite (@ap_transport _ P _ _ _ p (fun _ => components_of) z)
           end;
    rewrite !transport_forall_constant;
    transport_to_ap;
    repeat match goal with
             | [ x : _ |- context[ap (fun x3 : ?T => ?f (object_of x3 ?z))] ]
               => rewrite (@ap_compose' _ _ _ (fun x3' : T => object_of x3') (fun Ox3 => f (Ox3 x)))
             | [ x : _ |- context[ap (fun x3 : ?T => ?f (object_of x3 ?z) ?w)] ]
               => rewrite (@ap_compose' _ _ _ (fun x3' : T => object_of x3') (fun Ox3 => f (Ox3 x) w))
           end;
    repeat match goal with
             | _ => done
             | [ |- context[fun F => @object_of ?C ?D F] ]
               => progress change (fun F' => @object_of C D F') with (@object_of C D)
             | [ |- context[helper_lem_match ?x] ]
               => rewrite (helper_lem x)
           end.

  (** ** respects identity *)
  Section identity_of.
    Variables C D : PreCategory.

    Lemma identity_of_helper_helper (x : Functor C D)
    : 1 o x o 1 = x.
    Proof.
      path_functor.
    Defined.

    Definition identity_of_helper_helper_object_of x
    : ap object_of (identity_of_helper_helper x) = idpath
      := path_functor_uncurried_fst _ _ _.

    Lemma identity_of_helper
    : (fun x : Functor C D => 1 o x o 1) = idmap.
    Proof.
      apply path_forall; intro x.
      apply identity_of_helper_helper.
    Defined.

    Lemma identity_of
    : pointwise (identity C) (identity D) = identity _.
    Proof.
      path_functor.
      exists identity_of_helper.
      unfold identity_of_helper.
      abstract functor_pointwise_t
               identity_of_helper_helper
               identity_of_helper_helper_object_of.
    Defined.
  End identity_of.

  (** ** respects composition *)
  Section composition_of.
    Variables C D C' D' C'' D'' : PreCategory.

    Variable F' : Functor C' C''.
    Variable G : Functor D D'.
    Variable F : Functor C C'.
    Variable G' : Functor D' D''.

    Lemma composition_of_helper_helper (x : Functor C'' D)
    : G' o G o x o (F' o F) = G' o (G o x o F') o F.
    Proof.
      path_functor.
    Defined.

    Definition composition_of_helper_helper_object_of x
    : ap object_of (composition_of_helper_helper x) = idpath
      := path_functor_uncurried_fst _ _ _.

    Lemma composition_of_helper
    : (fun x => G' o G o x o (F' o F)) = (fun x => G' o (G o x o F') o F).
    Proof.
      apply path_forall; intro x.
      apply composition_of_helper_helper.
    Defined.

    Lemma composition_of
    : pointwise (F' o F) (G' o G) = pointwise F G' o pointwise F' G.
    Proof.
      path_functor.
      exists composition_of_helper.
      unfold composition_of_helper.
      abstract functor_pointwise_t
               composition_of_helper_helper
               composition_of_helper_helper_object_of.
    Defined.
  End composition_of.
End parts.
