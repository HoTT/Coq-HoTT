Require Import Category.Core Functor.Core Functor.Pointwise NaturalTransformation.Core NaturalTransformation.Paths Functor.Composition.Core Functor.Identity Functor.Paths.
Require Import PathGroupoids types.Forall HoTT.Tactics.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope category_scope.
Local Open Scope functor_scope.

Section parts.
  Context `{Funext}.

  Let transport_idmap_ap A (P : A -> Type) x y (p : x = y) (u : P x)
  : transport idmap (ap P p) u = transport P p u
  := inverse (transport_compose idmap _ _ _).

  (** We could do this all in a big [repeat match], but we split it
      up, to shave off about two seconds per proof. *)
  Local Ltac functor_pointwise_t helper_lem_match helper_lem :=
    repeat (apply path_forall; intro);
    rewrite !transport_forall_constant, !path_forall_2_beta;
    path_natural_transformation;
    repeat match goal with
             | [ |- appcontext[components_of (transport ?P ?p ?z)] ]
               => rewrite (@ap_transport _ P _ _ _ p (fun _ => components_of) z)
           end;
    rewrite !transport_forall_constant;
    repeat match goal with
             | [ |- appcontext[transport ?P ?p ?u] ]
               => progress (rewrite <- (transport_idmap_ap P p u); simpl)
           end;
    repeat match goal with
             | [ x : _ |- appcontext[ap (fun x3 : ?T => ?f (object_of x3 ?z))] ]
               => rewrite (@ap_compose' _ _ _ (fun x3 : T => object_of x3) (fun Ox3 => f (Ox3 x)))
             | [ x : _ |- appcontext[ap (fun x3 : ?T => ?f (object_of x3 ?z) ?w)] ]
               => rewrite (@ap_compose' _ _ _ (fun x3 : T => object_of x3) (fun Ox3 => f (Ox3 x) w))
           end;
    repeat match goal with
             | _ => done
             | [ |- appcontext[fun F => @object_of ?C ?D F] ]
               => progress change (fun F => @object_of C D F) with (@object_of C D)
             | [ |- appcontext[helper_lem_match ?x] ]
               => rewrite (helper_lem x)
           end.

  Section identity_of.
    Variable C : PreCategory.
    Variable D : PreCategory.

    Local Transparent compose_identity_of compose_composition_of.

    Lemma identity_of_helper_helper (x : Functor C D)
    : 1 o x o 1 = x.
    Proof.
      path_functor.
    Defined.

    Definition identity_of_helper_helper_object_of x
    : ap object_of (identity_of_helper_helper x) = idpath
      := path_functor'_sig_fst _ _ _.

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

  Section composition_of.
    Variable C : PreCategory.
    Variable D : PreCategory.
    Variable C' : PreCategory.
    Variable D' : PreCategory.
    Variable C'' : PreCategory.
    Variable D'' : PreCategory.

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
      := path_functor'_sig_fst _ _ _.

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
