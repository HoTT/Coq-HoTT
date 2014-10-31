(* -*- mode: coq; mode: visual-line -*- *)

(** * Extensions and extendible maps *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp EquivalenceVarieties.
Require Import HoTT.Tactics.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** Given [C : B -> Type] and [f : A -> B], an extension of [g : forall a, C (f a)] along [f] is a section [h : forall b, C b] such that [h (f a) = g a] for all [a:A].  This is equivalently the existence of fillers for commutative squares, restricted to the case where the bottom of the square is the identity; type-theoretically, this approach is sometimes more convenient.  In this file we study the type of such extensions.  One of its crucial properties is that a path between extensions is equivalently an extension in a fibration of paths.

This turns out to be useful for several reasons.  For instance, by iterating it, we can to formulate universal properties without needing [Funext].  It also gives us a way to "quantify" a universal property by the connectedness of the type of extensions. *)

Section AssumeFunext.
  Context `{Funext}.

  (* TODO: consider naming for [ExtensionAlong] and subsequent lemmas.  As a name for the type itself, [Extension] or [ExtensionAlong] seems great; but resultant lemma names such as [path_extension] (following existing naming conventions) are rather misleading. *)

  (** This elimination rule (and others) can be seen as saying that, given a fibration over the codomain and a section of it over the domain, there is some *extension* of this to a section over the whole domain.  It can also be considered as an equivalent form of an [hfiber] of precomposition-with-[f] that replaces paths by pointwise paths, thereby avoiding [Funext]. *)
  Definition ExtensionAlong {A B : Type} (f : A -> B)
             (P : B -> Type) (d : forall x:A, P (f x))
    := { s : forall y:B, P y & forall x:A, s (f x) = d x }.

  Definition path_extension {A B : Type} {f : A -> B}
             {P : B -> Type} {d : forall x:A, P (f x)}
             (ext ext' : ExtensionAlong f P d)
  : (ExtensionAlong f
                    (fun y => pr1 ext y = pr1 ext' y)
                    (fun x => pr2 ext x @ (pr2 ext' x)^))
    -> ext = ext'.
  Proof.
    (* Note: written with liberal use of [compose], to facilitate later proving that it’s an equivalance. *)
    apply (compose (path_sigma_uncurried _ _ _)).
    apply (functor_sigma (path_forall (ext .1) (ext' .1))). intros p.
    apply (compose (path_forall _ _)). unfold pointwise_paths.
    apply (functor_forall idmap). intros x.
    apply (compose (B := (p (f x))^ @ (ext .2 x) = (ext' .2 x))).
    apply concat.
    transitivity ((apD10 (path_forall _ _ p) (f x))^ @ ext .2 x).
    assert (transp_extension : forall p : ext .1 = ext' .1,
                                 (transport (fun (s : forall y : B, P y) => forall x : A, s (f x) = d x)
                                            p (ext .2) x
                                  = ((apD10 p (f x))^ @ ext .2 x))).
    destruct ext as [g gd], ext' as [g' gd']; simpl.
    intros q; destruct q; simpl.
    apply inverse, concat_1p.
    apply transp_extension.
    apply whiskerR, ap, apD10_path_forall.
    apply (compose (moveR_Vp _ _ _)).
    apply (compose (moveL_pM _ _ _)).
    exact inverse.
  Defined.

  Global Instance isequiv_path_extension {A B : Type} {f : A -> B}
         {P : B -> Type} {d : forall x:A, P (f x)}
         (ext ext' : ExtensionAlong f P d)
  : IsEquiv (path_extension ext ext') | 0.
  Proof.
    apply @isequiv_compose.
    2: apply @isequiv_path_sigma.
    apply @isequiv_functor_sigma.
    apply @isequiv_path_forall.
    intros a. apply @isequiv_compose.
    2: apply @isequiv_path_forall.
    apply (@isequiv_functor_forall _).
    apply isequiv_idmap.
    intros x. apply @isequiv_compose.
    apply @isequiv_compose.
    apply @isequiv_compose.
    apply isequiv_path_inverse.
    apply isequiv_moveL_pM.
    apply isequiv_moveR_Vp.
    apply isequiv_concat_l.
  Qed.
  (** Note: opaque, since this term is big enough that using its computational content will probably be pretty intractable. *)

  (** Here is the iterated version. *)

  Fixpoint ExtendableAlong
           (n : nat) {A B : Type} (f : A -> B) (C : B -> Type) : Type
    := match n with
         | 0 => Unit
         | S n => (forall (g : forall a, C (f a)), ExtensionAlong f C g) *
                  forall (h k : forall b, C b),
                    ExtendableAlong n f (fun b => h b = k b)
       end.

  Definition equiv_extendable_pathsplit (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ExtendableAlong n f C
                    <~> PathSplit n (fun (g : forall b, C b) => g oD f).
  Proof.
    generalize dependent C; induction n as [ | n IHn]; intros C.
    1:apply equiv_idmap.
    apply equiv_functor_prod'; simpl.
    - refine (equiv_functor_forall' (equiv_idmap _) _); intros g; simpl.
      refine (equiv_functor_sigma' (equiv_idmap _) _); intros rec.
      apply equiv_path_forall.
    - refine (equiv_functor_forall' (equiv_idmap _) _); intros h.
      refine (equiv_functor_forall' (equiv_idmap _) _); intros k; simpl.
      refine (equiv_compose' _ (IHn (fun b => h b = k b))).
      symmetry; refine (equiv_functor_pathsplit n _ _
                                                (equiv_apD10 _ _ _) (equiv_apD10 _ _ _) _).
      intros []; reflexivity.
  Defined.

  Definition isequiv_extendable (n : nat)
             {A B : Type} {C : B -> Type} {f : A -> B}
  : ExtendableAlong n.+2 f C
    -> IsEquiv (fun g => g oD f)
    := isequiv_pathsplit n o (equiv_extendable_pathsplit n.+2 C f).

  Global Instance ishprop_extendable (n : nat)
         {A B : Type} (C : B -> Type) (f : A -> B)
  : IsHProp (ExtendableAlong n.+2 f C).
  Proof.
    (* TODO: Why is this so slow? *)
    refine (trunc_equiv _ (equiv_extendable_pathsplit n.+2 C f)^-1).
  Defined.

  Definition equiv_extendable_isequiv (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ExtendableAlong n.+2 f C
                    <~> IsEquiv (fun (g : forall b, C b) => g oD f).
  Proof.
    etransitivity.
    - apply equiv_extendable_pathsplit.
    - apply equiv_pathsplit_isequiv.
  Defined.

  (** Postcomposition with a known equivalence. *)
  Definition extendable_postcompose' (n : nat)
             {A B : Type} (C D : B -> Type) (f : A -> B)
             (g : forall b, C b <~> D b)
  : ExtendableAlong n f C -> ExtendableAlong n f D.
  Proof.
    generalize dependent D; revert C.
    induction n as [|n IHn]; intros C D g; simpl.
    1:apply idmap.
    refine (functor_prod _ _).
    - refine (functor_forall (functor_forall idmap
                                             (fun a => (g (f a))^-1)) _);
      intros h; simpl.
      refine (functor_sigma (functor_forall idmap g) _); intros k.
      refine (functor_forall idmap _);
        intros a; unfold functor_arrow, functor_forall, composeD; simpl.
      apply moveR_equiv_M.
    - refine (functor_forall (functor_forall idmap (fun b => (g b)^-1)) _);
      intros h.
      refine (functor_forall (functor_forall idmap (fun b => (g b)^-1)) _);
        intros k; simpl; unfold functor_forall.
      refine (IHn _ _ _); intros b.
      apply equiv_inverse, equiv_ap; exact _.
  Defined.

  Definition extendable_postcompose (n : nat)
             {A B : Type} (C D : B -> Type) (f : A -> B)
             (g : forall b, C b -> D b) `{forall b, IsEquiv (g b)}
  : ExtendableAlong n f C -> ExtendableAlong n f D
    := extendable_postcompose' n C D f (fun b => BuildEquiv _ _ (g b) _).

  (** And the oo-version. *)

  Definition ooExtendableAlong
             {A B : Type} (f : A -> B) (C : B -> Type) : Type
    := forall n, ExtendableAlong n f C.

  Definition isequiv_ooextendable
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ooExtendableAlong f C -> IsEquiv (fun g => g oD f)
    := fun ps => isequiv_extendable 0 (ps 2).

  Definition equiv_ooextendable_pathsplit
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ooExtendableAlong f C <~>
                      ooPathSplit (fun (g : forall b, C b) => g oD f).
  Proof.
    refine (equiv_functor_forall' (equiv_idmap _) _); intros n.
    apply equiv_extendable_pathsplit.
  Defined.

  Global Instance ishprop_ooextendable
         {A B : Type} (C : B -> Type) (f : A -> B)
  : IsHProp (ooExtendableAlong f C).
  Proof.
    refine (trunc_equiv _ (equiv_ooextendable_pathsplit C f)^-1).
  Defined.

  Definition equiv_ooextendable_isequiv 
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ooExtendableAlong f C
                      <~> IsEquiv (fun (g : forall b, C b) => g oD f).
  Proof.
    etransitivity.
    - apply equiv_ooextendable_pathsplit.
    - apply equiv_oopathsplit_isequiv.
  Defined.

  Definition ooextendable_postcompose
             {A B : Type} (C D : B -> Type) (f : A -> B)
             (g : forall b, C b -> D b) `{forall b, IsEquiv (g b)}
  : ooExtendableAlong f C -> ooExtendableAlong f D
    := fun ppp n => extendable_postcompose n C D f g (ppp n).

End AssumeFunext.
