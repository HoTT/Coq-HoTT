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

  (** Composition of the maps we extend along *)
  Definition extendable_compose (n : nat)
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ExtendableAlong n g P -> ExtendableAlong n f (P o g) -> ExtendableAlong n (g o f) P.
  Proof.
    revert P; induction n as [|n IHn]; intros P extg extf; [ exact tt | split ].
    - intros h.
      exists ((fst extg (fst extf h).1).1); intros a.
      refine ((fst extg (fst extf h).1).2 (f a) @ _).
      exact ((fst extf h).2 a).
    - intros h k.
      apply IHn.
      + exact (snd extg h k).
      + exact (snd extf (h oD g) (k oD g)).
  Defined.

  (** And cancellation *)
  Definition cancelL_extendable (n : nat)
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ExtendableAlong n g P -> ExtendableAlong n (g o f) P -> ExtendableAlong n f (P o g).
  Proof.
    revert P; induction n as [|n IHn]; intros P extg extgf; [ exact tt | split ].
    - intros h.
      exists ((fst extgf h).1 oD g); intros a.
      exact ((fst extgf h).2 a).
    - intros h k.
      pose (h' := (fst extg h).1).
      pose (k' := (fst extg k).1).
      refine (extendable_postcompose' n (fun b => h' (g b) = k' (g b)) (fun b => h b = k b) f _ _).
      + intros b.
        exact (equiv_concat_lr ((fst extg h).2 b)^ ((fst extg k).2 b)).
      + apply (IHn (fun c => h' c = k' c) (snd extg h' k') (snd extgf h' k')).
  Defined.

  Definition cancelR_extendable (n : nat)
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ExtendableAlong n.+1 f (P o g) -> ExtendableAlong n (g o f) P -> ExtendableAlong n g P.
  Proof.
    revert P; induction n as [|n IHn]; intros P extf extgf; [ exact tt | split ].
    - intros h.
      exists ((fst extgf (h oD f)).1); intros b.
      refine ((fst (snd extf ((fst extgf (h oD f)).1 oD g) h) _).1 b); intros a.
      apply ((fst extgf (h oD f)).2).
    - intros h k.
      apply IHn.
      + apply (snd extf (h oD g) (k oD g)).
      + apply (snd extgf h k).
  Defined.

  (** And transfer across homotopies *)
  Definition extendable_homotopic (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B) {g : A -> B} (p : f == g)
  : ExtendableAlong n f C -> ExtendableAlong n g C.
  Proof.
    revert C; induction n as [|n IHn]; intros C extf; [ exact tt | split ].
    - intros h.
      exists ((fst extf (fun a => (p a)^ # h a)).1); intros a.
      refine ((apD ((fst extf (fun a => (p a)^ # h a)).1) (p a))^ @ _).
      apply moveR_transport_p.
      exact ((fst extf (fun a => (p a)^ # h a)).2 a).
    - intros h k.
      apply IHn, (snd extf h k).
  Defined.

  (** We can extend along equivalences *)
  Definition extendable_equiv (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B) `{IsEquiv _ _ f}
  : ExtendableAlong n f C.
  Proof.
    revert C; induction n as [|n IHn]; intros C; [ exact tt | split ].
    - intros h.
      exists (fun b => eisretr f b # h (f^-1 b)); intros a.
      refine (transport2 C (eisadj f a) _ @ _).
      refine ((transport_compose C f _ _)^ @ _).
      exact (apD h (eissect f a)).
    - intros h k.
      apply IHn.
  Defined.

  (** And into contractible types *)
  Definition extendable_contr (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
             `{forall b, Contr (C b)}
  : ExtendableAlong n f C.
  Proof.
    generalize dependent C; induction n as [|n IHn];
      intros C ?; [ exact tt | split ].
    - intros h.
      exists (fun _ => center _); intros a.
      apply contr.
    - intros h k.
      apply IHn; exact _.
  Defined.

  (** This is inherited by types of homotopies. *)
  Definition extendable_homotopy (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
             (h k : forall b, C b)
  : ExtendableAlong n.+1 f C -> ExtendableAlong n f (fun b => h b = k b).
  Proof.
    revert C h k; induction n as [|n IHn];
      intros C h k ext; [exact tt | split].
    - intros p.
      exact (fst (snd ext h k) p).
    - intros p q.
      apply IHn, ext.
  Defined.

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

  Definition ooextendable_compose
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ooExtendableAlong g P -> ooExtendableAlong f (P o g) -> ooExtendableAlong (g o f) P
    := fun extg extf n => extendable_compose n P f g (extg n) (extf n).

  Definition cancelL_ooextendable
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ooExtendableAlong g P -> ooExtendableAlong (g o f) P -> ooExtendableAlong f (P o g)
  := fun extg extgf n => cancelL_extendable n P f g (extg n) (extgf n).

  Definition cancelR_ooextendable
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ooExtendableAlong f (P o g) -> ooExtendableAlong (g o f) P -> ooExtendableAlong g P
    := fun extf extgf n => cancelR_extendable n P f g (extf n.+1) (extgf n).

  Definition ooextendable_homotopic
             {A B : Type} (C : B -> Type) (f : A -> B) {g : A -> B} (p : f == g)
  : ooExtendableAlong f C -> ooExtendableAlong g C
    := fun extf n => extendable_homotopic n C f p (extf n).

  Definition ooextendable_equiv
             {A B : Type} (C : B -> Type) (f : A -> B) `{IsEquiv _ _ f}
  : ooExtendableAlong f C
  := fun n => extendable_equiv n C f.

  Definition ooextendable_contr
             {A B : Type} (C : B -> Type) (f : A -> B)
             `{forall b, Contr (C b)}
  : ooExtendableAlong f C
  := fun n => extendable_contr n C f.

  Definition ooextendable_homotopy
             {A B : Type} (C : B -> Type) (f : A -> B)
             (h k : forall b, C b)
  : ooExtendableAlong f C -> ooExtendableAlong f (fun b => h b = k b).
  Proof.
    intros ext n; apply extendable_homotopy, ext.
  Defined.

  (** Extendability of a family [C] along a map [f] can be detected by extendability of the constant family [C b] along the projection from the corresponding fiber of [f] to [Unit].  Note that this is *not* an if-and-only-if; the hypothesis can be genuinely stronger than the conclusion. *)
  Definition ooextendable_isnull_fibers {A B} (f : A -> B) (C : B -> Type)
  : (forall b, ooExtendableAlong (@const (hfiber f b) Unit tt)
                                 (fun _ => C b))
    -> ooExtendableAlong f C.
  Proof.
    intros orth n; revert C orth.
    induction n as [|n IHn]; intros C orth; [exact tt | split].
    - intros g.
      exists (fun b => (fst (orth b 1%nat) (fun x => x.2 # g x.1)).1 tt).
      intros a.
      rewrite (path_unit tt (const tt a)).
      exact ((fst (orth (f a) 1%nat) _).2 (a ; 1)).
    - intros h k.
      apply IHn; intros b.
      apply ooextendable_homotopy, orth.
  Defined.

End AssumeFunext.
