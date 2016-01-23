(* -*- mode: coq; mode: visual-line -*- *)

(** * Extensions and extendible maps *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp EquivalenceVarieties.
Require Import HoTT.Tactics.

Local Open Scope path_scope.

(** Given [C : B -> Type] and [f : A -> B], an extension of [g : forall a, C (f a)] along [f] is a section [h : forall b, C b] such that [h (f a) = g a] for all [a:A].  This is equivalently the existence of fillers for commutative squares, restricted to the case where the bottom of the square is the identity; type-theoretically, this approach is sometimes more convenient.  In this file we study the type of such extensions.  One of its crucial properties is that a path between extensions is equivalently an extension in a fibration of paths.

This turns out to be useful for several reasons.  For instance, by iterating it, we can to formulate universal properties without needing [Funext].  It also gives us a way to "quantify" a universal property by the connectedness of the type of extensions. *)

Section Extensions.

  (* TODO: consider naming for [ExtensionAlong] and subsequent lemmas.  As a name for the type itself, [Extension] or [ExtensionAlong] seems great; but resultant lemma names such as [path_extension] (following existing naming conventions) are rather misleading. *)

  (** This elimination rule (and others) can be seen as saying that, given a fibration over the codomain and a section of it over the domain, there is some *extension* of this to a section over the whole domain.  It can also be considered as an equivalent form of an [hfiber] of precomposition-with-[f] that replaces paths by pointwise paths, thereby avoiding [Funext]. *)

  Definition ExtensionAlong {A B : Type} (f : A -> B)
             (P : B -> Type) (d : forall x:A, P (f x))
    := { s : forall y:B, P y & forall x:A, s (f x) = d x }.
  (** [ExtensionAlong] takes 5 universe parameters:
      - the size of A
      - the size of B
      - the size of P
      - >= max(B,P)
      - >= max(A,P).
    The following [Check] verifies that this is in fact the case. *)
  (** We would like to say [Check], but because of bug #4517, https://coq.inria.fr/bugs/show_bug.cgi?id=4517, we can't. *)
  Definition check_ExtensionAlong@{a b p m n} : True.
  Proof.
    Check ExtensionAlong@{a b p m n}.
  Abort.
  (** If necessary, we could coalesce the latter two with a universe annotation, but that would make the definition harder to read. *)

  (** It's occasionally useful to be able to modify those max universes. *)
  Definition lift_extensionalong@{a b p m1 n1 m2 n2} {A : Type@{a}} {B : Type@{b}} (f : A -> B)
             (P : B -> Type@{p}) (d : forall x:A, P (f x))
  : ExtensionAlong@{a b p m1 n1} f P d -> ExtensionAlong@{a b p m2 n2} f P d
    := fun ext => (ext.1 ; ext.2).
  (** We called it [lift_extensionalong], but in fact it doesn't require the new universes to be bigger than the old ones, only that they both satisfy the max condition. *)
  Definition lower_extensionalong@{a b p e0 e1} {A : Type@{a}} {B : Type@{b}} (f : A -> B)
             (P : B -> Type@{p}) (d : forall x:A, P (f x))
    := lift_extensionalong@{a b p e0 e1 e0 e1} f P d.

  Definition equiv_path_extension `{Funext} {A B : Type} {f : A -> B}
             {P : B -> Type} {d : forall x:A, P (f x)}
             (ext ext' : ExtensionAlong f P d)
  : (ExtensionAlong f
                    (fun y => pr1 ext y = pr1 ext' y)
                    (fun x => pr2 ext x @ (pr2 ext' x)^))
    <~> ext = ext'.
  Proof.
    refine (equiv_path_sigma _ _ _ oE _).
    refine (equiv_functor_sigma' (equiv_path_forall (ext .1) (ext' .1)) _). intros p.
    refine (equiv_path_forall _ _ oE _). unfold pointwise_paths.
    refine (equiv_functor_forall' 1 _). intros x.
    refine (equiv_compose' (B := (p (f x))^ @ (ext .2 x) = (ext' .2 x)) _ _).
    - refine (equiv_concat_l _ _).
      transitivity ((apD10 (path_forall _ _ p) (f x))^ @ ext .2 x).
      + assert (transp_extension : forall p : ext .1 = ext' .1,
                                     (transport (fun (s : forall y : B, P y) => forall x : A, s (f x) = d x)
                                                p (ext .2) x
                                      = ((apD10 p (f x))^ @ ext .2 x))).
        * destruct ext as [g gd], ext' as [g' gd']; simpl.
          intros q; destruct q; simpl.
          apply inverse, concat_1p.
        * apply transp_extension.
      + apply whiskerR, ap, apD10_path_forall.
    - refine (equiv_moveR_Vp _ _ _ oE _).
      refine (equiv_moveL_pM _ _ _ oE _).
      apply equiv_path_inverse.
  Defined.

  Definition path_extension `{Funext} {A B : Type} {f : A -> B}
             {P : B -> Type} {d : forall x:A, P (f x)}
             (ext ext' : ExtensionAlong f P d)
  : (ExtensionAlong f
                    (fun y => pr1 ext y = pr1 ext' y)
                    (fun x => pr2 ext x @ (pr2 ext' x)^))
    -> ext = ext'
  := equiv_path_extension ext ext'.

  Global Instance isequiv_path_extension `{Funext} {A B : Type} {f : A -> B}
         {P : B -> Type} {d : forall x:A, P (f x)}
         (ext ext' : ExtensionAlong f P d)
  : IsEquiv (path_extension ext ext') | 0.
  Proof.
    exact _.
  Defined.

  (** Here is the iterated version. *)

  Fixpoint ExtendableAlong@{i j k l}
           (n : nat) {A : Type@{i}} {B : Type@{j}}
           (f : A -> B) (C : B -> Type@{k}) : Type@{l}
    := match n with
         | 0 => Unit@{l}
         | S n => (forall (g : forall a, C (f a)),
                     ExtensionAlong@{i j k l l} f C g) *
                  forall (h k : forall b, C b),
                    ExtendableAlong n f (fun b => h b = k b)
       end.
  (** [ExtendableAlong] takes 4 universe parameters:
      - size of A
      - size of B
      - size of C
      - size of result (>= A,B,C) *)
  (** We would like to say [Check], but because of bug #4517, https://coq.inria.fr/bugs/show_bug.cgi?id=4517, we can't. *)
  Definition check_ExtendableAlong@{a b c r} : True.
  Proof.
    Check ExtendableAlong@{a b c r}.
  Abort.

  Global Arguments ExtendableAlong n%nat_scope {A B}%type_scope (f C)%function_scope.

  (** We can modify the universes, as with [ExtensionAlong]. *)
  Definition lift_extendablealong@{i j k l1 l2}
             (n : nat) {A : Type@{i}} {B : Type@{j}}
             (f : A -> B) (C : B -> Type@{k})
  : ExtendableAlong@{i j k l1} n f C -> ExtendableAlong@{i j k l2} n f C.
  Proof.
    revert C; simple_induction n n IH; intros C.
    - intros _; exact tt.
    - intros ext; split.
      + intros g; exact (lift_extensionalong _ _ _ (fst ext g)).
      + intros h k; exact (IH _ (snd ext h k)).
  Defined.
  (** We would like to say [Check], but because of bug #4517, https://coq.inria.fr/bugs/show_bug.cgi?id=4517, we can't. *)
  Definition check_lift_extendablealong@{i j k l1 l2} : True.
  Proof.
    Check lift_extendablealong@{i j k l1 l2}.
  Abort.

  Definition lower_extendablealong@{i j k e}
             (n : nat) {A : Type@{i}} {B : Type@{j}}
             (f : A -> B) (C : B -> Type@{k})
    := lift_extendablealong@{i j k e e} n f C.

  Definition equiv_extendable_pathsplit `{Funext} (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ExtendableAlong n f C
    <~> PathSplit n (fun (g : forall b, C b) => g oD f).
  Proof.
    generalize dependent C; simple_induction n n IHn; intros C.
    1:apply equiv_idmap.
    refine (_ *E _); simpl.
    - refine (equiv_functor_forall' 1 _); intros g; simpl.
      refine (equiv_functor_sigma' 1 _); intros rec.
      apply equiv_path_forall.
    - refine (equiv_functor_forall' 1 _); intros h.
      refine (equiv_functor_forall' 1 _); intros k; simpl.
      refine (_ oE IHn (fun b => h b = k b)).
      apply equiv_inverse.
      refine (equiv_functor_pathsplit n _ _
               (equiv_apD10 _ _ _) (equiv_apD10 _ _ _) _).
      intros []; reflexivity.
  Defined.

  Definition isequiv_extendable `{Funext} (n : nat)
             {A B : Type} {C : B -> Type} {f : A -> B}
  : ExtendableAlong n.+2 f C
    -> IsEquiv (fun g => g oD f)
    := isequiv_pathsplit n o (equiv_extendable_pathsplit n.+2 C f).

  Global Instance ishprop_extendable `{Funext} (n : nat)
         {A B : Type} (C : B -> Type) (f : A -> B)
  : IsHProp (ExtendableAlong n.+2 f C).
  Proof.
    refine (trunc_equiv' _ (equiv_extendable_pathsplit n.+2 C f)^-1).
  Defined.

  Definition equiv_extendable_isequiv `{Funext} (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ExtendableAlong n.+2 f C
    <~> IsEquiv (fun (g : forall b, C b) => g oD f).
  Proof.
    etransitivity.
    - apply equiv_extendable_pathsplit.
    - apply equiv_pathsplit_isequiv.
  Defined.

  (** Postcomposition with a known equivalence.  Note that this does not require funext to define, although showing that it is an equivalence would require funext. *)
  Definition extendable_postcompose' (n : nat)
             {A B : Type} (C D : B -> Type) (f : A -> B)
             (g : forall b, C b <~> D b)
  : ExtendableAlong n f C -> ExtendableAlong n f D.
  Proof.
    generalize dependent C; revert D.
    simple_induction n n IH; intros C D g; simpl.
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
      refine (IH _ _ _); intros b.
      apply equiv_inverse, equiv_ap; exact _.
  Defined.

  Definition extendable_postcompose (n : nat)
             {A B : Type} (C D : B -> Type) (f : A -> B)
             (g : forall b, C b -> D b) `{forall b, IsEquiv (g b)}
  : ExtendableAlong n f C -> ExtendableAlong n f D
    := extendable_postcompose' n C D f (fun b => BuildEquiv _ _ (g b) _).

  (** Composition of the maps we extend along.  This also does not require funext. *)
  Definition extendable_compose (n : nat)
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ExtendableAlong n g P -> ExtendableAlong n f (fun b => P (g b)) -> ExtendableAlong n (g o f) P.
  Proof.
    revert P; simple_induction n n IHn; intros P extg extf; [ exact tt | split ].
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
  : ExtendableAlong n g P -> ExtendableAlong n (g o f) P -> ExtendableAlong n f (fun b => P (g b)).
  Proof.
    revert P; simple_induction n n IHn; intros P extg extgf; [ exact tt | split ].
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
  : ExtendableAlong n.+1 f (fun b => P (g b)) -> ExtendableAlong n (g o f) P -> ExtendableAlong n g P.
  Proof.
    revert P; simple_induction n n IHn; intros P extf extgf; [ exact tt | split ].
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
    revert C; simple_induction n n IHn; intros C extf; [ exact tt | split ].
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
    revert C; simple_induction n n IHn; intros C; [ exact tt | split ].
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
    generalize dependent C; simple_induction n n IHn;
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
    revert C h k; simple_induction n n IHn;
      intros C h k ext; [exact tt | split].
    - intros p.
      exact (fst (snd ext h k) p).
    - intros p q.
      apply IHn, ext.
  Defined.

  (** And the oo-version. *)

  Definition ooExtendableAlong@{i j k l}
             {A : Type@{i}} {B : Type@{j}}
             (f : A -> B) (C : B -> Type@{k}) : Type@{l}
    := forall n, ExtendableAlong@{i j k l} n f C.
  (** Universe parameters are the same as for [ExtendableAlong]. *)
  (** We would like to say [Check], but because of bug #4517, https://coq.inria.fr/bugs/show_bug.cgi?id=4517, we can't. *)
  Definition check_ooExtendableAlong@{a b c r} : True.
  Proof.
    Check ooExtendableAlong@{a b c r}.
  Abort.

  Global Arguments ooExtendableAlong {A B}%type_scope (f C)%function_scope.

  (** Universe modification. *)
  Definition lift_ooextendablealong@{i j k l1 l2}
             {A : Type@{i}} {B : Type@{j}}
             (f : A -> B) (C : B -> Type@{k})
  : ooExtendableAlong@{i j k l1} f C -> ooExtendableAlong@{i j k l2} f C
    := fun ext n => lift_extendablealong n f C (ext n).
  (** We would like to say [Check], but because of bug #4517, https://coq.inria.fr/bugs/show_bug.cgi?id=4517, we can't. *)
  Definition check_ooextendablealong@{i j k l1 l2} : True.
  Proof.
    Check lift_ooextendablealong@{i j k l1 l2}.
  Abort.
  Definition lower_ooextendablealong@{i j k e1 e2}
             {A : Type@{i}} {B : Type@{j}}
             (f : A -> B) (C : B -> Type@{k})
    := lift_ooextendablealong@{i j k e1 e2} f C.

  Definition isequiv_ooextendable `{Funext}
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ooExtendableAlong f C -> IsEquiv (fun g => g oD f)
    := fun ps => isequiv_extendable 0 (ps 2).

  Definition equiv_ooextendable_pathsplit `{Funext}
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ooExtendableAlong f C <~>
    ooPathSplit (fun (g : forall b, C b) => g oD f).
  Proof.
    refine (equiv_functor_forall' 1 _); intros n.
    apply equiv_extendable_pathsplit.
  Defined.

  Global Instance ishprop_ooextendable `{Funext}
         {A B : Type} (C : B -> Type) (f : A -> B)
  : IsHProp (ooExtendableAlong f C).
  Proof.
    refine (trunc_equiv _ (equiv_ooextendable_pathsplit C f)^-1).
  Defined.

  Definition equiv_ooextendable_isequiv `{Funext}
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ooExtendableAlong f C
    <~> IsEquiv (fun (g : forall b, C b) => g oD f)
    := equiv_oopathsplit_isequiv _ oE equiv_ooextendable_pathsplit _ _.

  Definition ooextendable_postcompose
             {A B : Type} (C D : B -> Type) (f : A -> B)
             (g : forall b, C b -> D b) `{forall b, IsEquiv (g b)}
  : ooExtendableAlong f C -> ooExtendableAlong f D
    := fun ppp n => extendable_postcompose n C D f g (ppp n).

  Definition ooextendable_compose
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ooExtendableAlong g P -> ooExtendableAlong f (fun b => P (g b)) -> ooExtendableAlong (g o f) P
    := fun extg extf n => extendable_compose n P f g (extg n) (extf n).

  Definition cancelL_ooextendable
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ooExtendableAlong g P -> ooExtendableAlong (g o f) P -> ooExtendableAlong f (fun b => P (g b))
  := fun extg extgf n => cancelL_extendable n P f g (extg n) (extgf n).

  Definition cancelR_ooextendable
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ooExtendableAlong f (fun b => P (g b)) -> ooExtendableAlong (g o f) P -> ooExtendableAlong g P
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

End Extensions.
