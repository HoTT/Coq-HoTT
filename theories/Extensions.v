(** * Extensions and extendible maps *)

Require Import HoTT.Basics HoTT.Types.
Require Import Equiv.PathSplit Homotopy.IdentitySystems.
Require Import Cubical.DPath Cubical.DPathSquare.
Require Import Colimits.Coeq Colimits.MappingCylinder.

Local Open Scope nat_scope.
Local Open Scope path_scope.

(** Given [C : B -> Type] and [f : A -> B], an extension of [g : forall a, C (f a)] along [f] is a section [h : forall b, C b] such that [h (f a) = g a] for all [a:A].  This is equivalently the existence of fillers for commutative squares, restricted to the case where the bottom of the square is the identity; type-theoretically, this approach is sometimes more convenient.  In this file we study the type of such extensions.  One of its crucial properties is that a path between extensions is equivalently an extension in a fibration of paths.

This turns out to be useful for several reasons.  For instance, by iterating it, we can to formulate universal properties without needing [Funext].  It also gives us a way to "quantify" a universal property by the connectedness of the type of extensions. *)

Section Extensions.

  (* TODO: consider naming for [ExtensionAlong] and subsequent lemmas.  As a name for the type itself, [Extension] or [ExtensionAlong] seems great; but resultant lemma names such as [path_extension] (following existing naming conventions) are rather misleading. *)

  (** This elimination rule (and others) can be seen as saying that, given a fibration over the codomain and a section of it over the domain, there is some *extension* of this to a section over the whole codomain.  It can also be considered as an equivalent form of an [hfiber] of precomposition-with-[f] that replaces paths by pointwise paths, thereby avoiding [Funext]. *)
  Definition ExtensionAlong@{a b p m} {A : Type@{a}} {B : Type@{b}} (f : A -> B)
             (P : B -> Type@{p}) (d : forall x:A, P (f x))
    := (* { s : forall y:B, P y & forall x:A, s (f x) = d x }. *)
       sig@{m m} (fun (s : forall y:B, P y) => forall x:A, s (f x) = d x).
   (** [ExtensionAlong] takes 4 universe parameters:
      - the size of A
      - the size of B
      - the size of P
      - >= max(A,B,P)
   *)

  (** It's occasionally useful to be able to modify those universes.  For each of the universes [a], [b], [p], we give an initial one, a final one, and a "minimum" one smaller than both and where the type actually lives. *)
  Definition lift_extensionalong@{a1 a2 amin b1 b2 bmin p1 p2 pmin m1 m2} {A : Type@{amin}} {B : Type@{bmin}} (f : A -> B)
             (P : B -> Type@{pmin}) (d : forall x:A, P (f x))
    : ExtensionAlong@{a1 b1 p1 m1} f P d -> ExtensionAlong@{a2 b2 p2 m2} f P d.
  Proof.
    intros ext.
    (** If we just give [ext], it will collapse the universes.  (Anyone stepping through this proof should do [Set Printing Universes] and look at the universes to see that they're different in [ext] and in the goal.)  So we decompose [ext] into two components and give them separately. *)
    assert (e2 := ext.2); set (e1 := ext.1) in e2.
    cbn in e2. (** Curiously, without this line we get a spurious universe inequality [p1 <= m2]. *)
    exact (e1;e2).
  Defined.
  (** We called it [lift_extensionalong], but in fact it doesn't require the new universes to be bigger than the old ones, only that they both satisfy the max condition. *)

  Definition equiv_path_extension `{Funext} {A B : Type} {f : A -> B}
             {P : B -> Type} {d : forall x:A, P (f x)}
             (ext ext' : ExtensionAlong f P d)
  : (ExtensionAlong f
                    (fun y => pr1 ext y = pr1 ext' y)
                    (fun x => pr2 ext x @ (pr2 ext' x)^))
    <~> ext = ext'.
  Proof.
    revert ext'.
    srapply equiv_path_from_contr.
    { unfold ExtensionAlong; cbn.
      exists (fun y => 1%path).
      intros x; symmetry; apply concat_pV. }
    destruct ext as [g gd]; unfold ExtensionAlong; cbn.
    refine (contr_sigma_sigma
              (forall y:B, P y) (fun s => forall x:A, s (f x) = d x)
              (fun a => g == a)
              (fun a b c => forall x:A, c (f x) = gd x @ (b x)^)
              g (fun y:B => idpath (g y))).
    refine (contr_equiv' {p:g o f == d & gd == p} _). cbn.
    refine (equiv_functor_sigma_id _); intros p.
    refine (equiv_functor_forall_id _); intros x; cbn.
    refine (_ oE equiv_path_inverse _ _).
    symmetry; apply equiv_moveR_1M.
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
    : IsEquiv (path_extension ext ext') | 0
    := equiv_isequiv _.

  (** Here is the iterated version. *)

  Fixpoint ExtendableAlong@{i j k l}
           (n : nat) {A : Type@{i}} {B : Type@{j}}
           (f : A -> B) (C : B -> Type@{k}) : Type@{l}
    := match n with
         | 0 => Unit
         | S n => (forall (g : forall a, C (f a)),
                     ExtensionAlong@{i j k l} f C g) *
                  forall (h k : forall b, C b),
                    ExtendableAlong n f (fun b => h b = k b)
       end.
  (** [ExtendableAlong] takes 4 universe parameters:
      - size of A
      - size of B
      - size of C
      - size of result (>= A,B,C) *)

  Global Arguments ExtendableAlong n%_nat_scope {A B}%_type_scope (f C)%_function_scope.

  (** We can modify the universes, as with [ExtensionAlong]. *)
  Definition lift_extendablealong@{a1 a2 amin b1 b2 bmin p1 p2 pmin m1 m2}
             (n : nat) {A : Type@{amin}} {B : Type@{bmin}}
             (f : A -> B) (P : B -> Type@{pmin})
  : ExtendableAlong@{a1 b1 p1 m1} n f P -> ExtendableAlong@{a2 b2 p2 m2} n f P.
  Proof.
    revert P; simple_induction n n IH; intros P.
    - intros _; exact tt.
    - intros ext; split.
      + intros g; exact (lift_extensionalong@{a1 a2 amin b1 b2 bmin p1 p2 pmin m1 m2} _ _ _ (fst ext g)).
      + intros h k. 
        (** Unles we give the universe explicitly here, [kmin] gets collapsed to [k1]. *)
        pose (P' := (fun b => h b = k b) : B -> Type@{pmin}).
        exact (IH P' (snd ext h k)).
  Defined.

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
    exact (istrunc_equiv_istrunc _ (equiv_extendable_pathsplit n.+2 C f)^-1).
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

  (* Without [Funext], we can prove a small part of the above equivalence.
     We suspect that the rest requires [Funext]. *)
  Definition extension_isequiv_precompose
           {A : Type} {B : Type}
           (f : A -> B) (C : B -> Type)
    : IsEquiv (fun (g : forall b, C b) => g oD f) -> forall g, ExtensionAlong f C g.
  Proof.
    intros E g.
    pose (e := Build_Equiv _ _ _ E).
    exists (e^-1 g).
    apply apD10.
    exact (eisretr e g).
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
    := extendable_postcompose' n C D f (fun b => Build_Equiv _ _ (g b) _).

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
    := forall n : nat, ExtendableAlong@{i j k l} n f C.
  (** Universe parameters are the same as for [ExtendableAlong]. *)

  Global Arguments ooExtendableAlong {A B}%_type_scope (f C)%_function_scope.

  (** Universe modification. *)
  Definition lift_ooextendablealong@{a1 a2 amin b1 b2 bmin p1 p2 pmin m1 m2}
             {A : Type@{amin}} {B : Type@{bmin}}
             (f : A -> B) (P : B -> Type@{pmin})
  : ooExtendableAlong@{a1 b1 p1 m1} f P -> ooExtendableAlong@{a2 b2 p2 m2} f P
    := fun ext n => lift_extendablealong@{a1 a2 amin b1 b2 bmin p1 p2 pmin m1 m2} n f P (ext n).

  (** We take part of the data from [ps 1] and part from [ps 2] so that the inverse chosen is the expected one. *)
  Definition isequiv_ooextendable `{Funext}
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ooExtendableAlong f C -> IsEquiv (fun g => g oD f)
    := fun ps => isequiv_extendable 0 (fst (ps 1%nat), snd (ps 2)).

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
    refine (istrunc_equiv_istrunc _ (equiv_ooextendable_pathsplit C f)^-1).
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

  Definition ooextendable_postcompose'
             {A B : Type} (C D : B -> Type) (f : A -> B)
             (g : forall b, C b <~> D b)
  : ooExtendableAlong f C -> ooExtendableAlong f D
    := fun ppp n => extendable_postcompose' n C D f g (ppp n).

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
  : (forall b, ooExtendableAlong (const_tt (hfiber f b))
                                 (fun _ => C b))
    -> ooExtendableAlong f C.
  Proof.
    intros orth n; revert C orth.
    induction n as [|n IHn]; intros C orth; [exact tt | split].
    - intros g.
      exists (fun b => (fst (orth b 1%nat) (fun x => x.2 # g x.1)).1 tt).
      intros a.
      rewrite (path_unit tt (const_tt _ a)).
      exact ((fst (orth (f a) 1%nat) _).2 (a ; 1)).
    - intros h k.
      apply IHn; intros b.
      apply ooextendable_homotopy, orth.
  Defined.

End Extensions.

(** ** Extendability along cofibrations *)

(** If a family is extendable along a cofibration (i.e. a mapping cylinder), it is extendable definitionally. *)
Definition cyl_extension {A B} (f : A -> B) (C : Cyl f -> Type)
           (g : forall a, C (cyl a))
           (ext : ExtensionAlong cyl C g)
  : ExtensionAlong cyl C g.
Proof.
  srefine (Cyl_ind C g (ext.1 o cyr) _ ; _); intros a.
  + refine ((ext.2 a)^ @Dl _)%dpath.
    apply apD.
  + reflexivity. (** The point is that this equality is now definitional. *)
Defined.

Definition cyl_extendable (n : nat)
           {A B} (f : A -> B) (C : Cyl f -> Type)
           (ext : ExtendableAlong n cyl C)
  : ExtendableAlong n cyl C.
Proof.
  revert C ext; simple_induction n n IH; intros C ext; [ exact tt | split ].
  - intros g.
    apply cyl_extension.
    exact (fst ext g).
  - intros h k; apply IH.
    exact (snd ext h k).
Defined.

Definition cyl_ooextendable
           {A B} (f : A -> B) (C : Cyl f -> Type)
           (ext : ooExtendableAlong cyl C)
  : ooExtendableAlong cyl C
  := fun n => cyl_extendable n f C (ext n).

Definition cyl_extension'
           {A B} (f : A -> B) (C : B -> Type)
           (g : forall a, C (pr_cyl (cyl a)))
           (ext : ExtensionAlong f C g)
  : ExtensionAlong cyl (C o pr_cyl) g.
Proof.
  rapply cyl_extension.
  exists (ext.1 o pr_cyl).
  intros x; apply ext.2.
Defined.

Definition cyl_extendable' (n : nat)
           {A B} (f : A -> B) (C : B -> Type)
           (ext : ExtendableAlong n f C)
  : ExtendableAlong n cyl (C o (pr_cyl' f)).
Proof.
  rapply cyl_extendable.
  refine (cancelL_extendable n C cyl pr_cyl _ ext).
  rapply extendable_equiv.
Defined.

Definition cyl_ooextendable'
           {A B} (f : A -> B) (C : B -> Type)
           (ext : ooExtendableAlong f C)
  : ooExtendableAlong cyl (C o (pr_cyl' f))
  := fun n => cyl_extendable' n f C (ext n).


(** ** Extendability along [functor_prod] *)

Definition extension_functor_prod
           {A B A' B'} (f : A -> A') (g : B -> B')
           (P : A' * B' -> Type)
           (ef : forall b', ExtendableAlong 1 f (fun a' => P (a',b')))
           (eg : forall a', ExtendableAlong 1 g (fun b' => P (a',b')))
           (s : forall z, P (functor_prod f g z))
  : ExtensionAlong (functor_prod f g) P s.
Proof.
  srefine (_;_).
  - intros [a' b']; revert b'.
    refine ((fst (eg a') _).1).
    intros b; revert a'.
    refine ((fst (ef (g b)) _).1).
    intros a.
    exact (s (a,b)).
  - intros [a b]; cbn.
    refine ((fst (eg (f a)) _).2 b @ _).
    exact ((fst (ef (g b)) _).2 a).
Defined.

Definition extendable_functor_prod (n : nat)
           {A B A' B'} (f : A -> A') (g : B -> B')
           (P : A' * B' -> Type)
           (ef : forall b', ExtendableAlong n f (fun a' => P (a',b')))
           (eg : forall a', ExtendableAlong n g (fun b' => P (a',b')))
  : ExtendableAlong n (functor_prod f g) P.
Proof.
  revert P ef eg; simple_induction n n IH; intros P ef eg; [ exact tt | split ].
  - apply extension_functor_prod.
    + intros b'; exact (fst (ef b'), fun _ _ => tt).
    + intros a'; exact (fst (eg a'), fun _ _ => tt).
  - intros h k; apply IH.
    + intros b'; apply (snd (ef b')).
    + intros a'; apply (snd (eg a')).
Defined.

Definition ooextendable_functor_prod
           {A B A' B'} (f : A -> A') (g : B -> B')
           (P : A' * B' -> Type)
           (ef : forall b', ooExtendableAlong f (fun a' => P (a',b')))
           (eg : forall a', ooExtendableAlong g (fun b' => P (a',b')))
  : ooExtendableAlong (functor_prod f g) P
  := fun n => extendable_functor_prod n f g P (fun b' => ef b' n) (fun a' => eg a' n).


(** ** Extendability along [functor_sigma] *)

Definition extension_functor_sigma_id
           {A} {P Q : A -> Type} (f : forall a, P a -> Q a)
           (C : sig Q -> Type)
           (ef : forall a, ExtendableAlong 1 (f a) (fun v => C (a;v)))
           (s : forall z, C (functor_sigma idmap f z))
  : ExtensionAlong (functor_sigma idmap f) C s.
Proof.
  srefine (_;_).
  - intros [a v]; revert v.
    refine ((fst (ef a) _).1).
    intros u.
    exact (s (a;u)).
  - intros [a u]; cbn.
    exact ((fst (ef a) _).2 u).
Defined.

Definition extendable_functor_sigma_id n
           {A} {P Q : A -> Type} (f : forall a, P a -> Q a)
           (C : sig Q -> Type)
           (ef : forall a, ExtendableAlong n (f a) (fun v => C (a;v)))
  : ExtendableAlong n (functor_sigma idmap f) C.
Proof.
  revert C ef; simple_induction n n IH; intros C ef; [ exact tt | split ].
  - apply extension_functor_sigma_id.
    intros a; exact (fst (ef a) , fun _ _ => tt).
  - intros h k; apply IH.
    intros a; apply (snd (ef a)).
Defined.

Definition ooextendable_functor_sigma_id
           {A} {P Q : A -> Type} (f : forall a, P a -> Q a)
           (C : sig Q -> Type)
           (ef : forall a, ooExtendableAlong (f a) (fun v => C (a;v)))
  : ooExtendableAlong (functor_sigma idmap f) C
  := fun n => extendable_functor_sigma_id n f C (fun a => ef a n).

(** Unfortunately, the technology of [ExtensionAlong] seems to be insufficient to state a general, funext-free version of [extension_functor_sigma] with a nonidentity map on the bases; the hypothesis on the fiberwise map would have to be the existence of an extension in a function-type "up to pointwise equality".  With wild oo-groupoids we could probably manage it.  For now, we say something a bit hacky. *)

Definition HomotopyExtensionAlong {A B} {Q : B -> Type}
           (f : A -> B) (C : sig Q -> Type)
           (p : forall (a:A) (v:Q (f a)), C (f a;v))
  := { q : forall (b:B) (v:Q b), C (b;v) & forall a v, q (f a) v = p a v }.

Fixpoint HomotopyExtendableAlong (n : nat)
         {A B} {Q : B -> Type} (f : A -> B) (C : sig Q -> Type) : Type
  := match n with
     | 0 => Unit
     | S n => ((forall (p : forall (a:A) (v:Q (f a)), C (f a;v)),
                   HomotopyExtensionAlong f C p) *
               (forall (h k : forall z, C z),
                   HomotopyExtendableAlong n f (fun z => h z = k z)))
     end.

Definition ooHomotopyExtendableAlong
           {A B} {Q : B -> Type} (f : A -> B) (C : sig Q -> Type)
  := forall n, HomotopyExtendableAlong n f C.

Definition extension_functor_sigma
           {A B} {P : A -> Type} {Q : B -> Type}
           (f : A -> B) (g : forall a, P a -> Q (f a))
           (C : sig Q -> Type)
           (ef : HomotopyExtendableAlong 1 f C)
           (eg : forall a, ExtendableAlong 1 (g a) (fun v => C (f a ; v)))
           (s : forall z, C (functor_sigma f g z))
  : ExtensionAlong (functor_sigma f g) C s.
Proof.
  srefine (_;_).
  - intros [b v]; revert b v.
    refine ((fst ef _).1).
    intros a.
    refine ((fst (eg a) _).1).
    intros u.
    exact (s (a;u)).
  - intros [a u]; cbn.
    refine ((fst ef _).2 _ _ @ _).
    exact ((fst (eg a) _).2 u).
Defined.

Definition extendable_functor_sigma (n : nat)
           {A B} {P : A -> Type} {Q : B -> Type}
           (f : A -> B) (g : forall a, P a -> Q (f a))
           (C : sig Q -> Type)
           (ef : HomotopyExtendableAlong n f C)
           (eg : forall a, ExtendableAlong n (g a) (fun v => C (f a ; v)))
  : ExtendableAlong n (functor_sigma f g) C.
Proof.
  revert C ef eg; simple_induction n n IH; intros C ef eg; [ exact tt | split ].
  - apply extension_functor_sigma.
    + exact (fst ef, fun _ _ => tt).
    + intros a; exact (fst (eg a) , fun _ _ => tt).
  - intros h k; apply IH.
    + exact (snd ef h k).
    + intros a; apply (snd (eg a)).
Defined.

Definition ooextendable_functor_sigma
           {A B} {P : A -> Type} {Q : B -> Type}
           (f : A -> B) (g : forall a, P a -> Q (f a))
           (C : sig Q -> Type)
           (ef : ooHomotopyExtendableAlong f C)
           (eg : forall a, ooExtendableAlong (g a) (fun v => C (f a ; v)))
  : ooExtendableAlong (functor_sigma f g) C
  := fun n => extendable_functor_sigma n f g C (ef n) (fun a => eg a n).


(** ** Extendability along [functor_sum] *)

Definition extension_functor_sum
           {A B A' B'} (f : A -> A') (g : B -> B')
           (P : A' + B' -> Type)
           (ef : ExtendableAlong 1 f (P o inl))
           (eg : ExtendableAlong 1 g (P o inr))
           (h : forall z, P (functor_sum f g z))
  : ExtensionAlong (functor_sum f g) P h.
Proof.
  srefine (sum_ind _ _ _ ; sum_ind _ _ _).
  + exact (fst ef (h o inl)).1.
  + exact (fst eg (h o inr)).1.
  + exact (fst ef (h o inl)).2.
  + exact (fst eg (h o inr)).2.
Defined.

Definition extendable_functor_sum (n : nat)
           {A B A' B'} (f : A -> A') (g : B -> B')
           (P : A' + B' -> Type)
           (ef : ExtendableAlong n f (P o inl))
           (eg : ExtendableAlong n g (P o inr))
  : ExtendableAlong n (functor_sum f g) P.
Proof.
  revert P ef eg; induction n as [|n IH]; intros P ef eg; [ exact tt | split ].
  - intros h; apply extension_functor_sum.
    + exact (fst ef, fun _ _ => tt).
    + exact (fst eg, fun _ _ => tt).
  - intros h k.
    apply IH.
    + exact (snd ef (h o inl) (k o inl)).
    + exact (snd eg (h o inr) (k o inr)).
Defined.

Definition ooextendable_functor_sum
           {A B A' B'} (f : A -> A') (g : B -> B')
           (P : A' + B' -> Type)
           (ef : ooExtendableAlong f (P o inl))
           (eg : ooExtendableAlong g (P o inr))
  : ooExtendableAlong (functor_sum f g) P.
Proof.
  intros n; apply extendable_functor_sum; [ apply ef | apply eg ].
Defined.


(** ** Extendability along [functor_coeq] *)

(** The path algebra in these proofs is terrible on its own.  But by replacing the maps with cofibrations so that many equalities hold definitionally, and modifying the extensions to also be strict, it becomes manageable with a bit of dependent-path technology. *)

(** First we show that if we can extend in [C] along [k], and we can extend in appropriate path-types of [C] along [h], then we can extend in [C] along [functor_coeq].  This is where the hard work is. *)
Definition extension_functor_coeq {B A f g B' A' f' g'}
           {h : B -> B'} {k : A -> A'}
           {p : k o f == f' o h} {q : k o g == g' o h}
           {C : Coeq f' g' -> Type}
           (ek : ExtendableAlong 1 k (C o coeq))
           (eh : forall (u v : forall x : B', C (coeq (g' x))),
               ExtendableAlong 1 h (fun x => u x = v x))
           (s : forall x, C (functor_coeq h k p q x))
  : ExtensionAlong (functor_coeq h k p q) C s.
Proof.
  (** We start by change the problem to involve [CylCoeq] with cofibrations. *)
  set (C' := C o pr_cylcoeq p q).
  set (s' x := pr_cyl_cylcoeq p q x # s x).
  assert (e : ExtensionAlong (cyl_cylcoeq p q) C' s').
  2:{ pose (ex := fst (extendable_equiv 1 C (pr_cylcoeq p q)) e.1).
      exists (ex.1); intros x.
      apply (equiv_inj (transport C (pr_cyl_cylcoeq p q x))).
      exact (apD _ (pr_cyl_cylcoeq p q x) @ ex.2 _ @ e.2 x). }
  (** We have to transfer the hypotheses along those equivalences too.  We do it using [cyl_extendable] so that the resulting extensions compute definitionally.  Note that this means we never need to refer to the [.2] parts of the extensions, since they are identity paths. *)
  pose (ea1 := fun u => (fst (cyl_extendable' 1 _ _ ek) u).1).
  assert (eb'' : forall u v,
             ExtendableAlong 1 cyl (fun x:Cyl h => DPath C' (cglue x) (u x) (v x))).
  { intros u v.
    rapply extendable_postcompose'.
    2:{ rapply (cancelL_extendable 1 _ cyl pr_cyl).
        - rapply extendable_equiv.
        - exact (eh (fun x => cglue x # u (cyr x)) (v o cyr)). }
    intros x; subst C'.
    refine ((dp_compose (pr_cylcoeq p q) C _)^-1 oE _).
    symmetry; srapply equiv_ds_fill_lr.
    3:rapply ap_pr_cylcoeq_cglue.
    all:srapply (transport (fun r => DPath C r _ _)).
    3:exact (dp_inverse (dp_compose _ C _ (apD u (eissect pr_cyl x) : DPath _ _ _ _))).
    4:exact (dp_inverse (dp_compose _ C _ (apD v (eissect pr_cyl x) : DPath _ _ _ _))).
    1:change (fun y => pr_cylcoeq p q (coeq (functor_cyl p y)))
      with (fun y => coeq (f := f') (g := g') (pr_cyl (functor_cyl p y))).
    2:change (fun y => pr_cylcoeq p q (coeq (functor_cyl q y)))
      with (fun y => coeq (f := f') (g := g') (pr_cyl (functor_cyl q y))).
    all:refine ((ap_V _ (eissect pr_cyl x))^ @ _).
    all: exact (ap_compose (fun x => pr_cyl (functor_cyl _ x)) coeq _). }
  pose (eb1 := fun u v w => (fst (cyl_extendable _ _ _ (eb'' u v)) w).1).
  (** Now we construct an extension using Coeq-induction, and prove that it *is* an extension also using Coeq-induction. *)
  srefine (_;_); srapply Coeq_ind.
  + exact (ea1 (s' o coeq)).
  + apply eb1; intros b.
    rapply (dp_compose' _ _ (ap_cyl_cylcoeq_cglue p q b)).
    exact (apD s' (cglue b)).
  + (** Since we're using cofibrations, this holds definitionally. *)
    intros a; reflexivity.
  + (** And this one is much simpler than it would be otherwise. *)
    intros b.
    apply ds_dp.
    rapply ds_G1.
    refine (dp_apD_compose' _ _ (ap_cyl_cylcoeq_cglue p q b) _ @ _).
    apply moveR_equiv_V.
    nrapply Coeq_ind_beta_cglue.
Defined.

(** Now we can easily iterate into higher extendability. *)
Definition extendable_functor_coeq (n : nat)
           {B A f g B' A' f' g'}
           {h : B -> B'} {k : A -> A'}
           {p : k o f == f' o h} {q : k o g == g' o h}
           {C : Coeq f' g' -> Type}
           (ek : ExtendableAlong n k (C o coeq))
           (eh : forall (u v : forall x : B', C (coeq (g' x))),
               ExtendableAlong n h (fun x => u x = v x))
  : ExtendableAlong n (functor_coeq h k p q) C.
Proof.
  revert C ek eh; simple_induction n n IH; intros C ek eh; [ exact tt | split ].
  - apply extension_functor_coeq.
    + exact (fst ek , fun _ _ => tt).
    + exact (fun u v => (fst (eh u v) , fun _ _ => tt)).
  - intros u v; apply IH.
    + exact (snd ek (u o coeq) (v o coeq)).
    + exact (snd (eh (u o coeq o g') (v o coeq o g'))).
Defined.

Definition ooextendable_functor_coeq
           {B A f g B' A' f' g'}
           {h : B -> B'} {k : A -> A'}
           {p : k o f == f' o h} {q : k o g == g' o h}
           {C : Coeq f' g' -> Type}
           (ek : ooExtendableAlong k (C o coeq))
           (eh : forall (u v : forall x : B', C (coeq (g' x))),
               ooExtendableAlong h (fun x => u x = v x))
  : ooExtendableAlong (functor_coeq h k p q) C
  := fun n => extendable_functor_coeq n (ek n) (fun u v => eh u v n).

(** Since extending at level [n.+1] into [C] implies extending at level [n] into path-types of [C], we get the following corollary. *)
Definition extendable_functor_coeq' (n : nat)
           {B A f g B' A' f' g'}
           {h : B -> B'} {k : A -> A'}
           {p : k o f == f' o h} {q : k o g == g' o h}
           {C : Coeq f' g' -> Type}
           (ek : ExtendableAlong n k (C o coeq))
           (eh : ExtendableAlong n.+1 h (C o coeq o g'))
  : ExtendableAlong n (functor_coeq h k p q) C.
Proof.
  apply extendable_functor_coeq.
  1:assumption.
  exact (snd eh).
Defined.

Definition ooextendable_functor_coeq'
           {B A f g B' A' f' g'}
           {h : B -> B'} {k : A -> A'}
           {p : k o f == f' o h} {q : k o g == g' o h}
           {C : Coeq f' g' -> Type}
           (ek : ooExtendableAlong k (C o coeq))
           (eh : ooExtendableAlong h (C o coeq o g'))
  : ooExtendableAlong (functor_coeq h k p q) C
  := fun n => extendable_functor_coeq' n (ek n) (eh n.+1).
