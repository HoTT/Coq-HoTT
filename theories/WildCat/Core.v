Require Import Basics.Overture Basics.Tactics.

(** * Wild categories, functors, and transformations *)

(** ** Directed graphs *)

Class IsGraph (A : Type) :=
{
  Hom : A -> A -> Type
}.

Notation "a $-> b" := (Hom a b).

Definition graph_hfiber {B C : Type} `{IsGraph C} (F : B -> C) (c : C)
  := {b : B & F b $-> c}.

(** ** 0-categorical structures *)

(** A wild (0,1)-category has 1-morphisms and operations on them, but no coherence. *)
Class Is01Cat (A : Type) `{IsGraph A} :=
{
  Id  : forall (a : A), a $-> a;
  cat_comp : forall (a b c : A), (b $-> c) -> (a $-> b) -> (a $-> c);
}.

(** The [&] symbol here is a "bidirectionality hint". It directs Rocq to typecheck the application of [Build_Is01Cat] to the argument [A] before computing the type of the full term and trying to unify it with the goal, and only afterwards to typecheck the remaining arguments; it will be easier for Rocq to elaborate and typecheck the later arguments [Id] and [cat_comp] if [A] is already known. *)
Arguments Build_Is01Cat A &.
Arguments cat_comp {A _ _ a b c} _ _.
Notation "g $o f" := (cat_comp g f).

Definition cat_postcomp {A} `{Is01Cat A} (a : A) {b c : A} (g : b $-> c)
  : (a $-> b) -> (a $-> c)
  := cat_comp g.

Definition cat_precomp {A} `{Is01Cat A} {a b : A} (c : A) (f : a $-> b)
  : (b $-> c) -> (a $-> c)
  := fun g => g $o f.

(** A wild 0-groupoid is a wild (0,1)-category whose morphisms can be reversed.  This is also known as a setoid. *)
Class Is0Gpd (A : Type) `{Is01Cat A} :=
  { gpd_rev : forall {a b : A}, (a $-> b) -> (b $-> a) }.

Definition GpdHom {A} `{Is0Gpd A} (a b : A) := a $-> b.
Notation "a $== b" := (GpdHom a b).

Instance reflexive_GpdHom {A} `{Is0Gpd A}
  : Reflexive GpdHom
  := fun a => Id a.

Instance reflexive_Hom {A} `{Is01Cat A}
  : Reflexive Hom
  := fun a => Id a.

Definition gpd_comp {A} `{Is0Gpd A} {a b c : A}
  : (a $== b) -> (b $== c) -> (a $== c)
  := fun p q => q $o p.
Infix "$@" := gpd_comp.

Instance transitive_GpdHom {A} `{Is0Gpd A}
  : Transitive GpdHom
  := fun a b c f g => f $@ g.

Instance transitive_Hom {A} `{Is01Cat A}
  : Transitive Hom
  := fun a b c f g => g $o f.

Notation "p ^$" := (gpd_rev p).

Instance symmetric_GpdHom {A} `{Is0Gpd A}
  : Symmetric GpdHom
  := fun a b f => f^$.

Instance symmetric_Hom {A} `{Is0Gpd A}
  : Symmetric Hom
  := fun a b f => f^$.

Definition Hom_path {A : Type} `{Is01Cat A} {a b : A} (p : a = b) : (a $-> b).
Proof.
  destruct p; apply Id.
Defined.

Definition GpdHom_path {A} `{Is0Gpd A} {a b : A} (p : a = b) : a $== b
  := Hom_path p.

(** A 0-functor acts on morphisms, but satisfies no axioms. *)
Class Is0Functor {A B : Type} `{IsGraph A} `{IsGraph B} (F : A -> B)
  := { fmap : forall (a b : A) (f : a $-> b), F a $-> F b }.

Arguments Build_Is0Functor {A B isgraph_A isgraph_B} F fmap : rename.
Arguments fmap {A B isgraph_A isgraph_B} F {is0functor_F a b} f : rename.

Class Is2Graph (A : Type) `{IsGraph A}
  := isgraph_hom : forall (a b : A), IsGraph (a $-> b).
Existing Instance isgraph_hom | 20.
#[global] Typeclasses Transparent Is2Graph.

(** ** Wild 1-categorical structures *)
Class Is1Cat (A : Type) `{!IsGraph A, !Is2Graph A, !Is01Cat A} :=
{
  is01cat_hom :: forall (a b : A), Is01Cat (a $-> b) ;
  is0gpd_hom :: forall (a b : A), Is0Gpd (a $-> b) ;
  is0functor_postcomp :: forall (a b c : A) (g : b $-> c), Is0Functor (cat_postcomp a g) ;
  is0functor_precomp :: forall (a b c : A) (f : a $-> b), Is0Functor (cat_precomp c f) ;
  cat_assoc : forall (a b c d : A) (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $== h $o (g $o f);
  cat_assoc_opp : forall (a b c d : A) (f : a $-> b) (g : b $-> c) (h : c $-> d),
    h $o (g $o f) $== (h $o g) $o f;
  cat_idl : forall (a b : A) (f : a $-> b), Id b $o f $== f;
  cat_idr : forall (a b : A) (f : a $-> b), f $o Id a $== f;
}.

Arguments cat_assoc {_ _ _ _ _ _ _ _ _} f g h.
Arguments cat_assoc_opp {_ _ _ _ _ _ _ _ _} f g h.
Arguments cat_idl {_ _ _ _ _ _ _} f.
Arguments cat_idr {_ _ _ _ _ _ _} f.

(** An alternate constructor that doesn't require the proof of [cat_assoc_opp].  This can be used for defining examples of wild categories, but shouldn't be used for the general theory of wild categories. *)
Definition Build_Is1Cat' (A : Type) `{!IsGraph A, !Is2Graph A, !Is01Cat A}
  (is01cat_hom : forall a b : A, Is01Cat (a $-> b))
  (is0gpd_hom : forall a b : A, Is0Gpd (a $-> b))
  (is0functor_postcomp : forall (a b c : A) (g : b $-> c), Is0Functor (cat_postcomp a g))
  (is0functor_precomp : forall (a b c : A) (f : a $-> b), Is0Functor (cat_precomp c f))
  (cat_assoc : forall (a b c d : A) (f : a $-> b) (g : b $-> c) (h : c $-> d),
      h $o g $o f $== h $o (g $o f))
  (cat_idl : forall (a b : A) (f : a $-> b), Id b $o f $== f)
  (cat_idr : forall (a b : A) (f : a $-> b), f $o Id a $== f)
  : Is1Cat A
  := Build_Is1Cat A _ _ _ is01cat_hom is0gpd_hom is0functor_postcomp is0functor_precomp
      cat_assoc (fun a b c d f g h => (cat_assoc a b c d f g h)^$) cat_idl cat_idr.

(** Whiskering and horizontal composition of 2-cells. *)

Definition cat_postwhisker {A} `{Is1Cat A} {a b c : A}
           {f g : a $-> b} (h : b $-> c) (p : f $== g)
  : h $o f $== h $o g
  := fmap (cat_postcomp a h) p.
Notation "h $@L p" := (cat_postwhisker h p).

Definition cat_prewhisker {A} `{Is1Cat A} {a b c : A}
           {f g : b $-> c} (p : f $== g) (h : a $-> b)
  : f $o h $== g $o h
  := fmap (cat_precomp c h) p.
Notation "p $@R h" := (cat_prewhisker p h).

Definition cat_comp2 {A} `{Is1Cat A} {a b c : A}
  {f g : a $-> b} {h k : b $-> c}
  (p : f $== g) (q : h $== k )
  : h $o f $== k $o g
  := (q $@R _) $@ (_ $@L p).

Notation "q $@@ p" := (cat_comp2 q p).

(** Epimorphisms and monomorphisms. *)

Class Epic {A} `{Is1Cat A} {a b : A} (f : a $-> b)
  := isepic : forall {c} (g h : b $-> c), g $o f $== h $o f -> g $== h.

Arguments isepic {A}%_type_scope {IsGraph0 Is2Graph0 Is01Cat0 H a b} f {Epic c} g h _.

Section Epimorphisms.

  Context {A : Type} `{Is1Cat A}.

  #[export]
  Instance epic_id (P : A) : Epic (Id P).
  Proof.
    intros B b b' h.
    exact ((cat_idr _)^$ $@ h $@ cat_idr _).
  Defined.

  Definition epic_homotopic {P P'} (f g : P $-> P') `{!Epic f} (h : f $== g)
    : Epic g.
  Proof.
    intros Q x x' h'.
    apply (isepic f).
    exact ((x $@L h) $@ h' $@ (x' $@L h^$)).
  Defined.

  #[export]
  Instance epic_compose {P P' P'' : A} (f : P $-> P') (g : P' $-> P'')
    `{!Epic f} `{!Epic g}
    : Epic (g $o f).
  Proof.
    intros Q x x' h.
    apply (isepic g).
    apply (isepic f).
    exact ((cat_assoc f g x) $@ h $@ (cat_assoc_opp f g x')).
  Defined.

  Definition epic_cancel {P P' P'' : A} (f : P $-> P') (g : P' $-> P'')
    `{!Epic (g $o f)}
    : Epic g.
  Proof.
    intros Q x x' h.
    rapply isepic.
    exact ((cat_assoc_opp f g x) $@ (h $@R f) $@ (cat_assoc f g x')).
  Defined.

  Definition Epi (P' P : A) := { e : P' $-> P & Epic e }.

  Definition hom_epi {P' P} (e : Epi P' P) := pr1 e : P' $-> P.
  Coercion hom_epi : Epi >-> Hom.

  #[export]
  Instance epic_epi {P' P} (e : Epi P' P) : Epic e := pr2 e.

  Definition id_epi P : Epi P P := (Id P; epic_id P).

End Epimorphisms.

Notation "P' $->> P" := (Epi P' P) (at level 99).

(** Monomorphisms could be defined as epimorphisms in the opposite category, which would allow us to reuse the proofs below.  We'd have to move the material on epis and monos to a separate file. *)

Class Monic {A} `{Is1Cat A} {b c: A} (f : b $-> c)
  := ismonic : forall {a} (g h : a $-> b), f $o g $== f $o h -> g $== h.

Arguments ismonic {A}%_type_scope {IsGraph0 Is2Graph0 Is01Cat0 H b c} f {Monic a} g h _.

Section Monomorphisms.

  Context {A : Type} `{Is1Cat A}.

  #[export]
  Instance monic_id (P : A) : Monic (Id P).
  Proof.
    intros B b b' h.
    exact ((cat_idl _)^$ $@ h $@ cat_idl _).
  Defined.

  Definition monic_homotopic {P P'} (f g : P $-> P') `{!Monic f} (h : f $== g)
    : Monic g.
  Proof.
    intros Q x x' h'.
    apply (ismonic f).
    exact ((h $@R x) $@ h' $@ (h^$ $@R x')).
  Defined.

  #[export]
  Instance monic_compose {P P' P'' : A} (f : P $-> P') (g : P' $-> P'')
    `{!Monic f} `{!Monic g}
    : Monic (g $o f).
  Proof.
    intros Q x x' h.
    apply (ismonic f).
    apply (ismonic g).
    exact ((cat_assoc_opp x f g) $@ h $@ (cat_assoc x' f g)).
  Defined.

  Definition monic_cancel {P P' P'' : A} (f : P $-> P') (g : P' $-> P'')
    `{!Monic (g $o f)}
    : Monic f.
  Proof.
    intros Q x x' h.
    rapply ismonic.
    exact ((cat_assoc x f g) $@ (g $@L h) $@ (cat_assoc_opp x' f g)).
  Defined.

  Definition Mono (P' P : A) := { e : P' $-> P & Monic e }.

  Definition hom_mono {P' P} (m : Mono P' P) := pr1 m : P' $-> P.
  Coercion hom_mono : Mono >-> Hom.

  #[export]
  Instance monic_mono {P' P} (e : Mono P' P) : Monic e := pr2 e.

  Definition id_mono P : Mono P P := (Id P; monic_id P).

End Monomorphisms.

Notation "P' $>-> P" := (Mono P' P) (at level 99).

(** Section might be a clearer name but it's better to avoid confusion with Coq keywords. *)

Record SectionOf {A} `{Is1Cat A} {a b : A} (f : a $-> b) :=
  {
    comp_right_inverse : b $-> a;
    is_section : f $o comp_right_inverse $== Id b
  }.

Record RetractionOf {A} `{Is1Cat A} {a b : A} (f : a $-> b) :=
  {
    comp_left_inverse : b $-> a;
    is_retraction : comp_left_inverse $o f $== Id a
  }.

(** Often, the coherences are actually equalities rather than homotopies. *)
Class Is1Cat_Strong (A : Type)`{!IsGraph A, !Is2Graph A, !Is01Cat A} :=
{
  is01cat_hom_strong : forall (a b : A), Is01Cat (a $-> b) ;
  is0gpd_hom_strong : forall (a b : A), Is0Gpd (a $-> b) ;
  is0functor_postcomp_strong : forall (a b c : A) (g : b $-> c),
    Is0Functor (cat_postcomp a g) ;
  is0functor_precomp_strong : forall (a b c : A) (f : a $-> b),
    Is0Functor (cat_precomp c f) ;
  cat_assoc_strong : forall (a b c d : A)
    (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f = h $o (g $o f) ;
  cat_assoc_opp_strong : forall (a b c d : A)
    (f : a $-> b) (g : b $-> c) (h : c $-> d),
    h $o (g $o f) = (h $o g) $o f ;
  cat_idl_strong : forall (a b : A) (f : a $-> b), Id b $o f = f ;
  cat_idr_strong : forall (a b : A) (f : a $-> b), f $o Id a = f ;
}.

Arguments cat_assoc_strong {_ _ _ _ _ _ _ _ _} f g h.
Arguments cat_assoc_opp_strong {_ _ _ _ _ _ _ _ _} f g h.
Arguments cat_idl_strong {_ _ _ _ _ _ _} f.
Arguments cat_idr_strong {_ _ _ _ _ _ _} f.

Definition is1cat_is1cat_strong (A : Type) `{Is1Cat_Strong A}
  : Is1Cat A.
Proof.
  srapply Build_Is1Cat.
  all: intros a b.
  - apply is01cat_hom_strong.
  - apply is0gpd_hom_strong.
  - apply is0functor_postcomp_strong.
  - apply is0functor_precomp_strong.
  - intros; apply GpdHom_path, cat_assoc_strong.
  - intros; apply GpdHom_path, cat_assoc_opp_strong.
  - intros; apply GpdHom_path, cat_idl_strong.
  - intros; apply GpdHom_path, cat_idr_strong.
Defined.

Hint Immediate is1cat_is1cat_strong : typeclass_instances.

(** Initial objects *)
Definition IsInitial {A : Type} `{Is1Cat A} (x : A)
  := forall (y : A), {f : x $-> y & forall g, f $== g}.
Existing Class IsInitial.

Definition mor_initial {A : Type} `{Is1Cat A} (x y : A) {h : IsInitial x}
  : x $-> y
  := (h y).1.

Definition mor_initial_unique {A : Type} `{Is1Cat A} (x y : A) {h : IsInitial x}
  (f : x $-> y)
  : mor_initial x y $== f
  := (h y).2 f.

(** Terminal objects *)
Definition IsTerminal {A : Type} `{Is1Cat A} (y : A)
  := forall (x : A), {f : x $-> y & forall g, f $== g}.
Existing Class IsTerminal.

Definition mor_terminal {A : Type} `{Is1Cat A} (x y : A) {h : IsTerminal y}
  : x $-> y
  := (h x).1.

Definition mor_terminal_unique {A : Type} `{Is1Cat A} (x y : A) {h : IsTerminal y}
  (f : x $-> y)
  : mor_terminal x y $== f
  := (h x).2 f.

(** Generalizing function extensionality, "Morphism extensionality" states that homwise [GpdHom_path] is an equivalence. *)
Class HasMorExt (A : Type) `{Is1Cat A} :=
  isequiv_Htpy_path :: forall (a b : A) f g, IsEquiv (@GpdHom_path (a $-> b) _ _ _ f g).

Definition path_hom {A} `{HasMorExt A} {a b : A} {f g : a $-> b} (p : f $== g)
  : f = g
  := GpdHom_path^-1 p.

(** A 1-category with morphism extensionality induces a strong 1-category *)
Instance is1cat_strong_hasmorext {A : Type} `{HasMorExt A}
  : Is1Cat_Strong A.
Proof.
  rapply Build_Is1Cat_Strong; hnf; intros; apply path_hom.
  + apply cat_assoc.
  + apply cat_assoc_opp.
  + apply cat_idl.
  + apply cat_idr.
Defined.

(** A 1-functor acts on 2-cells (satisfying no axioms) and also preserves composition and identities up to a 2-cell. *)
  (* The [!] tells Coq to use typeclass search to find the [IsGraph] parameters of [Is0Functor] instead of assuming additional copies of them. *)
Class Is1Functor {A B : Type} `{Is1Cat A} `{Is1Cat B}
  (F : A -> B) `{!Is0Functor F} :=
{
  fmap2 : forall a b (f g : a $-> b), (f $== g) -> (fmap F f $== fmap F g) ;
  fmap_id : forall a, fmap F (Id a) $== Id (F a);
  fmap_comp : forall a b c (f : a $-> b) (g : b $-> c),
    fmap F (g $o f) $== fmap F g $o fmap F f;
}.

Arguments fmap2 {A B
  isgraph_A is2graph_A is01cat_A is1cat_A
  isgraph_B is2graph_B is01cat_B is1cat_B}
  F {is0functor_F is1functor_F a b f g} p : rename.
Arguments fmap_id {A B
  isgraph_A is2graph_A is01cat_A is1cat_A
  isgraph_B is2graph_B is01cat_B is1cat_B}
  F {is0functor_F is1functor_F} a : rename.
Arguments fmap_comp {A B
  isgraph_A is2graph_A is01cat_A is1cat_A
  isgraph_B is2graph_B is01cat_B is1cat_B}
  F {is0functor_F is1functor_F a b c} f g : rename.

Class Faithful {A B : Type} (F : A -> B) `{Is1Functor A B F} :=
  faithful : forall (x y : A) (f g : x $-> y),
      fmap F f $== fmap F g -> f $== g.

(** Identity functor *)

Section IdentityFunctor.

  #[export] Instance is0functor_idmap {A : Type} `{IsGraph A} : Is0Functor idmap.
  Proof.
    by apply Build_Is0Functor.
  Defined.

  #[export] Instance is1functor_idmap {A : Type} `{Is1Cat A} : Is1Functor idmap.
  Proof.
    by apply Build_Is1Functor.
  Defined.

  #[export] Instance isFaithful_idmap {A : Type} `{Is1Cat A}: Faithful idmap.
  Proof.
    by unfold Faithful.
  Defined.
End IdentityFunctor.

(** Constant functor *)

Section ConstantFunctor.

  Context {A B : Type}.

  #[export] Instance is01functor_const
    `{IsGraph A} `{Is01Cat B} (x : B)
    : Is0Functor (fun _ : A => x).
  Proof.
    srapply Build_Is0Functor.
    intros a b f; apply Id.
  Defined.

  #[export] Instance is1functor_const
   `{Is1Cat A} `{Is1Cat B} (x : B)
    : Is1Functor (fun _ : A => x).
  Proof.
    srapply Build_Is1Functor.
    - intros a b f g p; apply Id.
    - intro; apply Id.
    - intros a b c f g. cbn.
      symmetry.
      apply cat_idl.
  Defined.

End ConstantFunctor.

(** Composite functors *)

Instance is0functor_compose {A B C : Type}
  `{IsGraph A, IsGraph B, IsGraph C}
  (F : A -> B) `{!Is0Functor F} (G : B -> C) `{!Is0Functor G}
  : Is0Functor (G o F).
Proof.
  srapply Build_Is0Functor.
  intros a b f; exact (fmap G (fmap F f)).
Defined.

Instance is1functor_compose {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A -> B) `{!Is0Functor F, !Is1Functor F}
  (G : B -> C) `{!Is0Functor G, !Is1Functor G}
  : Is1Functor (G o F).
Proof.
  srapply Build_Is1Functor.
  - intros a b f g p; exact (fmap2 G (fmap2 F p)).
  - intros a; exact (fmap2 G (fmap_id F a) $@ fmap_id G (F a)).
  - intros a b c f g.
    lhs' rapply (fmap2 G (fmap_comp F f g)).
    exact (fmap_comp G (fmap F f) (fmap F g)).
Defined.

(** We give all arguments names in order to refer to them later. This allows us to write things like [is0functor (isgraph_A := _)] without having to make all the variables explicit. *)
Arguments is0functor_compose {A B C} {isgraph_A isgraph_B isgraph_C}
  F {is0functor_F} G {is0functor_G} : rename.

Arguments is1functor_compose {A B C}
  {isgraph_A is2graph_A is01cat_A is1cat_A
   isgraph_B is2graph_B is01cat_B is1cat_B
   isgraph_C is2graph_C is01cat_C is1cat_C}
  F {is0functor_F} {is1functor_F}
  G {is0functor_G} {is1functor_G}
  : rename.

(** ** Wild 1-groupoids *)

Class Is1Gpd (A : Type) `{Is1Cat A, !Is0Gpd A} :=
{
  gpd_issect : forall {a b : A} (f : a $-> b), f^$ $o f $== Id a ;
  gpd_isretr : forall {a b : A} (f : a $-> b), f $o f^$ $== Id b ;
}.

(** Some more convenient equalities for morphisms in a 1-groupoid. The naming scheme is similar to [PathGroupoids.v].*)

Definition gpd_V_hh {A} `{Is1Gpd A} {a b c : A} (f : b $-> c) (g : a $-> b)
  : f^$ $o (f $o g) $== g :=
  (cat_assoc _ _ _)^$ $@ (gpd_issect f $@R g) $@ cat_idl g.

Definition gpd_h_Vh {A} `{Is1Gpd A} {a b c : A} (f : c $-> b) (g : a $-> b)
  : f $o (f^$ $o g) $== g :=
  (cat_assoc _ _ _)^$ $@ (gpd_isretr f $@R g) $@ cat_idl g.

Definition gpd_hh_V {A} `{Is1Gpd A} {a b c : A} (f : b $-> c) (g : a $-> b)
  : (f $o g) $o g^$ $== f :=
  cat_assoc _ _ _ $@ (f $@L gpd_isretr g) $@ cat_idr f.

Definition gpd_hV_h {A} `{Is1Gpd A} {a b c : A} (f : b $-> c) (g : b $-> a)
  : (f $o g^$) $o g $== f :=
  cat_assoc _ _ _ $@ (f $@L gpd_issect g) $@ cat_idr f.

Definition gpd_moveL_1M {A} `{Is1Gpd A} {x y : A} {p q : x $-> y}
  (r : p $o q^$ $== Id _) : p $== q.
Proof.
  lhs' exact ((cat_idr p)^$ $@ (p $@L (gpd_issect q)^$) $@ (cat_assoc _ _ _)^$).
  exact ((r $@R q) $@ cat_idl q).
Defined.

Definition gpd_moveR_V1 {A} `{Is1Gpd A} {x y : A} {p : x $-> y}
  {q : y $-> x} (r : Id _ $== p $o q) : p^$ $== q.
Proof.
  lhs' exact ((cat_idr p^$)^$ $@ (p^$ $@L r)).
  apply gpd_V_hh.
Defined.

Definition gpd_moveR_M1 {A : Type} `{Is1Gpd A} {x y : A} {p q : x $-> y}
  (r : Id _ $== p^$ $o q) : p $== q.
Proof.
  rhs_V' exact ((cat_assoc _ _ _)^$ $@ (gpd_isretr p $@R q) $@ cat_idl q).
  exact ((cat_idr p)^$ $@ (p $@L r)).
Defined.

Definition gpd_moveR_1M {A : Type} `{Is1Gpd A} {x y : A} {p q : x $-> y}
  (r : Id _ $== q $o p^$) : p $== q.
Proof.
  refine ((cat_idl p)^$ $@ _ $@ cat_idr q).
  refine (_ $@ cat_assoc _ _ _ $@ (q $@L (gpd_issect p)^$)^$).
  exact (r $@R p).
Defined.

Definition gpd_moveL_1V {A : Type} `{Is1Gpd A} {x y : A} {p : x $-> y}
  {q : y $-> x} (r : p $o q $== Id _) : p $== q^$.
Proof.
  rhs_V' apply cat_idl.
  rhs_V' exact (r $@R q^$).
  exact (gpd_hh_V _ _)^$.
Defined.

Definition gpd_moveR_hV {A : Type} `{Is1Gpd A} {x y z : A} {p : y $-> z}
  {q : x $-> y} {r : x $-> z} (s : r $== p $o q)
  : r $o q^$ $== p
  := (s $@R q^$) $@ gpd_hh_V _ _.

Definition gpd_moveR_Vh {A : Type} `{Is1Gpd A} {x y z : A} {p : y $-> z}
  {q : x $-> y} {r : x $-> z} (s : r $== p $o q)
  : p^$ $o r $== q
  := (p^$ $@L s) $@ gpd_V_hh _ _.

Definition gpd_moveL_hM {A : Type} `{Is1Gpd A} {x y z : A} {p : y $-> z}
  {q : x $-> y} {r : x $-> z} (s : r $o q^$ $== p)
  : r $== p $o q := ((gpd_hV_h _ _)^$ $@ (s $@R _)).

Definition gpd_moveL_hV {A : Type} `{Is1Gpd A} {x y z : A} {p : y $-> z}
  {q : x $-> y} {r : x $-> z} (s : p $o q $== r)
  : p $== r $o q^$
  := (gpd_moveR_hV s^$)^$.

Definition gpd_moveL_Mh {A : Type} `{Is1Gpd A} {x y z : A} {p : y $-> z}
  {q : x $-> y} {r : x $-> z} (s : p^$ $o r $== q)
  : r $== p $o q := ((gpd_h_Vh _ _)^$ $@ (p $@L s)).

Definition gpd_moveL_Vh {A : Type} `{Is1Gpd A} {x y z : A} {p : y $-> z}
  {q : x $-> y} {r : x $-> z} (s : p $o q $== r)
  : q $== p^$ $o r
  := (gpd_moveR_Vh s^$)^$.

Definition gpd_rev2 {A : Type} `{Is1Gpd A} {x y : A} {p q : x $-> y}
  (r : p $== q) : p^$ $== q^$.
Proof.
  apply gpd_moveR_V1.
  apply gpd_moveL_hV.
  exact (cat_idl q $@ r^$).
Defined.

Definition gpd_rev_pp {A} `{Is1Gpd A} {a b c : A} (f : b $-> c) (g : a $-> b)
  : (f $o g)^$ $== g^$ $o f^$.
Proof.
  apply gpd_moveR_V1.
  rhs_V' napply cat_assoc.
  apply gpd_moveL_hV.
  lhs' napply cat_idl.
  exact (gpd_hh_V _ _)^$.
Defined.

Definition gpd_rev_1 {A} `{Is1Gpd A} {a : A} : (Id a)^$ $== Id a.
Proof.
  rhs_V' exact (gpd_isretr (Id a)).
  symmetry; apply cat_idl.
Defined.

Definition gpd_rev_rev {A} `{Is1Gpd A} {a0 a1 : A} (g : a0 $== a1)
  : (g^$)^$ $== g.
Proof.
  apply gpd_moveR_V1.
  exact (gpd_issect _)^$.
Defined.

(** 1-functors between 1-groupoids preserve identities *)
Definition gpd_1functor_V {A B} `{Is1Gpd A, Is1Gpd B}
           (F : A -> B) `{!Is0Functor F, !Is1Functor F}
           {a0 a1 : A} (f : a0 $== a1)
  : fmap F f^$ $== (fmap F f)^$.
Proof.
  apply gpd_moveL_1V.
  refine ((fmap_comp _ _ _)^$ $@ _ $@ fmap_id _ _).
  rapply fmap2.
  apply gpd_issect.
Defined.

(** Movement lemmas with extensionality *)

(** For more complex movements you probably want to apply [path_hom] and use the lemmas above. *)

Definition gpd_strong_V_hh {A} `{Is1Gpd A, !HasMorExt A} {a b c : A} (f : b $-> c) (g : a $-> b)
  : f^$ $o (f $o g) = g := path_hom (gpd_V_hh f g).

Definition gpd_strong_h_Vh {A} `{Is1Gpd A, !HasMorExt A} {a b c : A} (f : c $-> b) (g : a $-> b)
  : f $o (f^$ $o g) = g := path_hom (gpd_h_Vh f g).

Definition gpd_strong_hh_V {A} `{Is1Gpd A, !HasMorExt A} {a b c : A} (f : b $-> c) (g : a $-> b)
  : (f $o g) $o g^$ = f := path_hom (gpd_hh_V f g).

Definition gpd_strong_hV_h {A} `{Is1Gpd A, !HasMorExt A} {a b c : A} (f : b $-> c) (g : b $-> a)
  : (f $o g^$) $o g = f := path_hom (gpd_hV_h f g).

Definition gpd_strong_rev_pp {A} `{Is1Gpd A, !HasMorExt A} {a b c : A} (f : b $-> c) (g : a $-> b)
  : (f $o g)^$ = g^$ $o f^$
  := path_hom (gpd_rev_pp f g).

Definition gpd_strong_rev_1 {A} `{Is1Gpd A, !HasMorExt A} {a : A}
  : (Id a)^$ = Id a
  := path_hom gpd_rev_1.

Definition gpd_strong_rev_rev {A} `{Is1Gpd A, !HasMorExt A} {a0 a1 : A} (g : a0 $== a1)
  : (g^$)^$ = g := path_hom (gpd_rev_rev g).

Definition fmap_id_strong {A B} `{Is1Cat A, Is1Cat B, !HasMorExt B}
           (F : A -> B) `{!Is0Functor F, !Is1Functor F} (a : A)
  : fmap F (Id a) = Id (F a)
  := path_hom (fmap_id F a).

Definition gpd_strong_1functor_V {A B} `{Is1Gpd A, Is1Gpd B, !HasMorExt B}
           (F : A -> B) `{!Is0Functor F, !Is1Functor F}
           {a0 a1 : A} (f : a0 $== a1)
  : fmap F f^$ = (fmap F f)^$
  := path_hom (gpd_1functor_V F f).

Class Is3Graph (A : Type) `{Is2Graph A}
  := isgraph_hom_hom : forall (a b : A), Is2Graph (a $-> b).
Existing Instance isgraph_hom_hom | 30.
#[global] Typeclasses Transparent Is3Graph.

(** *** Preservation of initial and terminal objects *)

Class PreservesInitial {A B : Type} (F : A -> B)
  `{Is1Functor A B F} : Type
  := isinitial_preservesinitial
    :: forall (x : A), IsInitial x -> IsInitial (F x).

(** The initial morphism is preserved by such a functor. *)
Lemma fmap_initial {A B : Type} (F : A -> B)
  `{PreservesInitial A B F} (x y : A) (h : IsInitial x)
  : fmap F (mor_initial x y) $== mor_initial (F x) (F y).
Proof.
  exact (mor_initial_unique _ _ _)^$.
Defined.

Class PreservesTerminal {A B : Type} (F : A -> B)
  `{Is1Functor A B F} : Type
  := isterminal_preservesterminal
    :: forall (x : A), IsTerminal x -> IsTerminal (F x).

(** The terminal morphism is preserved by such a functor. *)
Lemma fmap_terminal {A B : Type} (F : A -> B)
  `{PreservesTerminal A B F} (x y : A) (h : IsTerminal y)
  : fmap F (mor_terminal x y) $== mor_terminal (F x) (F y).
Proof.
  exact (mor_terminal_unique _ _ _)^$.
Defined.

(** *** Functors preserving distinguished objects *)

Record BasepointPreservingFunctor (B C : Type)
       `{Is01Cat B, Is01Cat C} `{IsPointed B, IsPointed C} := {
    bp_map : B -> C;
    bp_is0functor :: Is0Functor bp_map;
    bp_pointed : bp_map (point B) $-> point C
  }.

Arguments bp_pointed {B C}%_type_scope {H H0 H1 H2 H3 H4} b.
Arguments Build_BasepointPreservingFunctor {B C}%_type_scope {H H0 H1 H2 H3 H4}
  bp_map%_function_scope {bp_is0functor} bp_pointed.

Coercion bp_map : BasepointPreservingFunctor >-> Funclass.

Notation "B -->* C" := (BasepointPreservingFunctor B C) (at level 70).

Definition basepointpreservingfunctor_compose {B C D : Type}
           `{Is01Cat B, Is01Cat C, Is01Cat D}
           `{IsPointed B, IsPointed C, IsPointed D}
           (F : B -->* C) (G : C -->* D)
  : B -->* D.
Proof.
  snapply Build_BasepointPreservingFunctor.
  - exact (G o F).
  - exact _.
  - exact (bp_pointed G $o fmap G (bp_pointed F)).
Defined.

Notation "G $o* F" := (basepointpreservingfunctor_compose F G) (at level 40).

