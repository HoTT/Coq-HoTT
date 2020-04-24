(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.

(** * Globular types *)

Generalizable Variables m n p A B C.

(** ** Category Dimensions *)

(** We parametrize by a natural number that will indicate the invertibility dimension, i.e. for [n] we are talking about (oo,n)-categories.  Of course, at the level of mere globular sets it doesn't mean anything substative, but it will allow us to use a different notation when we know we're in the invertible dimension. *)

(** Many of our definitions involve coinductive clauses that pass to hom-types and take the predecessor of the dimension.  These are sometimes hard for typeclass inference to find because it can't guess that [n] should be matched as [(n.+1).-1] or that [0] should be matched as [0.-1].  So we use the following hints.  We do unfortunately have to declare these hints separately for each typeclass we want it to apply to, and each natural number argument of that class. *)

Ltac change_dim n :=
  match n with
  | (pred ?m) => fail 1
  | _ => progress change n with (pred (S n))
  end.

Ltac change_dim_0 n :=
  match n with
  | (pred ?m) => fail 1
  | 0%nat => progress change 0%nat with (pred 0)
  end.


(** ** Basic Definition *)

(** Note that this is a "negative coinductive type", defined like a record with "fields" (i.e. destructors) rather than with a constructor (although it does still *have* a constructor, like a record does).  Negative coinductive types (new in Coq 8.9) make much more sense both syntactically and semantically than the previous "positive" version and should be used exclusively in new code.  It seems that here [A] functions like a "non-uniform parameter", although a negative coinductive type cannot have "indices" like an inductive type. *)
CoInductive IsGlob@{u} (n : nat) (A : Type@{u}) : Type :=
{
  Hom : A -> A -> Type@{u} ;
  isglob_hom : forall (x y : A), IsGlob n.-1 (Hom x y) ;
}.
(* Technically this definition could allow two universe parameters, [A : Type@{u1}] and [Hom a b : Type@{u0}] with u0 <= u1.  But nearly all subsequent definitions force [u0 = u1].  Moreover, curiously, allowing [u0 != u1] here causes [iscat0_type] to fail with a universe error, while forcing [u0 = u1] here allows [iscat0_type] to succeed.  I don't fully understand why that is. *)

Existing Class IsGlob.
Arguments Hom {n} A {_} a b.
Notation "a $-> b" := (@Hom _ _ _ a b).
Notation "a $== b" := (@Hom 0 _ _ a b). (** In the invertible dimensions, we use a notation that looks more like paths or homotopies *)
Global Existing Instance isglob_hom.

(** Here are our first predecessor hint declarations. *)
Hint Extern 1 (IsGlob ?n (Hom _ _ _)) => change_dim n : typeclass_instances.
Hint Extern 1 (IsGlob ?n (Hom _ _ _)) => change_dim_0 n : typeclass_instances.

(** Sometimes it's convenient to move the [n] around, since it doesn't matter at the level of globular sets. *)
CoFixpoint isglob_reindex {m n : nat} {A : Type} `{IsGlob m A}
  : IsGlob n A.
Proof.
  unshelve econstructor.
  - rapply (@Hom m).
  - intros. nrapply (isglob_reindex (pred m) (pred n)).
    clear isglob_reindex; exact _.
Defined.

(** We can induce a globular structure by pullback along a function.  This is not an instance, of course; we have to choose when to apply it. *)
Definition isglob_induced {A} `{IsGlob n B} (F : A -> B) : IsGlob n A
  := Build_IsGlob n A (fun a b => F a $-> F b) _.


(** ** Dependent/displayed globular types *)

(** For now, we require no relation between the invertibility dimensions of [A] and [B]. *)
CoInductive IsDGlob {m : nat} {A : Type@{u}} (n : nat) (B : A -> Type@{u})
            `{IsGlob m A} : Type :=
{
  DHom : forall (a b : A) (f : a $-> b) (u : B a) (v : B b), Type@{u} ;
  isdglob_dhom : forall (a b : A) (u : B a) (v : B b),
      @IsDGlob (pred m) (a $-> b) (pred n) (fun f => DHom a b f u v) _ ;
}.

Existing Class IsDGlob.
Arguments DHom {m A n B _ _ a b} f u v.
(** Since [DHom] has three arguments that generally need to be given explicitly, we don't try to give it an infix notation. *)
Global Existing Instance isdglob_dhom.

Hint Extern 1 (IsDGlob ?n _) => change_dim n : typeclass_instances.
Hint Extern 1 (IsDGlob ?n _) => change_dim_0 n : typeclass_instances.
Hint Extern 1 (@IsDGlob ?m (Hom _ _ _) _ _ _) => change_dim m : typeclass_instances.
Hint Extern 1 (@IsDGlob ?m (Hom _ _ _) _ _ _) => change_dim_0 m : typeclass_instances.

CoFixpoint isdglob_reindex {m n m' n' : nat} `{IsDGlob m A n B}
  : @IsDGlob m' A n' B isglob_reindex.
Proof.
  unshelve econstructor.
  - rapply (@DHom m A n B _ _).
  - intros.
    nrapply (isdglob_reindex (pred m) (pred n) (pred m') (pred n')).
    rapply (@isdglob_dhom m A n B _ _ a b u v).
Defined.

(** Constant families of globular types are dependently globular. *)
CoFixpoint constant_dglob `{IsGlob m A} `{IsGlob n B}
  : IsDGlob n (@const A Type B).
Proof.
  unshelve econstructor.
  - intros ? ? ? u v; exact (u $-> v).
  - intros; rapply constant_dglob.
Defined.

Global Existing Instance constant_dglob.


(** ** Sections of dependent globular types, i.e. dependent 0-coherent oo-functors *)

CoInductive IsCatSect0 {m A n B} `{IsDGlob m A n B} (F : forall a, B a) :=
{
  fmapD : forall (a b : A) (f : a $-> b), DHom f (F a) (F b) ;
  iscatsect0_fmapD : forall (a b : A),
      @IsCatSect0 (pred m) (a $-> b) (pred n) (fun f => DHom f (F a) (F b))
                  _ _ (fmapD a b) ;
}.

Existing Class IsCatSect0.
Arguments fmapD {_ _ _ _ _ _} F {_ a b} f.
Global Existing Instance iscatsect0_fmapD.

Hint Extern 1 (@IsCatSect0 ?m (Hom _ _ _) _ _ _ _ _) => change_dim m : typeclass_instances.
Hint Extern 1 (@IsCatSect0 ?m (Hom _ _ _) _ _ _ _ _) => change_dim_0 m : typeclass_instances.
Hint Extern 1 (@IsCatSect0 _ _ ?n _ _ _ _) => change_dim n : typeclass_instances.
Hint Extern 1 (@IsCatSect0 _ _ ?n _ _ _ _) => change_dim_0 n : typeclass_instances.

(** Often we want to specify the objects explicitly. *)
Notation fmapD' F a b := (@fmapD _ _ _ _ _ _ F _ a b) (only parsing).

CoFixpoint iscatsect0_reindex {m n m' n' : nat} `{IsDGlob m A n B}
           (F : forall a, B a) `{!IsCatSect0 F}
  : @IsCatSect0 m' A n' B isglob_reindex isdglob_reindex F.
Proof.
  unshelve econstructor.
  - cbn. intros a b f; exact (fmapD F f).
  - intros a b; cbn. apply iscatsect0_reindex.
    apply iscatsect0_fmapD.
Defined.

(** ** 0-coherent oo-functors, i.e. globular morphisms *)

(** Just as non-dependent functions are a special case of dependent ones, ordinary functors are definitionally a special case of sections of displayed categories.  But it's convenient to make them syntactically distinct. *)

(*
CoInductive IsFunctor0 {A B : Type} `{IsGlob A} `{IsGlob B} (F : A -> B) : Type :=
{
  fmap : forall (a b : A), (a $-> b) -> (F a $-> F b) ;
  isfunctor0_fmap : forall (a b : A), @IsFunctor0 (a $-> b) (F a $-> F b) _ _ (fmap a b) ;
}.

Existing Class IsFunctor0.
Arguments fmap {_ _ _ _} F {_ a b} f.
Global Existing Instance isfunctor0_fmap.
*)

(** TODO: Consider making this a Notation instead. *)

Class IsFunctor0 {m A n B} `{IsGlob m A} `{IsGlob n B} (F : A -> B) :=
  iscatsect0_isfunctor0 : @IsCatSect0 m A n (const B) _ _ F.
Global Existing Instance iscatsect0_isfunctor0.

(** This is a syntactic variant of [Build_IsCatSect0] for non-dependent functors that leaves its coinductive goal written in terms of [IsFunctor0] instead of [IsCatSect0].  Unfortunately, it is not officially a "constructor" of [IsFunctor0], so tactics like [econstructor] won't use it. *)
Definition Build_IsFunctor0 `{IsGlob m A} `{IsGlob n B} (F : A -> B)
           (fmap' : forall (a b : A), (a $-> b) -> (F a $-> F b))
           (isfunctor0_fmap' : forall (a b : A), IsFunctor0 (fmap' a b))
  : IsFunctor0 F
  := Build_IsCatSect0 _ _ _ _ _ _ F fmap' isfunctor0_fmap'.

Definition fmap `{IsGlob m A} `{IsGlob n B} (F : A -> B) `{!IsFunctor0 F}
           {a b : A} (f : a $-> b)
  : F a $-> F b
  := fmapD F f.

Notation fmap' F a b := (@fmap _ _ _ _ _ _ F _ a b) (only parsing).

Hint Extern 1 (@IsFunctor0 _ _ ?n _ _ _ _) => change_dim n : typeclass_instances.
Hint Extern 1 (@IsFunctor0 _ _ ?n _ _ _ _) => change_dim_0 n : typeclass_instances.
Hint Extern 1 (@IsFunctor0 ?m (Hom _ _ _) _ _ _ _ _) => change_dim m : typeclass_instances.
Hint Extern 1 (@IsFunctor0 ?m (Hom _ _ _) _ _ _ _ _) => change_dim_0 m : typeclass_instances.

Global Instance isfunctor0_fmap `{IsGlob m A} `{IsGlob n B}
       (F : A -> B) `{!IsFunctor0 F} {a b : A}
  : @IsFunctor0 _ (a $-> b) _ (F a $-> F b) _ _ (fmap' F a b)
  := iscatsect0_fmapD F _ a b.

(** Unfortunately, since [isglob_reindex] is not definitionally equal to [isdglob_reindex] applied to a [constant_dglob], we have to prove this separately rather than appeal to [iscatsect0_reindex]. *)
CoFixpoint isfunctor0_reindex {m n m' n' : nat} `{IsGlob m A, IsGlob n B}
           (F : A -> B) `{!IsFunctor0 F}
  : @IsFunctor0 m' A n' B isglob_reindex isglob_reindex F.
Proof.
  snrapply Build_IsFunctor0.
  - intros a b f; cbn. apply fmap; assumption.
  - intros a b; cbn. apply isfunctor0_reindex.
    exact _.
Defined.

(** The identity functor *)
CoFixpoint isfunctor0_idmap `{IsGlob m A}
  : @IsFunctor0 m A m A _ _ idmap.
Proof.
  refine (Build_IsFunctor0 _ _ _).
Defined.

(** Composition of functors *)
CoFixpoint isfunctor0_compose `{IsGlob m A} `{IsGlob n B} `{IsGlob p C}
       (G : B -> C) `{!IsFunctor0 G} (F : A -> B) `{!IsFunctor0 F}
  : IsFunctor0 (G o F).
Proof.
  unshelve econstructor.
  - intros a b; exact (fmap G o fmap' F a b).
  - intros a b; cbn. 
    exact (isfunctor0_compose _ _ _ _ _ _ _ _ _ (fmap G) _ (fmap F) _).
Defined.

Global Existing Instances isfunctor0_idmap isfunctor0_compose.

Global Instance isfunctor0_induced {A} `{IsGlob n B} (F : A -> B)
  : @IsFunctor0 n A n B (isglob_induced F) _ F.
Proof.
  rapply Build_IsFunctor0.
Defined.  

(** ** Dependent 0-coherent functors *)

(** These could alternatively be defined as sections of [B2] pulled back to [sig B1].  Conversely, a section of [B : A -> Type] could be defined as a dependent functor from [const Unit] to [B] over [idmap]. *)
CoInductive IsDFunctor0 {m1 A1 n1 B1 m2 A2 n2 B2}
            `{IsDGlob m1 A1 n1 B1} `{IsDGlob m2 A2 n2 B2}
      (F : A1 -> A2) `{!IsFunctor0 F} (G : forall a:A1, B1 a -> B2 (F a)) :=
{
  dfmap : forall (a b : A1) (u : B1 a) (v : B1 b) (f : a $-> b),
    DHom f u v -> DHom (fmap F f) (G a u) (G b v) ;
  isdfunctor0_dfmap : forall (a b : A1) (u : B1 a) (v : B1 b),
      @IsDFunctor0 _ _ _ _ _ _ _ _ _ _ _ _ (fmap F) _ (dfmap a b u v) ;
}.

Existing Class IsDFunctor0.
Arguments dfmap {_ _ _ _ _ _ _ _ _ _ _ _} F {_} G {_ a b u v f} p.
Global Existing Instance isdfunctor0_dfmap.

Hint Extern 1 (@IsDFunctor0 ?m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _) => change_dim m1 : typeclass_instances.
Hint Extern 1 (@IsDFunctor0 ?m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _) => change_dim_0 m1 : typeclass_instances.
Hint Extern 1 (@IsDFunctor0 _ _ ?n1 _ _ _ _ _ _ _ _ _ _ _ _) => change_dim n1 : typeclass_instances.
Hint Extern 1 (@IsDFunctor0 _ _ ?n1 _ _ _ _ _ _ _ _ _ _ _ _) => change_dim_0 n1 : typeclass_instances.
Hint Extern 1 (@IsDFunctor0 _ _ _ _ ?m2 _ _ _ _ _ _ _ _ _ _) => change_dim m2 : typeclass_instances.
Hint Extern 1 (@IsDFunctor0 _ _ _ _ ?m2 _ _ _ _ _ _ _ _ _ _) => change_dim_0 m2 : typeclass_instances.
Hint Extern 1 (@IsDFunctor0 _ _ _ _ _ _ ?n2 _ _ _ _ _ _ _ _) => change_dim n2 : typeclass_instances.
Hint Extern 1 (@IsDFunctor0 _ _ _ _ _ _ ?n2 _ _ _ _ _ _ _ _) => change_dim_0 n2 : typeclass_instances.

(** ** The identity dependent functor *)

CoFixpoint isdfunctor0_idmap `{IsDGlob m A n B}
  : IsDFunctor0 idmap (fun a => idmap).
Proof.
  unshelve econstructor.
  - intros a b u v f g; exact g.
  - intros a b u v; apply isdfunctor0_idmap.
Defined.

(** ** Composition of dependent functors with sections *)

CoFixpoint iscatsect0_isdfunctor0_compose {m A n1 B1 n2 B2}
           `{IsDGlob m A n1 B1} `{!IsDGlob n2 B2}
           (G : forall a:A, B1 a -> B2 a) `{!IsDFunctor0 idmap G}
           (F : forall a:A, B1 a) `{!IsCatSect0 F}
  : IsCatSect0 (fun a => G a (F a)).
Proof.
  unshelve econstructor.
  - intros a b f.
    exact (dfmap idmap G (fmapD F f)).
  - intros a b.
    exact (@iscatsect0_isdfunctor0_compose
             (pred m) (a $-> b) (pred n1) (fun f => DHom f (F a) (F b)) (pred n2) (fun f => DHom f (G a (F a)) (G b (F b)))
             _ _ _ (fun f => dfmap idmap G (f := f))
             (isdfunctor0_dfmap idmap G _ a b (F a) (F b)) (fmapD' F a b) _).
Defined.

(** ** Pullback of dependent globular types *)

CoFixpoint isdglob_compose {A1 A2 : Type} (B : A2 -> Type)
           `{IsGlob m1 A1} `{IsDGlob m2 A2 n B}
           (F : A1 -> A2) `{!IsFunctor0 F}
  : IsDGlob n (B o F).
Proof.
  unshelve econstructor.
  - intros a b f u v; exact (DHom (fmap F f) u v).
  - intros a b u v. 
    refine (isdglob_compose _ (F a $-> F b) (fun g => DHom g u v)
                            _ _ _ _ _ _ (fmap F) _).
Defined.
Existing Instance isdglob_compose.

(** Tlsil has suggested that we could also define a dependent globular type to be a globular map into a globular type of spans.  This would make [isdglob_compose] an instance of [isfunctor0_compose].  But it would require defining globular maps before dependent globular types, with the effect that globular maps wouldn't be definitionally globular sections of constant dependent globular types. *)


(** ** Truncatedness *)

(** We define a coinductive "categorical" notion of truncatedness.  A category is contractible (as a category), a.k.a. (-2)-truncated if it is inhabited and all its hom-categories are contractible.  And it is [n.+1]-truncated if all its hom-categories are [n]-truncated. *)

CoInductive CatTrunc (n : trunc_index) {m : nat} (A : Type) `{IsGlob m A} :=
{
  cat_center' : forall (isc : IsMinusTwo n), A ;
  cattrunc_hom : forall (a b : A), @CatTrunc (n.-1) _ (a $-> b) _ ;
}.
Existing Class CatTrunc.
Global Existing Instance cattrunc_hom.

Hint Extern 1 (@CatTrunc _ ?m (Hom _ _ _) _) => change_dim m : typeclass_instances.
Hint Extern 1 (@CatTrunc _ ?m (Hom _ _ _) _) => change_dim_0 m : typeclass_instances.

Definition cat_center `{CatTrunc (-2) m A} : A
  := @cat_center' (-2) m A _ _ tt.

Global Instance cattrunc_hom_succ `{CatTrunc n.+1 m A} (a b : A)
  : CatTrunc n (a $-> b)
  := @cattrunc_hom n.+1 m A _ _ a b.

Global Instance cattrunc_hom_minustwo `{CatTrunc (-2) m A} (a b : A)
  : CatTrunc (-2) (a $-> b)
  := @cattrunc_hom (-2) m A _ _ a b.

CoFixpoint cattrunc_pred `{CatTrunc n.-1 m A}
  : CatTrunc n A.
Proof.
  unshelve econstructor.
  - destruct n as [|n]; cbn in *.
    + intros; apply cat_center.
    + intros [].
  - intros; cbn.
    apply cattrunc_pred.
    rapply cattrunc_hom.
Defined.

CoFixpoint cattrunc_reindex {m'} `{CatTrunc n m A}
  : @CatTrunc n m' A isglob_reindex.
Proof.
  unshelve econstructor.
  - apply (cat_center' n A _).
  - intros; cbn.
    rapply (cattrunc_reindex (pred m')).
Defined.
Global Existing Instance cattrunc_reindex.

Notation CatContr := (CatTrunc (-2)).
Notation CatProp := (CatTrunc (-1)).
Notation CatPoset := (CatTrunc 0).
Notation Cat1Cat := (CatTrunc 1).

(** TODO: truncated displayed categories *)

(** ** Universal properties *)

Class IsInitial `{IsGlob n A} (a : A) :=
  catcontr_initial : forall b, CatContr (a $-> b).
Global Existing Instance catcontr_initial.

Class HasInitial `{IsGlob n A} :=
{
  initial_obj : A ;
  isinitial_initial : IsInitial initial_obj ;
}.
Global Existing Instance isinitial_initial.

Class IsTerminal `{IsGlob n A} (a : A) :=
  catcontr_terminal : forall b, CatContr (b $-> a).
Global Existing Instance catcontr_terminal.

Class HasTerminal `{IsGlob n A} :=
{
  terminal_obj : A ;
  isterminal_terminal : IsTerminal terminal_obj ;
}.
Global Existing Instance isterminal_terminal.
