(** * Equivalences *)

Require Import
  Basics.Overture
  Basics.PathGroupoids
  Basics.Contractible
  Basics.Tactics.
Local Open Scope path_scope.

(** We now give many ways to construct equivalences.  In each case, we define an instance of the typeclass [IsEquiv] named [isequiv_X], followed by an element of the record type [Equiv] named [equiv_X].

   Whenever we need to assume, as a hypothesis, that a certain function is an equivalence, we do it by assuming separately a function and a proof of [IsEquiv].  This is more general than assuming an inhabitant of [Equiv], since the latter has an implicit coercion and an existing instance to give us the former automatically.  Moreover, implicit generalization makes it easy to assume a function and a proof of [IsEquiv]. *)

(** A word on naming: some of the lemmas about equivalences are analogues of those for paths in PathGroupoids.  We name them in an analogous way but adding [_equiv] in an appropriate place, e.g. instead of [moveR_M] we have [moveR_equiv_M].  *)

Generalizable Variables A B C f g.

(** The identity map is an equivalence. *)
Global Instance isequiv_idmap (A : Type) : IsEquiv idmap | 0 :=
  Build_IsEquiv A A idmap idmap (fun _ => 1) (fun _ => 1) (fun _ => 1).

Definition equiv_idmap (A : Type) : A <~> A := Build_Equiv A A idmap _.

Arguments equiv_idmap {A} , A.

Notation "1" := equiv_idmap : equiv_scope.

Global Instance reflexive_equiv : Reflexive Equiv | 0 := @equiv_idmap.

Arguments reflexive_equiv /.

(** The composition of equivalences is an equivalence. *)
Global Instance isequiv_compose `{IsEquiv A B f} `{IsEquiv B C g}
  : IsEquiv (g o f) | 1000
  := Build_IsEquiv A C (g o f)
    (f^-1 o g^-1)
    (fun c => ap g (eisretr f (g^-1 c)) @ eisretr g c)
    (fun a => ap (f^-1) (eissect g (f a)) @ eissect f a)
    (fun a =>
      (whiskerL _ (eisadj g (f a))) @
      (ap_pp g _ _)^ @
      ap02 g
      ( (concat_A1p (eisretr f) (eissect g (f a)))^ @
        (ap_compose f^-1 f _ @@ eisadj f a) @
        (ap_pp f _ _)^
      ) @
      (ap_compose f g _)^
    ).

(* An alias of [isequiv_compose], with some arguments explicit; often convenient when type class search fails. *)
Definition isequiv_compose'
  {A B : Type} (f : A -> B) (_ : IsEquiv f)
  {C : Type} (g : B -> C) (_ : IsEquiv g)
  : IsEquiv (g o f)
  := isequiv_compose.

Definition equiv_compose {A B C : Type} (g : B -> C) (f : A -> B)
  `{IsEquiv B C g} `{IsEquiv A B f}
  : A <~> C
  := Build_Equiv A C (g o f) _.

Definition equiv_compose' {A B C : Type} (g : B <~> C) (f : A <~> B)
  : A <~> C
  := equiv_compose g f.

(** We put [g] and [f] in [equiv_scope] explicitly.  This is a partial work-around for https://github.com/coq/coq/issues/3990, which is that implicitly bound scopes don't nest well. *)
Notation "g 'oE' f" := (equiv_compose' g%equiv f%equiv) : equiv_scope.

(* The TypeClass [Transitive] has a different order of parameters than [equiv_compose].  Thus in declaring the instance we have to switch the order of arguments. *)
Global Instance transitive_equiv : Transitive Equiv | 0 :=
  fun _ _ _ f g => equiv_compose g f.

Arguments transitive_equiv /.

(** A tactic to simplify "oE".  See [ev_equiv] below for a more extensive tactic. *)
Ltac change_apply_equiv_compose :=
  match goal with
  | [ |- context [ equiv_fun (?f oE ?g) ?x ] ] =>
    change ((f oE g) x) with (f (g x))
  end.

(** Transporting is an equivalence. *)
Section EquivTransport.

  Context {A : Type} (P : A -> Type) {x y : A} (p : x = y).

  Global Instance isequiv_transport : IsEquiv (transport P p) | 0
    := Build_IsEquiv (P x) (P y) (transport P p) (transport P p^)
    (transport_pV P p) (transport_Vp P p) (transport_pVp P p).

  Definition equiv_transport : P x <~> P y
    := Build_Equiv _ _ (transport P p) _.

End EquivTransport.

(** In all the above cases, we were able to directly construct all the structure of an equivalence.  However, as is evident, sometimes it is quite difficult to prove the adjoint law.

   The following adjointification theorem allows us to be lazy about this if we wish.  It says that if we have all the data of an (adjoint) equivalence except the triangle identity, then we can always obtain the triangle identity by modifying the datum [equiv_is_section] (or [equiv_is_retraction]).  The proof is the same as the standard categorical argument that any equivalence can be improved to an adjoint equivalence.

   As a stylistic matter, we try to avoid using adjointification in the library whenever possible, to preserve the homotopies specified by the user.  *)

Section Adjointify.

  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (isretr : f o g == idmap) (issect : g o f == idmap).

  (* This is the modified [eissect]. *)
  Let issect' := fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

  Local Definition is_adjoint' (a : A) : isretr (f a) = ap f (issect' a).
  Proof.
    unfold issect'.
    apply moveR_M1.
    repeat rewrite ap_pp, concat_p_pp; rewrite <- ap_compose.
    rewrite (concat_pA1 (fun b => (isretr b)^) (ap f (issect a)^)).
    repeat rewrite concat_pp_p; rewrite ap_V; apply moveL_Vp; rewrite concat_p1.
    rewrite concat_p_pp, <- ap_compose.
    rewrite (concat_pA1 (fun b => (isretr b)^) (isretr (f a))).
    rewrite concat_pV, concat_1p; reflexivity.
  Qed.

  (** We don't make this a typeclass instance, because we want to control when we are applying it. *)
  Definition isequiv_adjointify : IsEquiv f
    := Build_IsEquiv A B f g isretr issect' is_adjoint'.

  Definition equiv_adjointify : A <~> B
    := Build_Equiv A B f isequiv_adjointify.

End Adjointify.

Arguments isequiv_adjointify {A B}%_type_scope (f g)%_function_scope isretr issect.
Arguments equiv_adjointify {A B}%_type_scope (f g)%_function_scope isretr issect.

(** Anything homotopic to an equivalence is an equivalence. This should not be an instance; it can cause the unifier to spin forever searching for functions to be homotopic to. *)
Definition isequiv_homotopic {A B : Type} (f : A -> B) {g : A -> B}
  `{IsEquiv A B f} (h : f == g)
  : IsEquiv g.
Proof.
  snrapply isequiv_adjointify.
  - exact f^-1.
  - intro b.  exact ((h _)^ @ eisretr f b).
  - intro a.  exact (ap f^-1 (h a)^ @ eissect f a).
Defined.

Definition isequiv_homotopic' {A B : Type} (f : A <~> B) {g : A -> B} (h : f == g)
  : IsEquiv g
  := isequiv_homotopic f h.

Definition equiv_homotopic {A B : Type} (f : A -> B) {g : A -> B}
  `{IsEquiv A B f} (h : f == g)
  : A <~> B
  := Build_Equiv _ _ g (isequiv_homotopic f h).

(** If [e] is an equivalence, [f] is homotopic to [e], and [g] is homotopic to [e^-1], then there is an equivalence whose underlying map is [f] and whose inverse is [g], definitionally. *)
Definition equiv_homotopic_inverse {A B} (e : A <~> B)
  {f : A -> B} {g : B -> A} (h : f == e) (k : g == e^-1)
  : A <~> B.
Proof.
  snrapply equiv_adjointify.
  - exact f.
  - exact g.
  - intro a.  exact (ap f (k a) @ h _ @ eisretr e a).
  - intro b.  exact (ap g (h b) @ k _ @ eissect e b).
Defined.

(** An involution is an endomap that is its own inverse. *)
Definition isequiv_involution {X : Type} (f : X -> X) (isinvol : f o f == idmap)
: IsEquiv f
  := isequiv_adjointify f f isinvol isinvol.

Definition equiv_involution {X : Type} (f : X -> X) (isinvol : f o f == idmap)
: X <~> X
  := equiv_adjointify f f isinvol isinvol.

(** Several lemmas useful for rewriting. *)
Definition moveR_equiv_M `{IsEquiv A B f} (x : A) (y : B) (p : x = f^-1 y)
  : (f x = y)
  := ap f p @ eisretr f y.

Definition moveR_equiv_M' `(f : A <~> B) (x : A) (y : B) (p : x = f^-1 y)
  : (f x = y)
  := moveR_equiv_M x y p.

Definition moveL_equiv_M `{IsEquiv A B f} (x : A) (y : B) (p : f^-1 y = x)
  : (y = f x)
  := (eisretr f y)^ @ ap f p.

Definition moveL_equiv_M' `(f : A <~> B) (x : A) (y : B) (p : f^-1 y = x)
  : (y = f x)
  := moveL_equiv_M x y p.

Definition moveR_equiv_V `{IsEquiv A B f} (x : B) (y : A) (p : x = f y)
  : (f^-1 x = y)
  := ap (f^-1) p @ eissect f y.

Definition moveR_equiv_V' `(f : A <~> B) (x : B) (y : A) (p : x = f y)
  : (f^-1 x = y)
  := moveR_equiv_V x y p.

Definition moveL_equiv_V `{IsEquiv A B f} (x : B) (y : A) (p : f y = x)
  : (y = f^-1 x)
  := (eissect f y)^ @ ap (f^-1) p.

Definition moveL_equiv_V' `(f : A <~> B) (x : B) (y : A) (p : f y = x)
  : (y = f^-1 x)
  := moveL_equiv_V x y p.

(** Equivalence preserves contractibility (which of course is trivial under univalence). *)
Lemma contr_equiv A {B} (f : A -> B) `{IsEquiv A B f} `{Contr A}
  : Contr B.
Proof.
  apply (Build_Contr _ (f (center A))).
  intro y.
  apply moveR_equiv_M.
  apply contr.
Defined.

Definition contr_equiv' A {B} `(f : A <~> B) `{Contr A}
  : Contr B
  := contr_equiv A f.

(** Any two contractible types are equivalent. *)
Global Instance isequiv_contr_contr {A B : Type}
       `{Contr A} `{Contr B} (f : A -> B)
  : IsEquiv f
  := Build_IsEquiv _ _ f (fun _ => (center A))
                  (fun x => path_contr _ _)
                  (fun x => path_contr _ _)
                  (fun x => path_contr _ _).

Definition equiv_contr_contr {A B : Type} `{Contr A} `{Contr B}
  : (A <~> B)
  := Build_Equiv _ _ (fun _ => center B) _.

(** The projection from the sum of a family of contractible types is an equivalence. *)
Global Instance isequiv_pr1 {A : Type} (P : A -> Type) `{forall x, Contr (P x)}
  : IsEquiv (@pr1 A P).
Proof.
  apply (Build_IsEquiv
           _ _ (@pr1 A P)
           (fun x => (x ; center (P x)))
           (fun x => 1)
           (fun xy => match xy with
                      | exist x y => ap (exist _ x) (contr _)
                      end)).
  intros [x y].
  rewrite <- ap_compose.
  symmetry; apply ap_const.
Defined.

Definition equiv_pr1 {A : Type} (P : A -> Type) `{forall x, Contr (P x)}
  : { x : A & P x } <~> A
  := Build_Equiv _ _ (@pr1 A P) _.

(** Equivalences between path spaces *)

(** If [f] is an equivalence, then so is [ap f].  We are lazy and use [adjointify]. *)
Global Instance isequiv_ap `{IsEquiv A B f} (x y : A)
  : IsEquiv (@ap A B f x y) | 1000
  := isequiv_adjointify (ap f)
  (fun q => (eissect f x)^  @  ap f^-1 q  @  eissect f y)
  (fun q =>
    ap_pp f _ _
    @ whiskerR (ap_pp f _ _) _
    @ ((ap_V f _ @ inverse2 (eisadj f _)^)
      @@ (ap_compose f^-1 f _)^
      @@ (eisadj f _)^)
    @ concat_pA1_p (eisretr f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _)
  (fun p =>
    whiskerR (whiskerL _ (ap_compose f f^-1 _)^) _
    @ concat_pA1_p (eissect f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _).

Definition equiv_ap `(f : A -> B) `{IsEquiv A B f} (x y : A)
  : (x = y) <~> (f x = f y)
  := Build_Equiv _ _ (ap f) _.

Global Arguments equiv_ap (A B)%_type_scope f%_function_scope _ _ _.

Definition equiv_ap' `(f : A <~> B) (x y : A)
  : (x = y) <~> (f x = f y)
  := equiv_ap f x y.

Definition equiv_inj `(f : A -> B) `{IsEquiv A B f} {x y : A}
  : (f x = f y) -> (x = y)
  := (ap f)^-1.

(** Assuming function extensionality, composing with an equivalence is itself an equivalence *)

Global Instance isequiv_precompose `{Funext} {A B C : Type}
  (f : A -> B) `{IsEquiv A B f}
  : IsEquiv (fun (g:B->C) => g o f) | 1000
  := isequiv_adjointify (fun (g:B->C) => g o f)
    (fun h => h o f^-1)
    (fun h => path_forall _ _ (fun x => ap h (eissect f x)))
    (fun g => path_forall _ _ (fun y => ap g (eisretr f y))).

Definition equiv_precompose `{Funext} {A B C : Type}
  (f : A -> B) `{IsEquiv A B f}
  : (B -> C) <~> (A -> C)
  := Build_Equiv _ _ (fun (g:B->C) => g o f) _.

Definition equiv_precompose' `{Funext} {A B C : Type} (f : A <~> B)
  : (B -> C) <~> (A -> C)
  := Build_Equiv _ _ (fun (g:B->C) => g o f) _.

Global Instance isequiv_postcompose `{Funext} {A B C : Type}
  (f : B -> C) `{IsEquiv B C f}
  : IsEquiv (fun (g:A->B) => f o g) | 1000
  := isequiv_adjointify (fun (g:A->B) => f o g)
    (fun h => f^-1 o h)
    (fun h => path_forall _ _ (fun x => eisretr f (h x)))
    (fun g => path_forall _ _ (fun y => eissect f (g y))).

Definition equiv_postcompose `{Funext} {A B C : Type}
  (f : B -> C) `{IsEquiv B C f}
  : (A -> B) <~> (A -> C)
  := Build_Equiv _ _ (fun (g:A->B) => f o g) _.

Definition equiv_postcompose' `{Funext} {A B C : Type} (f : B <~> C)
  : (A -> B) <~> (A -> C)
  := Build_Equiv _ _ (fun (g:A->B) => f o g) _.

(** Conversely, if pre- or post-composing with a function is always an equivalence, then that function is also an equivalence.  This is a form of the Yoneda lemma.  It's convenient to know that we only need to assume the equivalence when the other type is the domain or the codomain. *)

Definition isequiv_isequiv_precompose {A B : Type} (f : A -> B)
  (precomp := (fun (C : Type) (h : B -> C) => h o f))
  (Aeq : IsEquiv (precomp A)) (Beq : IsEquiv (precomp B))
  : IsEquiv f.
Proof.
  set (g:=(precomp A)^-1 idmap).
  pose proof (p:=eisretr (precomp A) idmap : g o f = idmap).
  refine (isequiv_adjointify f g (ap10 _) (ap10 p)).
  apply (equiv_inj (precomp B)).
  unfold precomp; cbn.
  exact (ap (fun k => f o k) p).
Defined.

Definition isequiv_isequiv_postcompose {A B : Type} (f : A -> B)
  (postcomp := (fun (C : Type) (h : C -> A) => f o h))
  (Aeq : IsEquiv (postcomp A)) (Beq : IsEquiv (postcomp B))
  : IsEquiv f.
Proof.
  set (g:=(postcomp B)^-1 idmap).
  pose proof (p:=eisretr (postcomp B) idmap : f o g = idmap).
  refine (isequiv_adjointify f g (ap10 p) (ap10 _)).
  apply (equiv_inj (postcomp A)).
  unfold postcomp; cbn.
  exact (ap (fun k => k o f) p).
Defined.

(** The inverse of an equivalence is an equivalence. *)
Global Instance isequiv_inverse {A B : Type} (f : A -> B) {feq : IsEquiv f}
  : IsEquiv f^-1 | 10000.
Proof.
  refine (Build_IsEquiv B A f^-1 f (eissect f) (eisretr f) _).
  intro b.
  apply (equiv_inj (ap f)).
(* We will prove the equality as a composite of four paths, working right to left.
  The LHS remains [ap f (eissect f (f^-1 b))] throughout the process.
  Both sides of the equation are paths of type [f (f^-1 (f (f^-1 b))) = f (f^-1 b)]. *)
  refine (_ @ _ @ _ @ _); revgoals.
  1: apply ap_compose.
  1: symmetry; apply (ap_homotopic_id (eisretr f)).
  1: symmetry; apply concat_pp_V.
  1: symmetry; apply eisadj.
Defined.

(** If the goal is [IsEquiv _^-1], then use [isequiv_inverse]; otherwise, don't pretend worry about if the goal is an evar and we want to add a [^-1]. *)
#[export]
Hint Extern 0 (IsEquiv _^-1) => apply @isequiv_inverse : typeclass_instances.

(** [Equiv A B] is a symmetric relation. *)
Theorem equiv_inverse {A B : Type} : (A <~> B) -> (B <~> A).
Proof.
  intro e.
  exists (e^-1).
  apply isequiv_inverse.
Defined.

Notation "e ^-1" := (@equiv_inverse _ _ e) : equiv_scope.

Global Instance symmetric_equiv : Symmetric Equiv | 0 := @equiv_inverse.

Arguments symmetric_equiv /.

(** Inversion respects composition *)
Definition equiv_inverse_compose {A B C} (f : A <~> B) (g : B <~> C)
  : (g oE f)^-1 == f^-1 oE g^-1.
Proof.
  intros x; reflexivity.
Defined.

(** Inversion respects homotopies *)
Definition equiv_inverse_homotopy {A B} (f g : A <~> B) (p : f == g)
  : g^-1 == f^-1.
Proof.
  intros x; refine (_ @ _ @ _).
  1:symmetry; apply (eissect f).
  1:apply ap, p.
  apply ap, eisretr.
Defined.

Definition equiv_ap_inv `(f : A -> B) `{IsEquiv A B f} (x y : B)
  : (f^-1 x = f^-1 y) <~> (x = y)
  := (@equiv_ap B A f^-1 _ x y)^-1%equiv.

Definition equiv_ap_inv' `(f : A <~> B) (x y : B)
  : (f^-1 x = f^-1 y) <~> (x = y)
  := (equiv_ap' f^-1%equiv x y)^-1%equiv.

(** If [g \o f] and [f] are equivalences, so is [g].  This is not an Instance because it would require Coq to guess [f]. *)
Definition cancelR_isequiv {A B C} (f : A -> B) {g : B -> C}
  `{IsEquiv A B f} `{IsEquiv A C (g o f)}
  : IsEquiv g
  := isequiv_homotopic ((g o f) o f^-1)
       (fun b => ap g (eisretr f b)).

Definition cancelR_equiv {A B C} (f : A -> B) {g : B -> C}
  `{IsEquiv A B f} `{IsEquiv A C (g o f)}
  : B <~> C
  := Build_Equiv B C g (cancelR_isequiv f).

(** If [g \o f] and [g] are equivalences, so is [f]. *)
Definition cancelL_isequiv {A B C} (g : B -> C) {f : A -> B}
  `{IsEquiv B C g} `{IsEquiv A C (g o f)}
  : IsEquiv f
  := isequiv_homotopic (g^-1 o (g o f))
       (fun a => eissect g (f a)).

Definition cancelL_equiv {A B C} (g : B -> C) {f : A -> B}
  `{IsEquiv B C g} `{IsEquiv A C (g o f)}
  : A <~> B
  := Build_Equiv _ _ f (cancelL_isequiv g).

(** Combining these with [isequiv_compose], we see that equivalences can be transported across commutative squares. *)
Definition isequiv_commsq {A B C D}
           (f : A -> B) (g : C -> D) (h : A -> C) (k : B -> D)
           (p : k o f == g o h)
           `{IsEquiv _ _ f} `{IsEquiv _ _ h} `{IsEquiv _ _ k}
: IsEquiv g.
Proof.
  refine (@cancelR_isequiv _ _ _ h g _ _).
  refine (isequiv_homotopic _ p).
Defined.

Definition isequiv_commsq' {A B C D}
           (f : A -> B) (g : C -> D) (h : A -> C) (k : B -> D)
           (p : g o h == k o f)
           `{IsEquiv _ _ g} `{IsEquiv _ _ h} `{IsEquiv _ _ k}
: IsEquiv f.
Proof.
  refine (@cancelL_isequiv _ _ _ k f _ _).
  refine (isequiv_homotopic _ p).
Defined.

(** Based homotopy spaces *)

Global Instance contr_basedhomotopy `{Funext}
       {A:Type} {B : A -> Type} (f : forall x, B x)
: Contr {g : forall x, B x & f == g }.
Proof.
  refine (contr_equiv' { g : forall x, B x & f = g } _).
  srapply equiv_adjointify; intros [g h].
  - exact (g; apD10 h).
  - exact (g; path_forall _ _ h).
  - apply ap, eisretr.
  - apply ap, eissect.
Defined.

Global Instance contr_basedhomotopy' `{Funext}
       {A:Type} {B : A -> Type} (f : forall x, B x)
: Contr {g : forall x, B x & g == f }.
Proof.
  refine (contr_equiv' { g : forall x, B x & g = f } _).
  srapply equiv_adjointify; intros [g h].
  - exact (g; apD10 h).
  - exact (g; path_forall _ _ h).
  - apply ap, eisretr.
  - apply ap, eissect.
Defined.


(** The function [equiv_ind] says that given an equivalence [f : A <~> B], and a hypothesis from [B], one may always assume that the hypothesis is in the image of [e].

In fibrational terms, if we have a fibration over [B] which has a section once pulled back along an equivalence [f : A <~> B], then it has a section over all of [B].  *)

Definition equiv_ind `{IsEquiv A B f} (P : B -> Type)
  : (forall x:A, P (f x)) -> forall y:B, P y
  := fun g y => transport P (eisretr f y) (g (f^-1 y)).

Arguments equiv_ind {A B} f {_} P _ _.

Definition equiv_ind_comp `{IsEquiv A B f} (P : B -> Type)
  (df : forall x:A, P (f x)) (x : A)
  : equiv_ind f P df (f x) = df x.
Proof.
  unfold equiv_ind.
  rewrite eisadj.
  rewrite <- transport_compose.
  exact (apD df (eissect f x)).
Defined.

(** Using [equiv_ind], we define a handy little tactic which introduces a variable [x] and simultaneously substitutes it along an equivalence [E]. *)
Ltac equiv_intro E x :=
  match goal with
    | |- forall y, @?Q y =>
      refine (equiv_ind E Q _); intros x
  end.

(** The same, but for several variables. *)

Tactic Notation "equiv_intros" constr(E) ident(x)
  := equiv_intro E x.
Tactic Notation "equiv_intros" constr(E) ident(x) ident(y)
  := equiv_intro E x; equiv_intro E y.
Tactic Notation "equiv_intros" constr(E) ident(x) ident(y) ident(z)
  := equiv_intro E x; equiv_intro E y; equiv_intro E z.

(** A lemma that combines equivalence induction with path induction.  If [e] is an equivalence from [a = b] to [X], then to prove [forall x, P x] it is enough to prove [forall p : a = b, P (e p)], and so by path induction it suffices to prove [P (e 1)]. The idiom for using this is to first [revert b X], which allows Coq to determine the family [P]. After using this, [b] will be replaced by [a] in the goal. *)
Definition equiv_path_ind {A} {a : A} {X : A -> Type}
           (e : forall (b : A), a = b <~> X b)
           (P : forall (b : A), X b -> Type)
           (r : P a (e a 1))
  : forall (b : A) (x : X b), P b x.
Proof.
  intro b.
  srapply (equiv_ind (e b)).
  intros [].
  exact r.
Defined.

(** [equiv_composeR'], a flipped version of [equiv_compose'], is (like [concatR]) most often useful partially applied, to give the “first half” of an equivalence one is constructing and leave the rest as a subgoal. One could similarly define [equiv_composeR] as a flip of [equiv_compose], but it doesn’t seem so useful since it doesn’t leave the remaining equivalence as a subgoal. *)
Definition equiv_composeR' {A B C} (f : A <~> B) (g : B <~> C)
  := equiv_compose' g f.

(* Shouldn't this become transitivity mid ? *)
Ltac equiv_via mid :=
  apply @equiv_composeR' with (B := mid).

(** It's often convenient when constructing a chain of equivalences to use [equiv_compose'], etc.  But when we treat an [Equiv] object constructed in that way as a function, via the coercion [equiv_fun], Coq sometimes needs a little help to realize that the result is the same as ordinary composition.  This tactic provides that help. *)
Ltac ev_equiv :=
  repeat match goal with
           | [ |- context[equiv_fun (equiv_inverse (equiv_inverse ?f))] ] =>
             change (equiv_fun (equiv_inverse (equiv_inverse f))) with (equiv_fun f)
           | [ |- context[(@equiv_inv ?B ?A (equiv_fun (equiv_inverse ?f)) ?iseq)] ] =>
             change (@equiv_inv B A (equiv_fun (equiv_inverse f)) iseq) with (equiv_fun f)
           | [ |- context[((equiv_fun ?f)^-1)^-1] ] =>
             change ((equiv_fun f)^-1)^-1 with (equiv_fun f)
           | [ |- context[equiv_fun (equiv_compose' ?g ?f) ?a] ] =>
             change (equiv_fun (equiv_compose' g f) a) with (g (f a))
           | [ |- context[equiv_fun (equiv_compose ?g ?f) ?a] ] =>
             change (equiv_fun (equiv_compose g f) a) with (g (f a))
           | [ |- context[equiv_fun (equiv_inverse ?f) ?a] ] =>
             change (equiv_fun (equiv_inverse f) a) with (f^-1 a)
           | [ |- context[equiv_fun (equiv_compose' ?g ?f)] ] =>
             change (equiv_fun (equiv_compose' g f)) with (g o f)
           | [ |- context[equiv_fun (equiv_compose ?g ?f)] ] =>
             change (equiv_fun (equiv_compose g f)) with (g o f)
           | [ |- context[equiv_fun (equiv_inverse ?f)] ] =>
             change (equiv_fun (equiv_inverse f)) with (f^-1)
         end.

(** ** Building equivalences between nested sigma and record types *)

(** The following tactic [make_equiv] builds an equivalence between two types built out of arbitrarily nested sigma and record types, not necessarily right-associated, as long as they have all the same underyling components.  This is more general than [issig] in that it doesn't just prove equivalences between a single record type and a single right-nested tower of sigma types, but less powerful in that it can't deduce the latter nested tower of sigmas automatically: you have to have both sides of the equivalence known. *)

(* Perform [intros] repeatedly, recursively destructing all possibly-nested record types. We use a custom induction principle for [Contr], since [elim] produces two goals. The [hnf] is important, for example to unfold [IsUnitPreserving] to an equality, which the [lazymatch] then ignores. *)
Ltac decomposing_intros :=
  let x := fresh in
  intros x; hnf in x; cbn in x;
  try lazymatch type of x with
  | ?a = ?b => idtac           (** Don't destruct paths *)
  | forall y:?A, ?B => idtac   (** Don't apply functions *)
  | Contr ?A => revert x; match goal with |- (forall y, ?P y) => snrefine (Contr_ind A P _) end
  | _ => elim x; clear x
  end;
  try decomposing_intros.

(* A multi-success version of [assumption].  That is, like [assumption], but if there are multiple hypotheses that match the type of the goal, then after choosing the first one, if a later tactic fails we can backtrack and choose another one. *)
Ltac multi_assumption :=
  multimatch goal with
    (* If we wrote [ H : ?A |- ?A ] here instead, it would prevent Coq from choosing an assumption that would require instantiating evars, which it has to do in the contr_basedpaths case below. *)
    [ H : ?A |- _ ] => exact H
  end.

(* Build an element of a possibly-nested record type out of hypotheses in the context. *)
Ltac build_record :=
  cbn; multi_assumption + (unshelve econstructor; build_record).

(* Construct an equivalence between two possibly-nested record/sigma types that differ only by associativity and permutation of their components.  We could use [Build_Equiv] and directly construct [eisadj] by decomposing to reflexivity as well, but often with large nested types it seems to be faster to adjointify. *)
Ltac make_equiv :=
  snrefine (equiv_adjointify _ _ _ _);
    [ decomposing_intros; build_record
    | decomposing_intros; build_record
    | decomposing_intros; exact idpath
    | decomposing_intros; exact idpath ].

(** In case anyone ever needs it, here's the version that doesn't adjointify. It's not the default, because it can be slow. *)
Ltac make_equiv_without_adjointification :=
  snrefine (Build_Equiv _ _ _ _);
    [ decomposing_intros; build_record |
      snrefine (Build_IsEquiv _ _ _ _ _ _ _);
      [ decomposing_intros; build_record
      | decomposing_intros; exact idpath
      | decomposing_intros; exact idpath
      | decomposing_intros; exact idpath ] ].

(** Here are some examples of the use of this tactic that you can uncomment and explore. *)

(**
<<
Goal forall (A : Type) (B : A -> Type) (C : forall a:A, B a -> Type) (D : forall (a:A) (b:B a), C a b -> Type),
     { ab : {a : A & B a } & { c : C ab.1 ab.2 & D ab.1 ab.2 c } }
     <~> { a : A & { bc : { b : B a & C a b } & D a bc.1 bc.2 } }.
  intros A B C D.
  make_equiv.
  Undo.
  (** Here's the eventually successful proof script produced by [make_equiv], extracted from [Info 0 make_equiv] and prettified, so you can step through it and see how the tactic works. *)
  snrefine (equiv_adjointify _ _ _ _).
  - (** Here begins [decomposing_intros] *)
    intros x; cbn in x.
    elim x; clear x.
    intros x; cbn in x.
    elim x; clear x.
    intros a; cbn in a.
    intros b; cbn in b.
    intros x; cbn in x.
    elim x; clear x.
    intros c; cbn in c. 
    intros d; cbn in d.
    (** Here begins [build_record] *)
    cbn; unshelve econstructor.
    { cbn; exact a. }
    { cbn; unshelve econstructor.
      { cbn; unshelve econstructor.
        { cbn; exact b. }
        { cbn; exact c. } }
      { cbn; exact d. } }
  - intros x; cbn in x.
    elim x; clear x.
    intros a; cbn in a.
    intros x; cbn in x.
    elim x; clear x.
    intros x; cbn in x.
    elim x; clear x. 
    intros b; cbn in b.
    intros c; cbn in c.
    intros d; cbn in d.
    cbn; unshelve econstructor.
    { cbn; unshelve econstructor.
      { cbn; exact a. }
      { cbn; exact b. } }
    { cbn; unshelve econstructor.
      { cbn; exact c. }
      { cbn; exact d. } }
  - intros x; cbn in x.
    elim x; clear x.
    intros a; cbn in a.
    intros x; cbn in x.
    elim x; clear x.
    intros x; cbn in x.
    elim x; clear x. 
    intros b; cbn in b.
    intros c; cbn in c.
    intros d; cbn in d.
    cbn; exact idpath.
  - intros x; cbn in x.
    elim x; clear x.
    intros x; cbn in x.
    elim x; clear x.
    intros a; cbn in a.
    intros b; cbn in b.
    intros x; cbn in x.
    elim x; clear x.
    intros c; cbn in c. 
    intros d; cbn in d.
    cbn; exact idpath.
Defined.
>>
*)

(** Here is an example illustrating the need for [multi_assumption] instead of just [assumption]. *)
(**
<<
Goal forall (A:Type) (R:A->A->Type),
    { x : A & { y : A & R x y } } <~> { xy : A * A & R (fst xy) (snd xy) }.
  intros A R.
  make_equiv.
  Undo.
  snrefine (equiv_adjointify _ _ _ _).
  - intros x; cbn in x.
    elim x; clear x.
    intros a1; cbn in a1.
    intros x; cbn in x.
    elim x; clear x.
    intros a2; cbn in a2.
    intros r; cbn in r.
    cbn; unshelve econstructor.
    { cbn; unshelve econstructor. 
      { (** [build_record] can't guess at this point that it needs to use [a1] instead of [a2], and in fact it tries [a2] first; but later on, [exact r] fails in that case, causing backtracking to this point and a re-try with [a1].  *)
        cbn; exact a1. }
      { cbn; exact a2. } }
    cbn; exact r.
  - intros x; cbn in x.
    elim x; clear x.
    intros x; cbn in x.
    elim x; clear x.
    intros a1; cbn in a1.
    intros a2; cbn in a2.
    intros r; cbn in r.
    cbn; unshelve econstructor.
    { cbn; exact a1. }
    { cbn; unshelve econstructor.
      { cbn; exact a2. }
      { cbn; exact r. } }
  - intros x; cbn in x.
    elim x; clear x.
    intros x; cbn in x.
    elim x; clear x.
    intros a1; cbn in a1.
    intros a2; cbn in a2.
    intros r; cbn in r.
    cbn; exact idpath.
  - intros x; cbn in x.
    elim x; clear x.
    intros a1; cbn in a1.
    intros x; cbn in x.
    elim x; clear x.
    intros a2; cbn in a2.
    intros r; cbn in r.
    cbn; exact idpath.
Defined.
>>
*)

(** Some "real-world" examples where [make_equiv] simplifies things a lot include the associativity/symmetry proofs in [Types/Sigma.v], [issig_pequiv'] in [Pointed/pEquiv.v], and [loop_susp_adjoint] in [Pointed/pSusp.v]. *)

(** Now we give a version of [make_equiv] that can also prove equivalences of nested sigma- and record types that involve contracting based path-spaces on either or both sides.  The basepoint and the path don't have to appear together, but can be in arbitrarily separated parts of the nested structure.  It does this by selectively applying path-induction to based paths appearing on both sides, if needed. *)

(** We start with a version of [decomposing_intros] that is willing to destruct paths, though as a second choice. *)
Ltac decomposing_intros_with_paths :=
  let x := fresh in
  intros x; hnf in x; cbn in x;
  multimatch type of x with
  | _ =>
    try match type of x with
        | (** Don't destruct paths at first *)
          ?a = ?b => fail 1
        | (** Don't apply functions at first *)
          forall y:?A, ?B => fail 1
        | _ => elim x; clear x
        end;
    try decomposing_intros_with_paths
  | ?a = ?b =>
    (** Destruct paths as a second choice.  But sometimes [destruct] isn't smart enough to generalize the other hypotheses that use the free endpoint, so we manually apply [paths_ind], or its right-handed version, instead. *)
    ((move x before b; (** Ensure that [b] and [x] come first in the [forall] goal resulting from [generalize dependent], so that [paths_ind] can apply to it. *)
      revert dependent b;
      assert_fails (move b at top); (** Check that [b] was actually reverted.  (If it's a section variable that the goal depends on, [generalize dependent b] will "succeed", but actually fail to generalize the goal over [b] (since that can't be done within the section) and not clear [b] from the context.)  *)
      refine (paths_ind _ _ _)) +
     (** Try the other endpoint too. *)
     (move x before a;
      revert dependent a;
      assert_fails (move a at top);
      refine (paths_ind_r _ _ _)));
    try decomposing_intros_with_paths
  end.

(** Going the other direction, we have to be willing to insert identity paths to fill in the based path-spaces that got destructed.  In fact [econstructor] is already willing to do that, since [idpath] is the constructor of [paths].  However, our previous [build_record] won't manage to get to the point of being able to apply [econstructor] to the necessary paths, since it'll get stuck earlier on trying to find the basepoint.  Thus, we give a version of [build_record] that is willing to create existential variables ("evars") for goals that it can't solve, in hopes that a later [idpath] (produced by [econstructor]) will determine them by unification.  Note that if there are other fields that depend on the basepoint that occur before the [idpath], the evar will -- and, indeed, must -- get instantiated by them instead.  This is why [multi_assumption], above, must be willing to instantiate evars. *)
Ltac build_record_with_evars :=
  (cbn; multi_assumption + (unshelve econstructor; build_record_with_evars)) +
  (** Create a fresh evar to solve this goal *)
  (match goal with
     |- ?G => let x := fresh in evar (x : G); exact x
   end; build_record_with_evars).

(** Now here's the improved version of [make_equiv]. *)
Ltac make_equiv_contr_basedpaths :=
  snrefine (equiv_adjointify _ _ _ _);
    (** [solve [ unshelve TAC ]] ensures that [TAC] succeeds without leaving any leftover evars. *)
    [ decomposing_intros_with_paths; solve [ unshelve build_record_with_evars ]
    | decomposing_intros_with_paths; solve [ unshelve build_record_with_evars ]
    | decomposing_intros_with_paths; exact idpath
    | decomposing_intros_with_paths; exact idpath ].

(** As before, we give some examples. *)

(**
<<
Section Examples.
  Context (A : Type) (B : A -> Type) (a0 : A).
  Goal { a : A & { b : B a & a = a0 } } <~> B a0.
  Proof.
    make_equiv_contr_basedpaths.
    Undo.
    snrefine (equiv_adjointify _ _ _ _).
    - (** Here begins [decomposing_intros_with_paths] *)
      intros x; cbn in x.
      elim x; clear x.
      intros a; cbn in a.
      intros x; cbn in x. 
      elim x; clear x.
      intros b; cbn in b.
      intros p; cbn in p.
      (** [decomposing_intros] wouldn't be willing to destruct [p] here, because it's a path.  But [decomposing_intros_with_paths] will try it when all else fails. *)
      move p before a.
      generalize dependent a.
      not (move a at top).
      refine (paths_ind_r _ _ _).
      intros b; cbn in b.
      (** Here begins [build_record_with_evars] *)
      exact b.
    - (** Here begins [decomposing_intros_with_paths] *)
      intros b; cbn in b.
      (** Here begins [build_record_with_evars] *)
      cbn; unshelve econstructor.
      { let x := fresh in evar (x : A); exact x. }
      cbn; unshelve econstructor.
      { (** This instantiates the evar. *)
        exact b. }
      { cbn; unshelve econstructor. }
    - intros b; cbn in b.
      exact idpath.
    - intros x; cbn in x.
      elim x; clear x.
      intros a; cbn in a.
      intros x; cbn in x. 
      elim x; clear x.
      intros b; cbn in b.
      intros p; cbn in p.
      move p before a.
      generalize dependent a.
      not (move a at top).
      refine (paths_ind_r _ _ _).
      intros b; cbn in b.
      exact idpath.
  Defined.
End Examples.
>>
*)

(** Some "real-world" examples where [make_equiv_contr_basedpaths] simplifies things a lot include [hfiber_compose] in [HFiber.v], [hfiber_pullback_along] in [Limits/Pullback.v], and [equiv_Ocodeleft2plus] in [BlakersMassey.v]. *)
