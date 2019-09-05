(* -*- mode: coq; mode: visual-line -*- *)
(** * Equivalences *)

Require Import Basics.Overture Basics.PathGroupoids Basics.Notations Basics.Contractible.
Local Open Scope path_scope.

(** We now give many ways to construct equivalences.  In each case, we define an instance of the typeclass [IsEquiv] named [isequiv_X], followed by an element of the record type [Equiv] named [equiv_X].

   Whenever we need to assume, as a hypothesis, that a certain function is an equivalence, we do it by assuming separately a function and a proof of [IsEquiv].  This is more general than assuming an inhabitant of [Equiv], since the latter has an implicit coercion and an existing instance to give us the former automatically.  Moreover, implicit generalization makes it easy to assume a function and a proof of [IsEquiv]. *)

(** A word on naming: some of the lemmas about equivalences are analogues of those for paths in PathGroupoids.  We name them in an analogous way but adding [_equiv] in an appropriate place, e.g. instead of [moveR_M] we have [moveR_equiv_M].  *)

Generalizable Variables A B C f g.

(** The identity map is an equivalence. *)
Global Instance isequiv_idmap (A : Type) : IsEquiv idmap | 0 :=
  BuildIsEquiv A A idmap idmap (fun _ => 1) (fun _ => 1) (fun _ => 1).

Definition equiv_idmap (A : Type) : A <~> A := BuildEquiv A A idmap _.

Arguments equiv_idmap {A} , A.

Notation "1" := equiv_idmap : equiv_scope.

Global Instance reflexive_equiv : Reflexive Equiv | 0 := @equiv_idmap.

(** The composition of equivalences is an equivalence. *)
Global Instance isequiv_compose `{IsEquiv A B f} `{IsEquiv B C g}
  : IsEquiv (compose g f) | 1000
  := BuildIsEquiv A C (compose g f)
    (compose f^-1 g^-1)
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
  := BuildEquiv A C (compose g f) _.

Definition equiv_compose' {A B C : Type} (g : B <~> C) (f : A <~> B)
  : A <~> C
  := equiv_compose g f.

(** We put [g] and [f] in [equiv_scope] explcitly.  This is a partial work-around for https://coq.inria.fr/bugs/show_bug.cgi?id=3990, which is that implicitly bound scopes don't nest well. *)
Notation "g 'oE' f" := (equiv_compose' g%equiv f%equiv) : equiv_scope.

(* The TypeClass [Transitive] has a different order of parameters than [equiv_compose].  Thus in declaring the instance we have to switch the order of arguments. *)
Global Instance transitive_equiv : Transitive Equiv | 0 :=
  fun _ _ _ f g => equiv_compose g f.

Ltac change_apply_equiv_compose :=
  match goal with
  | [ |- context [ equiv_fun (?f oE ?g) ?x ] ] =>
    change ((f oE g) x) with (f (g x))
  end.

(** Anything homotopic to an equivalence is an equivalence. *)
Section IsEquivHomotopic.

  Context {A B : Type} (f : A -> B) {g : A -> B}.
  Context `{IsEquiv A B f}.
  Hypothesis h : f == g.

  Let sect := (fun b:B => (h (f^-1 b))^ @ eisretr f b).
  Let retr := (fun a:A => (ap f^-1 (h a))^ @ eissect f a).

  (* We prove the triangle identity with rewrite tactics.  Since we lose control over the proof term that way, we make the result opaque with "Qed". *)
  Let adj (a : A) : sect (g a) = ap g (retr a).
  Proof.
    unfold sect, retr.
    rewrite ap_pp. apply moveR_Vp.
    rewrite concat_p_pp, <- concat_Ap, concat_pp_p, <- concat_Ap.
    rewrite ap_V; apply moveL_Vp.
    rewrite <- ap_compose; rewrite (concat_A1p (eisretr f) (h a)).
    apply whiskerR, eisadj.
  Qed.

  (* This should not be an instance; it can cause the unifier to spin forever searching for functions to be hoomotpic to. *)
  Definition isequiv_homotopic : IsEquiv g
    := BuildIsEquiv _ _ g (f ^-1) sect retr adj.

  Definition equiv_homotopic : A <~> B
    := BuildEquiv _ _ g isequiv_homotopic.

End IsEquivHomotopic.


(** The inverse of an equivalence is an equivalence. *)
Section EquivInverse.

  Context {A B : Type} (f : A -> B) {feq : IsEquiv f}.
  Open Scope long_path_scope.

  Theorem other_adj (b : B) : eissect f (f^-1 b) = ap f^-1 (eisretr f b).
  Proof.
    (* First we set up the mess. *)
    rewrite <- (concat_1p (eissect _ _)).
    rewrite <- (concat_Vp (ap f^-1 (eisretr f (f (f^-1 b))))).
    rewrite (whiskerR (inverse2 (ap02 f^-1 (eisadj f (f^-1 b)))) _).
    refine (whiskerL _ (concat_1p (eissect _ _))^ @ _).
    rewrite <- (concat_Vp (eissect f (f^-1 (f (f^-1 b))))).
    rewrite <- (whiskerL _ (concat_1p (eissect f (f^-1 (f (f^-1 b)))))).
    rewrite <- (concat_pV (ap f^-1 (eisretr f (f (f^-1 b))))).
    apply moveL_M1.
    repeat rewrite concat_p_pp.
    (* Now we apply lots of naturality and cancel things. *)
    rewrite <- (concat_pp_A1 (fun a => (eissect f a)^) _ _).
    rewrite (ap_compose' f f^-1).
    rewrite <- (ap_p_pp _ _ (ap f (ap f^-1 (eisretr f (f (f^-1 b))))) _).
    rewrite <- (ap_compose f^-1 f).
    rewrite (concat_A1p (eisretr f) _).
    rewrite ap_pp, concat_p_pp.
    rewrite (concat_pp_V _ (ap f^-1 (eisretr f (f (f^-1 b))))).
    repeat rewrite <- ap_V; rewrite <- ap_pp.
    rewrite <- (concat_pA1 (fun y => (eissect f y)^) _).
    rewrite ap_compose', <- (ap_compose f^-1 f).
    rewrite <- ap_p_pp.
    rewrite (concat_A1p (eisretr f) _).
    rewrite concat_p_Vp.
    rewrite <- ap_compose.
    rewrite (concat_pA1_p (eissect f) _).
    rewrite concat_pV_p; apply concat_Vp.
  Qed.

  Global Instance isequiv_inverse : IsEquiv f^-1 | 10000
    := BuildIsEquiv B A f^-1 f (eissect f) (eisretr f) other_adj.
End EquivInverse.

(** If the goal is [IsEquiv _^-1], then use [isequiv_inverse]; otherwise, don't pretend worry about if the goal is an evar and we want to add a [^-1]. *)
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

(** If [g \o f] and [f] are equivalences, so is [g].  This is not an Instance because it would require Coq to guess [f]. *)
Definition cancelR_isequiv {A B C} (f : A -> B) {g : B -> C}
  `{IsEquiv A B f} `{IsEquiv A C (g o f)}
  : IsEquiv g
  := isequiv_homotopic (compose (compose g f) f^-1)
       (fun b => ap g (eisretr f b)).

Definition cancelR_equiv {A B C} (f : A -> B) {g : B -> C}
  `{IsEquiv A B f} `{IsEquiv A C (g o f)}
  : B <~> C
  := BuildEquiv B C g (cancelR_isequiv f).

(** If [g \o f] and [g] are equivalences, so is [f]. *)
Definition cancelL_isequiv {A B C} (g : B -> C) {f : A -> B}
  `{IsEquiv B C g} `{IsEquiv A C (g o f)}
  : IsEquiv f
  := isequiv_homotopic (compose g^-1 (compose g f))
       (fun a => eissect g (f a)).

Definition cancelL_equiv {A B C} (g : B -> C) {f : A -> B}
  `{IsEquiv B C g} `{IsEquiv A C (g o f)}
  : A <~> B
  := BuildEquiv _ _ f (cancelL_isequiv g).

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

(** Transporting is an equivalence. *)
Section EquivTransport.

  Context {A : Type} (P : A -> Type) (x y : A) (p : x = y).

  Global Instance isequiv_transport : IsEquiv (transport P p) | 0
    := BuildIsEquiv (P x) (P y) (transport P p) (transport P p^)
    (transport_pV P p) (transport_Vp P p) (transport_pVp P p).

  Definition equiv_transport : P x <~> P y
    := BuildEquiv _ _ (transport P p) _.

End EquivTransport.

(** In all the above cases, we were able to directly construct all the structure of an equivalence.  However, as is evident, sometimes it is quite difficult to prove the adjoint law.

   The following adjointification theorem allows us to be lazy about this if we wish.  It says that if we have all the data of an (adjoint) equivalence except the triangle identity, then we can always obtain the triangle identity by modifying the datum [equiv_is_section] (or [equiv_is_retraction]).  The proof is the same as the standard categorical argument that any equivalence can be improved to an adjoint equivalence.

   As a stylistic matter, we try to avoid using adjointification in the library whenever possible, to preserve the homotopies specified by the user.  *)

Section Adjointify.

  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (isretr : Sect g f) (issect : Sect f g).

  (* This is the modified [eissect]. *)
  Let issect' := fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

  Let is_adjoint' (a : A) : isretr (f a) = ap f (issect' a).
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
    := BuildIsEquiv A B f g isretr issect' is_adjoint'.

  Definition equiv_adjointify : A <~> B
    := BuildEquiv A B f isequiv_adjointify.

End Adjointify.

Arguments isequiv_adjointify {A B}%type_scope (f g)%function_scope isretr issect.
Arguments equiv_adjointify {A B}%type_scope (f g)%function_scope isretr issect.

(** An involution is an endomap that is its own inverse. *)
Definition isequiv_involution {X : Type} (f : X -> X) (isinvol : Sect f f)
: IsEquiv f
  := isequiv_adjointify f f isinvol isinvol.

Definition equiv_involution {X : Type} (f : X -> X) (isinvol : Sect f f)
: X <~> X
  := equiv_adjointify f f isinvol isinvol.

(** Several lemmas useful for rewriting. *)
Definition moveR_equiv_M `{IsEquiv A B f} (x : A) (y : B) (p : x = f^-1 y)
  : (f x = y)
  := ap f p @ eisretr f y.

Definition moveL_equiv_M `{IsEquiv A B f} (x : A) (y : B) (p : f^-1 y = x)
  : (y = f x)
  := (eisretr f y)^ @ ap f p.

Definition moveR_equiv_V `{IsEquiv A B f} (x : B) (y : A) (p : x = f y)
  : (f^-1 x = y)
  := ap (f^-1) p @ eissect f y.

Definition moveL_equiv_V `{IsEquiv A B f} (x : B) (y : A) (p : f y = x)
  : (y = f^-1 x)
  := (eissect f y)^ @ ap (f^-1) p.

(** Equivalence preserves contractibility (which of course is trivial under univalence). *)
Lemma contr_equiv A {B} (f : A -> B) `{IsEquiv A B f} `{Contr A}
  : Contr B.
Proof.
  exists (f (center A)).
  intro y.
  apply moveR_equiv_M.
  apply contr.
Qed.

Definition contr_equiv' A {B} `(f : A <~> B) `{Contr A}
  : Contr B
  := contr_equiv A f.

(** Any two contractible types are equivalent. *)
Global Instance isequiv_contr_contr {A B : Type}
       `{Contr A} `{Contr B} (f : A -> B)
  : IsEquiv f
  := BuildIsEquiv _ _ f (fun _ => (center A))
                  (fun x => path_contr _ _)
                  (fun x => path_contr _ _)
                  (fun x => path_contr _ _).

Lemma equiv_contr_contr {A B : Type} `{Contr A} `{Contr B}
  : (A <~> B).
Proof.
  apply equiv_adjointify with (fun _ => center B) (fun _ => center A);
  intros ?; apply contr.
Defined.

(** The projection from the sum of a family of contractible types is an equivalence. *)
Global Instance isequiv_pr1 {A : Type} (P : A -> Type) `{forall x, Contr (P x)}
  : IsEquiv (@pr1 A P).
Proof.
  apply (BuildIsEquiv
           _ _ (@pr1 A P)
           (fun x => (x ; center (P x)))
           (fun x => 1)
           (fun xy => match xy with
                      | existT x y => ap (exist _ x) (contr _)
                      end)).
  intros [x y].
  rewrite <- ap_compose.
  symmetry; apply ap_const.
Defined.

Definition equiv_pr1 {A : Type} (P : A -> Type) `{forall x, Contr (P x)}
  : { x : A & P x } <~> A
  := BuildEquiv _ _ (@pr1 A P) _.


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
  := BuildEquiv _ _ (fun (g:B->C) => g o f) _.

Definition equiv_precompose' `{Funext} {A B C : Type} (f : A <~> B)
  : (B -> C) <~> (A -> C)
  := BuildEquiv _ _ (fun (g:B->C) => g o f) _.

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
  := BuildEquiv _ _ (fun (g:A->B) => f o g) _.

Definition equiv_postcompose' `{Funext} {A B C : Type} (f : B <~> C)
  : (A -> B) <~> (A -> C)
  := BuildEquiv _ _ (fun (g:A->B) => f o g) _.

(** Conversely, if pre- or post-composing with a function is always an equivalence, then that function is also an equivalence.  It's convenient to know that we only need to assume the equivalence when the other type is the domain or the codomain. *)

Definition isequiv_isequiv_precompose {A B : Type} (f : A -> B)
  (precomp := (fun (C : Type) (h : B -> C) => h o f))
  (Aeq : IsEquiv (precomp A)) (Beq : IsEquiv (precomp B))
  : IsEquiv f.
Proof.
  assert (H : forall (C D : Type)
                     (Ceq : IsEquiv (precomp C)) (Deq : IsEquiv (precomp D))
                     (k : C -> D) (h : A -> C),
                k o (precomp C)^-1 h = (precomp D)^-1 (k o h)).
  { intros C D ? ? k h.
    transitivity ((precomp D)^-1 (k o (precomp C ((precomp C)^-1 h)))).
    - transitivity ((precomp D)^-1 (precomp D (k o ((precomp C)^-1 h)))).
      + rewrite (eissect (precomp D) _); reflexivity.
      + reflexivity.
    - rewrite (eisretr (precomp C) h); reflexivity. }
  refine (isequiv_adjointify f ((precomp A)^-1 idmap) _ _).
  - intros x.
    change ((f o (precomp A)^-1 idmap) x = idmap x).
    apply ap10.
    rewrite (H A B Aeq Beq).
    change ((precomp B)^-1 (precomp B idmap) = idmap).
    apply eissect.
  - intros x.
    change ((precomp A ((precomp A)^-1 idmap)) x = idmap x).
    apply ap10, eisretr.
Qed.

(*
Definition isequiv_isequiv_postcompose {A B : Type} (f : A -> B)
  (postcomp := (fun (C : Type) (h : C -> A) => f o h))
  (feq : forall C:Type, IsEquiv (postcomp C))
  : IsEquiv f.
(* TODO *)
*)

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

(** Using [equiv_ind], we define a handy little tactic which introduces a variable and simultaneously substitutes it along an equivalence. *)

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

(** [equiv_composeR'], a flipped version of [equiv_compose'], is (like [concatR]) most often useful partially applied, to give the “first half” of an equivalence one is constructing and leave the rest as a subgoal. One could similarly define [equiv_composeR] as a flip of [equiv_compose], but it doesn’t seem so useful since it doesn’t leave the remaining equivalence as a subgoal. *)
Definition equiv_composeR' {A B C} (f : A <~> B) (g : B <~> C)
  := equiv_compose' g f.

(* Shouldn't this become transitivity mid ? *)
Ltac equiv_via mid :=
  apply @equiv_composeR' with (B := mid).

(** It's often convenient when constructing a chain of equivalences to use [equiv_compose'], etc.  But when we treat an [Equiv] object constructed in that way as a function, via the coercion [equiv_fun], Coq sometimes needs a little help to realize that the result is the same as ordinary composition.  This tactic provides that help. *)
Ltac ev_equiv :=
  repeat match goal with
           | [ |- context[equiv_fun (equiv_compose' ?g ?f) ?a] ] =>
             change ((equiv_compose' g f) a) with (g (f a))
           | [ |- context[equiv_fun (equiv_compose ?g ?f) ?a] ] =>
             change ((equiv_compose g f) a) with (g (f a))
           | [ |- context[equiv_fun (equiv_inverse ?f) ?a] ] =>
             change ((equiv_inverse f) a) with (f^-1 a)
         end.
