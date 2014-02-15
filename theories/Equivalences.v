(* -*- mode: coq; mode: visual-line -*- *)
(** * Equivalences *)

Require Import Overture PathGroupoids.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** We now give many ways to construct equivalences.  In each case, we define an instance of the typeclass [IsEquiv] named [isequiv_X], followed by an element of the record type [Equiv] named [equiv_X].

   Whenever we need to assume, as a hypothesis, that a certain function is an equivalence, we do it by assuming separately a function and a proof of [IsEquiv].  This is more general than assuming an inhabitant of [Equiv], since the latter has an implicit coercion and an existing instance to give us the former automatically.  Moreover, implicit generalization makes it easy to assume a function and a proof of [IsEquiv]. *)

Generalizable Variables A B C f g.

(** The identity map is an equivalence. *)
Instance isequiv_idmap (A : Type) : IsEquiv idmap | 0 :=
  BuildIsEquiv A A idmap idmap (fun _ => 1) (fun _ => 1) (fun _ => 1).

Definition equiv_idmap (A : Type) : A <~> A := BuildEquiv A A idmap _.

Instance reflexive_equiv : Reflexive Equiv | 0 := equiv_idmap.

(** The composition of equivalences is an equivalence. *)
Instance isequiv_compose `{IsEquiv A B f} `{IsEquiv B C g}
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

(* The TypeClass [Transitive] has a different order of parameters than [equiv_compose].  Thus in declaring the instance we have to switch the order of arguments. *)
Instance transitive_equiv : Transitive Equiv | 0 :=
  fun _ _ _ f g => equiv_compose g f.


(** Anything homotopic to an equivalence is an equivalence. *)
Section IsEquivHomotopic.

  Context `(f : A -> B) `(g : A -> B).
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
    rewrite <- ap_compose; unfold compose; rewrite (concat_A1p (eisretr f) (h a)).
    apply whiskerR, eisadj.
  Qed.

  (* It's unclear to me whether this should be a declared instance.  Will it cause the unifier to spin forever searching for homotopies?  For now, we give it a very large priority number, which means that other instances will be preferred over this one. *)
  Global Instance isequiv_homotopic : IsEquiv g | 10000
    := BuildIsEquiv _ _ g (f ^-1) sect retr adj.

  Definition equiv_homotopic : A <~> B
    := BuildEquiv _ _ g isequiv_homotopic.

End IsEquivHomotopic.


(** The inverse of an equivalence is an equivalence. *)
Section EquivInverse.

  Context `{IsEquiv A B f}.
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
    rewrite <- (ap_compose f^-1 f); unfold compose.
    rewrite (concat_A1p (eisretr f) _).
    rewrite ap_pp, concat_p_pp.
    rewrite (concat_pp_V _ (ap f^-1 (eisretr f (f (f^-1 b))))).
    repeat rewrite <- ap_V; rewrite <- ap_pp.
    rewrite <- (concat_pA1 (fun y => (eissect f y)^) _).
    rewrite ap_compose', <- (ap_compose f^-1 f); unfold compose.
    rewrite <- ap_p_pp.
    rewrite (concat_A1p (eisretr f) _).
    rewrite concat_p_Vp.
    rewrite <- ap_compose; unfold compose.
    rewrite (concat_pA1_p (eissect f) _).
    rewrite concat_pV_p; apply concat_Vp.
  Qed.

  Global Instance isequiv_inverse : IsEquiv f^-1 | 1000
    := BuildIsEquiv B A f^-1 f (eissect f) (eisretr f) other_adj.
End EquivInverse.

(** [Equiv A B] is a symmetric relation. *)
Theorem equiv_inverse {A B : Type} : (A <~> B) -> (B <~> A).
Proof.
  intro e.
  exists (e^-1).
  apply isequiv_inverse.
Defined.

Instance symmetric_equiv : Symmetric Equiv | 0 := @equiv_inverse.

(** If [g \o f] and [f] are equivalences, so is [g]. *)
Instance cancelR_isequiv `{IsEquiv A B f} `{IsEquiv A C (g o f)}
  : IsEquiv g | 10000
:= isequiv_homotopic (compose (compose g f) f^-1) g
       (fun b => ap g (eisretr f b)).

Arguments cancelR_isequiv {_ _ _ _ _} g {_}.

Definition cancelR_equiv `{IsEquiv A B f} `{IsEquiv A C (g o f)}
  : B <~> C
:= BuildEquiv _ _ g (cancelR_isequiv g).

(** If [g \o f] and [g] are equivalences, so is [f]. *)
Instance cancelL_isequiv `{IsEquiv B C g} `{IsEquiv A C (g o f)}
  : IsEquiv f | 10000
:= isequiv_homotopic (compose g^-1 (compose g f)) f
       (fun a => eissect g (f a)).

Arguments cancelL_isequiv {_ _ _ _ _} f {_}.

Definition cancelL_equiv `{IsEquiv B C g} `{IsEquiv A C (g o f)}
  : A <~> B
:= BuildEquiv _ _ f (cancelL_isequiv f).

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
    repeat rewrite ap_pp, concat_p_pp; rewrite <- ap_compose; unfold compose.
    rewrite (concat_pA1 (fun b => (isretr b)^) (ap f (issect a)^)).
    repeat rewrite concat_pp_p; rewrite ap_V; apply moveL_Vp; rewrite concat_p1.
    rewrite concat_p_pp, <- ap_compose; unfold compose.
    rewrite (concat_pA1 (fun b => (isretr b)^) (isretr (f a))).
    rewrite concat_pV, concat_1p; reflexivity.
  Qed.

  (** We don't make this a typeclass instance, because we want to control when we are applying it. *)
  Definition isequiv_adjointify : IsEquiv f
    := BuildIsEquiv A B f g isretr issect' is_adjoint'.

  Definition equiv_adjointify : A <~> B
    := BuildEquiv A B f isequiv_adjointify.

End Adjointify.

(** Several lemmas useful for rewriting. *)
Definition moveR_E `{IsEquiv A B f} (x : A) (y : B) (p : x = f^-1 y)
  : (f x = y)
  := ap f p @ eisretr f y.

Definition moveL_E `{IsEquiv A B f} (x : A) (y : B) (p : f^-1 y = x)
  : (y = f x)
  := (eisretr f y)^ @ ap f p.

(** Equivalence preserves contractibility (which of course is trivial under univalence). *)
Lemma contr_equiv `(f : A -> B) `{IsEquiv A B f} `{Contr A}
  : Contr B.
Proof.
  exists (f (center A)).
  intro y.
  apply moveR_E.
  apply contr.
Qed.

Definition contr_equiv' `(f : A <~> B) `{Contr A}
  : Contr B
  := contr_equiv f.

(** Assuming function extensionality, composing with an equivalence is itself an equivalence *)

Instance isequiv_precompose `{Funext} {A B C : Type}
  (f : A -> B) `{IsEquiv A B f}
  : IsEquiv (fun g => @compose A B C g f) | 1000
  := isequiv_adjointify (fun g => @compose A B C g f)
    (fun h => @compose B A C h f^-1)
    (fun h => path_forall _ _ (fun x => ap h (eissect f x)))
    (fun g => path_forall _ _ (fun y => ap g (eisretr f y))).

Definition equiv_precompose `{Funext} {A B C : Type}
  (f : A -> B) `{IsEquiv A B f}
  : (B -> C) <~> (A -> C)
  := BuildEquiv _ _ (fun g => @compose A B C g f) _.

Definition equiv_precompose' `{Funext} {A B C : Type} (f : A <~> B)
  : (B -> C) <~> (A -> C)
  := BuildEquiv _ _ (fun g => @compose A B C g f) _.

Instance isequiv_postcompose `{Funext} {A B C : Type}
  (f : B -> C) `{IsEquiv B C f}
  : IsEquiv (fun g => @compose A B C f g) | 1000
  := isequiv_adjointify (fun g => @compose A B C f g)
    (fun h => @compose A C B f^-1 h)
    (fun h => path_forall _ _ (fun x => eisretr f (h x)))
    (fun g => path_forall _ _ (fun y => eissect f (g y))).

Definition equiv_postcompose `{Funext} {A B C : Type}
  (f : B -> C) `{IsEquiv B C f}
  : (A -> B) <~> (A -> C)
  := BuildEquiv _ _ (fun g => @compose A B C f g) _.

Definition equiv_postcompose' `{Funext} {A B C : Type} (f : B <~> C)
  : (A -> B) <~> (A -> C)
  := BuildEquiv _ _ (fun g => @compose A B C f g) _.


(** The function [equiv_rect] says that given an equivalence [f : A <~> B], and a hypothesis from [B], one may always assume that the hypothesis is in the image of [e].

In fibrational terms, if we have a fibration over [B] which has a section once pulled back along an equivalence [f : A <~> B], then it has a section over all of [B].  *)

Definition equiv_rect `{IsEquiv A B f} (P : B -> Type)
  : (forall x:A, P (f x)) -> forall y:B, P y
  := fun g y => transport P (eisretr f y) (g (f^-1 y)).

Arguments equiv_rect {A B} f {_} P _ _.

(** Using [equiv_rect], we define a handy little tactic which introduces a variable and simultaneously substitutes it along an equivalence. *)

Ltac equiv_intro E x :=
  match goal with
    | |- forall y, @?Q y =>
      refine (equiv_rect E Q _); intros x
  end.

(** [equiv_composeR'], a flipped version of [equiv_compose'], is (like [concatR]) most often useful partially applied, to give the “first half” of an equivalence one is constructing and leave the rest as a subgoal. One could similarly define [equiv_composeR] as a flip of [equiv_compose], but it doesn’t seem so useful since it doesn’t leave the remaining equivalence as a subgoal. *)
Definition equiv_composeR' {A B C} (f : A <~> B) (g : B <~> C)
  := equiv_compose' g f.

Ltac equiv_via mid :=
  apply @equiv_composeR' with (B := mid).
