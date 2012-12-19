(** * Equivalences -*- mode: coq; mode: visual-line -*- *)

Require Import Common Paths Fibrations Contractible.

Local Open Scope path_scope.
Local Open Scope contr_scope.

(** Homotopy equivalences are a central concept in homotopy type theory. Before we define equivalences, let us consider when two types [A] and [B] should be considered "the same".

   The first option is to require existence of [f : A -> B] and [g : B -> A] which are inverses of each other, up to homotopy.  Homotopically speaking, we should also require a certain condition on these homotopies, which is one of the triangle identities for adjunctions in category theory.  Thus, we call this notion an *adjoint equivalence*.

  The other triangle identity is provable from the first one, along with all the higher coherences, so it is reasonable to only assume one of them.  Moreover, as we will see, if we have maps which are inverses up to homotopy, it is always possible to make the triangle identity hold by modifying one of the homotopies.

   The second option is to use Vladimir Voevodsky's definition of an equivalence as a map whose homotopy fibers are contractible.  We call this notion a *homotopy bijection*.

   An interesting third option was suggested by André Joyal: a map [f] which has separate left and right homotopy inverses.  We call this notion a *homotopy isomorphism*.

   While the second option was the one used originally, and it is the most concise one, it makes more sense to use the first one in a formalized development, since it exposes most directly equivalence as a structure.  In particular, it is easier to extract directly from it the data of a homotopy inverse to [f], which is what we care about having most in practice.  Thus, adjoint equivalences are what we will refer to merely as *equivalences*. *)

(** Naming convention: we use [equiv] and [Equiv] systematically to denote equivalences, and [is_equiv] and [IsEquiv] systematically to denote the assertion that a given map is an equivalence. *)

(** The fact that [r] is a left inverse of [s]. It is called [cancel] in ssreflect. *)
Definition section {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

(** A record that includes the data making [f] into an adjoint equivalence. *)
Record IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  equiv_is_retraction : section equiv_inv f ; 
  equiv_is_section : section f equiv_inv ;
  equiv_is_adjoint : forall x : A,
    equiv_is_retraction (f x) = ap f (equiv_is_section x)
}.

(** A record that includes all the data of an adjoint equivalence. *)
Record Equiv A B := BuildEquiv' {
  equiv_fun :> A -> B ;
  equiv_isequiv :> IsEquiv equiv_fun
}.

(* Putting together an [Equiv] with a single function. *)
Definition BuildEquiv A B (f : A -> B) (g : B -> A)
  (is_retr : section g f) (is_sect : section f g)
  (is_adj : forall x:A, is_retr (f x) = ap f (is_sect x))
  : Equiv A B
  := BuildEquiv' A B f (BuildIsEquiv A B f g is_retr is_sect is_adj).

Delimit Scope equiv_scope with equiv.
Local Open Scope equiv_scope.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.

(** We use the canonical structures to recover the equivalence structure of a map which is canonically known to be an equivalence. *)

Definition equiv_of A B := 
  fun (f : A -> B) (e : A <~> B) (_ : (f = e :> (A -> B))) => e.

Notation "[ 'equiv' 'of' f ]" := (equiv_of _ _ f _ (idpath _))
  (at level 0, format "[ 'equiv'  'of'  f ]") : equiv_scope.

(** Now we want to define the inverse of an equivalence, which should be another equivalence.  Eventually, we should do this carefully, but unfortunately it is very tricky to prove that the other triangle identity holds.  Thus, for now we are lazy and invoke instead the following "adjointification" theorem.

   The adjointification theorem says that if we have all the data of an (adjoint) equivalence except the triangle identity, then we can always obtain the triangle identity by modifying the datum [equiv_is_section] (or [equiv_is_retraction]).  The proof is the same as the standard categorical argument that any equivalence can be improved to an adjoint equivalence. *)

Section Adjointify.

  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (isretr : section g f) (issect : section f g).

  (* This is the modified [equiv_is_section]. *)
  Let issect' := fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

  (* We prove the triangle identity with rewrite tactics.  Since we lose control over the proof term that way, we make the result opaque with "Qed". *)
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

  Definition adjointify : A <~> B
    := BuildEquiv A B f g isretr issect' is_adjoint'.

End Adjointify.

(** As a side remark: when adjointifying, it suffices to have both a section and a retraction, even though they may be different maps.  A map with both a section and a retraction is called a "homotopy isomorphism".  As data, being a homotopy isomorphism is also homotopically well-behaved (unlike the ordinary input data to [adjointify]). *)

Definition equiv_hiso {A B : Type} (f : A -> B) (s r : B -> A)
  (issect : forall b, f (s b) = b) (isretr : forall a, r (f a) = a)
  : A <~> B
  := adjointify f s issect
  (fun a => (isretr (s (f a)))^ @ ap r (issect (f a)) @ isretr a).


(** Now we can define the inverse equivalence of an equivalence. *)

Definition equiv_inverse {A B : Type} (f : A <~> B) : (B <~> A)
  := adjointify (equiv_inv f f) f (equiv_is_section f f) (equiv_is_retraction f f).

Canonical Structure equiv_inverse.

Notation "f ^-1" := (@equiv_inverse _ _ f) (at level 3) : equiv_scope.

(* Now that we have the inverse being an equivalence, and a notation for it, we redefine [equiv_is_retraction] and [equiv_is_section] and [equiv_is_adjoint] so that they will recognize the notation [f ^-1]. *)

Definition eissect {A B} (f : A <~> B) (x : A) : f^-1 (f x) = x
  := equiv_is_section f _ x.

Definition eisretr {A B} (f : A <~> B) (y : B) : f (f^-1 y) = y
  := equiv_is_retraction f _ y.

Definition eisadj {A B} (f : A <~> B) (x : A) :
  eisretr f (f x) = ap f (eissect f x)
  := equiv_is_adjoint f _ x.


(** Now we move on to canonical constructions of equivalences. *)

(** The identity map is an equivalence. *)
Canonical Structure equiv_idmap (A : Type) :=
  BuildEquiv A A idmap idmap (fun _ => 1) (fun _ => 1) (fun _ => 1).

(** A contractible type is equivalent to [unit].  TODO: Does this really belong here, or should it be in Types/Unit.v ? *)
Definition equiv_contr_unit (A : Contr) : A <~> unit.
Proof.
  refine (BuildEquiv _ _
    (fun (_ : A) => tt)
    (fun (_ : unit) => [ center of A ])
    (fun t : unit => match t with tt => 1 end)
    (fun x : A => contr x) _).
  intro x. apply inverse, ap_const.
Defined.

Canonical Structure equiv_contr_unit.

(* A type equivalent to [unit] is contractible. TODO: Same. *)
Definition contr_equiv_unit (A : Type) (f : A <~> unit) : Contr
  := BuildContr A (f^-1 tt)
  (fun a => ap f^-1 (contr (f a)) @ eissect f a).

Canonical Structure contr_equiv_unit.

(** The composition of equivalences is an equivalence. *)
Definition is_equiv_compose {A B C : Type} (f : B <~> C) (e : A <~> B)
  : IsEquiv (compose f e)
  := BuildIsEquiv A C _
    (compose e^-1 f^-1)
    (fun c => ap f (eisretr e (f^-1 c)) @ eisretr f c)
    (fun a => ap (e^-1) (eissect f (e a)) @ eissect e a)
    (fun a =>
      (whiskerL _ (eisadj f (e a))) @
      (ap_pp f _ _)^ @
      ap02 f
      ( (concat_A1p (eisretr e) (eissect f (e a)))^ @
        (ap_compose e^-1 e _ @@ eisadj e a) @
        (ap_pp e _ _)^
      ) @
      (ap_compose e f _)^
    ).

Canonical Structure is_equiv_compose.

Definition equiv_compose {A B C : Type} (f : B <~> C) (e : A <~> B)
  : A <~> C
  := BuildEquiv' A C (compose f e) (is_equiv_compose f e).

Canonical Structure equiv_compose.

(** Anything homotopic to an equivalence is an equivalence. *)
Section IsEquivHomotopic.

  Context {A B : Type} (f : A <~> B) (g : A -> B).
  Context (H : forall a:A, f a = g a).

  Let sect := (fun b:B => (H (f^-1 b))^ @ eisretr f b).
  Let retr := (fun a:A => (ap f^-1 (H a))^ @ eissect f a).

  (* Opaque since we use rewrite tactics. *)
  Let adj (a : A) : sect (g a) = ap g (retr a).
  Proof.
    unfold sect, retr.
    rewrite ap_pp. apply moveR_Vp.
    rewrite concat_p_pp, <- concat_Ap, concat_pp_p, <- concat_Ap.
    rewrite ap_V; apply moveL_Vp.
    rewrite <- ap_compose; unfold compose; rewrite (concat_A1p (eisretr f) (H a)).
    apply cancelR, eisadj.
  Qed.

  Definition is_equiv_homotopic : IsEquiv g
    := BuildIsEquiv _ _ g (f ^-1) sect retr adj.

End IsEquivHomotopic.

Canonical Structure is_equiv_homotopic.

(** If [g \o f] and [f] are equivalences, so is [g]. *)
Definition is_equiv_cancelR {A B C} (f : A <~> B) (g : B -> C) :
  IsEquiv (compose g f) -> IsEquiv g
  := fun gfi =>
    let gf := BuildEquiv' _ _ (compose g f) gfi in
      let g' := equiv_compose gf f^-1 in
        is_equiv_homotopic g' g (fun b => ap g (eisretr f b)).

Canonical Structure is_equiv_cancelR.

(** If [g \o f] and [g] are equivalences, so is [f]. *)
Definition is_equiv_cancelL {A B C} (g : B <~> C) (f : A -> B) :
  IsEquiv (compose g f) -> IsEquiv f
  := fun gfi =>
    let gf := BuildEquiv' _ _ (compose g f) gfi in
      let f' := equiv_compose g^-1 gf in
        is_equiv_homotopic f' f (fun a => eissect g (f a)).

Canonical Structure is_equiv_cancelL.

(** If [f] is an equivalence, then so is [ap f].  Here again we are lazy and use [adjointify]. *)
Definition equiv_ap {A B : Type} (f : A <~> B) (x y : A)
  : (x = y) <~> (f x = f y)
  := adjointify (ap f)
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

Canonical Structure equiv_ap.

(** If [f] is an equivalence, then its homotopy fibers are contractible.  That is, it is a Voevodsky equivalence, or a homotopy bijection.  Probably the following two proofs should really be using some standard facts about paths in Sigma types.  *)

Definition contr_hfiber_of_equiv {A B : Type} (f : A <~> B) (b : B) : Contr.
Proof.
  assert (fp : forall (x x':A) (p:f x = b) (p':f x' = b)
      (q : x = x') (r : ap f q @ p' = p), (x;p) = (x';p') :> {x:A & f x = b}).
    intros x x' p p' q r; destruct q; apply ap; exact (r^ @ concat_1p _).
  refine (BuildContr {a:A & f a = b} (f^-1 b; eisretr f b) _).
  intros [a p].
  refine (fp (f^-1 b) a (eisretr f b) p ((ap f^-1 p)^ @ eissect f a) _).
  rewrite ap_pp, ap_V, <- ap_compose, concat_pp_p, <- eisadj.
  apply moveR_Vp.
  exact ((concat_A1p (eisretr f) p)^).
Qed.

(* TODO: Why isn't this allowed? *)
(* Canonical Structure contr_hfiber_of_equiv. *)

(** The converse is also true. *)
Definition is_contr (A : Type) := { x:A & forall (y:A), x = y }.

Definition equiv_is_contr_hfibers {A B : Type} (f : A -> B)
  : (forall y:B, is_contr {x:A & f x = y})  ->  (A <~> B).
Proof.
  intros hfc.
  pose (g b := projT1 (projT1 (hfc b))).
  pose (isretr b := projT2 (projT1 (hfc b))).
  assert (sa : forall a, { issect : g (f a) = a & isretr (f a) = ap f issect }).
    intros a.
    assert (fp : forall (x x' : {x:A & f x = f a}) (q : x = x'),
        { p : projT1 x = projT1 x' & projT2 x = ap f p @ projT2 x' }).
      intros x _ []. exists 1; exact ((concat_1p _)^).
    set (r := fp (projT1 (hfc (f a))) (a;1) (projT2 (hfc (f a)) (a;1))).
    exact (projT1 r ; projT2 r @ concat_p1 _).
  exact (BuildEquiv _ _ f g isretr
    (fun a => projT1 (sa a)) (fun a => projT2 (sa a))).
Defined.

Canonical Structure equiv_is_contr_hfibers.

