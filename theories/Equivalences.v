(** * Equivalences -*- mode: coq; mode: visual-line -*- *)

Require Import Common Paths Fibrations Contractible.

Local Open Scope path_scope.

(** Homotopy equivalences are a central concept in homotopy type theory. Before we define equivalences, let us consider when two types [A] and [B] should be considered "the same".

   The first option is to require existence of [f : A -> B] and [g : B -> A] which are inverses of each other, up to homotopy.  Homotopically speaking, we should also require a certain condition on these homotopies, which is one of the triangle identities for adjunctions in category theory.  Thus, we call this notion an *adjoint equivalence*.

  The other triangle identity is provable from the first one, along with all the higher coherences, so it is reasonable to only assume one of them.  Moreover, as we will see, if we have maps which are inverses up to homotopy, it is always possible to make the triangle identity hold by modifying one of the homotopies.

   The second option is to use Vladimir Voevodsky's definition of an equivalence as a map whose homotopy fibers are contractible.  We call this notion a *homotopy bijection*.

   An interesting third option was suggested by André Joyal: a map [f] which has separate left and right homotopy inverses.  We call this notion a *homotopy isomorphism*.

   While the second option was the one used originally, and it is the most concise one, it makes more sense to use the first one in a formalized development, since it exposes most directly equivalence as a structure.  In particular, it is easier to extract directly from it the data of a homotopy inverse to [f], which is what we care about having most in practice.  Thus, adjoint equivalences are what we will refer to merely as *equivalences*. *)

(** Naming convention: we use [equiv] and [Equiv] systematically to denote types of equivalences, and [isequiv] and [IsEquiv] systematically to denote the assertion that a given map is an equivalence. *)

(** The fact that [r] is a left inverse of [s]. It is called [cancel] in ssreflect.  As a mnemonic, note that the partially applied type [Sect s] is the type of proofs that [s] is a section. *)
Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

(** A typeclass that includes the data making [f] into an adjoint equivalence. *)
Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.

(** A record that includes all the data of an adjoint equivalence. *)
Record Equiv A B := BuildEquiv {
  equiv_fun :> A -> B ;
  equiv_isequiv :> IsEquiv equiv_fun
}.

Existing Instance equiv_isequiv.

Delimit Scope equiv_scope with equiv.
Local Open Scope equiv_scope.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.

(** A notation for the inverse of an equivalence.  We can apply this to a function as long as there is a typeclass instance asserting it to be an equivalence.  We can also apply it to an element of [A <~> B], since there is an implicit coercion to [A -> B] and also an existing instance of [IsEquiv]. *)

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3) : equiv_scope.


(** We now give many ways to construct equivalences.  In each case, we define an instance of the typeclass [IsEquiv] named [isequiv_X], followed by an element of the record type [Equiv] named [equiv_X].

   Whenever we need to assume, as a hypothesis, that a certain function is an equivalence, we do it by assuming separately a function and a proof of [IsEquiv].  This is more general than assuming an inhabitant of [Equiv], since the latter has an implicit coercion and an existing instance to give us the former automatically.  Moreover, implicit generalization makes it easy to assume a function and a proof of [IsEquiv]. *)

Generalizable Variables A B C f g.

(** The identity map is an equivalence. *)
Instance isequiv_idmap (A : Type) : IsEquiv idmap :=
  BuildIsEquiv A A idmap idmap (fun _ => 1) (fun _ => 1) (fun _ => 1).

Definition equiv_idmap (A : Type) : A <~> A := BuildEquiv A A idmap _.

(** The composition of equivalences is an equivalence. *)
Instance isequiv_compose `{IsEquiv A B f} `{IsEquiv B C g}
  : IsEquiv (compose g f)
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

Definition equiv_compose `{IsEquiv B C g} `{IsEquiv A B f}
  : A <~> C
  := BuildEquiv A C (compose g f) _.

(** Anything homotopic to an equivalence is an equivalence. *)
Section IsEquivHomotopic.

  Context `(f : A -> B) `(g : A -> B).
  Context `{IsEquiv A B f}.
  Context (h : forall a:A, f a = g a).

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
    apply cancelR, eisadj.
  Qed.

  (* It's unclear to me whether this should be a declared instance.  Will it cause the unifier to spin forever searching for homotopies? *)
  Global Instance isequiv_homotopic : IsEquiv g
    := BuildIsEquiv _ _ g (f ^-1) sect retr adj.

  Definition equiv_homotopic : A <~> B
    := BuildEquiv _ _ g isequiv_homotopic.

End IsEquivHomotopic.


(** The inverse of an equivalence is an equivalence. *)
Section EquivInverse.

  Context `{IsEquiv A B f}.
  Open Scope long_path_scope.

  Let other_adj (b : B) : eissect f (f^-1 b) = ap f^-1 (eisretr f b).
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

  Global Instance isequiv_inverse : IsEquiv f^-1
    := BuildIsEquiv B A f^-1 f (eissect f) (eisretr f) other_adj.

  Definition equiv_inverse : (B <~> A)
    := BuildEquiv B A f^-1 _.

End EquivInverse.

(** If [g \o f] and [f] are equivalences, so is [g]. *)
Section EquivCancelR.

  Context `{fe : IsEquiv A B f} `(g : B -> C).
  Context `{gfe : IsEquiv A C (compose g f)}.
  Existing Instance fe.
  Existing Instance gfe.

  (* Same question as with isequiv_homotopic. *)
  Global Instance isequiv_cancelR : IsEquiv g
  := isequiv_homotopic (compose (compose g f) f^-1) g
       (fun b => ap g (eisretr f b)).

  Definition equiv_cancelR : B <~> C
    := BuildEquiv _ _ g isequiv_cancelR.

End EquivCancelR.

(** If [g \o f] and [g] are equivalences, so is [f]. *)
Section EquivCancelL.

  Context `{IsEquiv B C g} `(f : A -> B).
  Context `{IsEquiv A C (compose g f)}.

  (* Same question as with isequiv_homotopic. *)
  Global Instance isequiv_cancelL : IsEquiv f
  := isequiv_homotopic (compose g^-1 (compose g f)) f
       (fun a => eissect g (f a)).

  Definition equiv_cancelL : A <~> B
    := BuildEquiv _ _ f isequiv_cancelL.

End EquivCancelL.

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

(** As a side remark: when adjointifying, it suffices to have both a section and a retraction, even though they may be different maps.  A map with both a section and a retraction is called a "homotopy isomorphism".  As data, being a homotopy isomorphism is also homotopically well-behaved (unlike the ordinary input data to [adjointify]). *)

Section HIso.

  Context {A B : Type} (f : A -> B) (s r : B -> A).
  Context (isretr : Sect s f) (issect : Sect f r).

  Definition isequiv_hiso : IsEquiv f
    := isequiv_adjointify f s isretr
         (fun a => (issect (s (f a)))^ @ ap r (isretr (f a)) @ issect a).

  Definition equiv_hiso : A <~> B
    := BuildEquiv A B f isequiv_hiso.

End HIso.


(** If [f] is an equivalence, then so is [ap f].  Here again we are lazy and use [adjointify]. *)
Instance isequiv_ap `{IsEquiv A B f} (x y : A)
  : IsEquiv (@ap A B f x y)
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

Definition equiv_ap `{IsEquiv A B f} (x y : A)
  : (x = y) <~> (f x = f y)
  := BuildEquiv _ _ (ap f) _.
  
(** If [f] is an equivalence, then its homotopy fibers are contractible.  That is, it is a Voevodsky equivalence, or a homotopy bijection.  Probably the following two proofs should really be using some standard facts about paths in Sigma types.  *)

Instance contr_hfiber_equiv `(IsEquiv A B f) (b : B)
  : Contr {a:A & f a = b}.
Proof.
  assert (fp : forall (x x':A) (p:f x = b) (p':f x' = b)
      (q : x = x') (r : ap f q @ p' = p), (x;p) = (x';p') :> {x:A & f x = b}).
    intros x x' p p' q r; destruct q; apply ap; exact (r^ @ concat_1p _).
  refine (BuildContr _ (f^-1 b; eisretr f b) _).
  intros [a p].
  refine (fp (f^-1 b) a (eisretr f b) p ((ap f^-1 p)^ @ eissect f a) _).
  rewrite ap_pp, ap_V, <- ap_compose, concat_pp_p, <- eisadj.
  apply moveR_Vp.
  exact ((concat_A1p (eisretr f) p)^).
Qed.

Instance isequiv_contr_hfibers `(f : A -> B)
  (hfc : forall y:B, Contr {x:A & f x = y})
  : IsEquiv f.
Proof.
  pose (g b := projT1 (@center _ (hfc b))).
  pose (isretr b := projT2 (@center _ (hfc b))).
  assert (sa : forall a, { issect : g (f a) = a & isretr (f a) = ap f issect }).
    intros a.
    assert (fp : forall (x x' : {x:A & f x = f a}) (q : x = x'),
        { p : projT1 x = projT1 x' & projT2 x = ap f p @ projT2 x' }).
      intros x _ []. exists 1; exact ((concat_1p _)^).
    set (r := fp (@center _ (hfc (f a))) (a;1) (@contr _ (hfc (f a)) (a;1))).
    exact (projT1 r ; projT2 r @ concat_p1 _).
  exact (BuildIsEquiv _ _ f g isretr
    (fun a => projT1 (sa a)) (fun a => projT2 (sa a))).
Defined.

Definition equiv_contr_hfibers `(f : A -> B)
  (hfc : forall y:B, Contr {x:A & f x = y})
  : (A <~> B)
  := BuildEquiv _ _ f (isequiv_contr_hfibers f hfc).
