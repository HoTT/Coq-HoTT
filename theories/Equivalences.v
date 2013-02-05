(** * Equivalences -*- mode: coq; mode: visual-line -*- *)

Require Import Overture PathGroupoids.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** We now give many ways to construct equivalences.  In each case, we define an instance of the typeclass [IsEquiv] named [isequiv_X], followed by an element of the record type [Equiv] named [equiv_X].

   Whenever we need to assume, as a hypothesis, that a certain function is an equivalence, we do it by assuming separately a function and a proof of [IsEquiv].  This is more general than assuming an inhabitant of [Equiv], since the latter has an implicit coercion and an existing instance to give us the former automatically.  Moreover, implicit generalization makes it easy to assume a function and a proof of [IsEquiv]. *)

Generalizable Variables A B C f g.

(** The identity map is an equivalence. *)
Instance isequiv_idmap (A : Type) : IsEquiv idmap :=
  BuildIsEquiv A A idmap idmap (fun _ => 1) (fun _ => 1) (fun _ => 1).

Definition equiv_idmap (A : Type) : A <~> A := BuildEquiv A A idmap _.

Instance equiv_Reflexive : Reflexive Equiv := equiv_idmap.

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


(* Note: Transitive TypeClass has a different order of parameters than equiv_compose. 
   Note: This is "Let" definition and private to this file.  Use equiv_compose.*)
Let equiv_transitivity (A B C : Type) (ab : A <~> B) (bc : B <~> C) : A <~> C
  := 
  match ab, bc with
    | BuildEquiv ab_fun ab_isequiv, BuildEquiv bc_fun bc_isequiv 
      => (@equiv_compose B C bc_fun bc_isequiv A ab_fun ab_isequiv)
end.
Instance equiv_Transitive : Transitive Equiv := equiv_transitivity.

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
End EquivInverse.

(** [Equiv A B] is a symmetric relation. *)
Theorem equiv_inverse (A B : Type): (A <~> B) -> (B <~> A).
Proof.
  intro e.
  exists (e^-1).
  apply isequiv_inverse.
Defined.

Instance equiv_Symmetric : Symmetric Equiv := equiv_inverse.


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

  
(** If [f] is an equivalence, then its homotopy fibers are contractible.  That is, it is a Voevodsky equivalence, or a homotopy bijection.  Probably the following two proofs should really be using some standard facts about paths in Sigma types.  *)

(** Several lemmas useful for rewriting. *)
Lemma moveR_E (A B : Type) (e : A <~> B) (x : A) (y : B) :
  x = e^-1 y -> e x = y.
Proof.
  intro H.
  rewrite H.
  apply eisretr.
Qed.

Lemma moveL_E (A B : Type) (e : A <~> B) (x : A) (y : B) :
  e^-1 y = x -> y = e x.
Proof.
  intro H.
  rewrite <- H.
  apply symmetry, eisretr.
Qed.

(** Equivalence preserves contractibility (which of course is trivial under univalence). *)
Lemma Contr_equiv_contr (A B : Type) : (A <~> B) -> Contr A -> Contr B.
Proof.
  intros e C.
  exists (e (center A)).
  intro y.
  apply moveR_E.
  apply C.
Qed.
