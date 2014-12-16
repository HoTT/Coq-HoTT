(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import HoTT.Tactics.
Require Import UnivalenceImpliesFunext.
Require Import hit.Truncations.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Splitting of Idempotents *)

(** TODO: [IsIdempotent] should be a section/retraction pair.  By HTT 4.4.5.7 this has the correct homotopy type for being a *coherent* idempotent.  Then we can have [IsPreIdempotent] and [IsQuasiIdempotent] or something for the incoherent and "partially coherent" ones.  We should be able to prove that the [J] of a quasi-idempotent is not generally recovered from its splitting, e.g. the same [id,I] can admit different [J], but their splitting factor through the contractible type [{Z:Type & Z <~> X}].  Thus quasi-idempotents are analogous to quasi-inverses, with splitting being analogous to adjointification. *)


(** The naive definition of "idempotent" would be a morphism [f : X -> X] such that [forall x, f (f x) = f x].  However, homotopically we may naturally expect to need some coherence on the witness to idempotency.  Indeed, in homotopy theory there are "idempotents" in this sense which do not split; see for instance Warning 1.2.4.8 in *Higher Algebra*.

A priori, a "coherent idempotent" would involve infinitely many data.  However, Lemma 7.3.5.14 of *Higher Algebra* suggests that for an idempotent to be coherent (or, at least, coherentifiable), it suffices to have *one* additional datum.  By modifying the construction given there, we can show in type theory that any idempotent satisfying an additional coherence datum splits. *)

Definition Idempotent {A : Type} (f : A -> A)
  := forall x, f (f x) = f x.

Definition CoherentIdempotent {A : Type} (f : A -> A)
  := { I : forall x, f (f x) = f x
     (** Here is the extra coherence datum. *)
     & forall x, ap f (I x) = I (f x) }.

(** ** Split idempotents are coherent *)

Definition coherent_split
           {X A : Type} (r : X -> A) (s : A -> X) (H : r o s == idmap)
: CoherentIdempotent (s o r).
Proof.
  exists (fun x => ap s (H (r x))); intros x.
  refine ((ap_compose _ _ _) @ _).
  apply ap.
  refine ((ap_compose _ _ _)^ @ _).
  refine (cancelR _ _ (H (r x)) _).
  refine (concat_A1p H (H (r x))).
Defined.

(** ** Coherent idempotents split *)

Section CoherentIdempotents.
  (** We need funext because our construction will involve a sequential limit.  We could probably also use a HIT sequential colimit, which is more like what Lurie does. *)
  Context `{Funext}.
  Context {X : Type} (f : X -> X).
  Context (IJ : CoherentIdempotent f).

  Let I := IJ.1.
  Let J : forall x, ap f (I x) = I (f x)
    := IJ.2.

  (** The splitting will be the sequential limit of the sequence [... -> X -> X -> X]. *)
  Definition split_idempotent : Type
    := { a : nat -> X & forall n, f (a n.+1) = a n }.

  Definition split_idempotent_pr1 : split_idempotent -> (nat -> X)
    := pr1.
  Coercion split_idempotent_pr1 : split_idempotent >-> Funclass.
  Arguments split_idempotent_pr1 / .

  (** The section, retraction, and the fact that the composite in one direction is [f] are easy. *)

  Definition split_idempotent_sect : split_idempotent -> X
    := fun a => a 0.
  Arguments split_idempotent_sect / .

  Definition split_idempotent_retr : X -> split_idempotent.
  Proof.
    intros x.
    exists (fun n => f x).
    exact (fun n => I x).
  Defined.
  Arguments split_idempotent_retr / .

  Definition split_idempotent_splits (x : X)
  : split_idempotent_sect (split_idempotent_retr x) = f x
    := 1.

  (** What remains is to show that the composite in the other direction is the identity.  We begin by showing how to construct paths in [split_idempotent]. *)

  Definition path_split_idempotent {a a' : split_idempotent}
             (p : a.1 == a'.1)
             (q : forall n, a.2 n @ p n
                            = ap f (p n.+1) @ a'.2 n)
  : a = a'.
  Proof.
    refine (path_sigma' _ _ _).
    - apply path_arrow; intros n.
      exact (p n).
    - apply path_forall; intros n.
      abstract (
          rewrite transport_forall_constant;
          rewrite transport_paths_FlFr;
          rewrite ap_apply_l, ap10_path_arrow;
          rewrite (ap_compose (fun b => b n.+1) (fun x => f x) _);
          rewrite ap_apply_l, ap10_path_arrow;
          rewrite concat_pp_p;
          apply moveR_Vp; by symmetry ).
  Defined.

  Definition sect_path_split_idempotent {a a' : split_idempotent}
             (p : a.1 == a'.1)
             (q : forall n, a.2 n @ p n
                            = ap f (p n.+1) @ a'.2 n)
  : ap (fun (a:split_idempotent) => a 0) (path_split_idempotent p q) = p 0.
  Proof.
    change (ap ((fun b => b 0) o pr1) (path_split_idempotent p q) = p 0).
    refine (ap_compose pr1 (fun b => b 0) _ @ _).
    refine (ap (ap (fun b => b 0)) (pr1_path_sigma _ _) @ _).
    refine (ap_apply_l _ 0 @ _).
    apply ap10_path_arrow.
  Defined.

  (** Next we show that every element of [split_idempotent] can be nudged to an equivalent one in which all the elements of [X] occurring are double applications of [f]. *)

  Local Definition nudge (a : split_idempotent) : split_idempotent.
  Proof.
    exists (fun n => f (f (a (n.+1)))).
    exact (fun n => ap f (ap f (a.2 n.+1))).
  Defined.

  Local Definition nudge_eq a : nudge a = a.
  Proof.
    transparent assert (a' : split_idempotent).
    { exists (fun n => f (a (n.+1))).
      exact (fun n => ap f (a.2 n.+1)). }
    transitivity a'; refine (path_split_idempotent _ _); intros n; simpl.
    - exact (I (a n.+1)).
    - exact ((ap_compose f f _ @@ 1)^
               @ concat_Ap I (a.2 n.+1)
               @ (J _ @@ 1)^).
    - exact (a.2 n).
    - reflexivity.
  Defined.

  (** Now we're ready to prove the final condition. *)

  Local Definition split_idempotent_issect_1 (a : split_idempotent) (n : nat)
  : f (f (a n.+1)) = f (a 0).
  Proof.
    induction n as [|n IH].
    - exact (ap f (a.2 0)).
    - exact (ap f (a.2 n.+1) @ (I (a n.+1))^ @ IH).
  Defined.

  Local Definition split_idempotent_issect_2 (a : split_idempotent) (n : nat)
  : ap f (ap f (a.2 n.+1)) @ split_idempotent_issect_1 a n =
    ap f ((ap f (a.2 n.+1) @ (I (a.1 n.+1))^) @ split_idempotent_issect_1 a n) @ I (a.1 0).
  Proof.
    induction n as [|n IH]; simpl.
    Open Scope long_path_scope.
    - rewrite !ap_pp, ap_V, !concat_pp_p.
      apply whiskerL, moveL_Vp.
      rewrite J.
      rewrite <- ap_compose; symmetry; apply (concat_Ap I).
    - rewrite ap_pp.
      refine (_ @ (1 @@ IH) @ concat_p_pp _ _ _).
      rewrite !ap_pp, !concat_p_pp, ap_V.
      rewrite J.
      rewrite <- !ap_compose.
      refine ((concat_pA_p (fun x => (I x)^) _ _) @@ 1).
    Close Scope long_path_scope.
  Qed.

  Definition split_idempotent_issect (a : split_idempotent)
  : split_idempotent_retr (split_idempotent_sect a) = a.
  Proof.
    refine (_ @ nudge_eq a); symmetry.
    refine (path_split_idempotent _ _).
    - exact (split_idempotent_issect_1 a).
    - exact (split_idempotent_issect_2 a).
  Defined.

  (** The following observation shows that the resulting splitting is "coherent" with the given witness of idempotence [I]. *)
  Definition split_idempotent_coherent (x : X)
  : ap split_idempotent_sect (split_idempotent_issect (split_idempotent_retr x))
    @ split_idempotent_splits x
    = split_idempotent_splits (split_idempotent_sect (split_idempotent_retr x))
      @ ap f (split_idempotent_splits x)
      @ I x.
  Proof.
    unfold split_idempotent_issect, nudge_eq.
    repeat (rewrite !ap_pp, ?ap_V, !sect_path_split_idempotent; simpl).
    unfold split_idempotent_splits.
    rewrite concat_p1, concat_1p; apply moveR_Vp.
    apply whiskerR; symmetry; apply J.
  Qed.

  (** Another way to say this is that if we use [coherent_split] to recover a witness of idempotence from the above splitting, we recover the same witness [I] that we started with. *)
  Definition idempotent_split_idempotent
  : transport Idempotent
    (path_arrow (split_idempotent_sect o split_idempotent_retr) f split_idempotent_splits)
    (coherent_split split_idempotent_retr split_idempotent_sect split_idempotent_issect).1
    = I.
  Proof.
    unfold coherent_split; simpl.
    apply path_forall; intros x.
    unfold Idempotent; rewrite transport_forall_constant.
    rewrite transport_paths_FlFr.
    rewrite ap_apply_l, ap10_path_arrow.
    rewrite_moveR_Vp_p.
    refine (split_idempotent_coherent x @ _).
    apply whiskerR.
    unfold split_idempotent_splits.
    rewrite path_arrow_1; reflexivity.
  Qed.

  (** It would be nice to know whether [J] is also recovered, but that would involve a lot of path algebra. *)

End CoherentIdempotents.

(** ** Splitting already-split idempotents *)

(** In the other direction, suppose we are given a section/retraction pair, we deduce a coherent idempotent, and then split it by the above construction.  Then we get an equivalent type to the one occurring in the original pair .*)

(** We want to make the equivalence transparent so that we can reason about it later.  In fact, we want to reason not only about the equivalence function and its inverse, but the section and retraction homotopies!  Therefore, instead of using [equiv_adjointify] we will give the coherence proof explicitly.  However, we can (and should) make the coherence proof opaque.  Thus, we prove it first and end it with [Qed].  *)
Lemma equiv_split_coherent_split_2 `{fs : Funext}
           {X A : Type} (r : X -> A) (s : A -> X) (H : r o s == idmap)
           (a : split_idempotent (s o r))
: H (r (s (r (split_idempotent_sect (s o r) a)))) @
   H (r (split_idempotent_sect (s o r) a)) =
   ap (r o split_idempotent_sect (s o r))
     (ap (split_idempotent_retr (s o r) (coherent_split r s H))
        (1 @
         ap (split_idempotent_sect (s o r))
           (split_idempotent_issect (s o r) (coherent_split r s H) a)) @
      split_idempotent_issect (s o r) (coherent_split r s H) a).
Proof.
  rewrite ap_pp.
  rewrite <- ap_compose; simpl.
  rewrite concat_1p.
  rewrite <- (ap_compose (split_idempotent_sect (s o r)) (r o s o r)
                         (split_idempotent_issect (s o r) (coherent_split r s H) a)).
  rewrite (ap_compose _ (r o s o r) (split_idempotent_issect (s o r) (coherent_split r s H) a)).
  rewrite (ap_compose _ r (split_idempotent_issect (s o r) (coherent_split r s H) a)).
  unfold split_idempotent_issect, nudge_eq;
    repeat (rewrite !ap_pp, ?ap_V, !sect_path_split_idempotent; simpl).
  rewrite !concat_pp_p.
  rewrite <- !ap_compose.
  rewrite <- (ap_compose (s o r) r).
  rewrite <- (ap_compose (s o r) (r o s o r)).
  rewrite (concat_p_Vp (ap (r o s o r) (a.2 0))).
  rewrite_moveL_Vp_p.
  rewrite (ap_compose (r o s o r) (r o s) (a.2 0)).
  rewrite (concat_A1p H (ap (r o s o r) (a.2 0))).
  rewrite (ap_compose r (r o s) (a.2 0)).
  rewrite (concat_pA1_p H (ap r (a.2 0))).
  apply whiskerR.
  refine (cancelR _ _ (H (r (a.1 1%nat))) _).
  rewrite (concat_pA1_p H (H (r (a 1%nat)))).
  rewrite !concat_pp_p; symmetry; refine (_ @ concat_pp_p _ _ _).
  exact (concat_A1p (fun x => H (r (s x)) @ H x) (H (r (a 1%nat)))).
Qed.

(** Now we can construct the desired equivalence. *)
Definition equiv_split_coherent_split `{fs : Funext}
           {X A : Type} (r : X -> A) (s : A -> X) (H : r o s == idmap)
: split_idempotent (s o r) <~> A.
Proof.
  refine (BuildEquiv _ _ (r o split_idempotent_sect (s o r))
            (BuildIsEquiv _ _ _ (split_idempotent_retr (s o r) (coherent_split r s H) o s) _ _ _)).
  - intros a; simpl.
    refine (H _ @ H _).
  - intros a; simpl.
    refine (_ @ split_idempotent_issect (s o r) (coherent_split r s H) a).
    apply ap.
    refine ((split_idempotent_splits (s o r) (coherent_split r s H) _)^ @ _).
    apply ap, split_idempotent_issect.
  - intros a; simpl; apply equiv_split_coherent_split_2.
Defined.

(** In particular, this implies that if two section/retraction pairs induce the same endomap, then their splitting objects are equivalent.  Informally, "a given endomap splits through at most one type". *)

Definition equiv_split_coherent `{fs : Funext} {X A A' : Type}
           (r : X -> A) (s : A -> X) (H : r o s == idmap)
           (r' : X -> A') (s' : A' -> X) (H' : r' o s' == idmap)
           (K : s o r == s' o r')
: A <~> A'.
Proof.
  refine (equiv_compose' (equiv_split_coherent_split r' s' H') _).
  refine (equiv_compose' _ (equiv_inverse (equiv_split_coherent_split r s H))).
  unfold split_idempotent.
  refine (equiv_functor_sigma' (equiv_idmap _) (fun a => _)).
  refine (equiv_functor_forall' (equiv_idmap nat) (fun n => _)); simpl. 
  exact (equiv_concat_l (K (a n.+1))^ _).
Defined.

(** Moreover, these equivalences respect the section and the retraction map. *)

Definition equiv_split_coherent_split_retr `{fs : Funext}
           {X A : Type} (r : X -> A) (s : A -> X) (H : r o s == idmap)
           (x : X)
: equiv_split_coherent_split r s H (split_idempotent_retr (s o r) (coherent_split r s H) x) = r x
  := H (r x).

Definition equiv_split_coherent_split_sect `{fs : Funext}
           {X A : Type} (r : X -> A) (s : A -> X) (H : r o s == idmap)
           (a : A)
: split_idempotent_sect (s o r) ((equiv_split_coherent_split r s H)^-1 a) = s a
  := ap s (H a).

(** However, it could still be the case that a given endomap [f : X -> X] splits *in more than one way* through the same splitting type [A].  In other words, the above equivalence may not respect all the section/retraction data.

TODO: Try to verify whether this holds.  Is [IsIdempotent f] maybe a retract of [IsQuasiIdempotent f], the way that [IsEquiv f] is a retract of [QInv f]? *)

Definition equiv_split_coherent_split_splits `{fs : Funext}
           {X A : Type} (r : X -> A) (s : A -> X) (H : r o s == idmap)
           (x : X)
: split_idempotent_splits (s o r) (coherent_split r s H) x
  = ap (split_idempotent_sect (s o r))
       (eissect (equiv_split_coherent_split r s H)
                (split_idempotent_retr (s o r) (coherent_split r s H) x))^
    @ equiv_split_coherent_split_sect r s H
        (equiv_split_coherent_split r s H (split_idempotent_retr (s o r) (coherent_split r s H) x))
    @ ap s (equiv_split_coherent_split_retr r s H x).
Proof.
  simpl.
  unfold equiv_split_coherent_split_retr, equiv_split_coherent_split_sect, split_idempotent_splits.
  rewrite concat_1p, concat_pp_p, ap_V; apply moveL_Vp; rewrite concat_p1.
  (** Brace yourself. *)
  unfold split_idempotent_issect, nudge_eq.
  repeat (rewrite !ap_pp, ?ap_V, !sect_path_split_idempotent; simpl).
  (** Whew, that's not so bad. *)
  Open Scope long_path_scope.
  rewrite !concat_p_pp.
  rewrite <- !ap_compose; simpl.
  apply whiskerR.
  refine (_ @ (concat_1p _)); apply whiskerR.
  apply moveR_pV; rewrite concat_1p, concat_pp_p; apply moveR_Vp.
  rewrite <- (ap_compose (s o r o s) (s o r)).
  rewrite (ap_compose (r o s) s _).
  rewrite (ap_compose (r o s) s _).
  rewrite (ap_compose (r o s o r o s) s _).
  rewrite <- !ap_pp; apply ap.
  refine (cancelR _ _ (H (r x)) _).
  rewrite (concat_pA1_p H (H (r x)) _).
  rewrite (concat_pA1_p H (H (r x)) _).
  refine ((concat_A1p H (H (r (s (r x)))) @@ 1) @ _).
  rewrite (ap_compose (r o s) (r o s) _).
  rewrite (concat_A1p H (ap (r o s) (H (r x)))).
  rewrite !concat_pp_p; apply whiskerL.
  symmetry; refine (concat_A1p H (H (r x))).
  Close Scope long_path_scope.
Qed.

Definition equiv_split_coherent_split_issect `{fs : Funext}
           {X A : Type} (r : X -> A) (s : A -> X) (H : r o s == idmap)
           (a : A)
: ap (equiv_split_coherent_split r s H)
     (split_idempotent_issect (s o r) (coherent_split r s H)
                              ((equiv_split_coherent_split r s H)^-1 a))
  @ eisretr (equiv_split_coherent_split r s H) a
  = equiv_split_coherent_split_retr r s H
      (split_idempotent_sect (s o r) ((equiv_split_coherent_split r s H)^-1 a))
    @ ap r (equiv_split_coherent_split_sect r s H a)
    @ H a.
Proof.
  simpl.
  unfold equiv_split_coherent_split_retr, equiv_split_coherent_split_sect.
  rewrite ap_compose.
  unfold split_idempotent_issect, nudge_eq.
  repeat (rewrite !ap_pp, ?ap_V, !sect_path_split_idempotent; simpl).
  Open Scope long_path_scope.
  rewrite !concat_pp_p; apply moveR_Vp; rewrite !concat_p_pp.
  do 4 rewrite <- ap_compose.
  (** For some reason this last one needs help. *)
  rewrite <- (ap_compose (s o r o s) r (H (r (s a)))).
  rewrite <- (ap_pp (r o s) _ _).
  rewrite <- (concat_A1p H (H (r (s a)))).
  rewrite ap_pp.
  rewrite <- (ap_compose (r o s) (r o s) _).
  rewrite !concat_pp_p; apply whiskerL; rewrite !concat_p_pp.
  rewrite (concat_A1p H (H (r (s a)))).
  rewrite !concat_pp_p; apply whiskerL.
  symmetry; refine (concat_A1p H (H a)).
  Close Scope long_path_scope.
Qed.

(** Therefore, the type of retractions of [X] is a retract of the type of "coherent idempotents". *)

Definition retraction_to_cohidem {X : Type}
: { A : Type & {rs : (X -> A) * (A -> X) & fst rs o snd rs == idmap }}
  -> {f : X -> X & CoherentIdempotent f}.
Proof.
  intros [A [[r s] H]].
  exists (s o r).
  exact (coherent_split r s H).
Defined.

Definition cohidem_to_retraction `{Funext} {X : Type}
: {f : X -> X & CoherentIdempotent f}
  -> { A : Type & {rs : (X -> A) * (A -> X) & fst rs o snd rs == idmap }}.
Proof.
  intros [f IJ].
  exists (split_idempotent f).
  exists (split_idempotent_retr f IJ , split_idempotent_sect f).
  exact (split_idempotent_issect f IJ).
Defined.

Definition path_retraction `{ua : Univalence} {X : Type}
           {A : Type} {r : X -> A} {s : A -> X} {H : r o s == idmap}
           {A' : Type} {r' : X -> A'} {s' : A' -> X} {H' : r' o s' == idmap}
           (Ap : A' <~> A) (rp : Ap o r' == r) (sp : s' o Ap^-1 == s)
           (Hp : forall a, ap Ap (H' (Ap^-1 a))
                           @ eisretr Ap a
                           = rp (s' (Ap^-1 a))
                             @ ap r (sp a)
                             @ H a)
: (A' ; ((r' , s') ; H')) = (A ; ((r , s) ; H))
    :> { A : Type & {rs : (X -> A) * (A -> X) & fst rs o snd rs == idmap }}.
Proof.
  refine (path_sigma' _ _ _).
  { apply path_universe_uncurried.
    exact Ap. }
  refine (transport_sigma _ _ @ _).
  refine (path_sigma' _ _ _); simpl.
  { refine (transport_prod _ _ @ _).
    apply path_prod; simpl.
    - apply path_arrow; intros x.
      refine (transport_arrow_fromconst _ _ _ @ _).
      refine (transport_path_universe_uncurried _ _ @ _).
      apply rp.
    - apply path_arrow; intros a.
      refine (transport_arrow_toconst _ _ _ @ _).
      refine (_ @ sp a); simpl; apply ap.
      refine (transport_path_universe_V_uncurried Ap a). }
  apply path_forall; intros a.
  unfold pointwise_paths.
  rewrite transport_forall_constant; simpl.
  rewrite transport_paths_Fl; simpl.
  apply moveR_Vp.
  rewrite ap_pp, concat_pp_p.
  apply moveL_Mp.
  (** Sneaky! *)
  transitivity (transport_arrow_fromconst (path_universe_uncurried Ap) r'
                 (transport (fun Z => Z -> X) (path_universe_uncurried Ap) s' a)
                @ ap (transport idmap (path_universe_uncurried Ap) o r')
                     (transport_arrow_toconst (path_universe_uncurried Ap) s' a)
                @ ap _ (H' _)
                @ transport_pV idmap (path_universe_uncurried Ap) a).
  - generalize (path_universe_uncurried Ap).
    intros p; destruct p; simpl.
    rewrite !concat_1p.
    symmetry; unfold transport. rewrite ap_idmap.
    (** I don't know why Coq won't simplify [transport_pV idmap 1 a] to [1]. *)
    apply concat_p1.
  - rewrite (ap_apply_FlFr _ (fun rs b => fst rs b) (fun rs => snd rs a)).
    rewrite (ap_compose (fun (rs:(X->A)*(A->X)) => snd rs) (fun (s:A->X) => s a)).
    rewrite ap_snd_path_prod.
    rewrite (ap_compose (fun (rs:(X->A)*(A->X)) => fst rs) (fun (r:X->A) => fun b => r b)).
    rewrite ap_fst_path_prod.
    rewrite ap_apply_l, ap10_path_arrow.
    rewrite ap11_is_ap10_ap01; simpl.
    rewrite ap_idmap.
    rewrite ap10_path_arrow; simpl.
    Open Scope long_path_scope.
    rewrite !concat_pp_p; apply whiskerL; rewrite !concat_p_pp.
    rewrite <- (concat_pA_p rp).
    rewrite ap_pp, concat_p_pp.
    rewrite (concat_pA_p rp).
    specialize (Hp a).
    rewrite concat_pp_p in Hp.
    rewrite !concat_pp_p, <- Hp, !concat_p_pp. clear Hp.
    rewrite (ap_compose r' Ap).
    rewrite !ap_pp, !concat_p_pp.
    rewrite <- (ap_compose r' Ap).
    rewrite <- (concat_Ap (fun x => transport_path_universe_uncurried Ap (r' x))).
    rewrite !concat_pp_p; apply whiskerL; rewrite !concat_p_pp.
    rewrite <- (ap_p_pp Ap).
    rewrite <- (ap_compose s' r').
    rewrite (concat_A1p H').
    rewrite ap_pp, concat_p_pp.
    rewrite <- (concat_Ap (transport_path_universe_uncurried Ap)).
    rewrite !concat_pp_p; apply whiskerL; rewrite !concat_p_pp.
    symmetry; apply transport_path_universe_pV.
Qed.

Definition retraction_to_cohidem_retr `{ua : Univalence} {X : Type}
           (Z : { A : Type & {rs : (X -> A) * (A -> X) & fst rs o snd rs == idmap }})
: cohidem_to_retraction (retraction_to_cohidem Z) = Z
:= path_retraction (equiv_split_coherent_split (fst Z.2.1) (snd Z.2.1) Z.2.2)
                   (equiv_split_coherent_split_retr (fst Z.2.1) (snd Z.2.1) Z.2.2)
                   (equiv_split_coherent_split_sect (fst Z.2.1) (snd Z.2.1) Z.2.2)
                   (equiv_split_coherent_split_issect (fst Z.2.1) (snd Z.2.1) Z.2.2).

Definition fully_coherent_idempotents `{Funext} (X : Type)
  := split_idempotent ((@retraction_to_cohidem X) o (@cohidem_to_retraction _ X)).

Definition equiv_coherentidempotent_retraction `{ua : Univalence} (X : Type)
: fully_coherent_idempotents X
  <~> { A : Type & {rs : (X -> A) * (A -> X) & fst rs o snd rs == idmap }}
:= equiv_split_coherent_split (@cohidem_to_retraction _ X) (@retraction_to_cohidem X)
                              (@retraction_to_cohidem_retr _ X).

(** For instance, here is the standard coherent idempotent structure on the identity map. *)
Definition fully_coherent_idmap `{ua : Univalence} (X : Type@{i})
: fully_coherent_idempotents@{i i j} X.
Proof.
  refine (split_idempotent_retr _
           (coherent_split (@cohidem_to_retraction _ X) (@retraction_to_cohidem X)
                           (@retraction_to_cohidem_retr _ X)) _).
  exists idmap.
  exists (fun x => 1).
  exact (fun x => 1).
Defined.

(** We note that [fully_coherent_idempotents X], unlike the type of retractions, lives in the same universe as [X], even if we demand that it contain the identity. *)
Check (fun (ua:Univalence) (X:Type@{i}) =>
         (fully_coherent_idmap X : (fully_coherent_idempotents X : Type@{i}))).

(** By contrast, the type of retractions does not live in the same universe as [X] if it is required to contain the identity retraction. *)
Definition identity_retraction (X:Type)
: { A : Type & {rs : (X -> A) * (A -> X) & fst rs o snd rs == idmap }}.
Proof.
  exists X.
  exists (idmap,idmap).
  intros x; reflexivity.
Defined.

Fail Check (fun (X:Type@{i}) =>
              (identity_retraction X :
                 ({ A : Type & {rs : (X -> A) * (A -> X) & fst rs o snd rs == idmap }}
                  : Type@{i}))).
  
(** ** An incoherent idempotent *)

(** Finally, we give a specific example of an incoherent idempotent that does not split, hence is not coherentifiable.  This is inspired by Warning 1.2.4.8 in *Higher Algebra*. *)

(** *** Cantor space 2^N *)

(** This should probably go somewhere else. *)

Definition cantor : Type := nat -> Bool.

Definition fold_cantor : cantor + cantor -> cantor.
Proof.
  intros [c|c]; intros n.
  - destruct n as [|n].
    + exact true.
    + exact (c n).
  - destruct n as [|n].
    + exact false.
    + exact (c n).
Defined.

Definition unfold_cantor : cantor -> cantor + cantor.
Proof.
  intros c.
  case (c 0).
  - exact (inl (fun n => c n.+1)).
  - exact (inr (fun n => c n.+1)).
Defined.

Global Instance isequiv_fold_cantor `{Funext} : IsEquiv fold_cantor.
Proof.
  refine (isequiv_adjointify fold_cantor unfold_cantor _ _).
  - intros c; apply path_arrow; intros n.
    induction n as [|n IH].
    + unfold unfold_cantor.
      case (c 0); reflexivity.
    + unfold unfold_cantor.
      case (c 0); reflexivity.
  - intros [c|c]; apply path_sum; reflexivity.
Defined.

Definition equiv_fold_cantor `{Funext} : cantor + cantor <~> cantor
  := BuildEquiv _ _ fold_cantor _.

(** *** BAut *)

(** This should probably go somewhere else too. *)
Definition BAut (C : Type) := { Z : Type & merely (Z = C) }.

Global Instance ispointed_baut C : IsPointed (BAut C)
  := (C ; tr 1).

Definition BAut_pr1 C : BAut C -> Type := pr1.
Coercion BAut_pr1 : BAut >-> Sortclass.

Definition path_baut `{Univalence} C (Z Z' : BAut C)
: (Z <~> Z') <~> (Z = Z' :> BAut C).
Proof.
  eapply equiv_compose'.
  - apply equiv_path_sigma_hprop.
  - apply equiv_path_universe.
Defined.

(** *** An idempotent on BAut(2^N) *)

(** We go into a non-exported module so that we can use short names for definitions without polluting the global namespace. *)

Module BAut_Cantor_Idempotent.
Section Assumptions.
  Context `{Univalence}.

  Definition f : BAut cantor -> BAut cantor.
  Proof.
    intros Z.
    (** Here is the important part of this definition. *)
    exists (Z + cantor).
    (** The rest is just a proof that [Z+cantor] is again equivalent to [cantor], using [fold_cantor] and the assumption that [Z] is equivalent to [cantor]. *)
    pose (e := Z.2); simpl in e; clearbody e.
    strip_truncations.
    apply tr.
    apply path_universe_uncurried.
    refine (equiv_compose' equiv_fold_cantor _).
    apply equiv_functor_sum'.
    - apply equiv_path, e.
    - apply equiv_idmap.
  Defined.

  (** For the idempotence of [f], the main point is again the existence of the equivalence [fold_cantor]. *)
  Definition idempotent_f : Idempotent f.
  Proof.
    intros Z.
    apply path_baut.
    unfold f; simpl.
    refine (equiv_compose' _ (equiv_sum_assoc Z cantor cantor)).
    apply (equiv_functor_sum' (equiv_idmap Z) equiv_fold_cantor).
  Defined.

  (** We record how the action of [f] and [f o f] on paths corresponds to an action on equivalences. *)
  Definition ap_f {Z Z' : BAut cantor} (p : Z = Z')
  : equiv_path _ _ (ap f p)..1
    = equiv_functor_sum' (equiv_path Z Z' p..1) (equiv_idmap cantor).
  Proof.
    destruct p. apply path_equiv, path_arrow.
    intros [z|a]; reflexivity.
  Defined.

  Definition ap_ff {Z Z' : BAut cantor} (p : Z = Z')
  : equiv_path _ _ (ap (f o f) p)..1
    = equiv_functor_sum'
        (equiv_functor_sum' (equiv_path Z Z' p..1) (equiv_idmap cantor))
        (equiv_idmap cantor).
  Proof.
    destruct p. apply path_equiv, path_arrow.
    intros [[z|a]|a]; reflexivity.
  Defined.

  (** Now let's assume [f] is a coherent idempotent. *)
  Context (IJ : CoherentIdempotent f).

  Definition I (Z : BAut cantor)
  : (Z + cantor) + cantor <~> Z + cantor
    := equiv_path _ _ (IJ.1 Z)..1.

  Definition I0
  : cantor + cantor + cantor + cantor <~> cantor + cantor + cantor
    := I (f (point (BAut cantor))).

  (** We don't know much about [I0], but we can show that it maps the rightmost two summands to the rightmost one, using the naturality of [I].  Here is the naturality. *)
  Definition Inat (Z Z' : BAut cantor) (e : Z <~> Z')
  : equiv_compose' (I Z') (equiv_functor_sum'
                             (equiv_functor_sum' e (equiv_idmap cantor))
                             (equiv_idmap cantor))
    = equiv_compose' (equiv_functor_sum' e (equiv_idmap cantor)) (I Z).
  Proof.
    revert e; equiv_intro (equiv_path Z Z') q.
    revert q; equiv_intro (equiv_inverse (equiv_path_sigma_hprop Z Z')) p.
    simpl. rewrite <- ap_ff, <- ap_f.
    unfold I. refine ((equiv_path_pp _ _)^ @ _ @ (equiv_path_pp _ _)).
    apply ap.
    refine ((pr1_path_pp (ap (f o f) p) (IJ.1 Z'))^ @ _ @ pr1_path_pp _ _).
    apply ap. apply (concat_Ap IJ.1).
  Qed.

  (** To show our claim about the action of [I0], we will apply this naturality to the flip automorphism of [cantor + cantor].  Here are the images of that automorphism under [f] and [f o f]. *)
  Definition f_flip :=
    equiv_functor_sum' (equiv_sum_symm cantor cantor)
                       (equiv_idmap cantor).
  Definition ff_flip :=
    equiv_functor_sum'
      (equiv_functor_sum' (equiv_sum_symm cantor cantor)
                          (equiv_idmap cantor))
      (equiv_idmap cantor).

  (** The naturality of [I] implies that [I0] commutes with these images of the flip. *)
  Definition I0nat_flip
        (x : ((cantor + cantor) + cantor) + cantor)
  : I0 (ff_flip x) = f_flip (I0 x)
    := ap10 (ap equiv_fun
                (Inat (f (point (BAut cantor))) (f (point (BAut cantor)))
                      (equiv_sum_symm cantor cantor)))
            x.

  (** The value of this is that we can detect which summand an element is in depending on whether or not it is fixed by [f_flip] or [ff_flip]. *)
  Definition f_flip_fixed_iff_inr (x : cantor + cantor + cantor)
  : (f_flip x = x) <-> is_inr x.
  Proof.
    split; intros p; destruct x as [[c|c]|c]; simpl in p.
    - apply path_sum_inl in p.
      elim (inl_ne_inr _ _ p^).
    - apply path_sum_inl in p.
      elim (inl_ne_inr _ _ p).
    - exact tt.
    - elim p.
    - elim p.
    - reflexivity.
  Defined.

  Definition ff_flip_fixed_iff_inr
        (x : cantor + cantor + cantor + cantor)
  : (ff_flip x = x) <-> (is_inr x + is_inl_and is_inr x).
  Proof.
    split; intros p; destruct x as [[[c|c]|c]|c]; simpl in p.
    - do 2 apply path_sum_inl in p.
      elim (inl_ne_inr _ _ p^).
    - do 2 apply path_sum_inl in p.
      elim (inl_ne_inr _ _ p).
    - exact (inr tt).
    - exact (inl tt).
    - destruct p as [e|e]; elim e.
    - destruct p as [e|e]; elim e.
    - destruct p as [e|_]; [ elim e | reflexivity ].
    - destruct p as [_|e]; [ reflexivity | elim e ].
  Defined.
  
  (** And the naturality guarantees that [I0] preserves fixed points. *)
  Definition I0_fixed_iff_fixed
        (x : cantor + cantor + cantor + cantor)
  : (ff_flip x = x) <-> (f_flip (I0 x) = I0 x).
  Proof.
    split; intros p.
    - refine ((I0nat_flip x)^ @ ap I0 p).
    - apply (equiv_inj I0).
      refine (I0nat_flip x @ p).
  Defined.

  (** Putting it all together, here is the proof of our claim about [I0]. *)
  Definition I0_preserves_inr
        (x : cantor + cantor + cantor + cantor)
  : (is_inr x + is_inl_and is_inr x) <-> is_inr (I0 x).
  Proof.
    refine (iff_compose (f_flip_fixed_iff_inr (I0 x)) _).
    refine (iff_compose (I0_fixed_iff_fixed x) _).
    apply iff_inverse, ff_flip_fixed_iff_inr.
  Defined.

  (** Now we bring the coherence [J] into play. *)
  Definition J (Z : BAut cantor)
  : equiv_functor_sum' (I Z) (equiv_idmap cantor)
    = I (f Z).
  Proof.
    unfold I; simpl.
    refine ((ap_f (IJ.1 Z))^ @ _).
    do 2 apply ap.
    apply IJ.2.
  Defined.

  (** We reach a contradiction by showing that the two maps which [J] claims are equal send elements of the third summand of the domain into different summands of the codomain. *)
  Definition impossible : Empty.
  Proof.
    pose (x := inl (inr (fun n => true))
               : ((f (point (BAut cantor))) + cantor) + cantor).
    apply (not_is_inl_and_inr' (I (f (point (BAut cantor))) x)).
    - exact (transport is_inl
                       (ap10 (ap equiv_fun (J (point (BAut cantor)))) x) tt).
    (** TODO: The following line takes 17 seconds with coqtop, but executes instantaneously with coqc.  Why? *)
    - exact (fst (I0_preserves_inr x) (inr tt)).
  Defined.
  
End Assumptions.
End BAut_Cantor_Idempotent.

(** Let's make the important conclusions available globally. *)

Definition baut_cantor_idem `{Univalence}
: BAut cantor -> BAut cantor
  := BAut_Cantor_Idempotent.f.

Definition idempotent_baut_cantor_idem  `{Univalence}
: Idempotent baut_cantor_idem
  := BAut_Cantor_Idempotent.idempotent_f.

Definition not_coherent_baut_cantor_idem `{Univalence}
: ~(CoherentIdempotent baut_cantor_idem)
  := BAut_Cantor_Idempotent.impossible.
