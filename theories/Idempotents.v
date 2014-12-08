(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import HoTT.Tactics.
Require Import hit.Truncations.

Local Open Scope path_scope.
Local Open Scope equiv_scope.
Local Arguments compose / .

(** * Splitting of Idempotents *)

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
  Let J := IJ.2.

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
      rewrite transport_forall_constant.
      rewrite transport_paths_FlFr.
      rewrite ap_apply_l, ap10_path_arrow.
      rewrite (ap_compose (fun b => b n.+1) (fun x => f x) _).
      rewrite ap_apply_l, ap10_path_arrow.
      rewrite concat_pp_p.
      apply moveR_Vp; by symmetry.
  Qed.

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

  Definition split_idempotent_issect (a : split_idempotent)
  : split_idempotent_retr (split_idempotent_sect a) = a.
  Proof.
    refine (_ @ nudge_eq a); symmetry.
    transparent assert (p : (forall n, f (f (a n.+1)) = f (a 0))).
    { induction n as [|n IH].
      - exact (ap f (a.2 0)).
      - exact ((I (f (a n.+2)))^ @ (ap f (ap f (a.2 n.+1))) @ IH). }
    refine (path_split_idempotent _ _); [ exact p | intros n; simpl ].
    induction n as [|n IH]; simpl.
    Open Scope long_path_scope.
    - rewrite !ap_pp, ap_V.
      rewrite_moveL_Vp_p.
      rewrite J.
      rewrite <- !ap_pp.
      with_rassoc ltac:(rewrite <- !ap_pp).
      rewrite <- ap_compose.
      exact ((concat_Ap I (ap f (a.2 1%nat) @ a.2 0))^).
    - (* For some reason [rewrite concat_pp_p] here rewrites *twice*? *)
      refine ((1 @@ concat_pp_p _ _ _) @ _).
      rewrite IH.
      rewrite !ap_pp, !concat_p_pp.
      do 4 apply whiskerR.
      rewrite ap_V; apply moveL_Vp; rewrite concat_p_pp; apply moveR_pV.
      refine (_ @ (ap_compose f f _ @@ 1)).
      rewrite J.
      exact ((concat_Ap I (ap f (a.2 n.+2)))^).
    Close Scope long_path_scope.
  Qed.

  (** Note that a splitting of [f] induces a witness of idempotency of [f] and also any amount of coherence on it that one might ask for.  We ought in theory to investigate whether these witnesses arising from this splitting agree with the given [I] and [J]. *)

End CoherentIdempotents.

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
    apply ap, concat_Ap.
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
