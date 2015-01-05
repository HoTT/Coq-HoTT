(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Idempotents.
Require Import hit.Truncations Spaces.BAut Spaces.Cantor.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * BAut(Cantor) *)

(** ** A pre-idempotent on [BAut Cantor] that does not split *)

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

  (** For the pre-idempotence of [f], the main point is again the existence of the equivalence [fold_cantor]. *)
  Definition preidem_f : IsPreIdempotent f.
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

  (** Now let's assume [f] is quasi-idempotent, but not necessarily using the same witness of pre-idempotency. *)
  Context (Ip : IsPreIdempotent f) (Jp : @IsQuasiIdempotent _ f Ip).

  Definition I (Z : BAut cantor)
  : (Z + cantor) + cantor <~> Z + cantor
    := equiv_path _ _ (Ip Z)..1.

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
    refine ((pr1_path_pp (ap (f o f) p) (Ip Z'))^ @ _ @ pr1_path_pp _ _).
    apply ap. apply (concat_Ap Ip).
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

  (** Now we bring quasi-idempotence into play. *)
  Definition J (Z : BAut cantor)
  : equiv_functor_sum' (I Z) (equiv_idmap cantor)
    = I (f Z).
  Proof.
    unfold I; simpl.
    refine ((ap_f (Ip Z))^ @ _).
    do 2 apply ap.
    apply Jp.
  Defined.

  (** We reach a contradiction by showing that the two maps which [J] claims are equal send elements of the third summand of the domain into different summands of the codomain. *)
  Definition impossible : Empty.
  Proof.
    pose (x := inl (inr (fun n => true))
               : ((f (point (BAut cantor))) + cantor) + cantor).
    apply (not_is_inl_and_inr' (I (f (point (BAut cantor))) x)).
    - exact (transport is_inl
                       (ap10 (ap equiv_fun (J (point (BAut cantor)))) x) tt).
    - exact (fst (I0_preserves_inr x) (inr tt)).
  Defined.

End Assumptions.
End BAut_Cantor_Idempotent.

(** Let's make the important conclusions available globally. *)

Definition baut_cantor_idem `{Univalence}
: BAut cantor -> BAut cantor
  := BAut_Cantor_Idempotent.f.

Definition preidem_baut_cantor_idem `{Univalence}
: IsPreIdempotent baut_cantor_idem
  := BAut_Cantor_Idempotent.preidem_f.

Definition not_qidem_baut_cantor_idem `{Univalence}
: ~ { I : IsPreIdempotent baut_cantor_idem
        & IsQuasiIdempotent baut_cantor_idem }
  := fun IJ => BAut_Cantor_Idempotent.impossible IJ.1 IJ.2.
