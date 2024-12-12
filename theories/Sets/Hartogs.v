From HoTT Require Import TruncType ExcludedMiddle Modalities.ReflectiveSubuniverse abstract_algebra HSet.
From HoTT Require Import Universes.Smallness.
From HoTT Require Import Spaces.Card.

From HoTT.Sets Require Import Ordinals Powers.

Close Scope trunc_scope.

(** This file contains a construction of the Hartogs number. *)

(** We begin with some results about changing the universe of a power set using propositional resizing. *)

Definition power_inj `{PropResizing} {C : Type@{i}} (p : C -> HProp@{j})
  : C -> HProp@{k}.
Proof.
  exact (fun a => Build_HProp (smalltype@{k j} (p a))).
Defined.

Lemma injective_power_inj `{PropResizing} {ua : Univalence} (C : Type@{i})
  : IsInjective (@power_inj _ C).
Proof.
  intros p p'. unfold power_inj. intros q. apply path_forall. intros a. apply path_iff_hprop; intros Ha.
  - eapply equiv_smalltype. change ((fun a => Build_HProp (smalltype (p' a))) a).
    rewrite <- q. apply equiv_smalltype. apply Ha.
  - eapply equiv_smalltype. change ((fun a => Build_HProp (smalltype (p a))) a).
    rewrite q. apply equiv_smalltype. apply Ha.
Qed.

(* TODO: Could factor this as something keeping the [HProp] universe the same, followed by [power_inj]. *)
Definition power_morph `{PropResizing} {ua : Univalence} {C B : Type@{i}} (f : C -> B)
  : (C -> HProp) -> (B -> HProp).
Proof.
  intros p b. exact (Build_HProp (smalltype (forall a, f a = b -> p a))).
Defined.

Definition injective_power_morph `{PropResizing} {ua : Univalence} {C B : Type@{i}} (f : C -> B)
  : IsInjective f -> IsInjective (@power_morph _ _ C B f).
Proof.
  intros Hf p p' q. apply path_forall. intros a. apply path_iff_hprop; intros Ha.
  - enough (Hp : power_morph f p (f a)).
    + rewrite q in Hp. apply equiv_smalltype in Hp. apply Hp. reflexivity.
    + apply equiv_smalltype. intros a' -> % Hf. apply Ha.
  - enough (Hp : power_morph f p' (f a)).
    + rewrite <- q in Hp. apply equiv_smalltype in Hp. apply Hp. reflexivity.
    + apply equiv_smalltype. intros a' -> % Hf. apply Ha.
Qed.

(** We'll also need this result. *)
Lemma le_Cardinal_lt_Ordinal `{PropResizing} `{Univalence} (B C : Ordinal)
  : B < C -> card B ≤ card C.
Proof.
  intros B_C. apply tr. cbn. rewrite (bound_property B_C).
  exists out. apply isinjective_simulation. apply is_simulation_out.
Qed.

(** * Hartogs number *)

Section Hartogs_Number.

  Declare Scope Hartogs.
  Open Scope Hartogs.

  Notation "'𝒫'" := power_type (at level 30) : Hartogs.

  Local Coercion subtype_as_type' {X} (Y : 𝒫 X) := { x : X & Y x }.

  Universe A.
  Context {univalence : Univalence}
          {prop_resizing : PropResizing}
          {lem: ExcludedMiddle}
          (A : HSet@{A}).

  (* The Hartogs number of [A] consists of all ordinals that embed into [A]. Note that this construction necessarily increases the universe level. *)

  Fail Check { B : Ordinal@{A _} | card B <= card A } : Type@{A}.

  Definition hartogs_number' : Ordinal.
  Proof.
    set (carrier := {B : Ordinal@{A _} & card B <= card A}).
    set (relation := fun (B C : carrier) => B.1 < C.1).
    exists carrier relation. snrapply (isordinal_simulation pr1).
    1-4: exact _.
    - apply isinj_embedding, (mapinO_pr1 (Tr (-1))). (* Faster than [exact _.] *)
    - constructor.
      + intros a a' a_a'. exact a_a'.
      + intros [B small_B] C C_B; cbn in *. apply tr.
        unshelve eexists (C; _); cbn; auto.
        revert small_B. srapply Trunc_rec. intros [f isinjective_f]. apply tr.
        destruct C_B as [b ->].
        exists (fun '(x; x_b) => f x); cbn.
        intros [x x_b] [y y_b] fx_fy. apply path_sigma_hprop; cbn.
        apply (isinjective_f x y). exact fx_fy.
  Defined.

  Definition proper_subtype_inclusion (U V : 𝒫 A)
    := (forall a, U a -> V a) /\ merely (exists a : A, V a /\ ~(U a)).

  Infix "⊊" := proper_subtype_inclusion (at level 50) : Hartogs.
  Notation "(⊊)" := proper_subtype_inclusion : Hartogs.

  (* The hartogs number of [A] embeds into the threefold power set of [A].  This preliminary injection also increases the universe level though. *)

  Lemma hartogs_number'_injection
    : exists f : hartogs_number' -> (𝒫 (𝒫 (𝒫 A))), IsInjective f.
  Proof.
    transparent assert (ϕ : (forall X : 𝒫 (𝒫 A), Lt X)). {
      intros X. intros x1 x2. exact (x1.1 ⊊ x2.1).
    }
    unshelve eexists.
    - intros [B _]. intros X. exact (merely (Isomorphism (X : Type; ϕ X) B)).
    - intros [B B_A] [C C_A] H0. apply path_sigma_hprop; cbn.
      revert B_A. rapply Trunc_rec. intros [f injective_f].
      apply equiv_path_Ordinal.
      assert {X : 𝒫 (𝒫 A) & Isomorphism (X : Type; ϕ X) B} as [X iso]. {
        assert (H2 :
                  forall X : 𝒫 A,
                    IsHProp { b : B & forall a, X a <-> exists b', b' < b /\ a = f b' }). {
          intros X. apply hprop_allpath; intros [b1 Hb1] [b2 Hb2].
          snrapply path_sigma_hprop; cbn.
          - intros b. snrapply istrunc_forall.
            intros a. snrapply istrunc_prod. 2: exact _.
            snrapply istrunc_arrow.
            rapply ishprop_sigma_disjoint. intros b1' b2' [_ ->] [_ p].
            apply (injective_f). exact p.
          - apply extensionality. intros b'. split.
            + intros b'_b1.
              specialize (Hb1 (f b')). apply snd in Hb1.
              specialize (Hb1 (b'; (b'_b1, idpath))).
              apply Hb2 in Hb1. destruct Hb1 as (? & H2 & H3).
              apply injective in H3. 2: assumption. destruct H3.
              exact H2.
            + intros b'_b2.
              specialize (Hb2 (f b')). apply snd in Hb2.
              specialize (Hb2 (b'; (b'_b2, idpath))).
              apply Hb1 in Hb2. destruct Hb2 as (? & H2 & H3).
              apply injective in H3. 2: assumption. destruct H3.
              exact H2.
        }
        exists (fun X : 𝒫 A =>
             Build_HProp { b : B & forall a, X a <-> exists b', b' < b /\ a = f b' }). {
          unfold subtype_as_type'.
          unshelve eexists.
          - srapply equiv_adjointify.
            + intros [X [b _]]. exact b.
            + intros b.
              unshelve eexists (fun a => Build_HProp (exists b', b' < b /\ a = f b')).
              1: exact _.
              {
                apply hprop_allpath. intros [b1 [b1_b p]] [b2 [b2_b q]].
                apply path_sigma_hprop; cbn. apply (injective f).
                destruct p, q. reflexivity.
              }
              exists b. intros b'. cbn. reflexivity.
            + cbn. reflexivity.
            + cbn. intros [X [b Hb]]. apply path_sigma_hprop. cbn.
              apply path_forall; intros a. apply path_iff_hprop; apply Hb.
          - cbn. intros [X1 [b1 H'1]] [X2 [b2 H'2]].
            unfold ϕ, proper_subtype_inclusion. cbn.
            split.
            + intros H3.
              refine (Trunc_rec _ (trichotomy_ordinal b1 b2)). intros [b1_b2 | H4].
              * exact b1_b2.
              * revert H4. rapply Trunc_rec. intros [b1_b2 | b2_b1].
                -- apply Empty_rec. destruct H3 as [_ H3]. revert H3. rapply Trunc_rec. intros [a [X2a not_X1a]].
                   apply not_X1a. apply H'1. rewrite b1_b2. apply H'2. exact X2a.
                -- apply Empty_rec. destruct H3 as [_ H3]. revert H3. rapply Trunc_rec. intros [a [X2a not_X1a]].
                   apply not_X1a. apply H'1.
                   apply H'2 in X2a. destruct X2a as [b' [b'_b2 a_fb']].
                   exists b'. split.
                   ++ transitivity b2; assumption.
                   ++ assumption.
            + intros b1_b2. split.
              * intros a X1a. apply H'2. apply H'1 in X1a. destruct X1a as [b' [b'_b1 a_fb']].
                exists b'. split.
                -- transitivity b1; assumption.
                -- assumption.
              * apply tr. exists (f b1). split.
                -- apply H'2. exists b1; auto.
                -- intros X1_fb1. apply H'1 in X1_fb1. destruct X1_fb1 as [b' [b'_b1 fb1_fb']].
                   apply (injective f) in fb1_fb'. destruct fb1_fb'.
                   apply irreflexivity in b'_b1. 2: exact _. assumption.
        }
      }
      assert (IsOrdinal X (ϕ X)) by exact (isordinal_simulation iso.1). 
      apply apD10 in H0. specialize (H0 X). cbn in H0.
      refine (transitive_Isomorphism _ (X : Type; ϕ X) _ _ _). {
        apply isomorphism_inverse. assumption.
      }
      enough (merely (Isomorphism (X : Type; ϕ X) C)). {
        revert X1. nrapply Trunc_rec. {
          exact (ishprop_Isomorphism (Build_Ordinal X (ϕ X) _) C).
        }
        auto.
      }
      rewrite <- H0. apply tr. exact iso.
  Qed.

  (** Using hprop resizing, the threefold power set can be pushed to the same universe level as [A]. *)

  Definition uni_fix (X : 𝒫 (𝒫 (𝒫 A))) : ((𝒫 (𝒫 (𝒫 A))) : Type@{A}).
  Proof.
    revert X.
    nrapply power_morph.
    nrapply power_morph.
    nrapply power_inj.
  Defined.

  Lemma injective_uni_fix : IsInjective uni_fix.
  Proof.
    intros X Y. unfold uni_fix. intros H % injective_power_morph; trivial.
    intros P Q. intros H' % injective_power_morph; trivial.
    intros p q. apply injective_power_inj.
  Qed.

  (* We can therefore resize the Hartogs number of A to the same universe level as A. *)

  Definition hartogs_number_carrier : Type@{A}
    := {X : 𝒫 (𝒫 (𝒫 A)) | smalltype (merely (exists a, uni_fix (hartogs_number'_injection.1 a) = X))}.

  Lemma hartogs_equiv : hartogs_number_carrier <~> hartogs_number'.
  Proof.
    apply equiv_inverse. unshelve eexists.
    - intros a. exists (uni_fix (hartogs_number'_injection.1 a)).
      apply equiv_smalltype, tr. exists a. reflexivity.
    - snrapply isequiv_surj_emb.
      + apply BuildIsSurjection. intros [X HX]. eapply merely_destruct.
        * eapply equiv_smalltype, HX.
        * intros [a <-]. cbn. apply tr. exists a. cbn. apply ap. apply path_ishprop.
      + apply isembedding_isinj_hset. intros a b. intros H % pr1_path. cbn in H.
        specialize (injective_uni_fix (hartogs_number'_injection.1 a) (hartogs_number'_injection.1 b)).
        intros H'. apply H' in H. by apply hartogs_number'_injection.2.
  Qed.

  Definition hartogs_number : Ordinal@{A _}
    := resize_ordinal hartogs_number' hartogs_number_carrier hartogs_equiv.

  (* This final definition by satisfies the expected cardinality properties. *)

  Lemma hartogs_number_injection
    : exists f : hartogs_number -> 𝒫 (𝒫 (𝒫 A)), IsInjective f.
  Proof.  
    cbn. exists proj1. intros [X HX] [Y HY]. cbn. intros ->.
    apply ap. apply path_ishprop.
  Qed.

  Lemma hartogs_number_no_injection
    : ~ (exists f : hartogs_number -> A, IsInjective f).
  Proof.
    cbn. intros [f Hf]. cbn in f.
    assert (HN : card hartogs_number <= card A). { apply tr. by exists f. }
    transparent assert (HNO : hartogs_number'). { exists hartogs_number. apply HN. }
    apply (ordinal_initial hartogs_number' HNO).
    eapply (transitive_Isomorphism hartogs_number' hartogs_number).
    - apply isomorphism_inverse.
      unfold hartogs_number.
      exact (resize_ordinal_iso hartogs_number' hartogs_number_carrier hartogs_equiv).
    - assert (Isomorphism hartogs_number ↓hartogs_number) by apply isomorphism_to_initial_segment.
      eapply transitive_Isomorphism. 1: exact X.
      unshelve eexists.
      + srapply equiv_adjointify.
        * intros [a Ha % equiv_smalltype]. unshelve eexists.
          -- exists a. transitivity (card hartogs_number).
             ++ nrapply le_Cardinal_lt_Ordinal; apply Ha.
             ++ apply HN.
          -- apply equiv_smalltype. cbn. exact Ha.
        * intros [[a Ha] H % equiv_smalltype]. exists a.
          apply equiv_smalltype. apply H.
        * intro a. apply path_sigma_hprop. apply path_sigma_hprop. reflexivity.
        * intro a. apply path_sigma_hprop. reflexivity.
      + reflexivity.
  Defined.

End Hartogs_Number.
