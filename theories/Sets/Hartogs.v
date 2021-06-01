From HoTT Require Import Basics TruncType ExcludedMiddle abstract_algebra.
From HoTT Require Import PropResizing.PropResizing.
From HoTT Require Import Spaces.Card.

From HoTT.Sets Require Import Ordinals Powers.

(** This file contains a construction of the Hartogs number. *)


(** * Hartogs number *)

Section Hartogs_Number.

  Universe A.
  Context {univalence : Univalence}
          {prop_resizing : PropResizing}
          {lem: ExcludedMiddle}
          (A : HSet@{A}).

  Lemma le_Cardinal_lt_Ordinal (B C : Ordinal)
    : B < C -> card B ≤ card C.
  Proof.
    intros B_C. apply tr. cbn. rewrite (bound_property B_C).
    exists out. apply isinjective_simulation. apply is_simulation_out.
  Qed.

  (* The Hartogs number of A consists of all ordinals that embed into A.
     Note that this constructions necessarily increases the universe level. *)

  Fail Check { B : Ordinal@{A _} | card B <= card A } : Type@{A}.

  Definition hartogs_number' : Ordinal.
  Proof.
    set (carrier := {B : Ordinal & card B <= card A}).
    set (relation := fun (B C : carrier) => B.1 < C.1).

    exists carrier relation. srapply (isordinal_simulation pr1).
    - exact _.
    - exact _.
    - intros B C. apply path_sigma_hprop.
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

  Declare Scope Hartogs.
  Open Scope Hartogs.

  Notation "'𝒫'" := power_type (at level 30) : Hartogs.

  Definition proper_subtype_inclusion {A} (U V : 𝒫 A)
    := (forall a, U a -> V a) /\ merely (exists a : A, V a /\ ~U a).
  Coercion subtype_as_type' {X} (Y : 𝒫 X) : Type
    := { x : X & Y x }.

  Infix "⊊" := proper_subtype_inclusion (at level 50) : Hartogs.
  Notation "(⊊)" := proper_subtype_inclusion : Hartogs.

  (* The hartogs number of A embeds into the threefold power set of A.
     This preliminary injection also increases the universe level though. *)

  Lemma hartogs_number'_injection
    : exists f : hartogs_number' -> (𝒫 (𝒫 (𝒫 A)) : Type),
        IsInjective f.
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
            intros a. srapply istrunc_prod.
            srapply istrunc_arrow.
            rapply ishprop_sigma_disjoint. intros b1' b2' [_ ->] [_ p].
            apply (injective_f). exact p.
          - apply extensionality. intros b'. split.
            + intros b'_b1.
              specialize (Hb1 (f b')). apply snd in Hb1.
              specialize (Hb1 (b'; (b'_b1, idpath))).
              apply Hb2 in Hb1. destruct Hb1 as (? & H2 & H3).
              apply injective in H3; try exact _. destruct H3.
              exact H2.
            + intros b'_b2.
              specialize (Hb2 (f b')). apply snd in Hb2.
              specialize (Hb2 (b'; (b'_b2, idpath))).
              apply Hb1 in Hb2. destruct Hb2 as (? & H2 & H3).
              apply injective in H3; try exact _. destruct H3.
              exact H2.
        }
        exists (fun X : 𝒫 A =>
             Build_HProp { b : B & forall a, X a <-> exists b', b' < b /\ a = f b' }). {
          unfold subtype_as_type'.
          unshelve eexists.
          - srapply equiv_adjointify.
            + intros [X [b _]]. exact b.
            + intros b.
              unshelve eexists (fun a => Build_HProp (exists b', b' < b /\ a = f b'))
              ; try exact _. {
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
                   apply irreflexivity in b'_b1; try exact _. assumption.
        }
      }
      assert (IsOrdinal X (ϕ X)). {
        srefine (isordinal_simulation iso.1); try exact _.
        intros x1 x2 p.
        rewrite <- (eissect iso.1 x1).
        rewrite <- (eissect iso.1 x2).
        f_ap.
      }
      apply apD10 in H0. specialize (H0 X). cbn in H0.
      refine (transitive_Isomorphism _ (X : Type; ϕ X) _ _ _). {
        apply isomorphism_inverse. assumption.
      }
      enough (merely (Isomorphism (X : Type; ϕ X) C)). {
        revert X1. rapply Trunc_rec. {
          exact (ishprop_Isomorphism (Build_Ordinal X (ϕ X) _) C).
        }
        auto.
      }
      rewrite <- H0. apply tr. exact iso.
  Qed.

  (* Using hprop resizing, the threefold power set can be pushed to the same universe level as A. *)

  Definition power_inj {pr : PropResizing} {C : Type@{i}} (p : C -> HProp) :
    (C -> HProp : Type@{i}).
  Proof.
    exact (fun a => Build_HProp (resize_hprop (p a))).
  Defined.

  Lemma injective_power_inj {pr : PropResizing} {ua : Univalence} (C : Type@{i}) :
    IsInjective (@power_inj _ C).
  Proof.
    intros p p'. unfold power_inj. intros H. apply path_forall. intros a. apply path_iff_hprop; intros Ha.
    - eapply equiv_resize_hprop. change ((fun a => Build_HProp (resize_hprop (p' a))) a).
      rewrite <- H. apply equiv_resize_hprop. apply Ha.
    - eapply equiv_resize_hprop. change ((fun a => Build_HProp (resize_hprop (p a))) a).
      rewrite H. apply equiv_resize_hprop. apply Ha.
  Qed.

  Definition power_morph {pr : PropResizing} {ua : Univalence} {C B : Type@{i}} (f : C -> B) :
    (C -> HProp) -> (B -> HProp).
  Proof.
    intros p b. exact (Build_HProp (resize_hprop (forall a, f a = b -> p a))).
  Defined.

  Definition injective_power_morph {pr : PropResizing} {ua : Univalence} {C B : Type@{i}} (f : C -> B) :
    IsInjective f -> IsInjective (@power_morph _ _ C B f).
  Proof.
    intros Hf p p' H. apply path_forall. intros a. apply path_iff_hprop; intros Ha.
    - enough (Hp : power_morph f p (f a)).
      + rewrite H in Hp. apply equiv_resize_hprop in Hp. apply Hp. reflexivity.
      + apply equiv_resize_hprop. intros a' -> % Hf. apply Ha.
    - enough (Hp : power_morph f p' (f a)).
      + rewrite <- H in Hp. apply equiv_resize_hprop in Hp. apply Hp. reflexivity.
      + apply equiv_resize_hprop. intros a' -> % Hf. apply Ha.
  Qed.

  Definition uni_fix (X : 𝒫 (𝒫 (𝒫 A))) :
    ((𝒫 (𝒫 (𝒫 A))) : Type@{i}).
  Proof.
    srapply power_morph. 3: apply X. intros P.
    srapply power_morph. 3: apply P.
    srapply power_inj.
  Defined.

  Lemma injective_uni_fix :
    IsInjective uni_fix.
  Proof.
    intros X Y. unfold uni_fix. intros H % injective_power_morph; trivial.
    intros P Q. intros H' % injective_power_morph; trivial.
    intros p q. apply injective_power_inj.
  Qed.

  (* We can therefore resize the Hartogs number of A to the same universe level as A. *)

  Definition hartogs_number_carrier : Type@{A} :=
    {X : 𝒫 (𝒫 (𝒫 A)) | resize_hprop (merely (exists a, uni_fix (hartogs_number'_injection.1 a) = X))}.

  Lemma hartogs_equiv :
    hartogs_number_carrier <~> hartogs_number'.
  Proof.
    apply equiv_inverse. unshelve eapply equiv_hset_bijection.
    - intros a. exists (uni_fix (hartogs_number'_injection.1 a)).
      apply equiv_resize_hprop, tr. exists a. reflexivity.
    - exact _.
    - intros a b. intros H % pr1_path. cbn in H.
      specialize (injective_uni_fix (hartogs_number'_injection.1 a) (hartogs_number'_injection.1 b)).
      intros H'. apply H' in H. now apply hartogs_number'_injection.2.
    - intros [X HX]. eapply merely_destruct.
      + eapply equiv_resize_hprop, HX.
      + intros [a <-]. cbn. apply tr. exists a. cbn. apply ap.
        apply ishprop_resize_hprop.
  Defined.

  Definition resize_ordinal@{i j +} (B : Ordinal@{i _}) (C : Type@{j}) (g : C <~> B) :
    Ordinal@{j _}.
  Proof.
    exists C (fun c1 c2 : C => resize_hprop (g c1 < g c2)).
    srapply (isordinal_simulation g); try exact _.
    - apply (istrunc_equiv_istrunc B (equiv_inverse g)).
    - intros c1 c2. intros p.
      rewrite <- (eissect g c1).  rewrite <- (eissect g c2). f_ap.
    - constructor.
      + intros a a' a_a'. apply (equiv_resize_hprop _)^-1. exact a_a'.
      + intros a b b_fa. apply tr. exists (g^-1 b). split.
        * apply equiv_resize_hprop. rewrite eisretr. exact b_fa.
        * apply eisretr.
  Defined.

  Definition hartogs_number : Ordinal@{A _} :=
    resize_ordinal hartogs_number' hartogs_number_carrier hartogs_equiv.

  (* This final definition now satisfies the expected cardinality properties. *)

  Lemma hartogs_number_injection :
    exists f : hartogs_number -> 𝒫 (𝒫 (𝒫 A)), IsInjective f.
  Proof.  
    cbn. exists proj1. intros [X HX] [Y HY]. cbn. intros ->.
    apply ap. apply ishprop_resize_hprop.
  Qed.

  Lemma ordinal_initial (O : Ordinal) (a : O) :
    Isomorphism O ↓a -> Empty.
  Proof.
    intros H % equiv_path_Ordinal.
    enough (HO : O < O) by apply (irreflexive_ordinal_relation _ _ _ _ HO).
    exists a. apply H.
  Qed.

  Lemma resize_ordinal_iso@{i j +} (B : Ordinal@{i _}) (C : Type@{j}) (g : C <~> B) :
    Isomorphism (resize_ordinal B C g) B.
  Proof.
    exists g. intros a a'. cbn. split; apply equiv_resize_hprop.
  Qed.

  Lemma hartogs_number_no_injection :
    ~ (exists f : hartogs_number -> A, IsInjective f).
  Proof.
    cbn. intros [f Hf]. cbn in f.
    assert (HN : card hartogs_number <= card A). { apply tr. now exists f. }
    transparent assert (HNO : hartogs_number'). { exists hartogs_number. apply HN. }
    apply (ordinal_initial hartogs_number' HNO).
    eapply (transitive_Isomorphism hartogs_number' hartogs_number).
    - apply isomorphism_inverse, resize_ordinal_iso.
    - assert (Isomorphism hartogs_number ↓hartogs_number) by apply isomorphism_to_initial_segment.
      eapply transitive_Isomorphism; try apply X.
      unshelve eexists.
      + srapply equiv_adjointify.
        * intros [a Ha % equiv_resize_hprop]. unshelve eexists.
          -- exists a. eapply transitive_card; try apply HN.
             now apply le_Cardinal_lt_Ordinal.
          -- apply equiv_resize_hprop. cbn. exact Ha.
        * intros [[a Ha] H % equiv_resize_hprop]. exists a.
          apply equiv_resize_hprop. apply H.
        * intros [[a Ha] H]. apply path_sigma_hprop. apply path_sigma_hprop. reflexivity.
        * intros [a Ha]. apply path_sigma_hprop. reflexivity.
      + intros [[a Ha] H1] [[b H] H2]. cbn. reflexivity.
  Qed.

End Hartogs_Number.
