From HoTT Require Import TruncType ExcludedMiddle Modalities.ReflectiveSubuniverse abstract_algebra.
From HoTT Require Import Universes.Smallness.
From HoTT Require Import Colimits.Quotient.
From HoTT Require Import HSet.

Local Close Scope trunc_scope.
Local Open Scope hprop_scope.

(** This file contains a definition of ordinals and some fundamental results,
    roughly following the presentation in the HoTT book. *)


(** * Well-foundedness *)

Inductive Accessible {A} (R : Lt A) (a : A) :=
  acc : (forall b, b < a -> Accessible R b) -> Accessible R a.

Global Instance ishprop_Accessible `{Funext} {A} (R : Lt A) (a : A) :
  IsHProp (Accessible R a).
Proof.
  apply hprop_allpath.
  intros acc1. induction acc1 as [a acc1' IH].
  intros [acc2']. apply ap.
  apply path_forall; intros b. apply path_forall; intros Hb.
  apply IH.
Qed.

Class WellFounded {A} (R : Relation A) :=
  well_foundedness : forall a : A, Accessible R a.

Global Instance ishprop_WellFounded `{Funext} {A} (R : Relation A) :
  IsHProp (WellFounded R).
Proof.
  apply hprop_allpath; intros H1 H2.
  apply path_forall; intros a.
  apply path_ishprop.
Qed.

(** * Extensionality *)

Class Extensional {A} (R : Lt A) :=
  extensionality : forall a b : A, (forall c : A, c < a <-> c < b) -> a = b.

Global Instance ishprop_Extensional `{Funext} {A} `{IsHSet A} (R : Relation A)
  : IsHProp (Extensional R).
Proof. unfold Extensional. exact _. Qed.

(** * Ordinals *)

Class IsOrdinal@{carrier relation} (A : Type@{carrier}) (R : Relation@{carrier relation} A) := {
  ordinal_is_hset : IsHSet A ;
  ordinal_relation_is_mere : is_mere_relation A R ;
  ordinal_extensionality : Extensional R ;
  ordinal_well_foundedness : WellFounded R ;
  ordinal_transitivity : Transitive R ;
}.
#[export] Existing Instances
  ordinal_is_hset
  ordinal_relation_is_mere
  ordinal_extensionality
  ordinal_well_foundedness
  ordinal_transitivity.

Global Instance ishprop_IsOrdinal `{Funext} A R
  : IsHProp (IsOrdinal A R).
Proof.
  eapply istrunc_equiv_istrunc. {
    issig.
  }
  unfold Transitive. exact _.
Qed.

Record Ordinal@{carrier relation +} :=
  { ordinal_carrier : Type@{carrier}
    ; ordinal_relation : Lt@{carrier relation} ordinal_carrier
    ; ordinal_property : IsOrdinal@{carrier relation} ordinal_carrier (<)
  }.

Global Existing Instances ordinal_relation ordinal_property.

Coercion ordinal_as_hset (A : Ordinal) : HSet
  := Build_HSet (ordinal_carrier A).

Global Instance irreflexive_ordinal_relation A R
  : IsOrdinal A R -> Irreflexive R.
Proof.
  intros is_ordinal a H.
  induction (well_foundedness a) as [a _ IH].
  apply (IH a); assumption.
Qed.

Definition TypeWithRelation
  := { A : Type & Relation A }.

Coercion ordinal_as_type_with_relation (A : Ordinal) : TypeWithRelation
  := (A : Type; (<)).

(** * Paths in Ordinal *)

Definition equiv_Ordinal_to_sig
  : Ordinal <~> { R : { A : Type & Relation A } & IsOrdinal _ R.2 }.
Proof.
  transitivity { A : Type & { R : Relation A & IsOrdinal A R } }. {
    symmetry. issig.
  }
  apply equiv_sigma_assoc'.
Defined.

Definition Isomorphism : TypeWithRelation -> TypeWithRelation -> Type
  := fun '(A; R__A) '(B; R__B) =>
       { f : A <~> B & forall a a', R__A a a' <-> R__B (f a) (f a') }.

Global Instance isomorphism_id : Reflexive Isomorphism.
Proof. intros A. exists equiv_idmap. cbn. intros a a'. reflexivity. Qed.

Lemma isomorphism_inverse
  : forall A B, Isomorphism A B -> Isomorphism B A.
Proof.
  intros [A R__A] [B R__B] [f H].
  exists (equiv_inverse f).
  intros b b'.
  cbn.
  rewrite <- (eisretr f b). set (a := f^-1 b). rewrite eissect.
  rewrite <- (eisretr f b'). set (a' := f^-1 b'). rewrite eissect.
  (* We don't apply the symmetry tactic because that would introduce bad universe constraints *)
  split; apply H.
Defined.

(** We state this first without using [Transitive] to allow more general universe variables. *)
Lemma transitive_Isomorphism
  : forall A B C, Isomorphism A B -> Isomorphism B C -> Isomorphism A C.
Proof.
  intros [A R__A] [B R__B] [C R__C].
  intros [f Hf] [g Hg].
  exists (equiv_compose' g f).
  intros a a'.
  split.
  - intros a_a'. apply Hg. apply Hf. exact a_a'.
  - intros gfa_gfa'. apply Hf. apply Hg. exact gfa_gfa'.
Defined.

Global Instance isomorphism_compose_backwards : Transitive Isomorphism
  := transitive_Isomorphism.

Definition equiv_path_Ordinal `{Univalence} (A B : Ordinal)
  : Isomorphism A B <~> A = B.
Proof.
  unfold Isomorphism. rapply symmetric_equiv.
  transitivity (equiv_Ordinal_to_sig A = equiv_Ordinal_to_sig B). {
    apply equiv_ap'.
  }
  transitivity ((equiv_Ordinal_to_sig A).1 = (equiv_Ordinal_to_sig B).1). {
    exists pr1_path. exact (isequiv_pr1_path_hprop _ _).
  }
  transitivity (exist Relation A (<) = exist Relation B (<)). {
    reflexivity.
  }
  transitivity { p : A = B :> Type & p # (<) = (<) }. {
    symmetry.
    exact (equiv_path_sigma Relation
                            (exist Relation A (<))
                            (exist Relation B (<))).
  }
  srapply equiv_functor_sigma'.
  - exact (equiv_equiv_path A B).
  - cbn. intros p.
    nrapply equiv_iff_hprop.
    + apply (istrunc_equiv_istrunc (forall b b' : B, (p # (<)) b b' = (b < b'))). {
        transitivity (forall b : B, (p # lt) b = lt b). {
          apply equiv_functor_forall_id; intros b. apply equiv_path_arrow.
        }
        apply equiv_path_arrow.
      }
      exact _.
    + exact _. 
    + intros <- a a'.
      rewrite transport_arrow. rewrite transport_arrow_toconst.
      repeat rewrite transport_Vp. reflexivity.
    + intros H0.
      by_extensionality b. by_extensionality b'.
      rewrite transport_arrow. rewrite transport_arrow_toconst.
      apply path_iff_ishprop_uncurried.
      specialize (H0 (transport idmap p^ b) (transport idmap p^ b')).
      repeat rewrite transport_pV in H0. exact H0.
Qed.

Lemma path_Ordinal `{Univalence} (A B : Ordinal)
  : forall f : A <~> B,
    (forall a a' : A, a < a' <-> f a < f a')
    -> A = B.
Proof.
  intros f H0. apply equiv_path_Ordinal. exists f. exact H0.
Qed.

Lemma trichotomy_ordinal `{ExcludedMiddle} {A : Ordinal} (a b : A)
  : a < b \/ a = b \/ b < a.
Proof.
  revert b. induction (well_foundedness a) as [a _ IHa]. intros b.
  induction (well_foundedness b) as [b _ IHb].
  destruct (LEM (merely (exists b', b' < b /\ (a = b' \/ a < b')))) as [H1 | H1]; try exact _.
  - revert H1. rapply Trunc_rec. intros [b' [b'_b Hb']].
    revert Hb'. rapply Trunc_rec. intros [a_b' | b'_a].
    + apply tr. left. rewrite a_b'. exact b'_b.
    + apply tr. left. transitivity b'; assumption.
  - destruct (LEM (merely (exists a', a' < a /\ (a' = b \/ b < a')))) as [H2 | H2]; try exact _.
    + revert H2. rapply Trunc_rec. intros [a' [a'_a Ha']].
      revert Ha'. rapply Trunc_rec. intros [a'_b | b_a'].
      * apply tr. right. apply tr. right. rewrite <- a'_b. exact a'_a.
      * apply tr. right. apply tr. right. transitivity a'; assumption.
    + apply tr. right. apply tr. left.
      apply extensionality. intros c. split.
      * intros c_a. apply LEM_to_DNE; try exact _. intros not_c_b.
        apply H2. apply tr. exists c. split.
        -- exact c_a.
        -- refine (Trunc_rec _ (IHa c c_a b)). intros [c_b | H3].
           ++ apply Empty_rec. exact (not_c_b c_b).
           ++ exact H3.
      * intros c_b. apply LEM_to_DNE; try exact _. intros not_c_a.
        apply H1. apply tr. exists c. split.
        -- exact c_b.
        -- refine (Trunc_rec _ (IHb c c_b)). intros [a_c | H3].
           ++ apply tr. right. exact a_c.
           ++ refine (Trunc_rec _ H3). intros [a_c | c_a].
              ** apply tr. left. exact a_c.
              ** apply tr. right. apply Empty_rec. exact (not_c_a c_a).
Qed.

Lemma ordinal_has_minimal_hsolutions {lem : ExcludedMiddle} (A : Ordinal) (P : A -> HProp)
  : merely (exists a, P a) -> merely (exists a, P a /\ forall b, P b -> a < b \/ a = b).
Proof.
  intros H'. eapply merely_destruct; try apply H'.
  intros [a Ha]. induction (well_foundedness a) as [a _ IH].
  destruct (LEM (merely (exists b, P b /\ b < a)) _) as [H|H].
  - eapply merely_destruct; try apply H. intros [b Hb]. apply (IH b); apply Hb.
  - apply tr. exists a. split; try apply Ha. intros b Hb.
    specialize (trichotomy_ordinal a b). intros H1.
    eapply merely_destruct; try apply H1.
    intros [H2|H2]. { apply tr. by left. }
    eapply merely_destruct; try apply H2.
    intros [H3|H3]. { apply tr. by right. }
    apply Empty_rec, H, tr. exists b. by split.
Qed.

(** * Simulations *)

(* We define the notion of simulations between arbitrary relations. For simplicity, most lemmas about simulations are formulated for ordinals only, even if they do not need all properties of ordinals. The only exception is isordinal_simulation which can be used to prove that a relation is an ordinal. *)

Class IsSimulation {A B : Type} {R__A : Lt A} {R__B : Lt B} (f : A -> B) :=
  { simulation_is_hom {a a'}
    : a < a' -> f a < f a'
    ; simulation_is_merely_minimal {a b}
      : b < f a -> hexists (fun a' => a' < a /\ f a' = b)
  }.
Arguments simulation_is_hom {_ _ _ _} _ {_ _ _}.

Global Instance ishprop_IsSimulation `{Funext}
         {A B : Ordinal} (f : A -> B) :
  IsHProp (IsSimulation f).
Proof.
  eapply istrunc_equiv_istrunc.
  - issig.
  - exact _.
Qed.

Global Instance isinjective_simulation
         {A : Type} {R : Lt A} `{IsOrdinal A R}
         {B : Type} {Q : Lt B} `{IsOrdinal B Q}
         (f : A -> B) {is_simulation : IsSimulation f}
  : IsInjective f.
Proof.
  intros a. induction (well_foundedness a) as [a _ IHa].
  intros b.
  revert a IHa. induction (well_foundedness b) as [b _ IHb]. intros a IHa.
  intros fa_fb. apply extensionality; intros c. split.
  - intros c_a.
    assert (fc_fa : f c < f a)
      by exact (simulation_is_hom f c_a).
    assert (fc_fb : f c < f b)
      by (rewrite <- fa_fb; exact fc_fa).
    assert (H1 : hexists (fun c' => c' < b /\ f c' = f c))
      by exact (simulation_is_merely_minimal fc_fb).
    refine (Trunc_rec _ H1). intros (c' & c'_b & fc'_fc).
    assert (c = c') as ->. {
      apply IHa.
      + exact c_a.
      + symmetry. exact fc'_fc.
    }
    exact c'_b.
  - intros c_b.
    assert (fc_fb : f c < f b)
      by exact (simulation_is_hom f c_b).
    assert (fc_fa : f c < f a)
      by (rewrite fa_fb; exact fc_fb).
    assert (H1 : hexists (fun c' => c' < a /\ f c' = f c))
      by exact (simulation_is_merely_minimal fc_fa).
    refine (Trunc_rec _ H1). intros (c' & c'_a & fc'_fc).
    assert (c' = c) as <-.
    + apply IHb.
      * exact c_b.
      * intros a' a'_c'. apply IHa. exact (transitivity a'_c' c'_a).
      * exact fc'_fc.
    + exact c'_a.
Qed.


Lemma simulation_is_minimal
      {A : Type} {R : Lt A} `{IsOrdinal A R}
      {B : Type} {Q : Lt B} `{IsOrdinal B Q}
      (f : A -> B) {is_simulation : IsSimulation f}
  : forall {a b}, b < f a -> exists a', a' < a /\ f a' = b.
Proof.
  intros a b H1.
  refine (Trunc_rec _ (simulation_is_merely_minimal H1)). {
    apply hprop_allpath. intros (a1 & ? & p) (a2 & ? & <-).
    apply path_sigma_hprop; cbn. apply (injective f). exact p.
  }
  exact idmap.
Qed.


Lemma path_simulation `{Funext}
      {A B : Ordinal}
      (f : A -> B) {is_simulation_f : IsSimulation f}
      (g : A -> B) {is_simulation_g : IsSimulation g}
  : f = g.
Proof.
  apply path_forall; intros a.
  induction (well_foundedness a) as [a _ IH].
  apply (extensionality (f a) (g a)).
  intros b.
  split.
  - intros b_fa.
    destruct (simulation_is_minimal f b_fa) as (a' & a'_a & <-).
    rewrite (IH _ a'_a). apply (simulation_is_hom g). exact a'_a.
  - intros b_ga.
    destruct (simulation_is_minimal g b_ga) as (a' & a'_a & <-).
    rewrite <- (IH _ a'_a). apply (simulation_is_hom f). exact a'_a.
Qed.


Global Instance is_simulation_isomorphism
         {A : Type} {R__A : Lt A}
         {B : Type} {R__B : Lt B}
         (f : Isomorphism (A; R__A) (B; R__B))
  : IsSimulation f.1.
Proof.
  constructor.
  - intros a a' a_a'. apply f.2. exact a_a'.
  - intros a b b_fa. apply tr. exists (f.1^-1 b). split.
    + apply f.2. rewrite eisretr. exact b_fa.
    + apply eisretr.
Qed.


Global Instance ishprop_Isomorphism `{Funext} (A B : Ordinal)
  : IsHProp (Isomorphism A B).
Proof.
  apply hprop_allpath; intros f g. apply path_sigma_hprop; cbn.
  apply path_equiv. apply path_simulation; exact _.
Qed.


Global Instance ishset_Ordinal `{Univalence}
  : IsHSet Ordinal.
Proof.
  apply istrunc_S.
  intros A B.
  apply (istrunc_equiv_istrunc (Isomorphism A B)). {
    apply equiv_path_Ordinal.
  }
  exact _.
Qed.



Lemma isordinal_simulation
      {A : Type}
     `{IsHSet A}

      {R : Lt A}
      {mere : is_mere_relation _ R}

      {B : Type}
      {Q : Lt B}
     `{IsOrdinal B Q}

      (f : A -> B)
     `{IsInjective _ _ f}
      {is_simulation : IsSimulation f}

  : IsOrdinal A R.
Proof.
  constructor.
  - exact _.
  - exact _.
  - intros a a' H1. apply (injective f). apply extensionality.
    intros b. split.
    + intros b_fa. refine (Trunc_rec _ (simulation_is_merely_minimal b_fa)).
      intros [a0 [a0_a <-]].
      apply (simulation_is_hom f). apply H1. exact a0_a.
    + intros b_fa'. refine (Trunc_rec _ (simulation_is_merely_minimal b_fa')).
      intros [a0 [a0_a' <-]].
      apply (simulation_is_hom f). apply H1. exact a0_a'.
  - intros a. remember (f a) as b eqn: fa_b.
    revert a fa_b. induction (well_foundedness b) as [b _ IH]. intros a <-.
    constructor; intros a' a'_a. apply (IH (f a')).
    + apply (simulation_is_hom f). exact a'_a.
    + reflexivity.
  - intros a b c a_b b_c.
    assert (fa_fc : f a < f c). {
      transitivity (f b). {
        apply (simulation_is_hom f). exact a_b.
      }
      apply (simulation_is_hom f). exact b_c.
    }
    refine (Trunc_rec _ (simulation_is_merely_minimal fa_fc)).
    intros [a' [a'_c fa'_fa]]. apply (injective f) in fa'_fa. subst a'.
    exact a'_c.
Qed.





(** * Initial segments *)

Definition initial_segment `{PropResizing}
           {A : Type} {R : Lt A} `{IsOrdinal A R} (a : A)
  : Ordinal.
Proof.
  srefine {| ordinal_carrier := {b : A & smalltype (b < a)}
           ; ordinal_relation := fun x y => x.1 < y.1
           |};
    try exact _.
  srapply (isordinal_simulation pr1).
  - unfold lt. exact _.
  - exact _.
  - exact _.
  - constructor.
    + intros x y x_y. exact x_y.
    + intros b a' a'_b; cbn in *. apply tr.
      assert (b_a : b.1 < a). {
        exact ((equiv_smalltype _) b.2).
      }
      srapply exist. {
        exists a'.
        apply equiv_smalltype. exact (transitivity a'_b b_a).
      }
      cbn. split.
      * exact a'_b.
      * reflexivity.
Defined.

Declare Scope Ordinals.
Open Scope Ordinals.

Notation "↓ a" := (initial_segment a) (at level 4, format "↓ a") : Ordinals.
(* 3 is the level of most unary postfix operators in the standard lib, e.g. f^-1 *)

Definition in_
          `{PropResizing}
           {A : Ordinal} {a : A}
           (x : A) (H : x < a)
  : ↓a
  := (x; (equiv_smalltype _)^-1 H).

Definition out
           `{PropResizing}
           {A : Ordinal} {a : A}
  : ↓a -> A
  := pr1.

Definition initial_segment_property `{PropResizing}
  {A : Ordinal} {a : A}
  : forall x : ↓a, out x < a.
Proof.
  intros x. exact (equiv_smalltype _ (proj2 x)).
Defined.


Global Instance is_simulation_out `{PropResizing}
  {A : Ordinal} (a : A)
  : IsSimulation (out : ↓a -> A).
Proof.
  unfold out.
  constructor.
  - auto.
  - intros x a' a'_x. apply tr.
    assert (a'_a : a' < a). {
      transitivity (out x). {
        assumption.
      }
      apply initial_segment_property.  (* TODO: Rename? *)
    }
    exists (in_ a' a'_a); cbn. auto.
Qed.


Global Instance isinjective_initial_segment `{Funext} `{PropResizing}
  (A : Ordinal)
  : IsInjective (initial_segment : A -> Ordinal).
Proof.
  enough (H1 : forall a1 a2 : A, ↓a1 = ↓a2 -> forall b : ↓a1, out b < a2). {
    intros a1 a2 p. apply extensionality; intros b. split.
    - intros b_a1. exact (H1 a1 a2 p (in_ b b_a1)).
    - intros b_a2. exact (H1 a2 a1 p^ (in_ b b_a2)).
  }

  intros a1 a2 p b.
  assert (out = transport (fun B : Ordinal => B -> A) p^ out)
    as ->. {
    apply path_simulation.
    - exact _.
    - apply transportD. exact _.
  }
  rewrite transport_arrow_toconst. rewrite inv_V. apply initial_segment_property.
Qed.

Lemma equiv_initial_segment_simulation
      `{PropResizing}
      {A : Type@{A}} {R : Lt@{_ R} A} `{IsOrdinal A R}
      {B : Type@{B}} {Q : Lt@{_ Q} B} `{IsOrdinal B Q}
      (f : A -> B) {is_simulation : IsSimulation f} (a : A)
  : Isomorphism ↓(f a) ↓a.
Proof.
  apply isomorphism_inverse.
  srapply exist.
  - srapply equiv_adjointify.
    + intros x. exists (f x.1). apply (equiv_smalltype _)^-1.
      rapply simulation_is_hom. apply (equiv_smalltype _). exact x.2.
    + intros x.
      assert (x_fa : x.1 < f a). {
        exact ((equiv_smalltype _) x.2).
      }
      destruct (simulation_is_minimal f x_fa) as (a' & a'_a & _).
      exact (a'; (equiv_smalltype _)^-1 a'_a).
    + cbn. intros x. apply path_sigma_hprop; cbn.
      transparent assert (x_fa : (x.1 < f a)). {
        exact (equiv_smalltype _ x.2).
      }
      exact (snd (simulation_is_minimal f x_fa).2).
    + cbn. intros x. apply path_sigma_hprop; cbn.
      transparent assert (x_a : (x.1 < a)). {
        exact (equiv_smalltype _ x.2).
      }
      apply (injective f).
      cbn. unfold initial_segment_property. cbn.
      rewrite eisretr.
      exact (snd (simulation_is_minimal f (simulation_is_hom f x_a)).2).
  - cbn. intros [x x_a] [y y_a]; cbn. split.
    + apply (simulation_is_hom f).
    + intros fx_fy.
      destruct (simulation_is_minimal f fx_fy) as (a' & a'_y & p).
      apply injective in p; try exact _. subst a'. exact a'_y.
Qed.

Lemma path_initial_segment_simulation `{Univalence}
      `{PropResizing}
      {A : Type} {R : Lt A} `{IsOrdinal A R}
      {B : Type} {Q : Lt B} `{IsOrdinal B Q}
      (f : A -> B) {is_simulation : IsSimulation f} (a : A)
  : ↓(f a) = ↓a.
Proof.
  apply equiv_path_Ordinal. apply (equiv_initial_segment_simulation f).
Qed.

(** * `Ordinal` is an ordinal *)

Global Instance lt_Ordinal@{carrier relation +} `{PropResizing}
  : Lt Ordinal@{carrier relation}
  := fun A B => exists b : B, A = ↓b.

Global Instance is_mere_relation_lt_on_Ordinal `{Univalence} `{PropResizing}
  : is_mere_relation Ordinal lt_Ordinal.
Proof.
  intros A B.
  apply ishprop_sigma_disjoint.
  intros b b' -> p. apply (injective initial_segment). exact p.
Qed.

Definition bound `{PropResizing}
  {A B : Ordinal} (H : A < B)
  : B
  := H.1.

(* We use this notation to hide the proof of A < B that `bound` takes as an argument *)
Notation "A ◁ B" := (@bound A B _) (at level 70) : Ordinals.

Definition bound_property `{PropResizing}
  {A B : Ordinal} (H : A < B)
  : A = ↓(bound H)
  := H.2.

Lemma isembedding_initial_segment `{PropResizing} `{Univalence}
  {A : Ordinal} (a b : A)
  : a < b <-> ↓a < ↓b.
Proof.
  split.
  - intros a_b. exists (in_ a a_b).
    exact (path_initial_segment_simulation out (in_ a a_b)).
  - intros a_b.
    assert (a = out (bound a_b))
           as ->. {
      apply (injective initial_segment).
      rewrite (path_initial_segment_simulation out).
      apply bound_property.
    }
    apply initial_segment_property.
Qed.

Global Instance Ordinal_is_ordinal `{PropResizing} `{Univalence}
  : IsOrdinal Ordinal (<).
Proof.
  constructor.
  - exact _.
  - exact is_mere_relation_lt_on_Ordinal.
  - intros A B H1.
    srapply path_Ordinal.
    + srapply equiv_adjointify.
      * assert (lt_B : forall a : A, ↓a < B). {
          intros a. apply H1. exists a. reflexivity.
        }
        exact (fun a => bound (lt_B a)).
      * assert (lt_A : forall b : B, ↓b < A). {
          intros b. apply H1. exists b. reflexivity.
        }
        exact (fun b => bound (lt_A b)).
      * cbn. intros b. apply (injective initial_segment).
        repeat rewrite <- bound_property. reflexivity.
      * cbn. intros a. apply (injective initial_segment).
        repeat rewrite <- bound_property. reflexivity.
    + cbn. intros a a'. split.
      * intros a_a'.
        apply isembedding_initial_segment.
        repeat rewrite <- bound_property.
        apply isembedding_initial_segment.
        assumption.
      * intros a_a'.
        apply isembedding_initial_segment in a_a'.
        repeat rewrite <- bound_property in a_a'.
        apply isembedding_initial_segment in a_a'.
        assumption.
  - intros A.
    constructor. intros ? [a ->].
    induction (well_foundedness a) as [a _ IH].
    constructor. intros ? [x ->].
    rewrite <- (path_initial_segment_simulation out).
    apply IH. apply initial_segment_property.
  - intros ? ? A [x ->] [a ->]. exists (out x).
    rewrite (path_initial_segment_simulation out).
    reflexivity.
Qed.


(* This is analogous to the set-theoretic statement that an ordinal is the set of all smaller ordinals. *)
Lemma isomorphism_to_initial_segment `{PropResizing} `{Univalence}
  (B : Ordinal@{A _})
  : Isomorphism B ↓B.
Proof.
  srapply exist.
  - srapply equiv_adjointify.
    + intros b. exists ↓b.
      apply equiv_smalltype.
      exists b. reflexivity.
    + intros [C HC]. eapply equiv_smalltype in HC.
      exact (bound HC).
    + cbn. intros [C HC]. apply path_sigma_hprop; cbn.
      symmetry. apply bound_property.
    + cbn. intros x. rewrite eisretr. reflexivity.
  - cbn. intros b b'. apply isembedding_initial_segment.
Qed.

(** But an ordinal isn't isomorphic to any initial segment of itself. *)
Lemma ordinal_initial `{PropResizing} `{Univalence} (O : Ordinal) (a : O)
  : Isomorphism O ↓a -> Empty.
Proof.
  intros p % equiv_path_Ordinal.
  enough (HO : O < O) by apply (irreflexive_ordinal_relation _ _ _ _ HO).
  exists a. apply p.
Qed.

(** * Ordinal successor *)

Definition successor (A : Ordinal) : Ordinal.
Proof.
  set (carrier := (A + Unit)%type).
  set (relation (x y : carrier) :=
         match x, y with
         | inl x, inl y => x < y
         | inl x, inr _ => Unit
         | inr _, inl y => Empty
         | inr _, inr _ => Empty
         end).
  exists carrier relation. constructor.
  - exact _.
  - intros [x | ?] [y | ?]; cbn; exact _.
  - intros [x | []] [y | []] H.
    + f_ap. apply extensionality. intros z. exact (H (inl z)).
    + enough (H0 : relation (inl x) (inl x)). {
        cbn in H0. destruct (irreflexivity _ _ H0).
      }
      apply H. cbn. exact tt.
    + enough (H0 : relation (inl y) (inl y)). {
        cbn in H0. destruct (irreflexivity _ _ H0).
      }
      apply H. cbn. exact tt.
    + reflexivity.
  - assert (H : forall a, Accessible relation (inl a)). {
      intros a. induction (well_foundedness a) as [a _ IH].
      constructor; intros [b | []]; cbn; intros H.
      + apply IH. exact H.
      + destruct H.
    }
    intros [x | []].
    + apply H.
    + constructor; intros [b | []]; cbn; intros H0.
      * apply H.
      * destruct H0.
  - intros [x | []] [y | []] [z | []]; cbn; auto.
    intros _ [].
Defined.


Lemma lt_successor `{PropResizing} `{Univalence} (A : Ordinal)
  : A < successor A.
Proof.
  exists (inr tt).
  srapply path_Ordinal.
  - srapply equiv_adjointify.
    + intros a. srapply in_.
      * exact (inl a).
      * exact tt.
    + intros [[a | []] Ha]; cbn in *.
      * exact a.
      * apply equiv_smalltype in Ha. destruct Ha.
    + intros [[a | []] Ha].
      * unfold in_. cbn. f_ap.
        assert (IsHProp (smalltype Unit)) by exact _.
        apply path_ishprop.
      * destruct (equiv_smalltype _ Ha).
    + intros a. reflexivity.
  - cbn. intros a a'. reflexivity.
Qed.

(** * Ordinal limit *)

Section Image.

  Universes i j.
  (** In the following, there are no constraints between [i] and [j]. *)
  Context `{PropResizing} `{Funext} {A : Type@{i}} {B : HSet@{j}} (f : A -> B).

  Local Definition qkfs := quotient_kernel_factor_small f.
  Local Definition image : Type@{i} := qkfs.1.
  Local Definition factor1 : A -> image := qkfs.2.1.
  Local Definition factor2 : image -> B := qkfs.2.2.1.
  Local Definition isinjective_factor2 : IsInjective factor2
    := isinj_embedding _ (snd (fst qkfs.2.2.2)).
  Local Definition image_ind_prop (P : image -> Type@{k}) `{forall x, IsHProp (P x)}
    (step : forall a : A, P (factor1 a))
    : forall x : image, P x
    := Quotient_ind_hprop _ P step.
  (** [factor2 o factor1 == f] is definitional, so we don't state that. *)

End Image.

Definition limit `{Univalence} `{PropResizing}
           {X : Type} (F : X -> Ordinal) : Ordinal.
Proof.
  set (f := fun x : {i : X & F i} => ↓x.2).
  set (carrier := image f : Type@{i}).
  set (relation := fun A B : carrier =>
                     smalltype (factor2 f A < factor2 f B)
                     : Type@{i}).
  exists carrier relation.
  snrapply (isordinal_simulation (factor2 f)).
  1-4: exact _.
  - apply isinjective_factor2.
  - constructor.
    + intros x x' x_x'.
      unfold lt, relation. apply equiv_smalltype in x_x'. exact x_x'.
    + nrefine (image_ind_prop f _ _). 1: exact _.
      intros a.
      change (factor2 f (class_of _ a)) with (f a).
      intros B B_fa. apply tr.
      exists (factor1 f (a.1; out (bound B_fa))).
      unfold lt, relation.
      change (factor2 f (factor1 f ?A)) with (f A).
      unfold f.
      assert (↓(out (bound B_fa)) = B) as ->. {
        rewrite (path_initial_segment_simulation out).
        symmetry. apply bound_property.
      }
      split.
      * apply equiv_smalltype. exact B_fa.
      * reflexivity.
Defined.

Global Instance le_on_Ordinal : Le Ordinal :=
  fun A B => exists f : A -> B, IsSimulation f.

Definition limit_is_upper_bound `{Univalence} `{PropResizing}
           {X : Type} (F : X -> Ordinal)
  : forall x, F x <= limit F.
Proof.
  set (f := fun x : {i : X & F i} => ↓x.2).
  intros x. unfold le, le_on_Ordinal.
  exists (fun u => factor1 f (x; u)).
  split.
  - intros u v u_v.
    change (smalltype (f (x; u) < f (x; v))).
    apply equiv_smalltype.
    apply isembedding_initial_segment. exact u_v.
  - intros u.
    nrefine (image_ind_prop f _ _). 1: exact _.
    intros a a_u.
    change (smalltype (f a < f (x; u))) in a_u.
    apply equiv_smalltype in a_u.
    apply tr. exists (out (bound a_u)). split.
    + apply initial_segment_property.
    + apply (isinjective_factor2 f); simpl.
      change (factor2 f (factor1 f ?A)) with (f A).
      unfold f.
      rewrite (path_initial_segment_simulation out).
      symmetry. apply bound_property.
Qed.

(** Any type equivalent to an ordinal is an ordinal, and we can change the universe that the relation takes values in. *)

(* TODO: Should factor this into two results:  (1) Anything equivalent to an ordinal is an ordinal (with the relation landing in the same universe for both).  (2) Under PropResizing, the universe that the relation takes values in can be changed. *)
Definition resize_ordinal@{i j +} `{PropResizing} (B : Ordinal@{i _}) (C : Type@{j}) (g : C <~> B)
  : Ordinal@{j _}.
Proof.
  exists C (fun c1 c2 : C => smalltype (g c1 < g c2)).
  snrapply (isordinal_simulation g). 2, 3, 4, 5: exact _.
  - apply (istrunc_equiv_istrunc B (equiv_inverse g)).
  - constructor.
    + intros a a' a_a'. apply (equiv_smalltype _). exact a_a'.
    + intros a b b_fa. apply tr. exists (g^-1 b). split.
      * apply equiv_smalltype. rewrite eisretr. exact b_fa.
      * apply eisretr.
Defined.

Lemma resize_ordinal_iso@{i j +} `{PropResizing} (B : Ordinal@{i _}) (C : Type@{j}) (g : C <~> B)
  : Isomorphism (resize_ordinal B C g) B.
Proof.
  exists g. intros a a'. cbn. split; apply equiv_smalltype.
Qed.
