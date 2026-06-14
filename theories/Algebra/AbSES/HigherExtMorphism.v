From HoTT Require Import Basics Types.
From HoTT.WildCat Require Import Core.
Require Import Truncations.Core.
Require Import Colimits.Quotient.
Require Import AbGroups.AbelianGroup AbGroups.AbHom.
Require Import Algebra.AbSES.Core Algebra.AbSES.Pushout Algebra.AbSES.Pullback
  Algebra.AbSES.BaerSum Algebra.AbSES.HigherExt.
Require Import Groups.Group.

Local Open Scope type_scope.

(** * Morphisms of length-[n] exact sequences

    A morphism of length-[n] sequences (Christensen and Flaten, Definition 2.4.4)
    fixes the two endpoints and gives a map of each intermediate module
    commuting with the splice maps.  We show that the relation [abses_es_rel]
    and the existence of such a morphism are logically equivalent (Lemma 2.4.5),
    and deduce that the set-quotient by morphisms agrees with [abses_ext]
    (Remark 2.4.6). *)

Section LengthNMorphism.
  Context `{Univalence}.

  (** A morphism of length-[n] sequences over a base map [β], fixing the deep
      coefficient. *)
  Definition abses_es_mor
    : forall (n : nat) (B B' A : AbGroup@{u}), (B $-> B')
        -> abses_es n B A -> abses_es n B' A -> Type.
  Proof.
    induction n as [|n IH]; intros B B' A β.
    - exact (fun E F => E = grp_homo_compose F β).
    - revert IH; destruct n as [|p]; intro IH.
      + exact (fun E F => { φ : AbSESMorphism E F
                            & (component1 φ == grp_homo_id)
                              * (component3 φ == β) }).
      + exact (fun E F => { γ : E.1 $-> F.1
                            & IH E.1 F.1 A γ (fst E.2) (fst F.2)
                              * { φ : AbSESMorphism (snd E.2) (snd F.2)
                                  & (component1 φ == γ)
                                    * (component3 φ == β) } }).
  Defined.

  Arguments abses_es_mor n {B B' A} β.

  (** The identity-ends morphism induced by a path of short exact sequences. *)
  Definition abses_morphism_of_path {B A : AbGroup@{u}} {E F : AbSES B A}
    (p : E = F)
    : AbSESMorphism E F
    := transport (fun X => AbSESMorphism E X) p (abses_morphism_id E).

  Definition component1_abses_morphism_of_path {B A : AbGroup@{u}}
    {E F : AbSES B A} (p : E = F)
    : component1 (abses_morphism_of_path p) == grp_homo_id.
  Proof.
    destruct p; exact (fun _ => idpath).
  Defined.

  Definition component3_abses_morphism_of_path {B A : AbGroup@{u}}
    {E F : AbSES B A} (p : E = F)
    : component3 (abses_morphism_of_path p) == grp_homo_id.
  Proof.
    destruct p; exact (fun _ => idpath).
  Defined.

  (** A morphism over [β] yields the relation to the pullback along [β]. *)
  Definition abses_es_mor_to_rel
    : forall (n : nat) {B B' A : AbGroup@{u}} (β : B $-> B')
        (E : abses_es n B A) (F : abses_es n B' A),
      abses_es_mor n β E F -> abses_es_rel n E (abses_es_pullback n β F).
  Proof.
    intro n; induction n as [|[|n] IH]; intros B B' A β E F mor.
    - exact mor.
    - destruct mor as [φ [hα hβ]].
      refine (abses_pullback_component1_id φ hα @ _).
      exact (ap (fun g => abses_pullback g F) (equiv_path_grouphomomorphism hβ)).
    - destruct mor as [γ [morrec [φ [hα hβ]]]].
      exists γ.
      refine (IH _ _ _ γ (fst E.2) (fst F.2) morrec, _).
      refine ((ap (fun g => abses_pushout g (snd E.2))
                 (equiv_path_grouphomomorphism hα))^ @ _).
      refine (abses_pushout_is_pullback φ @ _).
      exact (ap (fun g => abses_pullback g (snd F.2))
               (equiv_path_grouphomomorphism hβ)).
  Defined.

  (** Conversely, the relation to the pullback along [β] yields a morphism. *)
  Definition abses_es_rel_to_mor
    : forall (n : nat) {B B' A : AbGroup@{u}} (β : B $-> B')
        (E : abses_es n B A) (F : abses_es n B' A),
      abses_es_rel n E (abses_es_pullback n β F) -> abses_es_mor n β E F.
  Proof.
    intro n; induction n as [|[|n] IH]; intros B B' A β E F rel.
    - exact rel.
    - exists (absesmorphism_compose (abses_pullback_morphism F β)
                (abses_morphism_of_path rel)).
      refine (_, _).
      + intro x; exact (component1_abses_morphism_of_path rel x).
      + intro x; exact (ap β (component3_abses_morphism_of_path rel x)).
    - destruct rel as [γ [relrec q]].
      exists γ.
      refine (IH _ _ _ γ (fst E.2) (fst F.2) relrec, _).
      exists (absesmorphism_compose (abses_pullback_morphism (snd F.2) β)
                (absesmorphism_compose (abses_morphism_of_path q)
                   (abses_pushout_morphism (snd E.2) γ))).
      refine (_, _).
      + intro x.
        exact (component1_abses_morphism_of_path q (γ x)).
      + intro x.
        exact (ap β (component3_abses_morphism_of_path q x)).
  Defined.

  (** A morphism of length-[n] sequences fixing both endpoints (the base map is
      the identity). *)
  Definition abses_es_morphism (n : nat) {B A : AbGroup@{u}}
    (E F : abses_es n B A) : Type
    := abses_es_mor n grp_homo_id E F.

  (** The relation and morphism-existence are logically equivalent. *)
  Definition iff_abses_es_rel_morphism (n : nat) {B A : AbGroup@{u}}
    (E F : abses_es n B A)
    : abses_es_rel n E F <-> abses_es_morphism n E F.
  Proof.
    split.
    - intro rel.
      apply (abses_es_rel_to_mor n grp_homo_id E F).
      exact (transport (abses_es_rel n E) (abses_es_pullback_id n F)^ rel).
    - intro mor.
      refine (transport (abses_es_rel n E) (abses_es_pullback_id n F) _).
      exact (abses_es_mor_to_rel n grp_homo_id E F mor).
  Defined.

End LengthNMorphism.

(** ** The morphism quotient *)

Section MorphismQuotient.
  Context `{Univalence}.

  (** The set-quotient of length-[n] sequences by morphism-existence agrees
      with [abses_ext]. *)
  Definition equiv_abses_ext_morphism (n : nat) (B A : AbGroup@{u})
    : abses_ext n B A <~> Quotient (abses_es_morphism n (B:=B) (A:=A)).
  Proof.
    srapply equiv_adjointify.
    - srapply (Quotient_functor _ _ idmap).
      exact (fun E F => fst (iff_abses_es_rel_morphism n E F)).
    - srapply (Quotient_functor _ _ idmap).
      exact (fun E F => snd (iff_abses_es_rel_morphism n E F)).
    - srapply Quotient_ind_hprop; intro E; reflexivity.
    - srapply Quotient_ind_hprop; intro E; reflexivity.
  Defined.

End MorphismQuotient.
