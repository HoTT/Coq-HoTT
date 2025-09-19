From HoTT Require Import Basics Types.
Require Import WildCat Pointed.Core.
Require Import AbGroups.AbelianGroup AbGroups.Biproduct AbGroups.AbHom.
Require Import AbSES.Core AbSES.Pullback AbSES.Pushout AbSES.DirectSum.
Require Import Homotopy.HSpace.Core.

Local Open Scope mc_scope.
Local Open Scope mc_add_scope.

(** * The Baer sum of two short exact sequences, lemmas and consequences. *)

(** The Baer sum of two short exact sequences is obtained from the pointwise direct sum by pushing forward along the codiagonal and then pulling back along the diagonal. (Swapping the order of pushing forward and pulling back produces an isomorphic short exact sequence.) *)
Definition abses_baer_sum `{Univalence} {B A : AbGroup@{u}} (E F : AbSES B A)
  : AbSES B A
  := abses_pullback ab_diagonal (abses_pushout ab_codiagonal (abses_direct_sum E F)).


(** ** [AbSES'] is a bifunctor *)

(** Given a morphism [f] of short exact sequences, the pushout of the domain along [f_1] equals the pullback of the codomain along [f_3]. *)
Lemma abses_pushout_is_pullback' `{Univalence} {A A' B B' : AbGroup@{u}}
      {E : AbSES B A} {E' : AbSES B' A'} (f : AbSESMorphism E E')
  : abses_pushout (component1 f) E $== abses_pullback (component3 f) E'.
Proof.
  (* The morphism [f : E -> E'] factors as [E -> f_1 E -> E'], where the first map is the map defining the pushout [f_1 E] and the second map is denoted [abses_pushout_morphism_rec f] below.  This second map is the identity on the first component, so it presents its domain as the pullback of [E'] along [f_3]. *)
  exact (abses_pullback_component1_id' (abses_pushout_morphism_rec f) (fun _ => idpath)).
Defined.

(** Given a morphism [f] of short exact sequences, the pushout of the domain along [f_1] equals the pullback of the codomain along [f_3]. *)
Definition abses_pushout_is_pullback `{Univalence} {A A' B B' : AbGroup}
      {E : AbSES B A} {E' : AbSES B' A'} (f : AbSESMorphism E E')
  : abses_pushout (component1 f) E = abses_pullback (component3 f) E'
  := equiv_path_abses_iso (abses_pushout_is_pullback' f).

Definition abses_pushout_pullback_reorder' `{Univalence} {A A' B B' : AbGroup}
  (E : AbSES B A) (f : A $-> A') (g : B' $-> B)
  : abses_pushout f (abses_pullback g E) $== abses_pullback g (abses_pushout f E).
Proof.
  (* There are morphisms [Eg -> E] and [E -> fE] by definition of the pullback and pushout. We define [F : Eg -> fE] to be the composite. Its first and third components are [f o id] and [id o g]. *)
  pose (F := absesmorphism_compose (abses_pushout_morphism E f) (abses_pullback_morphism E g)).
  (* We change [F] to a morphism that is the same except that the first and third components are [f] and [g]. Then [abses_pushout_is_pullback] shows that the pushout of [Eg] along [f] is equal to the pullback of [fE] along [g]. *)
  refine (abses_pushout_is_pullback' (Build_AbSESMorphism f (component2 F) g _ _)); apply F.
Defined.

(** This is the statement that [AbSES'] is a bifunctor, but we state it separately because Coq is slow to unify [IsBifunctor AbSES'] against goals written in this form. *)
Definition abses_pushout_pullback_reorder `{Univalence} {A A' B B' : AbGroup}
  (E : AbSES B A) (f : A $-> A') (g : B' $-> B)
  : abses_pushout f (abses_pullback g E) = abses_pullback g (abses_pushout f E).
Proof.
  apply equiv_path_abses_iso.
  apply abses_pushout_pullback_reorder'.
Defined.

Instance is0bifunctor_abses' `{Univalence}
  : Is0Bifunctor (AbSES' : AbGroup^op -> AbGroup -> Type)
  := Build_Is0Bifunctor'' _.

Instance is1bifunctor_abses' `{Univalence}
  : Is1Bifunctor (AbSES' : AbGroup^op -> AbGroup -> Type).
Proof.
  snapply Build_Is1Bifunctor''.
  1,2: exact _.
  intros ? ? g ? ? f E; cbn.
  exact (abses_pushout_pullback_reorder E f g).
Defined.

(** Given a short exact sequence [A -> E -> B] and maps [f : A -> A'], [g : B' -> B], we can change the order of pushing out along [f] and pulling back along [g]. *)
Lemma abses_reorder_pullback_pushout `{Univalence} {A A' B B' : AbGroup}
      (E : AbSES B A) (f : A $-> A') (g : B' $-> B)
  : abses_pushout f (abses_pullback g E) = abses_pullback g (abses_pushout f E).
Proof.
  (* There are morphisms [Eg -> E] and [E -> fE] by definition of the pullback and pushout. We define [F : Eg -> fE] to be the composite. Its first and third components are [f o id] and [id o g]. *)
  pose (F := absesmorphism_compose (abses_pushout_morphism E f) (abses_pullback_morphism E g)).
  (* We change [F] to a morphism that is the same except that the first and third components are [f] and [g]. Then [abses_pushout_is_pullback] shows that the pushout of [Eg] along [f] is equal to the pullback of [fE] along [g]. *)
  refine (abses_pushout_is_pullback (Build_AbSESMorphism f (component2 F) g _ _)); apply F.
Defined.

(** The Baer sum distributes over pullbacks. *)
Lemma baer_sum_distributive_pullbacks `{Univalence} {A B B' : AbGroup}
  {E : AbSES B A} (f g : ab_hom B' B)
  : abses_pullback (f + g) E = abses_baer_sum (abses_pullback f E) (abses_pullback g E).
Proof.
  unfold abses_baer_sum.
  refine ((abses_pullback_compose (B1:=ab_biprod B B) _ _ E)^ @ _).
  refine (ap (abses_pullback _) (abses_pushout_is_pullback (abses_codiagonal E))^ @ _).
  unfold abses_codiagonal, component1.
  refine (_^ @ _ @ _).
  1,3: apply abses_reorder_pullback_pushout.
  refine (ap (abses_pushout _) _).
  refine (ap (fun h => abses_pullback h _) (ab_biprod_corec_diagonal _ _) @ _).
  refine ((abses_pullback_compose _ _ (abses_direct_sum E E))^ @ _).
  exact (ap (abses_pullback _) (abses_directsum_distributive_pullbacks f g)).
Defined.

(** The Baer sum is commutative. *)
Lemma baer_sum_commutative `{Univalence} {A B : AbGroup} (E F : AbSES B A)
  : abses_baer_sum E F = abses_baer_sum F E.
Proof.
  unfold abses_baer_sum.
  (* The next line uses that [direct_sum_swap $o ab_diagonal] is definitionally equal to [ab_diagonal]: *)
  refine (_ @ abses_pullback_compose ab_diagonal direct_sum_swap _).
  refine (ap (abses_pullback ab_diagonal) _).
  refine (ap (fun f => abses_pushout f _) ab_codiagonal_swap^ @ _).
  refine ((abses_pushout_compose _ _ _) @ _).
  refine (ap _ (abses_pushout_is_pullback (abses_swap_morphism E F)) @ _).
  unfold abses_swap_morphism, component3.
  apply abses_pushout_pullback_reorder.
Defined.

(** The right unit law for the Baer sum says that for all [E : AbSES B A], [E + E_0 = E], where [E_0] is the split short exact sequence. *)
Lemma baer_sum_unit_r `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_baer_sum E (point (AbSES B A)) = E.
Proof.
  refine (ap (abses_baer_sum E) _ @ _).
  - exact (abses_pullback_const E).
  - refine (ap (fun F => abses_baer_sum F (abses_pullback grp_homo_const E)) (abses_pullback_id E)^ @ _).
    refine ((baer_sum_distributive_pullbacks grp_homo_id grp_homo_const)^ @ _).
    refine (ap (fun f => abses_pullback f E) (grp_unit_r (G := ab_hom _ _) _) @ _).
    apply abses_pullback_id.
Defined.

(** The left unit law for the Baer sum is analogous. *)
Definition baer_sum_unit_l `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_baer_sum (point (AbSES B A)) E = E
  := baer_sum_commutative _ _ @ baer_sum_unit_r _.

(** For any [E : AbSES B A], the pullback of [E] along [-id_B] acts as an additive inverse for [E] with respect to the Baer sum. *)
Lemma baer_sum_inverse_l `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_baer_sum E (abses_pullback (- grp_homo_id) E) = point (AbSES B A).
Proof.
  refine (ap (fun F => abses_baer_sum F (abses_pullback _ E)) (abses_pullback_id E)^ @ _).
  refine ((baer_sum_distributive_pullbacks grp_homo_id (-grp_homo_id))^ @ _).
  refine (ap (fun f => abses_pullback f _) (grp_inv_r (G := ab_hom _ _) _) @ _).
  symmetry; apply abses_pullback_const.
Defined.

(** The right inverse law follows by commutativity. *)
Definition baer_sum_inverse_r `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_baer_sum (abses_pullback (-grp_homo_id) E) E = point (AbSES B A)
  := baer_sum_commutative _ _ @ baer_sum_inverse_l _.

(** The Baer sum distributes over pushouts. *)
Lemma baer_sum_distributive_pushouts `{Univalence}
      {A A' B : AbGroup} {E : AbSES B A'} (f g : ab_hom A' A)
  : abses_pushout (f + g) E = abses_baer_sum (abses_pushout f E) (abses_pushout g E).
Proof.
  unfold abses_baer_sum.
  refine (abses_pushout_compose (A1 := ab_biprod A A) _ _ E @ _).
  refine (_ @ abses_pushout_pullback_reorder _ _ _).
  refine (ap (abses_pushout ab_codiagonal) _).
  refine (ap (fun f => abses_pushout f E) (ab_biprod_corec_diagonal f g) @ _).
  refine (abses_pushout_compose _ _ E @ _).
  refine (ap (abses_pushout _) (abses_pushout_is_pullback (abses_diagonal E)) @ _).
  refine (abses_pushout_pullback_reorder _ _ _ @ _).
  exact (ap (abses_pullback _) (abses_directsum_distributive_pushouts f g)).
Defined.

(** Our next goal is to prove that the Baer sum is associative.  Rather than showing this directly, we first prove [baer_sum_twist], which says that [abses_baer_sum (abses_baer_sum E F) G = abses_baer_sum (abses_baer_sum G F) E].  The proof of this mimics the proof of commutativity above.  Then we prove associativity by combining this with commutativity. *)

(** The trinary Baer sum of three short exact sequences. *)
Definition abses_trinary_baer_sum `{Univalence}
  {A B : AbGroup@{u}} (E F G : AbSES B A)
  : AbSES B A
  := abses_pullback ab_triagonal
       (abses_pushout ab_cotriagonal
          (abses_direct_sum (abses_direct_sum E F) G)).

(** For [E, F, G : AbSES B A], the Baer sum of [E], [F] and [G] (associated left) is equal to the trinary Baer sum of [E], [F] and [G]. *)
Lemma baer_sum_is_trinary `{Univalence} {A B : AbGroup@{u}} (E F G : AbSES B A)
  : abses_baer_sum (abses_baer_sum E F) G = abses_trinary_baer_sum E F G.
Proof.
  unfold abses_baer_sum, abses_trinary_baer_sum, ab_triagonal, ab_cotriagonal.
  refine (ap (abses_pullback _ o abses_pushout _) _^ @ _).
  - refine (_ @ ap (abses_direct_sum _) (abses_pullback_id G)).
    refine (_ @ abses_directsum_distributive_pullbacks _ _).
    refine (ap (abses_pullback _) _).
    refine (_ @ ap (abses_direct_sum _) (abses_pushout_id G)).
    apply abses_directsum_distributive_pushouts.
  - refine (ap (abses_pullback _) (abses_pushout_pullback_reorder _ _ _) @ _).
    refine (abses_pullback_compose _ _ _ @ _).
    refine (ap (abses_pullback _) _^).
    apply abses_pushout_compose.
Defined.

(** For [E, F, G : AbSES B A], we can "twist" the order of the trinary Baer sum as follows. *)
Lemma twist_trinary_baer_sum `{Univalence}
  {A B : AbGroup@{u}} (E F G : AbSES B A)
  : abses_trinary_baer_sum E F G = abses_trinary_baer_sum G F E.
Proof.
  unfold abses_trinary_baer_sum.
  (* The next line uses the fact that [ab_triagonal] is definitionally equal to [ab_biprod_twist $o ab_triagonal]: *)
  refine (_ @ abses_pullback_compose ab_triagonal ab_biprod_twist _).
  refine (ap (abses_pullback _) _).
  refine (ap (fun f => abses_pushout f _) ab_cotriagonal_twist^ @ _).
  refine (abses_pushout_compose _ _ _ @ _).
  refine (ap _ (abses_pushout_is_pullback (abses_twist_directsum E F G)) @ _).
  unfold abses_twist_directsum, component3.
  exact (abses_pushout_pullback_reorder _ _ _).
Defined.

(** It now follows that we can twist the order of the summands in the Baer sum. *)
Lemma baer_sum_twist `{Univalence} {A B : AbGroup@{u}} (E F G : AbSES B A)
  : abses_baer_sum (abses_baer_sum E F) G = abses_baer_sum (abses_baer_sum G F) E.
Proof.
  refine ((baer_sum_is_trinary E F G) @ _ @ (baer_sum_is_trinary G F E)^).
  apply twist_trinary_baer_sum.
Defined.

(** From these results, it finally follows that the Baer sum is associative. *)
Lemma baer_sum_associative `{Univalence}
  {A B : AbGroup@{u}} (E F G : AbSES B A)
  : abses_baer_sum (abses_baer_sum E F) G = abses_baer_sum E (abses_baer_sum F G).
Proof.
  refine ((baer_sum_twist _ _ _)^ @ _).
  refine (baer_sum_commutative _ _ @ _).
  apply ap.
  apply baer_sum_commutative.
Defined.

(** The Baer sum makes [AbSES B A] into an H-space. (In fact, a coherent H-space, but we leave that for now.) *)
Instance ishspace_abses `{Univalence} {B A : AbGroup}
  : IsHSpace (AbSES B A).
Proof.
  snapply Build_IsHSpace.
  - exact abses_baer_sum.
  - intro; apply baer_sum_unit_l.
  - intro; apply baer_sum_unit_r.
Defined.

Instance is0bifunctor_abses `{Univalence}
  : Is0Bifunctor (AbSES : AbGroup^op -> AbGroup -> pType)
  := Build_Is0Bifunctor'' _.

Instance is1bifunctor_abses `{Univalence}
  : Is1Bifunctor (AbSES : AbGroup^op -> AbGroup -> pType).
Proof.
  snapply Build_Is1Bifunctor''.
  1,2: exact _.
  intros ? ? f ? ? g.
  rapply hspace_phomotopy_from_homotopy.
  1: exact ishspace_abses.
  intro E; cbn.
  apply abses_pushout_pullback_reorder.
Defined.

(** ** Pushouts and pullbacks respect the Baer sum *)

Definition baer_sum_pushout `{Univalence}
  {A A' B : AbGroup} (f : A $-> A') (E F : AbSES B A)
  : abses_pushout f (abses_baer_sum E F)
    = abses_baer_sum (abses_pushout f E) (abses_pushout f F).
Proof.
  unfold abses_baer_sum.
  refine (abses_pushout_pullback_reorder _ _ _
            @ ap _ _).
  refine ((abses_pushout_compose _ _ _)^ @ _).
  refine (abses_pushout_homotopic _ _ _ _ @ _).
  1: apply ab_codiagonal_natural.
  refine (abses_pushout_compose _ _ _ @ ap _ _).
  apply abses_directsum_distributive_pushouts.
Defined.

Definition baer_sum_pullback `{Univalence}
  {A B B' : AbGroup} (f : B' $-> B) (E F : AbSES B A)
  : abses_pullback f (abses_baer_sum E F)
    = abses_baer_sum (abses_pullback f E) (abses_pullback f F).
Proof.
  unfold abses_baer_sum.
  refine (abses_pullback_compose _ _ _ @ _).
  refine ((abses_pushout_pullback_reorder _ _ _)^
            @ ap _ _
              @ abses_pushout_pullback_reorder _ _ _).
  refine (abses_pullback_homotopic
            _ (functor_ab_biprod f f $o ab_diagonal) _ _ @ _).
  1: reflexivity.
  refine ((abses_pullback_compose _ _ _)^ @ ap _ _).
  apply abses_directsum_distributive_pullbacks.
Defined.
