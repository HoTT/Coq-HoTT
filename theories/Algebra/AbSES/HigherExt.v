From HoTT Require Import Basics Types.
From HoTT.WildCat Require Import Core.
Require Import Truncations.Core Truncations.SeparatedTrunc.
Require Import Universes.HSet.
Require Import Pointed.Core.
Require Import Homotopy.ExactSequence.
Require Import Colimits.Quotient.
Require Import AbelianGroup AbHom Biproduct AbProjective.
Require Import Spaces.FreeInt.
Require Import Groups.Group.
Require Import Algebra.AbSES.Core Algebra.AbSES.Pushout Algebra.AbSES.Pullback
  Algebra.AbSES.BaerSum Algebra.AbSES.DirectSum Algebra.AbSES.Ext
  Algebra.AbSES.PullbackFiberSequence.

(** * Higher Ext groups via length-[n] exact sequences

    Following Christensen and Flaten, "Ext groups in homotopy type theory",
    we define the higher Ext groups [abses_ext n B A] as set-quotients of
    length-[n] exact sequences.  A length-[0] sequence is a homomorphism, a
    length-[1] sequence is a short exact sequence, and a length-[m.+1]
    sequence is a short exact sequence [B <- ... <- C] spliced onto a
    length-[m] sequence [C <- ... <- A].

    The development proceeds in four stages: the type of length-[n]
    sequences and the splice; the functorial operations (pullback, pushout,
    direct sum and Baer sum) on sequences; the relation [⤳] of the paper,
    shown to be an equivalence relation respected by all the operations; and
    the higher Ext groups, with their bifunctoriality, the Yoneda product
    and the Baer sum. *)

Local Open Scope type_scope.

(** ** The type of length-[n] exact sequences *)

Section LengthNSequences.
  Context `{Univalence}.

  Fixpoint abses_es (n : nat) (B A : AbGroup@{u}) : Type :=
    match n with
    | 0%nat => ab_hom B A
    | 1%nat => pointed_type (AbSES B A)
    | S (S _ as m) => { C : AbGroup@{u} & abses_es m C A * pointed_type (AbSES B C) }
    end.

  (** The splice operation, attaching a short exact sequence [B <- ... <- C]
      to the front of a length-[m] sequence [C <- ... <- A].  When [m] is
      zero this pushes the short exact sequence out along the homomorphism;
      otherwise it records the new module and prepends. *)
  Definition abses_es_splice {A B C : AbGroup@{u}} (m : nat)
    : abses_es m C A -> AbSES B C -> abses_es m.+1%nat B A.
  Proof.
    destruct m as [|m].
    - exact (fun f s => abses_pushout f s).
    - exact (fun e s => (C; (e, s))).
  Defined.

End LengthNSequences.

(** ** Operations on length-[n] sequences *)

Section Operations.
  Context `{Univalence}.

  (** Pulling a length-[n] sequence back along [beta : B' -> B] changes only
      the leading short exact sequence (precomposition when [n] is zero). *)
  Definition abses_es_pullback {A : AbGroup@{u}} (n : nat)
    {B B' : AbGroup@{u}} (beta : B' $-> B)
    : abses_es n B A -> abses_es n B' A.
  Proof.
    destruct n as [|[|n]].
    - exact (fun f => grp_homo_compose f beta).
    - exact (fun s => abses_pullback beta s).
    - exact (fun e => (e.1; (fst e.2, abses_pullback beta (snd e.2)))).
  Defined.

  (** Pulling back along the identity is the identity. *)
  Definition abses_es_pullback_id (n : nat) {B A : AbGroup@{u}}
    (E : abses_es n B A)
    : abses_es_pullback n grp_homo_id E = E.
  Proof.
    destruct n as [|[|n0]].
    - apply equiv_path_grouphomomorphism; reflexivity.
    - apply abses_pullback_id.
    - exact (path_sigma' _ 1
        (path_prod (fst E.2, abses_pullback grp_homo_id (snd E.2)) E.2
                   1 (abses_pullback_id (snd E.2)))).
  Defined.

  (** Pullback is contravariantly functorial in the base. *)
  Definition abses_es_pullback_compose (n : nat)
    {A B0 B1 B2 : AbGroup@{u}} (f : B0 $-> B1) (g : B1 $-> B2)
    (Z : abses_es n B2 A)
    : abses_es_pullback n (g $o f) Z
      = abses_es_pullback n f (abses_es_pullback n g Z).
  Proof.
    destruct n as [|[|n0]].
    - apply equiv_path_grouphomomorphism; reflexivity.
    - exact (abses_pullback_compose f g Z)^.
    - exact (path_sigma' _ 1
        (path_prod (fst Z.2, abses_pullback (g $o f) (snd Z.2))
                   (fst Z.2, abses_pullback f (abses_pullback g (snd Z.2)))
                   1 (abses_pullback_compose f g (snd Z.2))^)).
  Defined.

  (** Pushing a length-[n] sequence out along [alpha : A -> A'] acts on the
      deep end, recursing into the trailing sequence (postcomposition when
      [n] is zero). *)
  Definition abses_es_pushout (n : nat)
    {A A' : AbGroup@{u}} (alpha : A $-> A')
    : forall {B : AbGroup@{u}}, abses_es n B A -> abses_es n B A'.
  Proof.
    induction n as [|n1 IH]; intro B.
    - exact (fun f => grp_homo_compose alpha f).
    - destruct n1 as [|n0].
      + exact (fun s => abses_pushout alpha s).
      + exact (fun e => (e.1; (IH e.1 (fst e.2), snd e.2))).
  Defined.

  (** Pushing out along the identity is the identity. *)
  Definition abses_es_pushout_id (n : nat) {B A : AbGroup@{u}}
    (E : abses_es n B A)
    : abses_es_pushout n grp_homo_id E = E.
  Proof.
    revert B A E; induction n as [|n1 IH]; intros B A E.
    - apply equiv_path_grouphomomorphism; reflexivity.
    - destruct n1 as [|n0].
      + apply abses_pushout_id.
      + exact (path_sigma' _ 1
          (path_prod (abses_es_pushout n0.+1 grp_homo_id (fst E.2), snd E.2)
                     (fst E.2, snd E.2)
                     (IH E.1 A (fst E.2)) 1)).
  Defined.

  (** Pushout is covariantly functorial in the deep end. *)
  Definition abses_es_pushout_compose (n : nat)
    {A0 A1 A2 : AbGroup@{u}} (f : A0 $-> A1) (g : A1 $-> A2) (B : AbGroup@{u})
    : forall E : abses_es n B A0,
      abses_es_pushout n (g $o f) E
      = abses_es_pushout n g (abses_es_pushout n f E).
  Proof.
    revert B; induction n as [|n1 IH]; intro B.
    - intro E; apply equiv_path_grouphomomorphism; reflexivity.
    - destruct n1 as [|n0].
      + intro E; exact (abses_pushout_compose f g E).
      + intro E.
        exact (path_sigma' _ 1
          (path_prod
            (abses_es_pushout n0.+1 (g $o f) (fst E.2), snd E.2)
            (abses_es_pushout n0.+1 g (abses_es_pushout n0.+1 f (fst E.2)), snd E.2)
            (IH E.1 (fst E.2)) 1)).
  Defined.

  (** Pushout and pullback act on disjoint ends, so they commute. *)
  Definition abses_es_pushout_pullback (n : nat)
    {A A' B B' : AbGroup@{u}} (alpha : A $-> A') (beta : B' $-> B)
    (E : abses_es n B A)
    : abses_es_pushout n alpha (abses_es_pullback n beta E)
      = abses_es_pullback n beta (abses_es_pushout n alpha E).
  Proof.
    destruct n as [|[|n0]].
    - apply equiv_path_grouphomomorphism; reflexivity.
    - apply abses_pushout_pullback_reorder.
    - reflexivity.
  Defined.

  (** The direct sum of two length-[n] sequences, taken componentwise; the
      intermediate modules become biproducts. *)
  Definition abses_es_direct_sum (n : nat)
    : forall {B A B' A' : AbGroup@{u}},
      abses_es n B A -> abses_es n B' A' -> abses_es n (ab_biprod B B') (ab_biprod A A').
  Proof.
    induction n as [|n1 IH]; intros B A B' A'.
    - exact (fun E F => functor_ab_biprod E F).
    - destruct n1 as [|n0].
      + exact (fun E F => abses_direct_sum E F).
      + exact (fun E F => (ab_biprod E.1 F.1;
          (IH E.1 A F.1 A' (fst E.2) (fst F.2),
           abses_direct_sum (snd E.2) (snd F.2)))).
  Defined.

  (** The direct sum commutes with pullback along [functor_ab_biprod];
      pullback touches only the leading sequence, so no recursion is
      needed. *)
  Definition abses_es_directsum_pullback (n : nat)
    {A A' B B' D D' : AbGroup@{u}} (beta : B' $-> B) (delta : D' $-> D)
    (X : abses_es n B A) (Y : abses_es n D A')
    : abses_es_direct_sum n (abses_es_pullback n beta X) (abses_es_pullback n delta Y)
      = abses_es_pullback n (functor_ab_biprod beta delta) (abses_es_direct_sum n X Y).
  Proof.
    destruct n as [|[|n0]].
    - apply equiv_path_grouphomomorphism; reflexivity.
    - exact (abses_directsum_distributive_pullbacks beta delta)^.
    - srapply path_sigma'.
      1: reflexivity.
      srapply path_prod.
      1: reflexivity.
      exact (abses_directsum_distributive_pullbacks beta delta)^.
  Defined.

  (** The direct sum commutes with pushout along [functor_ab_biprod]; pushout
      recurses into the trailing sequence. *)
  Definition abses_es_directsum_pushout (n : nat)
    {A A2 A' A'2 : AbGroup@{u}} (alpha : A $-> A2) (alpha' : A' $-> A'2)
    : forall {B B' : AbGroup@{u}} (X : abses_es n B A) (Y : abses_es n B' A'),
      abses_es_pushout n (functor_ab_biprod alpha alpha') (abses_es_direct_sum n X Y)
      = abses_es_direct_sum n (abses_es_pushout n alpha X) (abses_es_pushout n alpha' Y).
  Proof.
    induction n as [|n1 IH]; intros B B' X Y.
    - apply equiv_path_grouphomomorphism; reflexivity.
    - destruct n1 as [|n0].
      + apply abses_directsum_distributive_pushouts.
      + exact (path_sigma' _ 1
          (path_prod
            (abses_es_pushout n0.+1 (functor_ab_biprod alpha alpha')
               (abses_es_direct_sum n0.+1 (fst X.2) (fst Y.2)),
             abses_direct_sum (snd X.2) (snd Y.2))
            (abses_es_direct_sum n0.+1 (abses_es_pushout n0.+1 alpha (fst X.2))
               (abses_es_pushout n0.+1 alpha' (fst Y.2)),
             abses_direct_sum (snd X.2) (snd Y.2))
            (IH X.1 Y.1 (fst X.2) (fst Y.2)) 1)).
  Defined.

  (** The twist morphism on a triple direct sum, for arbitrary objects (the
      analogous library construction is stated only for equal objects). *)
  Definition abses_twist_directsum' {A1 B1 A2 B2 A3 B3 : AbGroup@{u}}
    (E : AbSES B1 A1) (F : AbSES B2 A2) (G : AbSES B3 A3)
    : AbSESMorphism (abses_direct_sum (abses_direct_sum E F) G)
                    (abses_direct_sum (abses_direct_sum G F) E).
  Proof.
    snapply Build_AbSESMorphism.
    1,2,3: exact ab_biprod_twist.
    all: reflexivity.
  Defined.

  (** The Baer sum of two length-[n] sequences with the same endpoints: take
      the direct sum, push out along the codiagonal and pull back along the
      diagonal. *)
  Definition abses_es_baer_sum (n : nat) {B A : AbGroup@{u}}
    (E F : abses_es n B A) : abses_es n B A
    := abses_es_pullback n ab_diagonal
         (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n E F)).

  (** The biproduct with the trivial group is the identity, projecting away
      the trivial factor. *)
  Definition ab_biprod_trivial_r (A : AbGroup@{u})
    : GroupIsomorphism (ab_biprod A abgroup_trivial) A.
  Proof.
    snapply Build_GroupIsomorphism.
    - exact ab_biprod_pr1.
    - snapply isequiv_adjointify.
      + exact (fun a => (a, mon_unit)).
      + reflexivity.
      + intro x; srapply path_prod; [ reflexivity | apply path_contr ].
  Defined.

  (** Adding the split trivial summand on the deep end and projecting away the
      trivial factor leaves a short exact sequence unchanged, up to reindexing
      the base along the projection. *)
  Definition abses_absorb_trivial {C A : AbGroup@{u}} (X : AbSES C A)
    : abses_pushout ab_codiagonal
        (abses_direct_sum X (point (AbSES abgroup_trivial A)))
      = abses_pullback ab_biprod_pr1 X.
  Proof.
    pose (cst := @grp_homo_const abgroup_trivial C).
    transitivity (abses_pushout ab_codiagonal
                    (abses_direct_sum X (abses_pullback cst X))).
    1: napply (ap (fun s => abses_pushout ab_codiagonal (abses_direct_sum X s)));
       exact (abses_pullback_const X).
    transitivity (abses_pushout ab_codiagonal
                    (abses_direct_sum (abses_pullback grp_homo_id X)
                       (abses_pullback cst X))).
    1: napply (ap (fun s => abses_pushout ab_codiagonal (abses_direct_sum s _)));
       exact (abses_pullback_id X)^.
    transitivity (abses_pushout ab_codiagonal
                    (abses_pullback (functor_ab_biprod grp_homo_id cst)
                       (abses_direct_sum X X))).
    1: napply (ap (abses_pushout ab_codiagonal));
       exact (abses_directsum_distributive_pullbacks grp_homo_id cst)^.
    transitivity (abses_pullback (functor_ab_biprod grp_homo_id cst)
                    (abses_pushout ab_codiagonal (abses_direct_sum X X))).
    1: exact (abses_pushout_pullback_reorder _ _ _).
    transitivity (abses_pullback (functor_ab_biprod grp_homo_id cst)
                    (abses_pullback ab_codiagonal X)).
    1: napply (ap (abses_pullback (functor_ab_biprod grp_homo_id cst)));
       exact (abses_pushout_is_pullback (abses_codiagonal X)).
    transitivity (abses_pullback
                    (ab_codiagonal $o functor_ab_biprod grp_homo_id cst) X).
    1: exact (abses_pullback_compose
                (functor_ab_biprod grp_homo_id cst) ab_codiagonal X).
    napply (ap (fun h => abses_pullback h X)).
    apply equiv_path_grouphomomorphism; intro x; cbn.
    apply grp_unit_r.
  Defined.

  (** The trinary Baer sum, used to organise the proof of associativity. *)
  Definition abses_es_trinary_baer_sum (n : nat) {B A : AbGroup@{u}}
    (E F G : abses_es n B A) : abses_es n B A
    := abses_es_pullback n ab_triagonal
         (abses_es_pushout n ab_cotriagonal
            (abses_es_direct_sum n (abses_es_direct_sum n E F) G)).

  (** The split length-[n] sequence, the neutral element for the Baer sum: the
      zero homomorphism, the split short exact sequence, and otherwise the
      trivial group spliced in. *)
  Definition abses_es_zero (n : nat) {A : AbGroup@{u}}
    : forall {B : AbGroup@{u}}, abses_es n B A.
  Proof.
    induction n as [|n1 IH]; intro B.
    - exact grp_homo_const.
    - destruct n1 as [|n0].
      + exact (point (AbSES B A)).
      + exact (abgroup_trivial; (IH abgroup_trivial, point (AbSES B abgroup_trivial))).
  Defined.

  (** Pulling the zero sequence back along the unique map to the trivial group
      gives the zero sequence again. *)
  Definition abses_es_pullback_zero (m : nat) {A C : AbGroup@{u}}
    : abses_es_pullback m (@grp_homo_const C abgroup_trivial)
        (@abses_es_zero m A abgroup_trivial)
      = @abses_es_zero m A C.
  Proof.
    destruct m as [|[|m0]].
    - apply equiv_path_grouphomomorphism; reflexivity.
    - exact (abses_pullback_const _)^.
    - srapply path_sigma'.
      1: reflexivity.
      srapply path_prod.
      1: reflexivity.
      exact (abses_pullback_const (point (AbSES abgroup_trivial abgroup_trivial)))^.
  Defined.

  (** Pushout is additive for the Baer sum, by naturality of the codiagonal. *)
  Definition abses_es_pushout_baer_sum (n : nat) {A A' : AbGroup@{u}}
    (alpha : A $-> A') {B : AbGroup@{u}} (E F : abses_es n B A)
    : abses_es_pushout n alpha (abses_es_baer_sum n E F)
      = abses_es_baer_sum n (abses_es_pushout n alpha E) (abses_es_pushout n alpha F).
  Proof.
    unfold abses_es_baer_sum.
    transitivity (abses_es_pullback n ab_diagonal
                    (abses_es_pushout n alpha
                       (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n E F)))).
    1: exact (abses_es_pushout_pullback n alpha ab_diagonal _).
    napply (ap (abses_es_pullback n ab_diagonal)).
    transitivity (abses_es_pushout n (alpha $o ab_codiagonal)
                    (abses_es_direct_sum n E F)).
    1: exact (abses_es_pushout_compose n ab_codiagonal alpha (ab_biprod B B)
                (abses_es_direct_sum n E F))^.
    transitivity (abses_es_pushout n (ab_codiagonal $o functor_ab_biprod alpha alpha)
                    (abses_es_direct_sum n E F)).
    1: napply (ap (fun h => abses_es_pushout n h (abses_es_direct_sum n E F)));
       exact (equiv_path_grouphomomorphism (ab_codiagonal_natural alpha)).
    transitivity (abses_es_pushout n ab_codiagonal
                    (abses_es_pushout n (functor_ab_biprod alpha alpha)
                       (abses_es_direct_sum n E F))).
    1: exact (abses_es_pushout_compose n (functor_ab_biprod alpha alpha) ab_codiagonal
                (ab_biprod B B) (abses_es_direct_sum n E F)).
    napply (ap (abses_es_pushout n ab_codiagonal)).
    exact (abses_es_directsum_pushout n alpha alpha E F).
  Defined.

  (** Pullback is additive for the Baer sum, by naturality of the diagonal. *)
  Definition abses_es_pullback_baer_sum (n : nat) {A : AbGroup@{u}}
    {B B' : AbGroup@{u}} (beta : B' $-> B) (E F : abses_es n B A)
    : abses_es_pullback n beta (abses_es_baer_sum n E F)
      = abses_es_baer_sum n (abses_es_pullback n beta E) (abses_es_pullback n beta F).
  Proof.
    unfold abses_es_baer_sum.
    transitivity (abses_es_pullback n (ab_diagonal $o beta)
                    (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n E F))).
    1: exact (abses_es_pullback_compose n beta ab_diagonal _)^.
    transitivity (abses_es_pullback n (functor_ab_biprod beta beta $o ab_diagonal)
                    (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n E F))).
    1: napply (ap (fun h => abses_es_pullback n h
                    (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n E F))));
       apply equiv_path_grouphomomorphism; reflexivity.
    transitivity (abses_es_pullback n ab_diagonal
                    (abses_es_pullback n (functor_ab_biprod beta beta)
                       (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n E F)))).
    1: exact (abses_es_pullback_compose n ab_diagonal (functor_ab_biprod beta beta) _).
    napply (ap (abses_es_pullback n ab_diagonal)).
    transitivity (abses_es_pushout n ab_codiagonal
                    (abses_es_pullback n (functor_ab_biprod beta beta)
                       (abses_es_direct_sum n E F))).
    1: exact (abses_es_pushout_pullback n ab_codiagonal (functor_ab_biprod beta beta) _)^.
    napply (ap (abses_es_pushout n ab_codiagonal)).
    exact (abses_es_directsum_pullback n beta beta E F)^.
  Defined.

  (** Splicing a short exact sequence [xi : AbSES A'' A] of coefficients onto
      the deep end of a length-[n] sequence raises the degree; this is the
      connecting map of the long exact sequence.  At degree zero it is pullback
      along the homomorphism; otherwise it recurses to the deepest sequence. *)
  Definition abses_es_dsplice (n : nat) {A A'' : AbGroup@{u}} (xi : AbSES A'' A)
    : forall {B : AbGroup@{u}}, abses_es n B A'' -> abses_es n.+1 B A.
  Proof.
    induction n as [|n1 IH]; intro B.
    - exact (fun f => abses_pullback f xi).
    - destruct n1 as [|n0].
      + exact (fun s => (A''; (xi, s))).
      + exact (fun e => (e.1; (IH e.1 (fst e.2), snd e.2))).
  Defined.

  (** The deep-end splice commutes with pullback in the base. *)
  Definition abses_es_dsplice_pullback (n : nat) {A A'' : AbGroup@{u}}
    (xi : AbSES A'' A) {B B' : AbGroup@{u}} (beta : B' $-> B)
    (X : abses_es n B A'')
    : abses_es_dsplice n xi (abses_es_pullback n beta X)
      = abses_es_pullback n.+1 beta (abses_es_dsplice n xi X).
  Proof.
    destruct n as [|[|n0]].
    - exact (abses_pullback_compose beta X xi)^.
    - reflexivity.
    - reflexivity.
  Defined.

  (** Pushing out the deep end of a spliced sequence is the same as splicing
      with the pushed-out short exact sequence: the pushout in degree [n.+1]
      acts on the deepest sequence, which is exactly [xi]. *)
  Definition abses_es_dsplice_pushout (n : nat) {A A2 A'' : AbGroup@{u}}
    (xi : AbSES A'' A) (alpha : A $-> A2)
    : forall {B : AbGroup@{u}} (Y : abses_es n B A''),
      abses_es_pushout n.+1 alpha (abses_es_dsplice n xi Y)
      = abses_es_dsplice n (abses_pushout alpha xi) Y.
  Proof.
    induction n as [|n1 IH]; intro B.
    - exact (fun Y => abses_pushout_pullback_reorder xi alpha Y).
    - destruct n1 as [|n0].
      + exact (fun s => idpath).
      + intro e.
        srapply path_sigma'.
        1: reflexivity.
        srapply path_prod.
        1: exact (IH e.1 (fst e.2)).
        reflexivity.
  Defined.

  (** The deep-end splice distributes over the direct sum: the direct sum of
      two splices by [xi] is the splice by [xi (+) xi] of the direct sum.  The
      pullback at the deepest level is handled by the distributivity of the
      direct sum over pullbacks. *)
  Definition abses_es_directsum_dsplice (n : nat) {A A'' : AbGroup@{u}}
    (xi : AbSES A'' A)
    : forall {B B' : AbGroup@{u}} (E : abses_es n B A'') (F : abses_es n B' A''),
      abses_es_direct_sum n.+1 (abses_es_dsplice n xi E) (abses_es_dsplice n xi F)
      = abses_es_dsplice n (abses_direct_sum xi xi) (abses_es_direct_sum n E F).
  Proof.
    induction n as [|n1 IH]; intros B B' E F.
    - exact (abses_directsum_distributive_pullbacks E F)^.
    - destruct n1 as [|n0].
      + reflexivity.
      + srapply path_sigma'.
        1: reflexivity.
        srapply path_prod.
        1: exact (IH E.1 F.1 (fst E.2) (fst F.2)).
        reflexivity.
  Defined.

End Operations.

(** ** The relation [⤳] *)

Section Relation.
  Context `{Univalence}.

  (** The relation [E ⤳ F] of Christensen-Flaten: equality in low degrees,
      and otherwise a homomorphism of the intermediate modules under which
      the leading sequences push out and the trailing sequences pull back to
      matching ones. *)
  Definition abses_es_rel (n : nat) {B A : AbGroup@{u}}
    : abses_es n B A -> abses_es n B A -> Type.
  Proof.
    revert B A; induction n as [|n1 IH]; intros B A.
    - exact (fun E F => E = F).
    - destruct n1 as [|n0].
      + exact (fun E F => E = F).
      + intros E F.
        exact { beta : ab_hom E.1 F.1
                & IH E.1 A (fst E.2) (abses_es_pullback n0.+1 beta (fst F.2))
                  * (abses_pushout beta (snd E.2) = snd F.2) }.
  Defined.

  (** The relation is preserved by pullback along [beta], since [beta] only
      touches the leading short exact sequence. *)
  Definition abses_es_rel_pullback (n : nat)
    {A B B' : AbGroup@{u}} (beta : B' $-> B)
    : forall X Y : abses_es n B A, abses_es_rel n X Y
      -> abses_es_rel n (abses_es_pullback n beta X) (abses_es_pullback n beta Y).
  Proof.
    destruct n as [|[|n0]]; intros X Y r.
    - exact (ap (abses_es_pullback 0 beta) r).
    - exact (ap (abses_es_pullback 1 beta) r).
    - exists r.1.
      exact (fst r.2,
             abses_pushout_pullback_reorder (snd X.2) r.1 beta
               @ ap (abses_pullback beta) (snd r.2)).
  Defined.

  (** The relation is preserved by pushout along [alpha], using that pushout
      commutes with the pullback appearing in the relation. *)
  Definition abses_es_rel_pushout (n : nat)
    {A A' : AbGroup@{u}} (alpha : A $-> A') (B : AbGroup@{u})
    : forall E F : abses_es n B A, abses_es_rel n E F
      -> abses_es_rel n (abses_es_pushout n alpha E) (abses_es_pushout n alpha F).
  Proof.
    revert B; induction n as [|n1 IH]; intro B.
    - intros E F r; exact (ap (abses_es_pushout 0 alpha) r).
    - destruct n1 as [|n0].
      + intros E F r; exact (ap (abses_es_pushout 1 alpha) r).
      + intros E F r.
        exists r.1.
        exact (transport
                 (abses_es_rel n0.+1 (abses_es_pushout n0.+1 alpha (fst E.2)))
                 (abses_es_pushout_pullback n0.+1 alpha r.1 (fst F.2))
                 (IH E.1 (fst E.2) (abses_es_pullback n0.+1 r.1 (fst F.2)) (fst r.2)),
               snd r.2).
  Defined.

  (** The relation is reflexive, witnessed by the identity homomorphism. *)
  Definition abses_es_rel_refl (n : nat) {B A : AbGroup@{u}}
    (E : abses_es n B A)
    : abses_es_rel n E E.
  Proof.
    revert B A E; induction n as [|n1 IH]; intros B A E.
    - reflexivity.
    - destruct n1 as [|n0].
      + reflexivity.
      + exists grp_homo_id.
        exact (transport (abses_es_rel n0.+1 (fst E.2))
                 (abses_es_pullback_id n0.+1 (fst E.2))^
                 (IH E.1 A (fst E.2)),
               abses_pushout_id (snd E.2)).
  Defined.

  (** The relation is transitive: compose the intermediate homomorphisms,
      pulling the second witness back along the first and reassembling the
      pushout square by functoriality. *)
  Definition abses_es_rel_trans (n : nat) {B A : AbGroup@{u}}
    : forall X Y Z : abses_es n B A,
      abses_es_rel n X Y -> abses_es_rel n Y Z -> abses_es_rel n X Z.
  Proof.
    revert B A; induction n as [|n1 IH]; intros B A.
    - intros X Y Z r1 r2; exact (r1 @ r2).
    - destruct n1 as [|n0].
      + intros X Y Z r1 r2; exact (r1 @ r2).
      + intros X Y Z r1 r2.
        exists (grp_homo_compose r2.1 r1.1).
        refine (_, _).
        * refine (IH _ _ _ _ _ (fst r1.2) _).
          exact (transport
            (abses_es_rel n0.+1 (abses_es_pullback n0.+1 r1.1 (fst Y.2)))
            (abses_es_pullback_compose n0.+1 r1.1 r2.1 (fst Z.2))^
            (abses_es_rel_pullback n0.+1 r1.1 (fst Y.2)
               (abses_es_pullback n0.+1 r2.1 (fst Z.2)) (fst r2.2))).
        * exact (abses_pushout_compose r1.1 r2.1 (snd X.2)
                 @ ap (abses_pushout r2.1) (snd r1.2) @ snd r2.2).
  Defined.

  (** The direct sum respects the relation in both arguments, composing the
      two intermediate homomorphisms with [functor_ab_biprod]. *)
  Definition abses_es_direct_sum_rel (n : nat)
    : forall {B A B' A' : AbGroup@{u}} (E E' : abses_es n B A) (F F' : abses_es n B' A'),
      abses_es_rel n E E' -> abses_es_rel n F F'
      -> abses_es_rel n (abses_es_direct_sum n E F) (abses_es_direct_sum n E' F').
  Proof.
    induction n as [|n1 IH]; intros B A B' A'.
    - intros E E' F F' rE rF; exact (ap011 (abses_es_direct_sum 0) rE rF).
    - destruct n1 as [|n0].
      + intros E E' F F' rE rF; exact (ap011 (abses_es_direct_sum 1) rE rF).
      + intros E E' F F' rE rF.
        exists (functor_ab_biprod rE.1 rF.1).
        refine (_, _).
        * exact (transport
            (abses_es_rel n0.+1 (abses_es_direct_sum n0.+1 (fst E.2) (fst F.2)))
            (abses_es_directsum_pullback n0.+1 rE.1 rF.1 (fst E'.2) (fst F'.2))
            (IH E.1 A F.1 A' (fst E.2) (abses_es_pullback n0.+1 rE.1 (fst E'.2))
               (fst F.2) (abses_es_pullback n0.+1 rF.1 (fst F'.2))
               (fst rE.2) (fst rF.2))).
        * exact (abses_directsum_distributive_pushouts rE.1 rF.1
                 @ ap011 abses_direct_sum (snd rE.2) (snd rF.2)).
  Defined.

  (** Swapping the two summands of a direct sum is, up to the relation, the
      same as conjugating by [direct_sum_swap] on both ends.  In degrees at
      least two the intermediate modules differ, so this is a relation rather
      than an equality. *)
  Definition abses_es_directsum_swap (n : nat)
    : forall {B A B' A' : AbGroup@{u}} (E : abses_es n B A) (F : abses_es n B' A'),
      abses_es_rel n (abses_es_direct_sum n E F)
        (abses_es_pushout n direct_sum_swap
           (abses_es_pullback n direct_sum_swap (abses_es_direct_sum n F E))).
  Proof.
    induction n as [|n1 IH]; intros B A B' A'.
    - intros E F; apply equiv_path_grouphomomorphism; reflexivity.
    - destruct n1 as [|n0].
      + intros E F.
        transitivity (abses_pushout grp_homo_id (abses_direct_sum E F)).
        1: exact (abses_pushout_id _)^.
        transitivity (abses_pushout (grp_homo_compose direct_sum_swap direct_sum_swap)
                        (abses_direct_sum E F)).
        { napply (ap (fun h => abses_pushout h (abses_direct_sum E F))).
          symmetry; apply equiv_path_grouphomomorphism; reflexivity. }
        refine (abses_pushout_compose direct_sum_swap direct_sum_swap _ @ _).
        exact (ap (abses_pushout direct_sum_swap)
                 (abses_pushout_is_pullback (abses_swap_morphism E F))).
      + intros E F.
        exists direct_sum_swap.
        refine (_, _).
        * exact (transport
            (abses_es_rel n0.+1 (abses_es_direct_sum n0.+1 (fst E.2) (fst F.2)))
            (abses_es_pushout_pullback n0.+1 direct_sum_swap direct_sum_swap
               (abses_es_direct_sum n0.+1 (fst F.2) (fst E.2)))
            (IH E.1 A F.1 A' (fst E.2) (fst F.2))).
        * exact (abses_pushout_is_pullback (abses_swap_morphism (snd E.2) (snd F.2))).
  Defined.

  (** The triple direct sum, twisted by [ab_biprod_twist], is the conjugate of
      the reversed triple sum; the analog of [abses_es_directsum_swap] used for
      associativity. *)
  Definition abses_es_directsum_twist (n : nat)
    : forall {B1 A1 B2 A2 B3 A3 : AbGroup@{u}}
        (E : abses_es n B1 A1) (F : abses_es n B2 A2) (G : abses_es n B3 A3),
      abses_es_rel n (abses_es_direct_sum n (abses_es_direct_sum n E F) G)
        (abses_es_pushout n ab_biprod_twist
           (abses_es_pullback n ab_biprod_twist
              (abses_es_direct_sum n (abses_es_direct_sum n G F) E))).
  Proof.
    induction n as [|n1 IH]; intros B1 A1 B2 A2 B3 A3.
    - intros E F G; apply equiv_path_grouphomomorphism; reflexivity.
    - destruct n1 as [|n0].
      + intros E F G.
        transitivity (abses_pushout grp_homo_id
                        (abses_direct_sum (abses_direct_sum E F) G)).
        1: exact (abses_pushout_id _)^.
        transitivity (abses_pushout (grp_homo_compose ab_biprod_twist ab_biprod_twist)
                        (abses_direct_sum (abses_direct_sum E F) G)).
        { napply (ap (fun h => abses_pushout h
                       (abses_direct_sum (abses_direct_sum E F) G))).
          symmetry; apply equiv_path_grouphomomorphism; reflexivity. }
        refine (abses_pushout_compose ab_biprod_twist ab_biprod_twist _ @ _).
        exact (ap (abses_pushout ab_biprod_twist)
                 (abses_pushout_is_pullback (abses_twist_directsum' E F G))).
      + intros E F G.
        exists ab_biprod_twist.
        refine (_, _).
        * exact (transport
            (abses_es_rel n0.+1 (abses_es_direct_sum n0.+1
               (abses_es_direct_sum n0.+1 (fst E.2) (fst F.2)) (fst G.2)))
            (abses_es_pushout_pullback n0.+1 ab_biprod_twist ab_biprod_twist
               (abses_es_direct_sum n0.+1
                  (abses_es_direct_sum n0.+1 (fst G.2) (fst F.2)) (fst E.2)))
            (IH E.1 A1 F.1 A2 G.1 A3 (fst E.2) (fst F.2) (fst G.2))).
        * exact (abses_pushout_is_pullback
                   (abses_twist_directsum' (snd E.2) (snd F.2) (snd G.2))).
  Defined.

  (** The Baer sum respects the relation in both arguments, since each of its
      three constituent operations does. *)
  Definition abses_es_baer_sum_rel (n : nat) {B A : AbGroup@{u}}
    {E E' F F' : abses_es n B A}
    (rE : abses_es_rel n E E') (rF : abses_es_rel n F F')
    : abses_es_rel n (abses_es_baer_sum n E F) (abses_es_baer_sum n E' F')
    := abses_es_rel_pullback n ab_diagonal _ _
         (abses_es_rel_pushout n ab_codiagonal _ _ _
            (abses_es_direct_sum_rel n E E' F F' rE rF)).

  (** The Baer sum is commutative: the swap-conjugation relation is carried
      by the codiagonal pushout and diagonal pullback, which absorb the swap
      on each end. *)
  Definition abses_es_baer_sum_comm (n : nat) {B A : AbGroup@{u}}
    (E F : abses_es n B A)
    : abses_es_rel n (abses_es_baer_sum n E F) (abses_es_baer_sum n F E).
  Proof.
    snrefine (transport (abses_es_rel n (abses_es_baer_sum n E F)) _
              (abses_es_rel_pullback n ab_diagonal _ _
                 (abses_es_rel_pushout n ab_codiagonal _ _ _
                    (abses_es_directsum_swap n E F)))).
    unfold abses_es_baer_sum.
    transitivity (abses_es_pullback n ab_diagonal
                    (abses_es_pushout n ab_codiagonal
                       (abses_es_pullback n direct_sum_swap (abses_es_direct_sum n F E)))).
    { napply (ap (abses_es_pullback n ab_diagonal)).
      refine ((abses_es_pushout_compose n direct_sum_swap ab_codiagonal _ _)^ @ _).
      napply (ap (fun h => abses_es_pushout n h
                    (abses_es_pullback n direct_sum_swap (abses_es_direct_sum n F E)))).
      exact ab_codiagonal_swap. }
    transitivity (abses_es_pullback n ab_diagonal
                    (abses_es_pullback n direct_sum_swap
                       (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n F E)))).
    { napply (ap (abses_es_pullback n ab_diagonal)).
      exact (abses_es_pushout_pullback n ab_codiagonal direct_sum_swap
               (abses_es_direct_sum n F E)). }
    exact (abses_es_pullback_compose n ab_diagonal direct_sum_swap
             (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n F E)))^.
  Defined.

  (** The trinary Baer sum is symmetric under reversing the outer summands,
      by the same argument as commutativity with [ab_biprod_twist] in place of
      [direct_sum_swap]. *)
  Definition abses_es_trinary_twist (n : nat) {B A : AbGroup@{u}}
    (E F G : abses_es n B A)
    : abses_es_rel n (abses_es_trinary_baer_sum n E F G)
                     (abses_es_trinary_baer_sum n G F E).
  Proof.
    snrefine (transport (abses_es_rel n (abses_es_trinary_baer_sum n E F G)) _
              (abses_es_rel_pullback n ab_triagonal _ _
                 (abses_es_rel_pushout n ab_cotriagonal _ _ _
                    (abses_es_directsum_twist n E F G)))).
    unfold abses_es_trinary_baer_sum.
    transitivity (abses_es_pullback n ab_triagonal
                    (abses_es_pushout n ab_cotriagonal
                       (abses_es_pullback n ab_biprod_twist
                          (abses_es_direct_sum n (abses_es_direct_sum n G F) E)))).
    { napply (ap (abses_es_pullback n ab_triagonal)).
      refine ((abses_es_pushout_compose n ab_biprod_twist ab_cotriagonal _ _)^ @ _).
      napply (ap (fun h => abses_es_pushout n h
                    (abses_es_pullback n ab_biprod_twist
                       (abses_es_direct_sum n (abses_es_direct_sum n G F) E)))).
      exact ab_cotriagonal_twist. }
    transitivity (abses_es_pullback n ab_triagonal
                    (abses_es_pullback n ab_biprod_twist
                       (abses_es_pushout n ab_cotriagonal
                          (abses_es_direct_sum n (abses_es_direct_sum n G F) E)))).
    { napply (ap (abses_es_pullback n ab_triagonal)).
      exact (abses_es_pushout_pullback n ab_cotriagonal ab_biprod_twist
               (abses_es_direct_sum n (abses_es_direct_sum n G F) E)). }
    exact (abses_es_pullback_compose n ab_triagonal ab_biprod_twist
             (abses_es_pushout n ab_cotriagonal
                (abses_es_direct_sum n (abses_es_direct_sum n G F) E)))^.
  Defined.

  (** The left-associated Baer sum equals the trinary Baer sum: move the inner
      diagonal and codiagonal out through the outer direct sum, then combine
      with the outer ones into the triagonal and cotriagonal. *)
  Definition abses_es_baer_sum_is_trinary (n : nat) {B A : AbGroup@{u}}
    (E F G : abses_es n B A)
    : abses_es_baer_sum n (abses_es_baer_sum n E F) G
      = abses_es_trinary_baer_sum n E F G.
  Proof.
    unfold abses_es_baer_sum, abses_es_trinary_baer_sum.
    transitivity (abses_es_pullback n ab_diagonal
                    (abses_es_pushout n ab_codiagonal
                       (abses_es_pullback n (functor_ab_biprod ab_diagonal grp_homo_id)
                          (abses_es_pushout n (functor_ab_biprod ab_codiagonal grp_homo_id)
                             (abses_es_direct_sum n (abses_es_direct_sum n E F) G))))).
    { napply (ap (fun z => abses_es_pullback n ab_diagonal
                    (abses_es_pushout n ab_codiagonal z))).
      transitivity (abses_es_direct_sum n
                      (abses_es_pullback n ab_diagonal
                         (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n E F)))
                      (abses_es_pullback n grp_homo_id G)).
      1: exact (ap (abses_es_direct_sum n _) (abses_es_pullback_id n G)^).
      transitivity (abses_es_pullback n (functor_ab_biprod ab_diagonal grp_homo_id)
                      (abses_es_direct_sum n
                         (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n E F)) G)).
      1: exact (abses_es_directsum_pullback n ab_diagonal grp_homo_id _ G).
      napply (ap (abses_es_pullback n (functor_ab_biprod ab_diagonal grp_homo_id))).
      transitivity (abses_es_direct_sum n
                      (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n E F))
                      (abses_es_pushout n grp_homo_id G)).
      1: exact (ap (abses_es_direct_sum n _) (abses_es_pushout_id n G)^).
      exact (abses_es_directsum_pushout n ab_codiagonal grp_homo_id _ G)^. }
    transitivity (abses_es_pullback n ab_diagonal
                    (abses_es_pullback n (functor_ab_biprod ab_diagonal grp_homo_id)
                       (abses_es_pushout n ab_codiagonal
                          (abses_es_pushout n (functor_ab_biprod ab_codiagonal grp_homo_id)
                             (abses_es_direct_sum n (abses_es_direct_sum n E F) G))))).
    { napply (ap (abses_es_pullback n ab_diagonal)).
      exact (abses_es_pushout_pullback n ab_codiagonal
               (functor_ab_biprod ab_diagonal grp_homo_id)
               (abses_es_pushout n (functor_ab_biprod ab_codiagonal grp_homo_id)
                  (abses_es_direct_sum n (abses_es_direct_sum n E F) G))). }
    refine ((abses_es_pullback_compose n ab_diagonal
               (functor_ab_biprod ab_diagonal grp_homo_id) _)^ @ _).
    napply (ap (abses_es_pullback n ab_triagonal)).
    exact (abses_es_pushout_compose n (functor_ab_biprod ab_codiagonal grp_homo_id)
             ab_codiagonal _ (abses_es_direct_sum n (abses_es_direct_sum n E F) G))^.
  Defined.

  (** Twisting the order of a left-associated triple Baer sum, via the trinary
      form. *)
  Definition abses_es_baer_sum_twist (n : nat) {B A : AbGroup@{u}}
    (E F G : abses_es n B A)
    : abses_es_rel n (abses_es_baer_sum n (abses_es_baer_sum n E F) G)
                     (abses_es_baer_sum n (abses_es_baer_sum n G F) E)
    := transport (fun p => abses_es_rel n p
                    (abses_es_baer_sum n (abses_es_baer_sum n G F) E))
         (abses_es_baer_sum_is_trinary n E F G)^
         (transport (abses_es_rel n (abses_es_trinary_baer_sum n E F G))
            (abses_es_baer_sum_is_trinary n G F E)^
            (abses_es_trinary_twist n E F G)).

  (** The Baer sum is associative, by combining the twist with commutativity. *)
  Definition abses_es_baer_sum_assoc (n : nat) {B A : AbGroup@{u}}
    (E F G : abses_es n B A)
    : abses_es_rel n (abses_es_baer_sum n (abses_es_baer_sum n E F) G)
                     (abses_es_baer_sum n E (abses_es_baer_sum n F G)).
  Proof.
    refine (abses_es_rel_trans n _ _ _ (abses_es_baer_sum_twist n E F G) _).
    refine (abses_es_rel_trans n _ _ _
              (abses_es_baer_sum_comm n (abses_es_baer_sum n G F) E) _).
    exact (abses_es_baer_sum_rel n (abses_es_rel_refl n E)
             (abses_es_baer_sum_comm n G F)).
  Defined.

  (** Adding the split zero sequence on the deep end and projecting away the
      trivial factor recovers the original, up to reindexing the base.  This is
      the engine of the unit law; the leading sequence uses [abses_absorb_trivial]
      and the trailing sequence recurses. *)
  Definition abses_es_absorb_zero (m : nat) {A : AbGroup@{u}}
    : forall {C : AbGroup@{u}} (X : abses_es m C A),
      abses_es_rel m
        (abses_es_pushout m ab_codiagonal
           (abses_es_direct_sum m X (@abses_es_zero _ m A abgroup_trivial)))
        (abses_es_pullback m ab_biprod_pr1 X).
  Proof.
    induction m as [|m1 IH]; intros C X.
    - apply equiv_path_grouphomomorphism; intro x; cbn; apply grp_unit_r.
    - destruct m1 as [|m0].
      + exact (abses_absorb_trivial X).
      + exists ab_biprod_pr1.
        refine (IH X.1 (fst X.2), _).
        pose (cst := @grp_homo_const abgroup_trivial X.1).
        transitivity (abses_pushout (ab_codiagonal $o functor_ab_biprod grp_homo_id cst)
                        (abses_direct_sum (snd X.2)
                           (point (AbSES abgroup_trivial abgroup_trivial)))).
        { napply (ap (fun h => abses_pushout h
                       (abses_direct_sum (snd X.2)
                          (point (AbSES abgroup_trivial abgroup_trivial))))).
          apply equiv_path_grouphomomorphism; intro x; cbn; symmetry; apply grp_unit_r. }
        transitivity (abses_pushout ab_codiagonal
                        (abses_pushout (functor_ab_biprod grp_homo_id cst)
                           (abses_direct_sum (snd X.2)
                              (point (AbSES abgroup_trivial abgroup_trivial))))).
        1: exact (abses_pushout_compose _ _ _).
        transitivity (abses_pushout ab_codiagonal
                        (abses_direct_sum (abses_pushout grp_homo_id (snd X.2))
                           (abses_pushout cst
                              (point (AbSES abgroup_trivial abgroup_trivial))))).
        1: napply (ap (abses_pushout ab_codiagonal));
           exact (abses_directsum_distributive_pushouts _ _).
        transitivity (abses_pushout ab_codiagonal
                        (abses_direct_sum (snd X.2)
                           (point (AbSES abgroup_trivial X.1)))).
        { napply (ap (abses_pushout ab_codiagonal)).
          napply (ap011 abses_direct_sum).
          - exact (abses_pushout_id _).
          - exact (abses_pushout_const _). }
        exact (abses_absorb_trivial (snd X.2)).
  Defined.

  (** The split sequence is a right unit for the Baer sum: the trailing
      sequence is handled by [abses_es_absorb_zero] and the leading one by the
      degree-one unit law. *)
  Definition abses_es_baer_sum_unit (n : nat) {B A : AbGroup@{u}}
    (E : abses_es n B A)
    : abses_es_rel n (abses_es_baer_sum n E (abses_es_zero n)) E.
  Proof.
    destruct n as [|[|n0]].
    - apply equiv_path_grouphomomorphism; intro x; cbn; apply grp_unit_r.
    - exact (baer_sum_unit_r E).
    - exists ab_biprod_pr1.
      refine (abses_es_absorb_zero n0.+1 (fst E.2), _).
      pose (cst := @grp_homo_const abgroup_trivial E.1).
      transitivity (abses_pullback ab_diagonal
                      (abses_pushout ab_biprod_pr1
                         (abses_direct_sum (snd E.2) (point (AbSES B abgroup_trivial))))).
      1: exact (abses_pushout_pullback_reorder _ _ _).
      transitivity (abses_pullback ab_diagonal
                      (abses_pushout (ab_codiagonal $o functor_ab_biprod grp_homo_id cst)
                         (abses_direct_sum (snd E.2) (point (AbSES B abgroup_trivial))))).
      { napply (ap (fun h => abses_pullback ab_diagonal
                     (abses_pushout h
                        (abses_direct_sum (snd E.2) (point (AbSES B abgroup_trivial)))))).
        apply equiv_path_grouphomomorphism; intro x; cbn; symmetry; apply grp_unit_r. }
      transitivity (abses_pullback ab_diagonal
                      (abses_pushout ab_codiagonal
                         (abses_pushout (functor_ab_biprod grp_homo_id cst)
                            (abses_direct_sum (snd E.2)
                               (point (AbSES B abgroup_trivial)))))).
      1: napply (ap (abses_pullback ab_diagonal)); exact (abses_pushout_compose _ _ _).
      transitivity (abses_pullback ab_diagonal
                      (abses_pushout ab_codiagonal
                         (abses_direct_sum (abses_pushout grp_homo_id (snd E.2))
                            (abses_pushout cst (point (AbSES B abgroup_trivial)))))).
      1: napply (ap (fun s => abses_pullback ab_diagonal (abses_pushout ab_codiagonal s)));
         exact (abses_directsum_distributive_pushouts _ _).
      transitivity (abses_pullback ab_diagonal
                      (abses_pushout ab_codiagonal
                         (abses_direct_sum (snd E.2) (point (AbSES B E.1))))).
      { napply (ap (fun s => abses_pullback ab_diagonal (abses_pushout ab_codiagonal s)));
        napply (ap011 abses_direct_sum);
          [ exact (abses_pushout_id _) | exact (abses_pushout_const _) ]. }
      exact (baer_sum_unit_r (snd E.2)).
  Defined.

  (** Pushing a sequence out along the zero map gives the split sequence: the
      leading sequence becomes split and the trailing sequence recurses. *)
  Definition abses_es_zero_absorb (m : nat) {A A' : AbGroup@{u}}
    : forall {C : AbGroup@{u}} (X : abses_es m C A),
      abses_es_rel m (abses_es_pushout m (@grp_homo_const A A') X)
                     (@abses_es_zero _ m A' C).
  Proof.
    induction m as [|m1 IH]; intros C X.
    - apply equiv_path_grouphomomorphism; reflexivity.
    - destruct m1 as [|m0].
      + exact (abses_pushout_const X).
      + exists grp_homo_const.
        refine (transport
                  (abses_es_rel m0.+1
                     (abses_es_pushout m0.+1 (@grp_homo_const A A') (fst X.2)))
                  (@abses_es_pullback_zero _ m0.+1 A' X.1)^
                  (IH X.1 (fst X.2)), _).
        exact (abses_pushout_const (snd X.2)).
  Defined.

  (** Pushing out along the diagonal of the deep end agrees, up to the
      relation, with pulling the self-direct-sum back along the diagonal of the
      base; the length-[n] analogue of [abses_pushout_is_pullback] for the
      diagonal morphism. *)
  Definition abses_es_diagonal_is_pullback (n : nat)
    : forall {B A : AbGroup@{u}} (E : abses_es n B A),
      abses_es_rel n (abses_es_pushout n ab_diagonal E)
                     (abses_es_pullback n ab_diagonal (abses_es_direct_sum n E E)).
  Proof.
    induction n as [|n1 IH]; intros B A E.
    - apply equiv_path_grouphomomorphism; reflexivity.
    - destruct n1 as [|n0].
      + exact (abses_pushout_is_pullback (abses_diagonal E)).
      + exists ab_diagonal.
        refine (IH E.1 A (fst E.2), _).
        exact (abses_pushout_is_pullback (abses_diagonal (snd E.2))).
  Defined.

  (** The Baer sum of [E] with its negation [pushout (-id) E] is related to the
      split sequence: feeding the diagonal lemma through [phi = a - a'] turns it
      into [pushout 0 E], which the zero-absorb lemma sends to the split. *)
  Definition abses_es_baer_sum_inv (n : nat) {B A : AbGroup@{u}}
    (E : abses_es n B A)
    : abses_es_rel n (abses_es_pushout n grp_homo_const E)
        (abses_es_baer_sum n E (abses_es_pushout n ab_homo_negation E)).
  Proof.
    pose (phi := ab_codiagonal $o functor_ab_biprod grp_homo_id (ab_homo_negation : A $-> A)).
    assert (eq1 : abses_es_pushout n grp_homo_const E
                  = abses_es_pushout n phi (abses_es_pushout n ab_diagonal E)).
    { transitivity (abses_es_pushout n (phi $o ab_diagonal) E).
      - napply (ap (fun h => abses_es_pushout n h E)).
        apply equiv_path_grouphomomorphism; intro a; cbn; symmetry; apply grp_inv_r.
      - exact (abses_es_pushout_compose n ab_diagonal phi B E). }
    assert (eq2 : abses_es_pushout n phi
                    (abses_es_pullback n ab_diagonal (abses_es_direct_sum n E E))
                  = abses_es_baer_sum n E (abses_es_pushout n ab_homo_negation E)).
    { unfold abses_es_baer_sum.
      transitivity (abses_es_pullback n ab_diagonal
                      (abses_es_pushout n phi (abses_es_direct_sum n E E))).
      1: exact (abses_es_pushout_pullback n phi ab_diagonal (abses_es_direct_sum n E E)).
      napply (ap (abses_es_pullback n ab_diagonal)).
      transitivity (abses_es_pushout n ab_codiagonal
                      (abses_es_pushout n (functor_ab_biprod grp_homo_id (ab_homo_negation : A $-> A))
                         (abses_es_direct_sum n E E))).
      1: exact (abses_es_pushout_compose n
                  (functor_ab_biprod grp_homo_id (ab_homo_negation : A $-> A)) ab_codiagonal
                  (ab_biprod B B) (abses_es_direct_sum n E E)).
      napply (ap (abses_es_pushout n ab_codiagonal)).
      transitivity (abses_es_direct_sum n (abses_es_pushout n grp_homo_id E)
                      (abses_es_pushout n ab_homo_negation E)).
      1: exact (abses_es_directsum_pushout n grp_homo_id (ab_homo_negation : A $-> A) E E).
      napply (ap (fun s => abses_es_direct_sum n s
                    (abses_es_pushout n ab_homo_negation E))).
      exact (abses_es_pushout_id n E). }
    exact (transport (abses_es_rel n (abses_es_pushout n grp_homo_const E)) eq2
             (transport (fun X => abses_es_rel n X
                (abses_es_pushout n phi
                   (abses_es_pullback n ab_diagonal (abses_es_direct_sum n E E))))
                eq1^
                (abses_es_rel_pushout n phi B _ _
                   (abses_es_diagonal_is_pullback n E)))).
  Defined.

  (** The deep-end splice respects the relation, so the connecting map is
      well-defined on Ext. *)
  Definition abses_es_dsplice_rel (n : nat) {A A'' : AbGroup@{u}}
    (xi : AbSES A'' A) (B : AbGroup@{u})
    : forall e e' : abses_es n B A'', abses_es_rel n e e'
      -> abses_es_rel n.+1 (abses_es_dsplice n xi e) (abses_es_dsplice n xi e').
  Proof.
    revert B; induction n as [|n1 IH]; intro B.
    - intros e e' r; exact (ap (fun f => abses_pullback f xi) r).
    - destruct n1 as [|n0].
      + intros e e' r.
        exact (transport (abses_es_rel 2 (abses_es_dsplice 1 xi e))
                 (ap (abses_es_dsplice 1 xi) r)
                 (abses_es_rel_refl 2 (abses_es_dsplice 1 xi e))).
      + intros e e' r.
        exists r.1.
        refine (transport (abses_es_rel n0.+2 (abses_es_dsplice n0.+1 xi (fst e.2)))
                  (abses_es_dsplice_pullback n0.+1 xi r.1 (fst e'.2))
                  (IH e.1 (fst e.2) (abses_es_pullback n0.+1 r.1 (fst e'.2)) (fst r.2)),
                snd r.2).
  Defined.

  (** The junction identity for the connecting map: splicing the pullback
      [abses_pullback g zeta] onto [W] is related to splicing [zeta] onto [W]
      after pushing the deep end out along [g].  At the deepest level this is
      the pushout-pullback adjunction [abses_pushout_is_pullback]; for the base
      case it is the composition of pullbacks; deeper levels recurse with the
      identity. *)
  Definition abses_es_dsplice_pushout_rel (n : nat) {A C D : AbGroup@{u}}
    (zeta : AbSES C A) (g : D $-> C)
    : forall {B : AbGroup@{u}} (W : abses_es n B D),
      abses_es_rel n.+1
        (abses_es_dsplice n (abses_pullback g zeta) W)
        (abses_es_dsplice n zeta (abses_es_pushout n g W)).
  Proof.
    induction n as [|n1 IH]; intro B.
    - exact (fun W => abses_pullback_compose W g zeta).
    - destruct n1 as [|n0].
      + intro W.
        exists g.
        exact (idpath, idpath).
      + intro W.
        exists grp_homo_id.
        exact (transport
                 (abses_es_rel n0.+2
                    (abses_es_dsplice n0.+1 (abses_pullback g zeta) (fst W.2)))
                 (abses_es_pullback_id n0.+2
                    (abses_es_dsplice n0.+1 zeta (abses_es_pushout n0.+1 g (fst W.2))))^
                 (IH W.1 (fst W.2)),
               abses_pushout_id (snd W.2)).
  Defined.

  (** Splicing the split short exact sequence onto the deep end gives the zero
      sequence: the spliced [pt] becomes split and the recursion proceeds as in
      [abses_es_zero_absorb]. *)
  Definition abses_es_dsplice_point (n : nat) {A A'' : AbGroup@{u}}
    : forall {B : AbGroup@{u}} (X : abses_es n B A''),
      abses_es_rel n.+1 (abses_es_dsplice n (point (AbSES A'' A)) X)
                        (@abses_es_zero _ n.+1 A B).
  Proof.
    induction n as [|n1 IH]; intros B X.
    - exact (abses_pullback_point X).
    - destruct n1 as [|n0].
      + exists grp_homo_const.
        exact ((abses_pullback_point _)^, abses_pushout_const X).
      + exists grp_homo_const.
        refine (transport
                  (abses_es_rel n0.+2
                     (abses_es_dsplice n0.+1 (point (AbSES A'' A)) (fst X.2)))
                  (@abses_es_pullback_zero _ n0.+2 A X.1)^
                  (IH X.1 (fst X.2)), _).
        exact (abses_pushout_const (snd X.2)).
  Defined.

  (** Splicing a fixed short exact sequence onto the front respects the
      relation in the trailing sequence, witnessed by the identity. *)
  Definition abses_es_splice_rel {A C : AbGroup@{u}} (m : nat)
    {B : AbGroup@{u}} (s : AbSES B C) {E E' : abses_es m C A}
    (r : abses_es_rel m E E')
    : abses_es_rel m.+1 (abses_es_splice m E s) (abses_es_splice m E' s).
  Proof.
    destruct m as [|m0].
    - exact (ap (fun f => abses_pushout f s) r).
    - exists grp_homo_id.
      exact (transport (abses_es_rel m0.+1 E)
               (abses_es_pullback_id m0.+1 E')^ r,
             abses_pushout_id s).
  Defined.

  (** The base splice is additive: it carries the Baer sum to the Baer sum, so
      the contravariant connecting map is a homomorphism.  Since the base splice
      merely prepends [xi] (no recursion), the witness for [n >= 1] is the
      diagonal, with the trailing reflexive and the leading short exact sequence
      handled by [abses_pushout_is_pullback (abses_diagonal xi)].  In degree zero
      it is the distributivity of the Baer sum over pushouts. *)
  Definition abses_es_splice_baer_sum (n : nat) {A B' B'' : AbGroup@{u}}
    (xi : AbSES B'' B') (E F : abses_es n B' A)
    : abses_es_rel n.+1 (abses_es_splice n (abses_es_baer_sum n E F) xi)
        (abses_es_baer_sum n.+1 (abses_es_splice n E xi) (abses_es_splice n F xi)).
  Proof.
    destruct n as [|n0].
    - change (abses_pushout (abses_es_baer_sum 0 E F) xi
              = abses_baer_sum (abses_pushout E xi) (abses_pushout F xi)).
      refine (_ @ baer_sum_distributive_pushouts (E:=xi) E F).
      napply (ap (fun h => abses_pushout h xi)).
      apply equiv_path_grouphomomorphism; intro b; reflexivity.
    - exists ab_diagonal.
      exact (abses_es_rel_refl n0.+1 _, abses_pushout_is_pullback (abses_diagonal xi)).
  Defined.

  (** Splicing commutes with pullback in the base: the pulled-back base only
      meets the leading sequence. *)
  Definition abses_es_splice_pullback {A C : AbGroup@{u}} (m : nat)
    {B B' : AbGroup@{u}} (beta : B' $-> B) (E : abses_es m C A) (s : AbSES B C)
    : abses_es_pullback m.+1 beta (abses_es_splice m E s)
      = abses_es_splice m E (abses_pullback beta s).
  Proof.
    destruct m as [|m0].
    - exact (abses_pushout_pullback_reorder s E beta)^.
    - reflexivity.
  Defined.

  (** Splicing commutes with pushout in the deep end. *)
  Definition abses_es_splice_pushout {C : AbGroup@{u}} (m : nat)
    {A A' : AbGroup@{u}} (alpha : A $-> A') {B : AbGroup@{u}}
    (E : abses_es m C A) (s : AbSES B C)
    : abses_es_pushout m.+1 alpha (abses_es_splice m E s)
      = abses_es_splice m (abses_es_pushout m alpha E) s.
  Proof.
    destruct m as [|m0].
    - exact (abses_pushout_compose E alpha s)^.
    - reflexivity.
  Defined.

  (** The direct sum of two base-splices is the base-splice of the direct
      sums. *)
  Definition abses_es_directsum_splice (m : nat)
    {A C A' C' B B' : AbGroup@{u}} (s : AbSES B C) (t : AbSES B' C')
    (X : abses_es m C A) (Y : abses_es m C' A')
    : abses_es_direct_sum m.+1 (abses_es_splice m X s) (abses_es_splice m Y t)
      = abses_es_splice m (abses_es_direct_sum m X Y) (abses_direct_sum s t).
  Proof.
    destruct m as [|m0].
    - exact (abses_directsum_distributive_pushouts X Y)^.
    - reflexivity.
  Defined.

  (** The junction identity for the base splice: splicing the pullback
      [pullback g X] onto [s] is related to splicing [X] onto [s] pushed out
      along [g].  As the base splice merely prepends, this is a single
      relation witnessed by [g]. *)
  Definition abses_es_splice_pushout_rel {A C C' : AbGroup@{u}} (m : nat)
    (g : C' $-> C) {B : AbGroup@{u}} (s : AbSES B C') (X : abses_es m C A)
    : abses_es_rel m.+1 (abses_es_splice m (abses_es_pullback m g X) s)
        (abses_es_splice m X (abses_pushout g s)).
  Proof.
    destruct m as [|m0].
    - exact (abses_pushout_compose g X s).
    - exists g.
      exact (abses_es_rel_refl m0.+1 _, idpath).
  Defined.

  (** The length-[n] analogue of [abses_pushout_is_pullback] for the
      codiagonal: pushing the self-direct-sum out along the deep codiagonal
      agrees, up to the relation, with pulling back along the base
      codiagonal. *)
  Definition abses_es_codiagonal_is_pullback (n : nat)
    : forall {B A : AbGroup@{u}} (E : abses_es n B A),
      abses_es_rel n (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n E E))
                     (abses_es_pullback n ab_codiagonal E).
  Proof.
    induction n as [|n1 IH]; intros B A E.
    - apply equiv_path_grouphomomorphism; intro x; exact (grp_homo_op E _ _)^.
    - destruct n1 as [|n0].
      + exact (abses_pushout_is_pullback (abses_codiagonal E)).
      + exists ab_codiagonal.
        exact (IH E.1 A (fst E.2),
               abses_pushout_is_pullback (abses_codiagonal (snd E.2))).
  Defined.

End Relation.

(** ** The higher Ext groups *)

Section HigherExt.
  Context `{Univalence}.

  (** The set-quotient of a type by its path relation is its 0-truncation. *)
  Definition equiv_quotient_paths_tr (X : Type@{u})
    : Quotient (fun x y : X => x = y) <~> Tr 0 X.
  Proof.
    srapply equiv_adjointify.
    - srapply Quotient_rec.
      + exact tr.
      + intros x y p; exact (ap tr p).
    - srapply Trunc_rec; exact (class_of _).
    - srapply Trunc_ind; intro x; reflexivity.
    - srapply Quotient_ind_hprop; intro x; reflexivity.
  Defined.

  (** The [n]-th Ext group is the set-quotient of length-[n] exact sequences
      by the relation [abses_es_rel].  For [n] at most one this recovers the
      set of homomorphisms and the usual [Ext]. *)
  Definition abses_ext (n : nat) (B A : AbGroup@{u}) : Type
    := Quotient (abses_es_rel n (B:=B) (A:=A)).

  (** In degree zero the relation is equality of homomorphisms, so the
      quotient is the group of homomorphisms. *)
  Definition equiv_abses_ext_hom (B A : AbGroup@{u})
    : abses_ext 0 B A <~> ab_hom B A
    := (@equiv_tr 0 (ab_hom B A) _)^-1%equiv oE equiv_quotient_paths_tr _.

  (** In degree one the relation is equality of short exact sequences, so the
      quotient is the usual [Ext]. *)
  Definition equiv_abses_ext_one (B A : AbGroup@{u})
    : abses_ext 1 B A <~> Ext B A
    := equiv_quotient_paths_tr _.

  (** Pullback descends to the quotient, making [abses_ext n -- A] a
      contravariant functor. *)
  Definition abses_ext_pullback (n : nat) {A : AbGroup@{u}}
    {B B' : AbGroup@{u}} (beta : B' $-> B)
    : abses_ext n B A -> abses_ext n B' A
    := Quotient_functor _ _ (abses_es_pullback n beta) (abses_es_rel_pullback n beta).

  (** Pullback along the identity is the identity. *)
  Definition abses_ext_pullback_id (n : nat) {B A : AbGroup@{u}}
    : abses_ext_pullback n (A:=A) (grp_homo_id (G:=B)) == idmap.
  Proof.
    srapply Quotient_ind_hprop; intro E.
    apply (ap (class_of _)), abses_es_pullback_id.
  Defined.

  (** Pullback is contravariantly functorial. *)
  Definition abses_ext_pullback_compose (n : nat)
    {A B0 B1 B2 : AbGroup@{u}} (f : B0 $-> B1) (g : B1 $-> B2)
    : abses_ext_pullback n (A:=A) (g $o f)
      == abses_ext_pullback n f o abses_ext_pullback n g.
  Proof.
    srapply Quotient_ind_hprop; intro E.
    apply (ap (class_of _)), abses_es_pullback_compose.
  Defined.

  (** Pushout descends to the quotient, making [abses_ext n B --] a covariant
      functor. *)
  Definition abses_ext_pushout (n : nat) {B : AbGroup@{u}}
    {A A' : AbGroup@{u}} (alpha : A $-> A')
    : abses_ext n B A -> abses_ext n B A'
    := Quotient_functor _ _ (abses_es_pushout n alpha) (abses_es_rel_pushout n alpha B).

  (** Pushout along the identity is the identity. *)
  Definition abses_ext_pushout_id (n : nat) {B A : AbGroup@{u}}
    : abses_ext_pushout n (B:=B) (grp_homo_id (G:=A)) == idmap.
  Proof.
    srapply Quotient_ind_hprop; intro E.
    apply (ap (class_of _)), abses_es_pushout_id.
  Defined.

  (** Pushout is covariantly functorial. *)
  Definition abses_ext_pushout_compose (n : nat) {B : AbGroup@{u}}
    {A0 A1 A2 : AbGroup@{u}} (f : A0 $-> A1) (g : A1 $-> A2)
    : abses_ext_pushout n (B:=B) (g $o f)
      == abses_ext_pushout n g o abses_ext_pushout n f.
  Proof.
    srapply Quotient_ind_hprop; intro E.
    apply (ap (class_of _)), abses_es_pushout_compose.
  Defined.

  (** The pushout and pullback actions on Ext commute, so [abses_ext n] is a
      bifunctor, contravariant in the base and covariant in the deep end. *)
  Definition abses_ext_pushout_pullback (n : nat)
    {A A' B B' : AbGroup@{u}} (alpha : A $-> A') (beta : B' $-> B)
    : abses_ext_pushout n alpha o abses_ext_pullback n beta
      == abses_ext_pullback n beta o abses_ext_pushout n alpha.
  Proof.
    srapply Quotient_ind_hprop; intro E.
    apply (ap (class_of _)), abses_es_pushout_pullback.
  Defined.

  (** Splicing a fixed short exact sequence descends to a map of Ext groups,
      raising the degree. *)
  Definition abses_ext_splice {A C : AbGroup@{u}} (m : nat)
    {B : AbGroup@{u}} (s : AbSES B C)
    : abses_ext m C A -> abses_ext m.+1 B A
    := Quotient_functor _ _ (fun E => abses_es_splice m E s)
         (fun E E' => abses_es_splice_rel m s (E:=E) (E':=E')).

  (** The splice depends only on the class of the short exact sequence in
      [Ext], since the target is a set.  This is the Yoneda product
      [Ext B C -> Ext^m C A -> Ext^{m+1} B A]. *)
  Definition abses_ext_yoneda {A C : AbGroup@{u}} (m : nat)
    {B : AbGroup@{u}} (t : Ext B C)
    : abses_ext m C A -> abses_ext m.+1 B A
    := fun x => Trunc_rec (fun s => abses_ext_splice m s x) t.

  (** On a represented class it computes to the underlying splice. *)
  Definition abses_ext_yoneda_tr {A C : AbGroup@{u}} (m : nat)
    {B : AbGroup@{u}} (s : AbSES B C) (x : abses_ext m C A)
    : abses_ext_yoneda m (tr s) x = abses_ext_splice m s x
    := idpath.

  (** The connecting map of the long exact sequence: a short exact sequence
      [xi : AbSES A'' A] of coefficients raises the degree, [Ext^n B A'' ->
      Ext^{n+1} B A]. *)
  Definition abses_ext_dsplice (n : nat) {A A'' : AbGroup@{u}} (xi : AbSES A'' A)
    {B : AbGroup@{u}}
    : abses_ext n B A'' -> abses_ext n.+1 B A
    := Quotient_functor _ _ (abses_es_dsplice n xi) (abses_es_dsplice_rel n xi B).

  (** The connecting map is natural in the deep coefficient: pushing out along
      [alpha] after splicing [xi] is splicing the pushed-out sequence. *)
  Definition abses_ext_dsplice_pushout (n : nat) {A A2 A'' : AbGroup@{u}}
    (xi : AbSES A'' A) (alpha : A $-> A2) {B : AbGroup@{u}}
    (x : abses_ext n B A'')
    : abses_ext_pushout n.+1 alpha (abses_ext_dsplice n xi x)
      = abses_ext_dsplice n (abses_pushout alpha xi) x.
  Proof.
    revert x; srapply Quotient_ind_hprop; intro Y.
    exact (ap (class_of _) (abses_es_dsplice_pushout n xi alpha Y)).
  Defined.

  (** The connecting map is natural in the base: splicing [xi] commutes with
      pullback along [beta]. *)
  Definition abses_ext_dsplice_pullback (n : nat) {A A'' : AbGroup@{u}}
    (xi : AbSES A'' A) {B B' : AbGroup@{u}} (beta : B' $-> B)
    (x : abses_ext n B A'')
    : abses_ext_dsplice n xi (abses_ext_pullback n beta x)
      = abses_ext_pullback n.+1 beta (abses_ext_dsplice n xi x).
  Proof.
    revert x; srapply Quotient_ind_hprop; intro Y.
    exact (ap (class_of _) (abses_es_dsplice_pullback n xi beta Y)).
  Defined.

  (** The Baer sum descends to a binary operation on the [n]-th Ext. *)
  Definition abses_ext_baer_sum (n : nat) {B A : AbGroup@{u}}
    : abses_ext n B A -> abses_ext n B A -> abses_ext n B A.
  Proof.
    srapply Quotient_rec2.
    - exact (fun E F => class_of _ (abses_es_baer_sum n E F)).
    - intros E E' F rE; apply qglue.
      exact (abses_es_baer_sum_rel n rE (abses_es_rel_refl n F)).
    - intros E F F' rF; apply qglue.
      exact (abses_es_baer_sum_rel n (abses_es_rel_refl n E) rF).
  Defined.

  (** The connecting map is additive: it carries the Baer sum to the Baer sum,
      so the splice [Ext^n B A'' -> Ext^{n+1} B A] is a homomorphism.  This is
      the bilinearity of the Yoneda splice in the deep-end variable; the only
      nontrivial step is the junction identity [abses_es_dsplice_pushout_rel],
      after rewriting [abses_pullback ab_codiagonal xi] as a pushout via
      [abses_pushout_is_pullback]. *)
  Definition abses_ext_dsplice_baer_sum (n : nat) {A A'' : AbGroup@{u}}
    (xi : AbSES A'' A) {B : AbGroup@{u}} (x y : abses_ext n B A'')
    : abses_ext_dsplice n xi (abses_ext_baer_sum n x y)
      = abses_ext_baer_sum n.+1 (abses_ext_dsplice n xi x) (abses_ext_dsplice n xi y).
  Proof.
    revert x y; srapply Quotient_ind2_hprop; intros E F.
    refine (ap (class_of _)
              (abses_es_dsplice_pullback n xi ab_diagonal
                 (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n E F))) @ _).
    refine (_ @ (ap (class_of _)
              (ap (abses_es_pullback n.+1 ab_diagonal)
                 (ap (abses_es_pushout n.+1 ab_codiagonal)
                    (abses_es_directsum_dsplice n xi E F)
                  @ abses_es_dsplice_pushout n (abses_direct_sum xi xi)
                       ab_codiagonal (abses_es_direct_sum n E F))))^).
    refine (_ @ (ap (class_of _)
              (ap (abses_es_pullback n.+1 ab_diagonal)
                 (ap (fun z => abses_es_dsplice n z (abses_es_direct_sum n E F))
                    (abses_pushout_is_pullback (abses_codiagonal xi)))))^).
    symmetry; apply qglue.
    exact (abses_es_rel_pullback n.+1 ab_diagonal _ _
             (abses_es_dsplice_pushout_rel n xi ab_codiagonal
                (abses_es_direct_sum n E F))).
  Defined.

  (** The contravariant connecting map (base splice) is additive: it carries the
      Baer sum to the Baer sum, so it is a homomorphism [Ext^n B' A ->
      Ext^{n+1} B'' A]. *)
  Definition abses_ext_splice_baer_sum (n : nat) {A B' B'' : AbGroup@{u}}
    (xi : AbSES B'' B') (x y : abses_ext n B' A)
    : abses_ext_splice n xi (abses_ext_baer_sum n x y)
      = abses_ext_baer_sum n.+1 (abses_ext_splice n xi x) (abses_ext_splice n xi y).
  Proof.
    revert x y; srapply Quotient_ind2_hprop; intros E F.
    exact (qglue (abses_es_splice_baer_sum n xi E F)).
  Defined.

  (** The base splice is additive in the short exact sequence slot: it carries
      the Baer sum of [s] and [t] to the Baer sum of the splices.  Both sides
      reduce, via the base-pullback and deep-pushout commutations and the
      junction, to a splice of [pullback Delta (direct_sum s t)]; the two deep
      arguments [pullback codiagonal X] and [pushout codiagonal (X (+) X)] are
      then identified by [abses_es_codiagonal_is_pullback]. *)
  Definition abses_ext_splice_baer_sum_ses (n : nat) {A B' B'' : AbGroup@{u}}
    (s t : AbSES B'' B') (x : abses_ext n B' A)
    : abses_ext_splice n (abses_baer_sum s t) x
      = abses_ext_baer_sum n.+1 (abses_ext_splice n s x) (abses_ext_splice n t x).
  Proof.
    revert x; srapply Quotient_ind_hprop; intro X.
    refine (ap (class_of _) (abses_es_splice_pullback n ab_diagonal X
              (abses_pushout ab_codiagonal (abses_direct_sum s t)))^ @ _).
    refine ((qglue (abses_es_rel_pullback n.+1 ab_diagonal _ _
              (abses_es_splice_pushout_rel n ab_codiagonal
                 (abses_direct_sum s t) X)))^ @ _).
    refine (ap (class_of _) (abses_es_splice_pullback n ab_diagonal
              (abses_es_pullback n ab_codiagonal X) (abses_direct_sum s t)) @ _).
    refine ((qglue (abses_es_splice_rel n
              (abses_pullback ab_diagonal (abses_direct_sum s t))
              (abses_es_codiagonal_is_pullback n X)))^ @ _).
    refine (ap (class_of _) (abses_es_splice_pullback n ab_diagonal
              (abses_es_pushout n ab_codiagonal (abses_es_direct_sum n X X))
              (abses_direct_sum s t))^ @ _).
    refine (ap (class_of _) (ap (abses_es_pullback n.+1 ab_diagonal)
              (abses_es_splice_pushout n ab_codiagonal
                 (abses_es_direct_sum n X X) (abses_direct_sum s t))^) @ _).
    exact (ap (class_of _) (ap (abses_es_pullback n.+1 ab_diagonal)
              (ap (abses_es_pushout n.+1 ab_codiagonal)
                 (abses_es_directsum_splice n s t X X)^))).
  Defined.

  (** The Baer sum on the [n]-th Ext is commutative. *)
  Definition abses_ext_baer_sum_comm (n : nat) {B A : AbGroup@{u}}
    (x y : abses_ext n B A)
    : abses_ext_baer_sum n x y = abses_ext_baer_sum n y x.
  Proof.
    revert x y; srapply Quotient_ind2_hprop; intros E F.
    exact (qglue (abses_es_baer_sum_comm n E F)).
  Defined.

  (** The Baer sum on the [n]-th Ext is associative. *)
  Definition abses_ext_baer_sum_assoc (n : nat) {B A : AbGroup@{u}}
    (x y z : abses_ext n B A)
    : abses_ext_baer_sum n (abses_ext_baer_sum n x y) z
      = abses_ext_baer_sum n x (abses_ext_baer_sum n y z).
  Proof.
    revert x y z.
    srapply Quotient_ind_hprop; intro E.
    srapply Quotient_ind_hprop; intro F.
    srapply Quotient_ind_hprop; intro G.
    exact (qglue (abses_es_baer_sum_assoc n E F G)).
  Defined.

  (** The class of the split sequence is the neutral element. *)
  Definition abses_ext_zero (n : nat) (B A : AbGroup@{u}) : abses_ext n B A
    := class_of _ (@abses_es_zero _ n A B).

  (** It is a right and left unit for the Baer sum. *)
  Definition abses_ext_baer_sum_unit_r (n : nat) {B A : AbGroup@{u}}
    (x : abses_ext n B A)
    : abses_ext_baer_sum n x (abses_ext_zero n B A) = x.
  Proof.
    revert x; srapply Quotient_ind_hprop; intro E.
    exact (qglue (abses_es_baer_sum_unit n E)).
  Defined.

  Definition abses_ext_baer_sum_unit_l (n : nat) {B A : AbGroup@{u}}
    (x : abses_ext n B A)
    : abses_ext_baer_sum n (abses_ext_zero n B A) x = x
    := abses_ext_baer_sum_comm n _ x @ abses_ext_baer_sum_unit_r n x.

  (** Pushout along negation is an additive inverse for the Baer sum. *)
  Definition abses_ext_baer_sum_inv_r (n : nat) {B A : AbGroup@{u}}
    (x : abses_ext n B A)
    : abses_ext_baer_sum n x (abses_ext_pushout n ab_homo_negation x)
      = abses_ext_zero n B A.
  Proof.
    revert x; srapply Quotient_ind_hprop; intro E.
    exact ((qglue (abses_es_baer_sum_inv n E))^ @ qglue (abses_es_zero_absorb n E)).
  Defined.

  Definition abses_ext_baer_sum_inv_l (n : nat) {B A : AbGroup@{u}}
    (x : abses_ext n B A)
    : abses_ext_baer_sum n (abses_ext_pushout n ab_homo_negation x) x
      = abses_ext_zero n B A
    := abses_ext_baer_sum_comm n _ x @ abses_ext_baer_sum_inv_r n x.

  (** The [n]-th Ext is a group under the Baer sum. *)
  Definition grp_abses_ext (n : nat) (B A : AbGroup@{u}) : Group.
  Proof.
    snapply (Build_Group (abses_ext n B A)).
    - exact (abses_ext_baer_sum n).
    - exact (abses_ext_zero n B A).
    - exact (abses_ext_pushout n ab_homo_negation).
    - repeat split.
      + exact _.
      + intros x y z; symmetry; apply abses_ext_baer_sum_assoc.
      + intro x; apply abses_ext_baer_sum_unit_l.
      + intro x; apply abses_ext_baer_sum_unit_r.
      + intro x; apply abses_ext_baer_sum_inv_l.
      + intro x; apply abses_ext_baer_sum_inv_r.
  Defined.

  (** In fact it is abelian. *)
  Definition ab_abses_ext (n : nat) (B A : AbGroup@{u}) : AbGroup.
  Proof.
    snapply (Build_AbGroup (grp_abses_ext n B A)).
    intros x y; apply abses_ext_baer_sum_comm.
  Defined.

  (** Pushout and pullback are group homomorphisms for the Baer sum, so
      [ab_abses_ext n] is a bifunctor valued in abelian groups. *)
  Definition grp_homo_abses_ext_pushout (n : nat) {B : AbGroup@{u}}
    {A A' : AbGroup@{u}} (alpha : A $-> A')
    : ab_abses_ext n B A $-> ab_abses_ext n B A'.
  Proof.
    snapply Build_GroupHomomorphism.
    - exact (abses_ext_pushout n alpha).
    - intros x y; revert x y.
      srapply Quotient_ind2_hprop; intros E F.
      exact (ap (class_of _) (abses_es_pushout_baer_sum n alpha E F)).
  Defined.

  Definition grp_homo_abses_ext_pullback (n : nat) {A : AbGroup@{u}}
    {B B' : AbGroup@{u}} (beta : B' $-> B)
    : ab_abses_ext n B A $-> ab_abses_ext n B' A.
  Proof.
    snapply Build_GroupHomomorphism.
    - exact (abses_ext_pullback n beta).
    - intros x y; revert x y.
      srapply Quotient_ind2_hprop; intros E F.
      exact (ap (class_of _) (abses_es_pullback_baer_sum n beta E F)).
  Defined.

  (** The connecting map of the long exact sequence, as a homomorphism
      [Ext^n B A'' -> Ext^{n+1} B A]. *)
  Definition grp_homo_abses_ext_dsplice (n : nat) {A A'' : AbGroup@{u}}
    (xi : AbSES A'' A) {B : AbGroup@{u}}
    : ab_abses_ext n B A'' $-> ab_abses_ext n.+1 B A.
  Proof.
    snapply Build_GroupHomomorphism.
    - exact (abses_ext_dsplice n xi).
    - intros x y; apply abses_ext_dsplice_baer_sum.
  Defined.

  (** The contravariant connecting map, as a homomorphism
      [Ext^n B' A -> Ext^{n+1} B'' A] from a short exact sequence of bases. *)
  Definition grp_homo_abses_ext_splice (n : nat) {A B' B'' : AbGroup@{u}}
    (xi : AbSES B'' B')
    : ab_abses_ext n B' A $-> ab_abses_ext n.+1 B'' A.
  Proof.
    snapply Build_GroupHomomorphism.
    - exact (abses_ext_splice n xi).
    - intros x y; apply abses_ext_splice_baer_sum.
  Defined.

  (** Pushing out along the zero map lands in the zero class. *)
  Definition abses_ext_pushout_const (n : nat) {B A A' : AbGroup@{u}}
    (x : abses_ext n B A)
    : abses_ext_pushout n (@grp_homo_const A A') x = abses_ext_zero n B A'.
  Proof.
    revert x; srapply Quotient_ind_hprop; intro E.
    exact (qglue (abses_es_zero_absorb n E)).
  Defined.

  (** The covariant Ext sequence of a coefficient short exact sequence is a
      complex: pushing out along the inclusion then the projection vanishes. *)
  Definition abses_ext_pushout_iscomplex (n : nat) {B A A'' : AbGroup@{u}}
    (xi : AbSES A'' A) (x : abses_ext n B A)
    : abses_ext_pushout n (projection xi) (abses_ext_pushout n (inclusion xi) x)
      = abses_ext_zero n B A''.
  Proof.
    refine ((abses_ext_pushout_compose n (inclusion xi) (projection xi) x)^ @ _).
    refine (_ @ abses_ext_pushout_const n x).
    napply (ap (fun h => abses_ext_pushout n h x)).
    apply equiv_path_grouphomomorphism; intro a.
    pose proof (iscomplex_abses xi) as hc; unfold ExactSequence.IsComplex in hc.
    destruct hc as [hc0 hc1]; exact (hc0 a).
  Defined.

  (** Splicing the split short exact sequence descends to the zero class. *)
  Definition abses_ext_dsplice_point (n : nat) {A A'' : AbGroup@{u}}
    {B : AbGroup@{u}} (x : abses_ext n B A'')
    : abses_ext_dsplice n (point (AbSES A'' A)) x = abses_ext_zero n.+1 B A.
  Proof.
    revert x; srapply Quotient_ind_hprop; intro X.
    exact (qglue (abses_es_dsplice_point n X)).
  Defined.

  (** The junction identity, descended to Ext. *)
  Definition abses_ext_dsplice_junction (n : nat) {A C D : AbGroup@{u}}
    (zeta : AbSES C A) (g : D $-> C) {B : AbGroup@{u}} (w : abses_ext n B D)
    : abses_ext_dsplice n (abses_pullback g zeta) w
      = abses_ext_dsplice n zeta (abses_ext_pushout n g w).
  Proof.
    revert w; srapply Quotient_ind_hprop; intro W.
    exact (qglue (abses_es_dsplice_pushout_rel n zeta g W)).
  Defined.

  (** The connecting map kills the image of the projection: the covariant Ext
      sequence is a complex at [Ext^n B A'']. *)
  Definition abses_ext_dsplice_projection_iscomplex (n : nat)
    {A A'' : AbGroup@{u}} (xi : AbSES A'' A) {B : AbGroup@{u}}
    (x : abses_ext n B xi)
    : abses_ext_dsplice n xi (abses_ext_pushout n (projection xi) x)
      = abses_ext_zero n.+1 B A.
  Proof.
    refine ((abses_ext_dsplice_junction n xi (projection xi) x)^ @ _).
    refine (ap (fun z => abses_ext_dsplice n z x) (abses_pullback_projection xi)^ @ _).
    exact (abses_ext_dsplice_point n x).
  Defined.

  (** The image of the connecting map is killed by the inclusion: the covariant
      Ext sequence is a complex at [Ext^{n+1} B A]. *)
  Definition abses_ext_inclusion_dsplice_iscomplex (n : nat)
    {A A'' : AbGroup@{u}} (xi : AbSES A'' A) {B : AbGroup@{u}}
    (x : abses_ext n B A'')
    : abses_ext_pushout n.+1 (inclusion xi) (abses_ext_dsplice n xi x)
      = abses_ext_zero n.+1 B xi.
  Proof.
    refine (abses_ext_dsplice_pushout n xi (inclusion xi) x @ _).
    refine (ap (fun z => abses_ext_dsplice n z x) (abses_pushout_inclusion xi) @ _).
    exact (abses_ext_dsplice_point n x).
  Defined.

  (** The connecting map is natural in the coefficient short exact sequence: a
      morphism [phi : xi -> xi'] gives a commuting square relating the two
      connecting maps via pushout along its end components.  The proof routes
      [abses_pushout_is_pullback phi] through the junction identity. *)
  Definition abses_ext_dsplice_natural (n : nat)
    {A A' A'' A''' : AbGroup@{u}} {xi : AbSES A'' A} {xi' : AbSES A''' A'}
    (phi : AbSESMorphism xi xi') {B : AbGroup@{u}} (x : abses_ext n B A'')
    : abses_ext_pushout n.+1 (component1 phi) (abses_ext_dsplice n xi x)
      = abses_ext_dsplice n xi' (abses_ext_pushout n (component3 phi) x).
  Proof.
    refine (abses_ext_dsplice_pushout n xi (component1 phi) x @ _).
    refine (ap (fun z => abses_ext_dsplice n z x) (abses_pushout_is_pullback phi) @ _).
    exact (abses_ext_dsplice_junction n xi' (component3 phi) x).
  Defined.

  (** Base pullback commutes with the base splice, descended to Ext. *)
  Definition abses_ext_splice_pullback (n : nat) {A C B B2 : AbGroup@{u}}
    (s : AbSES B C) (beta : B2 $-> B) (x : abses_ext n C A)
    : abses_ext_pullback n.+1 beta (abses_ext_splice n s x)
      = abses_ext_splice n (abses_pullback beta s) x.
  Proof.
    revert x; srapply Quotient_ind_hprop; intro X.
    exact (ap (class_of _) (abses_es_splice_pullback n beta X s)).
  Defined.

  (** The junction identity for the base splice, descended to Ext. *)
  Definition abses_ext_splice_pullback_junction (n : nat) {A C C' : AbGroup@{u}}
    (g : C' $-> C) {B : AbGroup@{u}} (s : AbSES B C') (y : abses_ext n C A)
    : abses_ext_splice n s (abses_ext_pullback n g y)
      = abses_ext_splice n (abses_pushout g s) y.
  Proof.
    revert y; srapply Quotient_ind_hprop; intro X.
    exact (qglue (abses_es_splice_pushout_rel n g s X)).
  Defined.

  (** Splicing the split short exact sequence onto the base is the zero map:
      by additivity in the sequence slot the splice [Z] of [point] satisfies
      [Z = Z + Z], hence [Z = 0]. *)
  Definition abses_ext_splice_point (n : nat) {A B' B'' : AbGroup@{u}}
    (x : abses_ext n B' A)
    : abses_ext_splice n (point (AbSES B'' B')) x = abses_ext_zero n.+1 B'' A.
  Proof.
    refine ((grp_cancelL1 (G := ab_abses_ext n.+1 B'' A)
               (z := abses_ext_splice n (point (AbSES B'' B')) x))^-1 _).
    exact ((abses_ext_splice_baer_sum_ses n (point _) (point _) x)^
           @ ap (fun s => abses_ext_splice n s x) (baer_sum_unit_r (point _))).
  Defined.

  (** The contravariant Ext sequence is a complex at [Ext^{n+1} B'' A]: the
      connecting map [delta' = splice xi] composed with the projection pullback
      vanishes. *)
  Definition abses_ext_splice_projection_iscomplex (n : nat)
    {A B' B'' : AbGroup@{u}} (xi : AbSES B'' B') (x : abses_ext n B' A)
    : abses_ext_pullback n.+1 (projection xi) (abses_ext_splice n xi x)
      = abses_ext_zero n.+1 xi A.
  Proof.
    refine (abses_ext_splice_pullback n xi (projection xi) x @ _).
    refine (ap (fun s => abses_ext_splice n s x) (abses_pullback_projection xi)^ @ _).
    exact (abses_ext_splice_point n x).
  Defined.

  (** The contravariant Ext sequence is a complex at [Ext^n B' A]: the
      inclusion pullback followed by the connecting map vanishes. *)
  Definition abses_ext_inclusion_splice_iscomplex (n : nat)
    {A B' B'' : AbGroup@{u}} (xi : AbSES B'' B') (x : abses_ext n xi A)
    : abses_ext_splice n xi (abses_ext_pullback n (inclusion xi) x)
      = abses_ext_zero n.+1 B'' A.
  Proof.
    refine (abses_ext_splice_pullback_junction n (inclusion xi) xi x @ _).
    refine (ap (fun s => abses_ext_splice n s x) (abses_pushout_inclusion xi) @ _).
    exact (abses_ext_splice_point n x).
  Defined.

  (** Pulling back along the zero map lands in the zero class. *)
  Definition abses_ext_pullback_const (n : nat) {A B' B'' : AbGroup@{u}}
    (x : abses_ext n B'' A)
    : abses_ext_pullback n (@grp_homo_const B' B'') x = abses_ext_zero n B' A.
  Proof.
    destruct n as [|[|n0]]; revert x; srapply Quotient_ind_hprop; intro X.
    - apply (ap (class_of _)).
      apply equiv_path_grouphomomorphism; intro b; exact (grp_homo_unit X).
    - exact (ap (class_of _) (abses_pullback_const X)^).
    - refine (ap (class_of _) (ap (fun s => (X.1; (fst X.2, s)) : abses_es n0.+2 B' A)
                (abses_pullback_const (snd X.2))^) @ _).
      exact (abses_ext_splice_point n0.+1 (class_of _ (fst X.2))).
  Defined.

  (** The contravariant Ext sequence is a complex at [Ext^n M A]: the projection
      pullback followed by the inclusion pullback vanishes. *)
  Definition abses_ext_projection_inclusion_iscomplex (n : nat)
    {A B' B'' : AbGroup@{u}} (xi : AbSES B'' B') (x : abses_ext n B'' A)
    : abses_ext_pullback n (inclusion xi) (abses_ext_pullback n (projection xi) x)
      = abses_ext_zero n B' A.
  Proof.
    refine ((abses_ext_pullback_compose n (inclusion xi) (projection xi) x)^ @ _).
    refine (ap (fun h => abses_ext_pullback n h x) _ @ abses_ext_pullback_const n x).
    apply equiv_path_grouphomomorphism; intro a.
    pose proof (iscomplex_abses xi) as hc; unfold ExactSequence.IsComplex in hc.
    destruct hc as [hc0 hc1]; exact (hc0 a).
  Defined.

  (** The contravariant connecting map is natural in the base short exact
      sequence: a morphism [phi : xi -> xi'] gives a commuting square relating
      the two connecting maps via pullback along its end components. *)
  Definition abses_ext_splice_natural (n : nat)
    {A B' B'' D' D'' : AbGroup@{u}} {xi : AbSES B'' B'} {xi' : AbSES D'' D'}
    (phi : AbSESMorphism xi xi') (x : abses_ext n D' A)
    : abses_ext_splice n xi (abses_ext_pullback n (component1 phi) x)
      = abses_ext_pullback n.+1 (component3 phi) (abses_ext_splice n xi' x).
  Proof.
    refine (abses_ext_splice_pullback_junction n (component1 phi) xi x @ _).
    refine (ap (fun s => abses_ext_splice n s x) (abses_pushout_is_pullback phi) @ _).
    exact (abses_ext_splice_pullback n xi' (component3 phi) x)^.
  Defined.

  (** The Yoneda product, as a homomorphism in the second variable: a class
      [t : Ext B C] gives a homomorphism [Ext^m C A -> Ext^{m+1} B A].  It is
      well-defined on [Ext] because the splice is additive, and the target is a
      set of homomorphisms. *)
  Definition grp_homo_abses_ext_yoneda {A C : AbGroup@{u}} (m : nat)
    {B : AbGroup@{u}} (t : Ext B C)
    : ab_abses_ext m C A $-> ab_abses_ext m.+1 B A
    := Trunc_rec (fun s => grp_homo_abses_ext_splice m s) t.

  (** If [E] splits after pushing out along [inclusion xi], it is the pullback
      of [xi] along some [g : B $-> A'']. *)
  Definition abses_inclusion_pushout_exact {A A'' : AbGroup@{u}}
    (xi : AbSES A'' A) {B : AbGroup@{u}} (E : AbSES B A)
    (h : abses_pushout (inclusion xi) E = point (AbSES B xi))
    : merely { g : ab_hom B A'' & abses_pullback g xi = E }.
  Proof.
    pose proof (abses_pushout_trivial_factors_inclusion (inclusion xi) E h)
      as [phi hphi].
    assert (hkill : forall n : middle E, grp_image (inclusion E) n
                      -> (projection xi $o phi) n = mon_unit).
    { intro n; srapply Trunc_rec; intros [a p].
      refine (ap (projection xi $o phi) p^ @ _).
      refine (ap (projection xi) (equiv_path_grouphomomorphism^-1 hphi a)^ @ _).
      pose proof (iscomplex_abses xi) as hc; unfold ExactSequence.IsComplex in hc.
      destruct hc as [hc0 hc1]; exact (hc0 a). }
    pose (g0 := quotient_abgroup_rec (grp_image (inclusion E)) A''
                  (projection xi $o phi) hkill).
    pose (g := grp_homo_compose g0
                 (grp_iso_inverse (abses_cokernel_iso (inclusion E) (projection E)))).
    snrefine (tr (g; (abses_pullback_component1_id
                        (Build_AbSESMorphism grp_homo_id phi g _ _)
                        (fun _ => idpath))^)).
    - exact (equiv_path_grouphomomorphism^-1 hphi).
    - intro e.
      exact (ap g0 (abses_cokernel_iso_inv_beta (inclusion E) (projection E) e))^.
  Defined.

  (** If [v] splits after pulling back along [projection xi], it is the pushout
      of [xi] along some [g : B' $-> A]. *)
  Definition abses_projection_pullback_exact {A B' B'' : AbGroup@{u}}
    (xi : AbSES B'' B') (v : AbSES B'' A)
    (h : abses_pullback (projection xi) v = point (AbSES xi A))
    : merely { g : ab_hom B' A & abses_pushout g xi = v }.
  Proof.
    pose proof (abses_pullback_trivial_factors_projection (projection xi) v h)
      as [phi hphi].
    pose proof (iscomplex_abses xi) as hc; unfold ExactSequence.IsComplex in hc.
    destruct hc as [hc0 hc1].
    pose (g0 := grp_kernel_corec (f:=projection v) (phi $o inclusion xi)
                  (fun b => (equiv_path_grouphomomorphism^-1 hphi (inclusion xi b))^
                            @ hc0 b)).
    pose (g := grp_homo_compose
                 (grp_iso_inverse (abses_kernel_iso (inclusion v) (projection v))) g0).
    snrefine (tr (g; abses_pushout_component3_id
                       (Build_AbSESMorphism g phi grp_homo_id _ _)
                       (fun _ => idpath))).
    - intro b.
      exact (abses_kernel_iso_inv_beta (inclusion v) (projection v) (g0 b)).
    - exact (fun m => (equiv_path_grouphomomorphism^-1 hphi m)^).
  Defined.

  (** If [E] splits after pushing out along [projection xi], it is the pushout
      along [inclusion xi] of some [E' : AbSES B A].  The witness [E'] is the
      sub-extension of [E] on the kernel of the factoring map [phi]. *)
  Definition abses_pushout_projection_exact {A A'' : AbGroup@{u}}
    (xi : AbSES A'' A) {B : AbGroup@{u}} (E : AbSES B xi)
    (h : abses_pushout (projection xi) E = point (AbSES B A''))
    : merely { E' : AbSES B A & abses_pushout (inclusion xi) E' = E }.
  Proof.
    pose proof (abses_pushout_trivial_factors_inclusion (projection xi) E h)
      as [phi hphi].
    pose proof (iscomplex_abses xi) as hcx; unfold ExactSequence.IsComplex in hcx.
    destruct hcx as [hcx0 hcx1].
    pose proof (iscomplex_abses E) as hcE; unfold ExactSequence.IsComplex in hcE.
    destruct hcE as [hcE0 hcE1].
    assert (hkill : phi $o (inclusion E $o inclusion xi) == grp_homo_const).
    { intro a.
      exact ((equiv_path_grouphomomorphism^-1 hphi (inclusion xi a))^ @ hcx0 a). }
    pose (iE' := grp_kernel_corec (inclusion E $o inclusion xi) hkill).
    pose (sub := subgroup_incl (grp_kernel phi)).
    snrefine (tr (Build_AbSES (ab_kernel phi) iE'
                    (grp_homo_compose (projection E) sub) _ _ _; _)).
    - apply isembedding_isinj_hset; intros a a' p.
      assert (beta : forall x, sub (iE' x) = inclusion E (inclusion xi x))
        by reflexivity.
      exact (isinj_embedding (inclusion xi) _ a a'
               (isinj_embedding (inclusion E) _ _ _
                  ((beta a)^ @ ap sub p @ beta a'))).
    - intro b.
      rapply contr_inhabited_hprop.
      assert (fe : merely (hfiber (projection E) b))
        by apply center, issurjection_projection.
      strip_truncations; destruct fe as [e qe].
      assert (fm : merely (hfiber (projection xi) (phi e)))
        by apply center, issurjection_projection.
      strip_truncations; destruct fm as [mu qmu].
      assert (mem : phi (sg_op e (inv (inclusion E mu))) = mon_unit).
      { refine (grp_homo_op phi e (inv (inclusion E mu)) @ _).
        refine (ap (sg_op (phi e)) (grp_homo_inv phi (inclusion E mu)) @ _).
        refine (ap (fun z => sg_op (phi e) (inv z))
                  ((equiv_path_grouphomomorphism^-1 hphi mu)^ @ qmu) @ _).
        exact (grp_inv_r (phi e)). }
      refine (tr (((sg_op e (inv (inclusion E mu)); mem)
                    : grp_kernel phi); _)).
      refine (grp_homo_op (projection E) e (inv (inclusion E mu)) @ _).
      refine (ap (sg_op (projection E e))
                (grp_homo_inv (projection E) (inclusion E mu)) @ _).
      refine (ap (fun z => sg_op (projection E e) (inv z)) (hcE0 mu) @ _).
      refine (ap (sg_op (projection E e)) grp_inv_unit @ _).
      exact (grp_unit_r _ @ qe).
    - snapply Build_IsExact.
      + srapply phomotopy_homotopy_hset.
        intro a.
        exact (hcE0 (inclusion xi a)).
      + intros [m q].
        rapply contr_inhabited_hprop.
        assert (fmu : merely (hfiber (inclusion E) (sub m)))
          by exact (isexact_preimage (Tr (-1)) (inclusion E) (projection E) (sub m) q).
        strip_truncations; destruct fmu as [mu rmu].
        assert (fa : merely (hfiber (inclusion xi) mu))
          by exact (isexact_preimage (Tr (-1)) (inclusion xi) (projection xi) mu
                      (equiv_path_grouphomomorphism^-1 hphi mu @ (ap phi rmu @ m.2))).
        strip_truncations; destruct fa as [a ra].
        refine (tr (a; _)).
        apply path_sigma_hprop.
        apply path_sigma_hprop; cbn.
        exact (ap (inclusion E) ra @ rmu).
    - snrefine (abses_pushout_component3_id
                 (Build_AbSESMorphism (inclusion xi) _ grp_homo_id _ _)
                 (fun _ => idpath)).
      + exact sub.
      + exact (fun _ => idpath).
      + exact (fun _ => idpath).
  Defined.

  (** Exactness of the covariant sequence at [Ext B A]: the kernel of
      [pushout (inclusion xi)] is the image of the connecting map from
      [Hom B A'']. *)
  Definition abses_ext_inclusion_exact_one {A A'' : AbGroup@{u}} (xi : AbSES A'' A)
    {B : AbGroup@{u}} (v : abses_ext 1 B A)
    : abses_ext_pushout 1 (inclusion xi) v = abses_ext_zero 1 B xi
      -> merely { w : abses_ext 0 B A'' & abses_ext_dsplice 0 xi w = v }.
  Proof.
    revert v; srapply Quotient_ind_hprop; intros V h.
    pose proof ((equiv_path_Tr _ _)^-1
                  (ap (equiv_quotient_paths_tr (AbSES B xi)) h)) as hm.
    strip_truncations.
    pose proof (abses_inclusion_pushout_exact xi V hm) as hg.
    strip_truncations; destruct hg as [g pq].
    exact (tr (class_of _ g; ap (class_of _) pq)).
  Defined.

  (** Exactness of the covariant sequence at [Ext B (middle xi)]: the kernel of
      [pushout (projection xi)] is the image of [pushout (inclusion xi)]. *)
  Definition abses_ext_pushout_inclusion_exact_one {A A'' : AbGroup@{u}}
    (xi : AbSES A'' A) {B : AbGroup@{u}} (v : abses_ext 1 B xi)
    : abses_ext_pushout 1 (projection xi) v = abses_ext_zero 1 B A''
      -> merely { w : abses_ext 1 B A & abses_ext_pushout 1 (inclusion xi) w = v }.
  Proof.
    revert v; srapply Quotient_ind_hprop; intros V h.
    pose proof ((equiv_path_Tr _ _)^-1
                  (ap (equiv_quotient_paths_tr (AbSES B A'')) h)) as hm.
    strip_truncations.
    pose proof (abses_pushout_projection_exact xi V hm) as hE.
    strip_truncations; destruct hE as [E' pq].
    exact (tr (class_of _ E'; ap (class_of _) pq)).
  Defined.

  (** Exactness of the contravariant sequence at [Ext B'' A]: the kernel of
      [pullback (projection xi)] is the image of the connecting map from
      [Hom B' A]. *)
  Definition abses_ext_pullback_projection_exact_one {A B' B'' : AbGroup@{u}}
    (xi : AbSES B'' B') (v : abses_ext 1 B'' A)
    : abses_ext_pullback 1 (projection xi) v = abses_ext_zero 1 xi A
      -> merely { w : abses_ext 0 B' A & abses_ext_splice 0 xi w = v }.
  Proof.
    revert v; srapply Quotient_ind_hprop; intros V h.
    pose proof ((equiv_path_Tr _ _)^-1
                  (ap (equiv_quotient_paths_tr (AbSES xi A)) h)) as hm.
    strip_truncations.
    pose proof (abses_projection_pullback_exact xi V hm) as hg.
    strip_truncations; destruct hg as [g pq].
    exact (tr (class_of _ g; ap (class_of _) pq)).
  Defined.

  (** Exactness of the contravariant sequence at [Ext (middle xi) A]: the kernel
      of [pullback (inclusion xi)] is the image of [pullback (projection xi)]. *)
  Definition abses_ext_pullback_inclusion_exact_one {A B' B'' : AbGroup@{u}}
    (xi : AbSES B'' B') (v : abses_ext 1 xi A)
    : abses_ext_pullback 1 (inclusion xi) v = abses_ext_zero 1 B' A
      -> merely { v'' : abses_ext 1 B'' A
                  & abses_ext_pullback 1 (projection xi) v'' = v }.
  Proof.
    revert v; srapply Quotient_ind_hprop; intros V h.
    pose proof ((equiv_path_Tr _ _)^-1
                  (ap (equiv_quotient_paths_tr (AbSES B' A)) h)) as hm.
    strip_truncations.
    pose (p := equiv_path_abses_iso^-1 hm).
    refine (tr (class_of _ (abses_pullback_trivial_preimage xi V p); _)).
    exact (ap (class_of _) (abses_pullback_component1_id
              (abses_pullback_inclusion0_map' xi V p) (fun _ => idpath))^).
  Defined.

  (** Exactness of the covariant sequence at [Hom B A'']: the kernel of the
      connecting map is the image of postcomposition with [projection xi]. *)
  Definition abses_ext_dsplice_projection_exact_zero {A A'' : AbGroup@{u}}
    (xi : AbSES A'' A) {B : AbGroup@{u}} (w : abses_ext 0 B A'')
    : abses_ext_dsplice 0 xi w = abses_ext_zero 1 B A
      -> merely { w' : abses_ext 0 B xi
                  & abses_ext_pushout 0 (projection xi) w' = w }.
  Proof.
    revert w; srapply Quotient_ind_hprop; intros W h.
    pose proof ((equiv_path_Tr _ _)^-1
                  (ap (equiv_quotient_paths_tr (AbSES B A)) h)) as hm.
    strip_truncations.
    destruct (abses_pullback_trivial_factors_projection W xi hm) as [phi pq].
    exact (tr (class_of _ phi; ap (class_of _) pq^)).
  Defined.

  (** Exactness of the covariant sequence at [Hom B (middle xi)]: the kernel of
      postcomposition with [projection xi] is the image of postcomposition with
      [inclusion xi]. *)
  Definition abses_ext_pushout_projection_exact_zero {A A'' : AbGroup@{u}}
    (xi : AbSES A'' A) {B : AbGroup@{u}} (f : abses_ext 0 B xi)
    : abses_ext_pushout 0 (projection xi) f = abses_ext_zero 0 B A''
      -> merely { f' : abses_ext 0 B A & abses_ext_pushout 0 (inclusion xi) f' = f }.
  Proof.
    revert f; srapply Quotient_ind_hprop; intros F h.
    pose proof ((equiv_path_Tr _ _)^-1
                  (ap (equiv_quotient_paths_tr (ab_hom B A'')) h)) as hm.
    strip_truncations.
    pose (k := grp_kernel_corec (f:=projection xi) F
                 (equiv_path_grouphomomorphism^-1 hm)).
    refine (tr (class_of _ (grp_homo_compose
                 (grp_iso_inverse (abses_kernel_iso (inclusion xi) (projection xi))) k); _)).
    apply (ap (class_of _)).
    apply equiv_path_grouphomomorphism; intro b.
    exact (abses_kernel_iso_inv_beta (inclusion xi) (projection xi) (k b)).
  Defined.

  (** Exactness of the contravariant sequence at [Hom (middle xi) A]: the kernel
      of precomposition with [inclusion xi] is the image of precomposition with
      [projection xi]. *)
  Definition abses_ext_pullback_inclusion_exact_zero {A B' B'' : AbGroup@{u}}
    (xi : AbSES B'' B') (g : abses_ext 0 xi A)
    : abses_ext_pullback 0 (inclusion xi) g = abses_ext_zero 0 B' A
      -> merely { f : abses_ext 0 B'' A & abses_ext_pullback 0 (projection xi) f = g }.
  Proof.
    revert g; srapply Quotient_ind_hprop; intros G h.
    pose proof ((equiv_path_Tr _ _)^-1
                  (ap (equiv_quotient_paths_tr (ab_hom B' A)) h)) as hm.
    strip_truncations.
    assert (hkill : forall n : middle xi, grp_image (inclusion xi) n -> G n = mon_unit).
    { intros n; srapply Trunc_rec; intros [b r].
      refine (ap G r^ @ _).
      exact (equiv_path_grouphomomorphism^-1 hm b). }
    pose (f := grp_homo_compose
                 (quotient_abgroup_rec (grp_image (inclusion xi)) A G hkill)
                 (grp_iso_inverse (abses_cokernel_iso (inclusion xi) (projection xi)))).
    refine (tr (class_of _ f; _)).
    apply (ap (class_of _)).
    apply equiv_path_grouphomomorphism; intro x.
    exact (ap (quotient_abgroup_rec (grp_image (inclusion xi)) A G hkill)
              (abses_cokernel_iso_inv_beta (inclusion xi) (projection xi) x)).
  Defined.

  (** Exactness of the contravariant sequence at [Hom B' A]: the kernel of the
      connecting map is the image of precomposition with [inclusion xi]. *)
  Definition abses_ext_splice_inclusion_exact_zero {A B' B'' : AbGroup@{u}}
    (xi : AbSES B'' B') (g : abses_ext 0 B' A)
    : abses_ext_splice 0 xi g = abses_ext_zero 1 B'' A
      -> merely { h : abses_ext 0 xi A & abses_ext_pullback 0 (inclusion xi) h = g }.
  Proof.
    revert g; srapply Quotient_ind_hprop; intros G h.
    pose proof ((equiv_path_Tr _ _)^-1
                  (ap (equiv_quotient_paths_tr (AbSES B'' A)) h)) as hm.
    strip_truncations.
    pose proof (abses_pushout_trivial_factors_inclusion G xi hm) as [phi hphi].
    exact (tr (class_of _ phi; ap (class_of _) hphi^)).
  Defined.

  (** The covariant sequence is exact at [Hom B A]: postcomposition with
      [inclusion xi] has trivial kernel. *)
  Definition abses_ext_pushout_inclusion_injective_zero {A A'' : AbGroup@{u}}
    (xi : AbSES A'' A) {B : AbGroup@{u}} (v : abses_ext 0 B A)
    : abses_ext_pushout 0 (inclusion xi) v = abses_ext_zero 0 B xi
      -> v = abses_ext_zero 0 B A.
  Proof.
    revert v; srapply Quotient_ind_hprop; intros F h.
    pose proof ((equiv_path_Tr _ _)^-1
                  (ap (equiv_quotient_paths_tr (ab_hom B xi)) h)) as hm.
    strip_truncations.
    apply (ap (class_of _)).
    apply equiv_path_grouphomomorphism; intro b.
    apply (isinj_embedding (inclusion xi) _).
    exact (equiv_path_grouphomomorphism^-1 hm b @ (grp_homo_unit (inclusion xi))^).
  Defined.

  (** The contravariant sequence is exact at [Hom B'' A]: precomposition with
      [projection xi] has trivial kernel. *)
  Definition abses_ext_pullback_projection_injective_zero {A B' B'' : AbGroup@{u}}
    (xi : AbSES B'' B') (v : abses_ext 0 B'' A)
    : abses_ext_pullback 0 (projection xi) v = abses_ext_zero 0 xi A
      -> v = abses_ext_zero 0 B'' A.
  Proof.
    revert v; srapply Quotient_ind_hprop; intros F h.
    pose proof ((equiv_path_Tr _ _)^-1
                  (ap (equiv_quotient_paths_tr (ab_hom xi A)) h)) as hm.
    strip_truncations.
    apply (ap (class_of _)).
    apply equiv_path_grouphomomorphism; intro b.
    assert (fm : merely (hfiber (projection xi) b))
      by apply center, issurjection_projection.
    strip_truncations; destruct fm as [m qm].
    exact ((ap F qm)^ @ equiv_path_grouphomomorphism^-1 hm m).
  Defined.

  (** The Yoneda product is additive in the first variable: it carries the Baer
      sum to the Baer sum of the products. *)
  Definition abses_ext_yoneda_baer_sum_l {A C : AbGroup@{u}} (m : nat)
    {B : AbGroup@{u}} (t t' : grp_ext B C) (x : abses_ext m C A)
    : abses_ext_yoneda m (sg_op t t') x
      = abses_ext_baer_sum m.+1 (abses_ext_yoneda m t x) (abses_ext_yoneda m t' x).
  Proof.
    revert t t'; srapply Trunc_ind; intro s; srapply Trunc_ind; intro s'.
    exact (abses_ext_splice_baer_sum_ses m s s' x).
  Defined.

  (** Splicing is surjective onto [Ext^{m+2}]: every length-[m.+2] extension is
      a splice of a short exact sequence onto a length-[m.+1] extension. *)
  Definition abses_ext_splice_surjective (m : nat) {A B : AbGroup@{u}}
    (w : abses_ext m.+2 B A)
    : merely { C : AbGroup@{u} & { s : AbSES B C
              & { t : abses_ext m.+1 C A & w = abses_ext_splice m.+1 s t } } }.
  Proof.
    revert w; srapply Quotient_ind_hprop; intros [C [t s]].
    exact (tr (C; (s; (class_of _ t; idpath)))).
  Defined.

  (** Higher Ext of a projective vanishes: [Ext^{n+1}(P, A)] is trivial for
      every [A] when [P] is projective. *)
  Definition abses_ext_projective_vanish {P : AbGroup@{u}} `{IsAbProjective P}
    (n : nat) {A : AbGroup@{u}} (x : abses_ext n.+1 P A)
    : x = abses_ext_zero n.+1 P A.
  Proof.
    destruct n as [|n].
    - pose proof (contr_equiv' (Ext P A)
                    (equiv_inverse (equiv_abses_ext_one P A))) as cc.
      exact (path_contr x (abses_ext_zero 1 P A)).
    - pose proof (abses_ext_splice_surjective n x) as hsurj.
      strip_truncations.
      destruct hsurj as [C [s [t p]]].
      refine (p @ (abses_ext_yoneda_tr n.+1 s t)^ @ _).
      refine (ap (fun u => abses_ext_yoneda n.+1 u t)
                (path_contr (tr s) (tr (point (AbSES P C)))) @ _).
      refine (abses_ext_yoneda_tr n.+1 (point (AbSES P C)) t @ _).
      exact (abses_ext_splice_point n.+1 t).
  Defined.

  (** Splicing with a projective-middle short exact sequence is surjective onto
      [Ext^{n+1}(B, A)]. *)
  Definition abses_ext_splice_projective_surjective {K B : AbGroup@{u}}
    (zeta : AbSES B K) `{IsAbProjective (middle zeta)} {A : AbGroup@{u}}
    (n : nat) (w : abses_ext n.+1 B A)
    : merely { x : abses_ext n K A & abses_ext_splice n zeta x = w }.
  Proof.
    destruct n as [|n].
    - refine (abses_ext_pullback_projection_exact_one zeta w _).
      pose proof (contr_equiv' (Ext (middle zeta) A)
                    (equiv_inverse (equiv_abses_ext_one (middle zeta) A))) as cc.
      exact (path_contr _ _).
    - pose proof (abses_ext_splice_surjective n w) as hsurj.
      strip_truncations; destruct hsurj as [C [s [t p]]].
      pose proof (contr_equiv' (Ext (middle zeta) C)
                    (equiv_inverse (equiv_abses_ext_one (middle zeta) C))) as cc.
      pose proof (abses_ext_pullback_projection_exact_one zeta (class_of _ s)
                    (path_contr _ _)) as hg.
      revert hg; apply Trunc_rec; intros [g pg]; revert g pg.
      srapply Quotient_ind_hprop; intros g0 pg.
      pose proof ((equiv_path_Tr _ _)^-1
                    (ap (equiv_quotient_paths_tr (AbSES B C)) pg)) as hs.
      strip_truncations.
      refine (tr (abses_ext_pullback (S n) g0 t; _)).
      refine (abses_ext_splice_pullback_junction (S n) g0 zeta t @ _).
      exact (ap (fun S0 => abses_ext_splice (S n) S0 t) hs @ p^).
  Defined.

  (** For a projective-middle [zeta], [Ext^1(B, A)] is the cokernel of
      precomposition with [inclusion zeta]. *)
  Definition ext_one_projective_presentation {K B : AbGroup@{u}}
    (zeta : AbSES B K) `{IsAbProjective (middle zeta)} {A : AbGroup@{u}}
    : GroupIsomorphism
        (ab_cokernel (grp_homo_abses_ext_pullback 0 (A:=A) (inclusion zeta)))
        (ab_abses_ext 1 B A).
  Proof.
    snapply (abses_cokernel_iso (grp_homo_abses_ext_pullback 0 (A:=A) (inclusion zeta))
               (grp_homo_abses_ext_splice 0 zeta)).
    - intro b; rapply contr_inhabited_hprop.
      exact (abses_ext_splice_projective_surjective zeta 0 b).
    - snapply Build_IsExact.
      + srapply phomotopy_homotopy_hset; intro f.
        exact (abses_ext_inclusion_splice_iscomplex 0 zeta f).
      + intros [g0 hg0].
        rapply contr_inhabited_hprop.
        pose proof (abses_ext_splice_inclusion_exact_zero zeta g0 hg0) as hpre.
        strip_truncations; destruct hpre as [h ph].
        refine (tr (h; _)).
        apply path_sigma_hprop; exact ph.
  Defined.

  (** [Ext^{n+2}(B, A)] vanishes when [zeta : AbSES B K] has projective middle
      and projective kernel. *)
  Definition abses_ext_vanish_short_resolution {K B : AbGroup@{u}}
    (zeta : AbSES B K) `{IsAbProjective (middle zeta)} `{IsAbProjective K}
    {A : AbGroup@{u}} (n : nat) (x : abses_ext n.+2 B A)
    : x = abses_ext_zero n.+2 B A.
  Proof.
    pose proof (abses_ext_splice_projective_surjective zeta n.+1 x) as hsurj.
    strip_truncations; destruct hsurj as [y py].
    refine (py^ @ ap (abses_ext_splice n.+1 zeta) (abses_ext_projective_vanish n y) @ _).
    exact (grp_homo_unit (grp_homo_abses_ext_splice n.+1 zeta)).
  Defined.

  (** The higher Ext groups [Ext^{m+2}(Z/n, A)] of a cyclic group vanish. *)
  Definition abses_ext_cyclic_higher_vanish (n : nat)
    `{IsEmbedding (Z1_mul_nat n)} {A : AbGroup@{u}} (m : nat)
    (x : abses_ext m.+2 (ab_cokernel_embedding (Z1_mul_nat n)) A)
    : x = abses_ext_zero m.+2 (ab_cokernel_embedding (Z1_mul_nat n)) A
    := abses_ext_vanish_short_resolution (abses_from_inclusion (Z1_mul_nat n)) m x.

  (** Pulling back along a sum of homomorphisms is the Baer sum of the
      pullbacks, so [Ext^n(-, A)] is additive in the homomorphism. *)
  Definition abses_ext_pullback_plus (n : nat) {A B B' : AbGroup@{u}}
    (f g : B' $-> B) (x : abses_ext n B A)
    : abses_ext_pullback n (sg_op f g) x
      = abses_ext_baer_sum n (abses_ext_pullback n f x) (abses_ext_pullback n g x).
  Proof.
    destruct n as [|[|n]]; revert x; srapply Quotient_ind_hprop.
    - intro phi.
      apply (ap (class_of _)).
      apply equiv_path_grouphomomorphism; intro b.
      exact (grp_homo_op phi (f b) (g b)).
    - intro E.
      exact (ap (class_of _) (baer_sum_distributive_pullbacks f g)).
    - intros [C [t s]].
      refine (abses_ext_splice_pullback n.+1 s (sg_op f g) (class_of _ t) @ _).
      refine (ap (fun S0 => abses_ext_splice n.+1 S0 (class_of _ t))
                (baer_sum_distributive_pullbacks f g) @ _).
      refine (abses_ext_splice_baer_sum_ses n.+1 (abses_pullback f s)
                (abses_pullback g s) (class_of _ t) @ _).
      exact (ap011 (abses_ext_baer_sum n.+2)
               (abses_ext_splice_pullback n.+1 s f (class_of _ t))^
               (abses_ext_splice_pullback n.+1 s g (class_of _ t))^).
  Defined.

End HigherExt.

(** ** Universality of the higher Ext delta-functor *)

(** A coefficient [G] and a target contravariant additive family [T] with
    connecting maps [Tdelta], natural in the short exact sequence. *)

Section ExtUniversal.
  Context `{Univalence} (G : AbGroup@{u}).
  Context (T : nat -> AbGroup@{u} -> AbGroup@{u})
          (Tmap : forall (n : nat) {B B' : AbGroup@{u}},
              (B' $-> B) -> (T n B $-> T n B'))
          (Tmap_id : forall (n : nat) (B : AbGroup@{u}) (x : T n B),
              Tmap n grp_homo_id x = x)
          (Tmap_comp : forall (n : nat) {B B' B'' : AbGroup@{u}}
              (f : B' $-> B) (g : B'' $-> B') (x : T n B),
              Tmap n (f $o g) x = Tmap n g (Tmap n f x))
          (Tdelta : forall (n : nat) {A B : AbGroup@{u}},
              AbSES B A -> (T n A $-> T (S n) B))
          (Tdelta_nat : forall (n : nat) {A B A' B' : AbGroup@{u}}
              (E : AbSES B A) (E' : AbSES B' A') (phi : AbSESMorphism E E')
              (x : T n A'),
              Tdelta n E (Tmap n (component1 phi) x)
              = Tmap (S n) (component3 phi) (Tdelta n E' x)).

  Arguments Tmap n {B B'} _.
  Arguments Tmap_id n {B} _.
  Arguments Tmap_comp n {B B' B''} _ _ _.
  Arguments Tdelta n {A B} _.
  Arguments Tdelta_nat n {A B A' B'} _ _ _ _.

  Local Open Scope nat_scope.

  (** The comparison map on representatives, by recursion on the length. *)
  Definition d_rep : forall (n : nat) {B : AbGroup@{u}},
      abses_es n B G -> (T 0 G $-> T n B).
  Proof.
    induction n as [|n IHn]; intros B w.
    - exact (Tmap 0 (w : B $-> G)).
    - destruct n as [|n].
      + exact (Tdelta 0 (w : AbSES B G)).
      + exact (grp_homo_compose (Tdelta (S n) (snd w.2)) (IHn w.1 (fst w.2))).
  Defined.

  (** The connecting map commutes with pullback in the base. *)
  Definition Tdelta_pullback (n : nat) {A B B' : AbGroup@{u}} (beta : B' $-> B)
    (E : AbSES B A)
    : Tdelta n (abses_pullback beta E)
      = grp_homo_compose (Tmap (S n) beta) (Tdelta n E).
  Proof.
    apply equiv_path_grouphomomorphism; intro x.
    exact ((ap (Tdelta n (abses_pullback beta E)) (Tmap_id n x))^
           @ Tdelta_nat n (abses_pullback beta E) E (abses_pullback_morphism E beta) x).
  Defined.

  (** The comparison map is natural in the base. *)
  Definition d_rep_natural (n : nat) {B B' : AbGroup@{u}} (beta : B' $-> B)
    (w : abses_es n B G)
    : d_rep n (abses_es_pullback n beta w)
      = grp_homo_compose (Tmap n beta) (d_rep n w).
  Proof.
    destruct n as [|[|n]].
    - apply equiv_path_grouphomomorphism; intro x.
      exact (Tmap_comp 0 (w : B $-> G) beta x).
    - exact (Tdelta_pullback 0 beta (w : AbSES B G)).
    - destruct w as [C [F E]].
      refine (ap (fun d => grp_homo_compose d (d_rep (S n) F))
                (Tdelta_pullback (S n) beta E) @ _).
      apply equiv_path_grouphomomorphism; intro x; reflexivity.
  Defined.

  (** The connecting map commutes with pushout in the coefficient. *)
  Definition Tdelta_pushout (n : nat) {A A' B : AbGroup@{u}} (alpha : A $-> A')
    (E : AbSES B A)
    : Tdelta n (abses_pushout alpha E)
      = grp_homo_compose (Tdelta n E) (Tmap n alpha).
  Proof.
    apply equiv_path_grouphomomorphism; intro x.
    exact ((Tdelta_nat n E (abses_pushout alpha E) (abses_pushout_morphism E alpha) x
            @ Tmap_id (S n) (Tdelta n (abses_pushout alpha E) x))^).
  Defined.

  (** The comparison map respects the relation, hence descends to [Ext]. *)
  Definition d_rep_rel (n : nat) {B : AbGroup@{u}} (w w' : abses_es n B G)
    (r : abses_es_rel n w w')
    : d_rep n w = d_rep n w'.
  Proof.
    revert B w w' r; induction n as [|[|n] IHn]; intros B w w' r.
    - exact (ap (d_rep 0) r).
    - exact (ap (d_rep 1) r).
    - destruct w as [C [F E]], w' as [C' [F' E']], r as [beta [rF rE]].
      apply equiv_path_grouphomomorphism; intro x.
      refine (ap (fun y => Tdelta (S n) E y)
                (equiv_path_grouphomomorphism^-1
                   (IHn C F (abses_es_pullback (S n) beta F') rF) x
                 @ equiv_path_grouphomomorphism^-1 (d_rep_natural (S n) beta F') x) @ _).
      refine (_ @ ap (fun E0 => Tdelta (S n) E0 (d_rep (S n) F' x)) rE).
      exact (equiv_path_grouphomomorphism^-1
               (Tdelta_pushout (S n) beta E) (d_rep (S n) F' x))^.
  Defined.

  (** The comparison map descends to a map out of [Ext]. *)
  Definition d_ext (n : nat) {B : AbGroup@{u}}
    : abses_ext n B G -> (T 0 G $-> T n B)
    := Quotient_rec (abses_es_rel n) (T 0 G $-> T n B) (@d_rep n B) (@d_rep_rel n B).

  (** It is natural in the base and carries the splice to the connecting map. *)
  Definition d_ext_natural (n : nat) {B B' : AbGroup@{u}} (beta : B' $-> B)
    (x : abses_ext n B G)
    : d_ext n (abses_ext_pullback n beta x)
      = grp_homo_compose (Tmap n beta) (d_ext n x).
  Proof.
    revert x; srapply Quotient_ind_hprop; intro w.
    exact (d_rep_natural n beta w).
  Defined.

  Definition d_ext_splice (n : nat) {B C : AbGroup@{u}} (E : AbSES B C)
    (x : abses_ext n C G)
    : d_ext (S n) (abses_ext_splice n E x)
      = grp_homo_compose (Tdelta n E) (d_ext n x).
  Proof.
    revert x; srapply Quotient_ind_hprop; intro w.
    destruct n as [|n].
    - exact (Tdelta_pushout 0 (w : C $-> G) E).
    - reflexivity.
  Defined.

  (** The induced map of delta-functors out of [Ext^* (- , G)] extending a
      degree-zero element [eta : T 0 G]. *)
  Definition d_morph (n : nat) {B : AbGroup@{u}} (eta : T 0 G)
    (x : abses_ext n B G) : T n B
    := d_ext n x eta.

  Definition d_morph_natural (n : nat) {B B' : AbGroup@{u}} (beta : B' $-> B)
    (eta : T 0 G) (x : abses_ext n B G)
    : d_morph n eta (abses_ext_pullback n beta x) = Tmap n beta (d_morph n eta x)
    := equiv_path_grouphomomorphism^-1 (d_ext_natural n beta x) eta.

  Definition d_morph_splice (n : nat) {B C : AbGroup@{u}} (E : AbSES B C)
    (eta : T 0 G) (x : abses_ext n C G)
    : d_morph (S n) eta (abses_ext_splice n E x) = Tdelta n E (d_morph n eta x)
    := equiv_path_grouphomomorphism^-1 (d_ext_splice n E x) eta.

  (** A family agreeing with the connecting maps and the degree-zero values
      equals [d_morph]. *)
  Definition d_morph_unique (eta : T 0 G)
    (v : forall (n : nat) (B : AbGroup@{u}), abses_ext n B G -> T n B)
    (v_zero : forall (B : AbGroup@{u}) (phi : ab_hom B G),
        v 0 B (class_of _ phi) = Tmap 0 phi eta)
    (v_splice : forall (n : nat) (B C : AbGroup@{u}) (E : AbSES B C)
        (x : abses_ext n C G),
        v (S n) B (abses_ext_splice n E x) = Tdelta n E (v n C x))
    : forall (n : nat) (B : AbGroup@{u}) (x : abses_ext n B G),
        v n B x = d_morph n eta x.
  Proof.
    intro n; induction n as [|[|n] IHn]; intros B x.
    - revert x; srapply Quotient_ind_hprop; intro phi.
      exact (v_zero B phi).
    - revert x; srapply Quotient_ind_hprop; intro E.
      refine (ap (v 1%nat B) (ap (class_of _) (abses_pushout_id E))^ @ _).
      refine (v_splice 0 B G E (class_of _ grp_homo_id) @ _).
      refine (ap (fun y => Tdelta 0 E y) (v_zero G grp_homo_id) @ _).
      exact (ap (fun y => Tdelta 0 E y) (Tmap_id 0 eta)).
    - revert x; srapply Quotient_ind_hprop; intros [C [F E]].
      refine (v_splice (S n) B C E (class_of _ F) @ _).
      exact (ap (fun y => Tdelta (S n) E y) (IHn C (class_of _ F))).
  Defined.

  (** A map of delta-functors from [Ext^* (- , G)] to [T]. *)
  Definition ExtDeltaMor : Type
    := { v : forall (n : nat) (B : AbGroup@{u}), abses_ext n B G -> T n B
       & (forall (n : nat) (B B' : AbGroup@{u}) (beta : B' $-> B)
              (x : abses_ext n B G),
            v n B' (abses_ext_pullback n beta x) = Tmap n beta (v n B x))
         * (forall (n : nat) (B C : AbGroup@{u}) (E : AbSES B C)
                (x : abses_ext n C G),
              v (S n) B (abses_ext_splice n E x) = Tdelta n E (v n C x)) }.

  (** Maps of delta-functors out of [Ext^* (- , G)] correspond to elements of
      [T 0 G]. *)
  Definition ext_universal_equiv : ExtDeltaMor <~> T 0 G.
  Proof.
    srapply equiv_adjointify.
    - exact (fun m => m.1 0%nat G (class_of _ grp_homo_id)).
    - intro eta.
      exists (fun n B => @d_morph n B eta).
      exact ((fun n B B' beta x => @d_morph_natural n B B' beta eta x),
             (fun n B C E x => @d_morph_splice n B C E eta x)).
    - intro eta; exact (Tmap_id 0 eta).
    - intro m.
      srapply path_sigma_hprop.
      apply path_forall; intro n; apply path_forall; intro B; apply path_forall; intro x.
      symmetry; srapply d_morph_unique.
      + intros B0 phi.
        transitivity (m.1 0%nat B0 (abses_ext_pullback 0 phi (class_of _ grp_homo_id))).
        * apply (ap (m.1 0%nat B0)); symmetry.
          apply (ap (class_of _)).
          apply equiv_path_grouphomomorphism; intro b; reflexivity.
        * exact (fst m.2 0%nat G B0 phi (class_of _ grp_homo_id)).
      + exact (snd m.2).
  Defined.

End ExtUniversal.
