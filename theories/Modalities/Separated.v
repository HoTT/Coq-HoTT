(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics HoTT.Types HoTT.Cubical.DPath.
Require Import HFiber Extensions Factorization.
Require Import ReflectiveSubuniverse Modality Accessible Localization Descent.
Require Import Truncations.Core.
Require Import Homotopy.Suspension.

Local Open Scope path_scope.
Local Open Scope subuniverse_scope.

(** * Subuniverses of separated types *)

(** The basic reference for subuniverses of separated types is
  - Christensen, Opie, Rijke, and Scoccola, "Localization in Homotopy Type Theory", https://arxiv.org/abs/1807.04155.
hereinafter referred to as "CORS".  *)

(** ** Definition *)

(** The definition is in [ReflectiveSubuniverse.v]. *)

(** ** Basic properties *)

(** Lemma 2.15 of CORS: If [O] is accessible, so is [Sep O].  Its generators are the suspension of those of [O], in the following sense: *)
Definition susp_localgen (f : LocalGenerators@{a}) : LocalGenerators@{a}.
Proof.
  econstructor; intros i.
  exact (functor_susp (f i)).
Defined.

Global Instance isaccrsu_sep (O : Subuniverse) `{IsAccRSU O}
  : IsAccRSU (Sep O).
Proof.
  exists (susp_localgen (acc_lgen O)).
  intros A; split; intros A_inO.
  { intros i.
    apply (ooextendable_iff_functor_susp (acc_lgen O i)).  
    intros [x y]. cbn in *.
    refine (ooextendable_postcompose' _ _ _ _ _).
    2:apply inO_iff_islocal; exact (A_inO x y).
    intros b.
    apply dp_const. }
  { intros x y.
    apply (inO_iff_islocal O); intros i.
    specialize (A_inO i).
    refine (ooextendable_postcompose' _ _ _ _ _).
    2:exact (fst (ooextendable_iff_functor_susp (acc_lgen O i) _) A_inO (x,y)).
    intros b.
    symmetry; apply dp_const. }
Defined.

Definition susp_nullgen (S : NullGenerators@{a}) : NullGenerators@{a}.
Proof.
  econstructor; intros i.
  exact (Susp (S i)).
Defined.

Global Instance isaccmodality_sep (O : Subuniverse) `{IsAccModality O}
  : IsAccModality (Sep O).
Proof.
  exists (susp_nullgen (acc_ngen O)).
  intros A; split; intros A_inO.
  { intros i.
    apply (ooextendable_compose _ (functor_susp (fun _:acc_ngen O i => tt)) (fun _:Susp Unit => tt)).
    1:apply ooextendable_equiv, isequiv_contr_contr.
    apply (ooextendable_iff_functor_susp (fun _:acc_ngen O i => tt)).  
    intros [x y].
    refine (ooextendable_postcompose' _ _ _ _ _).
    2:apply inO_iff_isnull; exact (A_inO x y).
    intros b.
    apply dp_const. }
  { intros x y.
    apply (inO_iff_isnull O); intros i.
    specialize (A_inO i).
    assert (ee : ooExtendableAlong (functor_susp (fun _:acc_ngen O i => tt)) (fun _ => A)).
    { refine (cancelL_ooextendable _ _ (fun _ => tt) _ A_inO).
      apply ooextendable_equiv.
      apply isequiv_contr_contr. }
    assert (e := fst (ooextendable_iff_functor_susp (fun _:acc_ngen O i => tt) _) ee (x,y)).
    cbn in e.
    refine (ooextendable_postcompose' _ _ _ _ e).
    intros b.
    symmetry; apply dp_const. }
Defined.

(** Remark 2.16(1) of CORS *)
Global Instance O_leq_SepO (O : ReflectiveSubuniverse)
  : O <= Sep O.
Proof.
  intros A ? x y; exact _.
Defined.

(** Part of Remark 2.16(2) of CORS *)
Definition in_SepO_embedding (O : Subuniverse)
           {A B : Type} (i : A -> B) `{IsEmbedding i} `{In (Sep O) B}
  : In (Sep O) A.
Proof.
  intros x y.
  refine (inO_equiv_inO' _ (equiv_ap_isembedding i x y)^-1).
Defined.

(* As a special case, if X embeds into an n-type for n >= -1 then X is an n-type. Note that this doesn't hold for n = -2. *)
Corollary istrunc_embedding_trunc `{Funext} {X Y : Type} {n : trunc_index} `{IsTrunc n.+1 Y}
      (i : X -> Y) `{IsEmbedding i} : IsTrunc n.+1 X.
Proof.
  exact (@in_SepO_embedding (Tr n) _ _ i IsEmbedding0 H0).
Defined.

Global Instance in_SepO_hprop (O : ReflectiveSubuniverse)
       {A : Type} `{IsHProp A}
  : In (Sep O) A.
Proof.
  srapply (in_SepO_embedding O (const tt)).
  intros x y; exact _.
Defined.


(** Remark 2.16(4) of CORS *)
Definition sigma_closed_SepO (O : Modality) {A : Type} (B : A -> Type)
           `{A_inO : In (Sep O) A} `{B_inO : forall a, In (Sep O) (B a)}
  : In (Sep O) (sig B).
Proof.
  intros [x u] [y v].
  specialize (A_inO x y).
  pose proof (fun p:x=y => B_inO y (p # u) v).
  pose @inO_sigma.  (* Speed up typeclass search. *)
  refine (inO_equiv_inO' _ (equiv_path_sigma B _ _)).
Defined.

(** Lemma 2.17 of CORS *)
Global Instance issurjective_to_SepO (O : ReflectiveSubuniverse) (X : Type)
           `{Reflects (Sep O) X}
  : IsSurjection (to (Sep O) X).
Proof.
  pose (im := himage (to (Sep O) X)).
  pose proof (in_SepO_embedding O (factor2 im)).
  pose (s := O_rec (factor1 im)).
  assert (h : factor2 im o s == idmap).
  - apply O_indpaths; intros x; subst s.
    rewrite O_rec_beta.
    apply fact_factors.
  - apply BuildIsSurjection.
    intros z.
    specialize (h z); cbn in h.
    set (w := s z) in *.
    destruct w as [w1 w2].
    destruct h.
    exact w2.
Defined.

(** Proposition 2.18 of CORS. *)
Definition almost_inSepO_typeO@{i j} `{Univalence}
           (O : ReflectiveSubuniverse) (A B : Type_@{i j} O)
  : { Z : Type@{i} & In O Z * (Z <~> (A = B)) }.
Proof.
  exists (A <~> B); split.
  - exact _.
  - refine (equiv_path_TypeO O A B oE _).
    apply equiv_path_universe.
Defined.

(** Lemma 2.21 of CORS *)
Global Instance inSepO_sigma (O : ReflectiveSubuniverse)
       {X : Type} {P : X -> Type} `{In (Sep O) X} `{forall x, In O (P x)}
  : In (Sep O) (sig P).
Proof.
  intros u v.
  refine (inO_equiv_inO' _ (equiv_path_sigma P _ _)).
Defined.

(** Proposition 2.22 of CORS (in funext-free form). *)
Global Instance reflectsD_SepO (O : ReflectiveSubuniverse)
       {X : Type} `{Reflects (Sep O) X}
  : ReflectsD (Sep O) O X.
Proof.
  srapply reflectsD_from_inO_sigma.
Defined.

(** Once we know that [Sep O] is a reflective subuniverse, this will mean that [O << Sep O]. *)

(** And now the version with funext. *)
Definition isequiv_toSepO_inO `{Funext} (O : ReflectiveSubuniverse)
           {X : Type} `{Reflects (Sep O) X}
           (P : O_reflector (Sep O) X -> Type) `{forall x, In O (P x)}
  : IsEquiv (fun g : (forall y, P y) => g o to (Sep O) X)
  := isequiv_ooextendable _ _ (extendable_to_OO P).

Definition equiv_toSepO_inO `{Funext} (O : ReflectiveSubuniverse)
           {X : Type} `{Reflects (Sep O) X}
           (P : O_reflector (Sep O) X -> Type) `{forall x, In O (P x)}
  : (forall y, P y) <~> (forall x, P (to (Sep O) X x))
  := Build_Equiv _ _ _ (isequiv_toSepO_inO O P).

(** TODO: Actually prove this, and put it somewhere more appropriate. *)
Section JoinConstruction.
  Universes i j.
  Context {X : Type@{i}} {Y : Type@{j}} (f : X -> Y)
          (ls : forall (y1 y2 : Y),
              @sig@{j j} Type@{i} (fun (Z : Type@{i}) => Equiv@{i j} Z (y1 = y2))).
  Definition jc_image@{} : Type@{i}. Admitted.
  Definition jc_factor1@{} : X -> jc_image. Admitted.
  Definition jc_factor2@{} : jc_image -> Y. Admitted.
  Definition jc_factors@{} : jc_factor2 o jc_factor1 == f. Admitted.
  Global Instance jc_factor1_issurj@{} : IsSurjection jc_factor1. Admitted.
  Global Instance jc_factor2_isemb : IsEmbedding jc_factor2. Admitted.
End JoinConstruction.

(** We'd like to say that the universe of [O]-modal types is [O]-separated, i.e. belongs to [Sep O].  But since a given subuniverse like [Sep O] lives only on a single universe size, trying to say that in the naive way yields a universe inconsistency. *)
Fail Instance: forall (O : ReflectiveSubuniverse), In (Sep O) (Type_ O).

(** Instead, we do as in Lemma 2.19 of CORS and prove the morally-equivalent "descent" property, using Lemma 2.18 and the join construction. *)
Global Instance SepO_lex_leq `{Univalence}
       (O : ReflectiveSubuniverse) {X : Type} `{Reflects (Sep O) X}
  : Descends (Sep O) O X.
Proof.
  assert (e : forall (P : X -> Type_ O),
             { Q : (O_reflector (Sep O) X -> Type_ O) &
                   forall x, Q (to (Sep O) X x) <~> P x }).
  2:{ unshelve econstructor; intros P' P_inO;
      pose (P := fun x => (P' x; P_inO x) : Type_ O);
      pose (ee := e P).
      - exact ee.1.
      - exact _.
      - intros x; cbn; apply ee.2. }
  intros P.
  assert (ls : forall A B : Type_ O, { Z : Type & Z <~> (A = B) }).
  { intros A B.
    pose (q := almost_inSepO_typeO O A B).
    exact (q.1; snd q.2). }
  pose (p := jc_factor2 P ls).
  set (J := jc_image P ls) in p.
  assert (In (Sep O) J).
  { intros x y.
    pose (q := almost_inSepO_typeO O (p x) (p y)).
    refine (inO_equiv_inO' q.1 _).
    refine (_ oE _).
    - symmetry; srapply (equiv_ap_isembedding p).
    - exact (snd q.2). }
  pose (O_rec (O := Sep O) (jc_factor1 P ls)).
  exists (p o j).
  intros x; subst p j.
  rewrite O_rec_beta.
  apply equiv_path.
  exact ((jc_factors P ls x)..1).
Defined.

(** Once we know that [Sep O] is a reflective subuniverse, this will imply [O <<< Sep O], and that if [Sep O] is accessible (such as if [O] is) then [Type_ O] belongs to its accessible lifting (see [inO_TypeO_lex_leq]. *)


(** ** Reflectiveness of [Sep O] *)

(** TODO *)


(** ** Left-exactness properties *)

(** Nearly all of these are true in the generality of a pair of reflective subuniverses with [O <<< O'] and/or [O' <= Sep O], and as such can be found in [Descent.v]. *)
