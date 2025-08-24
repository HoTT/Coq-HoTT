(** * Properties of compact and searchable types *)

Require Import Basics Types.
Require Import Truncations.Core Truncations.Connectedness.
Require Import Spaces.Nat.Core.
Require Import Misc.UStructures.
Require Import Spaces.NatSeq.Core Spaces.NatSeq.UStructure.
Require Import Homotopy.Suspension.
Require Import Pointed.Core.
Require Import Universes.TruncType.
Require Import Idempotents.

Local Open Scope nat_scope.
Local Open Scope pointed_scope.

(** ** Basic definitions of compact types *)

(** A type [A] is compact if for every decidable predicate [P] on [A] we can either find an element of [A] making [P] false or we can show that [P a] always holds. *)
Definition IsCompact (A : Type)
  := forall P : A -> Type, (forall a : A, Decidable (P a)) ->
                              {a : A & ~ P a} + (forall a : A, P a).

(** Any compact type is decidable. *)
Definition decidable_iscompact {A : Type} (c : IsCompact A) : Decidable A.
Proof.
  destruct (c (fun (_ : A) => Empty) _) as [c1|c2].
  - exact (inl c1.1).
  - exact (inr c2).
Defined.

(** Compactness is equivalent to assuming the same for [HProp]-valued decidable predicates. *)
Definition IsCompactProps (A : Type)
  := forall P : A -> HProp, (forall a : A, Decidable (P a)) ->
                              {a : A & ~ P a} + (forall a : A, P a).

Definition iscompact_iscompactprops {A} (c : IsCompactProps A) : IsCompact A.
Proof.
  intros P dP.
  destruct (c (merely o P) _) as [l|r].
  - exact (inl (l.1; fun p => l.2 (tr p))).
  - right.
    intro a.
    apply merely_inhabited_iff_inhabited_stable, r.
Defined.

(** Since decidable types are stable, it's also equivalent to negate [P] in the definition. *)
Definition IsCompact' (A : Type)
  := forall P : A -> Type, (forall a : A, Decidable (P a)) ->
                              {a : A & P a} + (forall a : A, ~ P a).

Definition iff_iscompact_iscompact' (A : Type)
  : IsCompact A <-> IsCompact' A.
Proof.
  split;
    napply (functor_forall (fun P => not o P)); intro P;
    rapply functor_forall; intro dP;
    apply functor_sum.
  2,3: exact idmap.
  1: apply (functor_sigma idmap).
  2: apply (functor_forall idmap).
  all: intro a; by apply stable_decidable.
Defined.

(** Another equivalent definition of compactness: If a family over the type is decidable, then the Σ-type is decidable. *)
Definition IsSigmaCompact (A : Type)
  := forall P : A -> Type, (forall a : A, Decidable (P a)) -> Decidable (sig P).

Definition equiv_iscompact'_issigmacompact {A : Type}
  : IsCompact' A <-> IsSigmaCompact A.
Proof.
  apply iff_functor_forall; intro P.
  apply iff_functor_forall; intro dP.
  apply iff_equiv.
  apply (equiv_functor_sum' equiv_idmap).
  napply equiv_sig_ind.
Defined.

(** Again, it is enough to consider [HProp]-valued families. *)
Definition IsSigmaCompactProps (A : Type)
  := forall P : A -> HProp,
      (forall a : A, Decidable (P a)) -> Decidable (sig P).

Definition issigmacompactprops_issigmacompact {A : Type}
  (h : IsSigmaCompact A)
  : IsSigmaCompactProps A
  := fun P hP => h P hP.

Definition issigmacompact_issigmacompactprops {A : Type}
  (h : IsSigmaCompactProps A)
  : IsSigmaCompact A.
Proof.
  intros P hP.
  refine (decidable_iff _ (h (merely o P) _)).
  apply iff_functor_sigma; intro a.
  exact merely_inhabited_iff_inhabited_stable.
Defined.

(** A weaker definition: for any decidable family, the dependent function type is decidable. *)
Definition IsPiCompact (A : Type)
  := forall (P : A -> Type) (dP : forall a : A, Decidable (P a)),
      Decidable (forall a : A, P a).

Definition ispicompact_issigmacompact {A : Type} (c : IsSigmaCompact A)
  : IsPiCompact A.
Proof.
  intros P dP.
  destruct (c (not o P) _) as [l|r].
  - right; exact (fun f => l.2 (f l.1)).
  - left.
    intro a.
    apply (stable_decidable (P a)).
    exact (fun u => r (a; u)).
Defined.

(** Compact types are closed under retracts. *)
Definition iscompact_retract {A : Type} (R : RetractOf A) (c : IsCompact A)
  : IsCompact (retract_type R).
Proof.
  intros P dP; destruct (c (P o (retract_retr R)) _) as [l|r].
  - exact (inl ((retract_retr R) l.1; l.2)).
  - exact (inr (fun a =>  ((retract_issect R) a) # r ((retract_sect R) a))).
Defined.

Definition iscompact_retract' {A R : Type} {f : A -> R} {g : R -> A}
  (s : f o g == idmap) (c : IsCompact A)
  : IsCompact R
  := iscompact_retract (Build_RetractOf A R f g s) c.

(** Assuming the set truncation map has a section, a type is compact if and only if its set truncation is compact. *)
Definition compact_set_trunc_compact `{Univalence} {A : Type}
  (f : (Tr 0 A) -> A) (s : tr o f == idmap)
  : IsCompact A <-> IsCompact (Tr 0 A).
Proof.
  constructor.
  1: exact (iscompact_retract' s).
  intro cpt; rapply iscompact_iscompactprops.
  intros P dP.
  destruct (cpt (Trunc_rec P)) as [l|r].
  - intro a; strip_truncations.
    exact (dP a).
  - exact (inl (f l.1; fun x => l.2 (ap (Trunc_rec P) (s l.1) # x))).
  - exact (inr (fun a => r (tr a))).
Defined.

(** ** Basic definitions of searchable types *)

(** A type is searchable if for every decidable predicate we can find a "universal witness" for whether the predicate is always true or not. *)
Definition IsSearchable (A : Type)
  := forall (P : A -> Type) (dP : forall a : A, Decidable (P a)),
      {x : A & P x -> forall a : A, P a}.

Definition IsSearchableProps (A : Type)
  := forall (P : A -> HProp) (dP : forall a : A, Decidable (P a)),
      {x : A & P x -> forall a : A, P a}.

Definition issearchable_issearchableprops {A : Type} (s : IsSearchableProps A)
  : IsSearchable A.
Proof.
  intros P dP.
  specialize (s (merely o P) _).
  exists s.1.
  intros h a.
  apply merely_inhabited_iff_inhabited_stable, s.2, tr, h.
Defined.

(** A type is searchable if and only if it is compact and inhabited. *)

Definition issearchable_iscompact_inhabited {A : Type}
  : IsCompact A -> A -> IsSearchable A.
Proof.
  intros c a P dP.
  induction (c P _) as [l|r].
  - exists l.1.
    intro h; contradiction (l.2 h).
  - exact (a; fun _ => r).
Defined.

Definition iscompact_issearchable {A : Type} : IsSearchable A -> IsCompact A.
Proof.
  intros h P dP.
  set (w := (h P dP).1).
  destruct (dP w) as [x|y].
  - exact (inr ((h P dP).2 x)).
  - exact (inl (w; y)).
Defined.

Definition inhabited_issearchable {A : Type} : IsSearchable A -> A
  := fun s => (s (fun a => Unit) _).1.

Definition searchable_iff {A : Type} : IsSearchable A <-> A * (IsCompact A)
  := (fun s => (inhabited_issearchable s, iscompact_issearchable s),
        fun c => issearchable_iscompact_inhabited (snd c) (fst c)).

(** ** Examples of searchable and compact types  *)

Definition issearchable_contr {A} (c : Contr A) : IsSearchable A.
Proof.
  intros P dP.
  exists (center A).
  intros p a.
  by induction (contr a).
Defined.

Definition issearchable_Bool : IsSearchable Bool.
Proof.
  intros P dP.
  induction (dP false) as [p | np]; [exists true | exists false].
  all: by intros p' [].
Defined.

(** The empty type is trivially compact. *)
Definition iscompact_empty : IsCompact Empty
  := fun P dP => inr (fun a => Empty_rec a).

Definition iscompact_empty' {A : Type} (na : ~A) : IsCompact A
  := fun p dP => inr (fun a => Empty_rec (na a)).

Definition iscompact_iff_not_or_issearchable {A : Type} :
  IsCompact A <-> (~ A) + IsSearchable A.
Proof.
  constructor.
  - intro c.
    destruct (decidable_iscompact c) as [l|r].
    + exact (inr (issearchable_iscompact_inhabited c l)).
    + exact (inl r).
  - intros [l|r].
    + exact (iscompact_empty' l).
    + exact (iscompact_issearchable r).
Defined.

(** Assuming univalence, the type of propositions is searchable. *)
Definition issearchable_hprop `{Univalence} : IsSearchable HProp.
Proof.
  apply issearchable_issearchableprops.
  intros P dP.
  destruct (dP Unit_hp) as [t|f].
  - exists False_hp; intros p a.
    rapply stable_decidable.
    by apply (not_not_constant_family_hprop P).
  - exact (Unit_hp; fun h => Empty_rec (f h)).
Defined.

(** Assuming univalence, if the domain of a surjective map is searchable, then so is its codomain. *)

Definition issearchableprops_image `{Univalence} (A B : Type)
  (s : IsSearchableProps A)
  (f : A -> B) (surj : IsSurjection f)
  : IsSearchableProps B.
Proof.
  intros P dP.
  specialize (s (P o f) _).
  exact (f s.1; fun t => conn_map_elim _ f _ (s.2 t)).
Defined.

Definition issearchable_image `{Univalence} (A B : Type)
  (s : IsSearchable A)
  (f : A -> B) (surj : IsSurjection f)
  : IsSearchable B
  := issearchable_issearchableprops (issearchableprops_image A B s f surj).

(** Assuming univalence, every connected pointed type is searchable. *)
Definition issearchable_isconnected_ptype `{Univalence} (A : pType)
  (c : IsConnected 0 A)
  : IsSearchable A
  := issearchable_image Unit A (issearchable_contr _) (fun _ => pt) _.

(** Assuming univalence, the suspension of any type is searchable. *)
Definition issearchable_suspension `{Univalence} (A : Type)
  : IsSearchable (Susp A).
Proof.
  snrefine (issearchable_image Bool (Susp A) issearchable_Bool _ _).
  - exact (Bool_rec _ North South).
  - snapply Susp_ind; cbn.
    1,2: rapply contr_inhabited_hprop; apply tr.
    1: exact (true; idpath).
    1: exact (false; idpath).
    intro x; by apply path_ishprop.
Defined.

Definition iscompact_image `{Univalence} (A B : Type)
  (c : IsCompact A)
  (f : A -> B) (surj : IsSurjection f)
  : IsCompact B.
Proof.
  apply iscompact_iff_not_or_issearchable.
  destruct ((fst iscompact_iff_not_or_issearchable) c) as [n|s].
  - left; by rapply conn_map_elim.
  - right; by rapply issearchable_image.
Defined.

Section Uniform_Search.

  (** ** Searchability of [nat -> A] *)

  (** Following https://www.cs.bham.ac.uk/~mhe/TypeTopology/TypeTopology.UniformSearch.html, we prove that if [A] is searchable then [nat -> A] is uniformly searchable. *)

  (** A type with a uniform structure is uniformly searchable if it is searchable over uniformly continuous predicates. Here the uniform structure on [Type] is the trivial one [trivial_us] involving the identity types at each level. *)
  Definition uniformly_searchable (A : Type) {usA : UStructure A}
    := forall (P : A -> Type) (dP : forall a : A, Decidable (P a)),
        uniformly_continuous P -> exists w0 : A, (P w0 -> forall u : A, P u).

  Context {A : Type} (issearchable_A : IsSearchable A).

  (** The witness function for uniformly continuous predicates on [nat -> A]. The first argument [n : nat] will be the modulus of uniform continuity, but we do not use the property in this definition. *)
  Definition uniformsearch_witness (n : nat) (P : (nat -> A) -> Type)
    (dP : forall (f : nat -> A), Decidable (P f))
    : nat -> A.
  Proof.
    induction n in P, dP.
    - exact (fun _ => inhabited_issearchable issearchable_A).
    - pose (g Q dQ := Q (IHn Q dQ)).
      pose (wA := (issearchable_A (fun x => g (P o (seq_cons x)) _) _).1).
      exact (seq_cons wA (IHn (P o (seq_cons wA)) _)).
  Defined.

  (** We often need to apply [P] to [uniformsearch_witness n P dP], and this saves repeating [P]. *)
  Local Definition pred_uniformsearch_witness (n : nat) (P : (nat -> A) -> Type)
    (dP : forall (f : nat -> A), Decidable (P f))
    := P (uniformsearch_witness n P dP).

  (** The desired property of the witness function. *)
  Definition uniformsearch_witness_spec {n : nat} (P : (nat -> A) -> Type)
    (dP : forall f : (nat -> A), Decidable (P f))
    (is_mod : is_modulus_of_uniform_continuity n P)
    (h : pred_uniformsearch_witness n P dP)
    : forall u : nat -> A, P u.
  Proof.
    induction n in P, dP, is_mod, h.
    - intro u.
      refine (transport idmap _ h).
      (* For [n = 0], [is_mod u1 u2] says that [P u1 = P u2]. *)
      apply is_mod, sequence_type_us_zero.
    - intro u.
      refine (transport idmap _ _).
      1: exact (uniformly_continuous_extensionality P (m:=0)
                  (uniformly_continuous_has_modulus is_mod)
                  (seq_cons_head_tail u)).
      rapply (IHn (P o (seq_cons (u 0)))).
      1: apply cons_decreases_modulus, is_mod.
      (* The universality of [uniformsearch_witness] says that it is enough to check this statement with [u 0] replaced with [wA] above, and that is exactly what [h] proves, by the inductive step. *)
      exact ((issearchable_A
                 (fun y => pred_uniformsearch_witness n (P o (seq_cons y)) _) _).2
                h (u 0)).
  Defined.

  Definition has_uniformly_searchable_seq_issearchable
    : uniformly_searchable (nat -> A).
  Proof.
    intros P dP contP.
    exists (uniformsearch_witness (contP 0).1 P dP).
    apply uniformsearch_witness_spec; exact (contP 0).2.
  Defined.

End Uniform_Search.
