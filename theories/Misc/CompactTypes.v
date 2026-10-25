(** * Properties of compact and searchable types *)

From HoTT Require Import Basics Types.
Require Import Truncations.Core Truncations.Connectedness.
Require Import Spaces.Nat.Core Finite.Fin.
Require Import Misc.UStructures.
Require Import Spaces.NatSeq.Core Spaces.NatSeq.UStructure.
Require Import Homotopy.Suspension.
Require Import Pointed.Core.
Require Import Universes.TruncType Universes.HProp.

Local Open Scope nat_scope.
Local Open Scope pointed_scope.

(** ** Basic definitions of compact types *)

(** A type [A] is compact if for every decidable family over [A], the Σ-type is decidable. *)
Definition IsSigmaCompact (A : Type)
  := forall P : A -> Type, (forall a : A, Decidable (P a)) -> Decidable (sig P).

(** It is enough to consider [HProp]-valued families. *)
Definition IsSigmaCompactProps (A : Type)
  := forall P : A -> HProp,
      (forall a : A, Decidable (P a)) -> Decidable (sig P).

Definition issigmacompactprops_issigmacompact {A : Type}
  (h : IsSigmaCompact A)
  : IsSigmaCompactProps A
  := h.

Definition issigmacompact_issigmacompactprops {A : Type}
  (h : IsSigmaCompactProps A)
  : IsSigmaCompact A.
Proof.
  intros P hP.
  refine (decidable_iff _ (h (merely o P) _)).
  apply iff_functor_sigma; intro a.
  exact merely_inhabited_iff_inhabited_stable.
Defined.

(** A weaker definition: a type is ∃-compact if for any decidable family, the propositional truncation of the Σ-type is decidable. *)
Definition IsHExistsCompact (A : Type)
  := forall P : A -> Type,
      (forall a : A, Decidable (P a)) -> Decidable (hexists P).

Definition ishprop_ishexistscompact `{Funext} (A : Type)
  : IsHProp (IsHExistsCompact A) := _.

Definition ishexistscompact_issigmacompact {A} (c : IsSigmaCompact A)
  : IsHExistsCompact A.
Proof.
  intros P dP.
  destruct (c P dP) as [l|r].
  - left; exact (tr l).
  - right; intros u; by strip_truncations.
Defined.

(** An even weaker definition: A type is Π-compact if for any decidable family, the dependent function type is decidable. *)
Definition IsPiCompact (A : Type)
  := forall (P : A -> Type) (dP : forall a : A, Decidable (P a)),
      Decidable (forall a : A, P a).

Definition IsPiCompactProps (A : Type)
  := forall P : A -> HProp,
      (forall a, Decidable (P a)) -> Decidable (forall a, P a).

Definition ishprop_ispicompactprops `{Funext} (A : Type)
  : IsHProp (IsPiCompactProps A) := _.

Definition ispicompactprops_ispicompact {A} (h : IsPiCompact A)
  : IsPiCompactProps A := h.

Definition ispicompact_ispicompactprops {A} (h : IsPiCompactProps A)
  : IsPiCompact A.
Proof.
  intros P dP.
  refine (decidable_iff _ (h (merely o P) _)); constructor.
  2: exact (fun f a => tr (f a)).
  intros f a.
  apply merely_inhabited_iff_inhabited_stable; exact (f a).
Defined.

Definition ispicompact_ishexistscompact {A} (c : IsHExistsCompact A)
  : IsPiCompact A.
Proof.
  intros P dP.
  destruct (c (not o P) _) as [l|r].
  - right; intro f; strip_truncations.
    exact (l.2 (f l.1)).
  - left; intro a.
    apply (stable_decidable (P a)).
    exact (fun u => r (tr (a; u))).
Defined.

Definition ispicompact_issigmacompact {A} (c : IsSigmaCompact A)
  : IsPiCompact A
  := (ispicompact_ishexistscompact (ishexistscompact_issigmacompact c)).

(** Compact types are closed under retracts. *)
Definition issigmacompact_retract {A R : Type} {f : A -> R} {g : R -> A}
  (s : f o g == idmap) (c : IsSigmaCompact A)
  : IsSigmaCompact R.
Proof.
  intros P dP; destruct (c (P o f) _) as [u|v].
  1: left; exact (f u.1; u.2).
  right; intros [r pr].
  apply v.
  exists (g r).
  exact ((s r)^ # pr).
Defined.

Definition issigmacompact_equiv {A B : Type} (f : A -> B) `{!IsEquiv f}
  (c : IsSigmaCompact B)
  : IsSigmaCompact A
  := issigmacompact_retract (eissect f) c.

(** Any compact type is decidable. *)
Definition decidable_issigmacompact {A : Type} (c : IsSigmaCompact A)
  : Decidable A.
Proof.
  destruct (c (fun (_ : A) => Unit) _) as [c1|c2].
  - exact (inl c1.1).
  - right; intro a.
    exact (c2 (a; pt)).
Defined.

(** Any ∃-compact type has decidable propositional truncation. *)
Definition decidable_tr_ishexistscompact {A : Type} (c : IsHExistsCompact A)
  : Decidable (Tr (-1) A).
Proof.
  destruct (c (fun (_ : A) => Unit) _) as [c1|c2].
  - left; strip_truncations; apply tr.
    exact c1.1.
  - right; intro a; strip_truncations.
    exact (c2 (tr (a; pt))).
Defined.

(** The negation of any Π-compact type is decidable. *)
Definition decidable_not_ispicompact {A} (h : IsPiCompact A)
  : Decidable (~A)
  := h (const False_hp) _.

(** ** Equivalent definitions *)

(** A type [A] is compact if for every decidable predicate [P] on [A] we can either find an element of [A] making [P] false or we can show that [P a] always holds. *)
Definition IsCompact (A : Type)
  := forall P : A -> Type, (forall a : A, Decidable (P a)) ->
                              {a : A & ~ P a} + (forall a : A, P a).

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

(** Since decidable types are stable, it's also equivalent to negate [P] in the definition. We use this as an intermediate notion to show that [IsCompact] and [IsSigmaCompact] are logically equivalent. *)
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

Definition iff_iscompact'_issigmacompact (A : Type)
  : IsCompact' A <-> IsSigmaCompact A.
Proof.
  apply iff_functor_forall; intro P.
  apply iff_functor_forall; intro dP.
  apply iff_equiv.
  apply (equiv_functor_sum' equiv_idmap).
  napply equiv_sig_ind.
Defined.

Definition iff_iscompact_issigmacompact (A : Type)
  : IsCompact A <-> IsSigmaCompact A
  := iff_compose (iff_iscompact_iscompact' A) (iff_iscompact'_issigmacompact A).

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

Definition issearchable_issigmacompact_inhabited {A : Type}
  (c : IsSigmaCompact A)
  : A -> IsSearchable A.
Proof.
  intros a P dP.
  destruct (c (fun x => ~ (P x)) _) as [l|r].
  - exists l.1.
    intro h; contradiction (l.2 h).
  - exists a; intros _ x.
    rapply stable_decidable.
    exact (fun u => r (x; u)).
Defined.

Definition issigmacompact_issearchable {A : Type} (s : IsSearchable A)
  : IsSigmaCompact A.
Proof.
  intros P dP.
  destruct (s (fun x => ~ (P x)) _) as [w hw].
  destruct (dP w) as [x|y].
  - exact (inl (w; x)).
  - exact (inr (fun u => hw y u.1 u.2)).
Defined.

Definition inhabited_issearchable {A : Type} (s : IsSearchable A) : A
  := (s (fun a => Unit) _).1.

Definition issearchable_iff (A : Type) : IsSearchable A <-> A * (IsSigmaCompact A)
  := (fun s => (inhabited_issearchable s, issigmacompact_issearchable s),
        fun c => issearchable_issigmacompact_inhabited (snd c) (fst c)).

(** Since compactness implies decidability, a type is compact if and only if it is either empty or searchable. *)
Definition issigmacompact_iff_not_or_issearchable (A : Type)
  : IsSigmaCompact A <-> (~ A) + IsSearchable A.
Proof.
  constructor.
  - intro c.
    destruct (decidable_issigmacompact c) as [l|r].
    + exact (inr (issearchable_issigmacompact_inhabited c l)).
    + exact (inl r).
  - intros [l|r].
    + exact (fun P dP => inr (l o pr1)).
    + exact (issigmacompact_issearchable r).
Defined.

(** ** Examples of searchable and compact types, and closure properties *)

(** Contractible types are compact. *)
Definition issigmacompact_contr {A} (c : Contr A) : IsSigmaCompact A.
Proof.
  intros P dP.
  rapply (decidable_equiv _ (equiv_contr_sigma _)^-1).
Defined.

(** Contractible types are searchable. *)
Definition issearchable_contr {A} (c : Contr A) : IsSearchable A.
Proof.
  intros P dP.
  exists (center A).
  intros p a.
  by induction (contr a).
Defined.

(** [Bool] is searchable. *)
Definition issearchable_Bool : IsSearchable Bool.
Proof.
  intros P dP.
  induction (dP false) as [p | np]; [exists true | exists false].
  all: by intros p' [].
Defined.

(** [Bool] is compact. *)
Definition issigmacompact_bool : IsSigmaCompact Bool
  := issigmacompact_issearchable issearchable_Bool.

(** The empty type is trivially compact. *)
Definition issigmacompact_empty : IsSigmaCompact Empty
  := fun P dP => inr pr1.

(** Any decidable proposition is compact. *)
Definition issigmacompact_decidable_hprop {A : HProp} (dA : Decidable A)
  : IsSigmaCompact A.
Proof.
  destruct (equiv_decidable_hprop A) as [e1|e2].
  - apply (issigmacompact_equiv e1).
    rapply issigmacompact_contr.
  - apply (issigmacompact_equiv e2).
    apply issigmacompact_empty.
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

(** Assuming the set truncation map has a section, a type is compact if and only if its set truncation is compact. *)
Definition issigmacompact_iff_issigmacompact_set_trunc `{Univalence} {A : Type}
  (f : (Tr 0 A) -> A) (s : tr o f == idmap)
  : IsSigmaCompact A <-> IsSigmaCompact (Tr 0 A).
Proof.
  constructor.
  1: exact (issigmacompact_retract s).
  intro cpt; rapply issigmacompact_issigmacompactprops.
  intros P dP.
  destruct (cpt (Trunc_rec P)) as [l|r].
  - intro a; strip_truncations.
    exact (dP a).
  - left; exists (f l.1).
    exact ((ap (Trunc_rec P) (s l.1))^ # l.2).
  - right; refine (fun a => r (tr a.1; a.2)).
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

(** Consequently, the same is true for compact types.  *)
Definition issigmacompact_image `{Univalence} {A B : Type}
  (c : IsSigmaCompact A)
  (f : A -> B) (surj : IsSurjection f)
  : IsSigmaCompact B.
Proof.
  apply issigmacompact_iff_not_or_issearchable.
  destruct (fst (issigmacompact_iff_not_or_issearchable A) c) as [n|s].
  - left; by rapply conn_map_elim.
  - right; by rapply issearchable_image.
Defined.

(** Assuming univalence, every pointed, connected type is searchable. *)
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

(** For any family of compact types over a compact type, the corresponding dependent sum type is compact. *)
Definition issigmacompact_sigma {A : Type} {P : A -> Type}
  (cA : IsSigmaCompact A) (cP : forall (a : A), IsSigmaCompact (P a))
  : IsSigmaCompact (sig P).
Proof.
  intros Q dQ.
  apply (decidable_equiv _ (equiv_sigma_assoc P Q)).
  apply cA; intro a.
  by apply cP; intro p.
Defined.

Definition issigmacompact_sum {A B : Type}
  (cA : IsSigmaCompact A) (cB : IsSigmaCompact B)
  : IsSigmaCompact (A + B).
Proof.
  apply (issigmacompact_equiv (sig_of_sum A B)).
  apply issigmacompact_sigma.
  - exact issigmacompact_bool.
  - by destruct a.
Defined.

(** Inductively, any type of the form [Fin n] is compact. *)
Definition issigmacompact_fin (n : nat)
  : IsSigmaCompact (Fin n).
Proof.
  induction n.
  - exact (fun P dP => inr proj1).
  - apply (issigmacompact_sum IHn).
    rapply issigmacompact_contr.
Defined.

(** A decidable subtype of a compact type is compact. *)
Definition issigmacompact_detachable_subtype {A : Type} {P : A -> HProp}
  (cA : IsSigmaCompact A) (dP : forall (a : A), Decidable (P a))
  : IsSigmaCompact (sig P).
Proof.
  apply (issigmacompact_sigma cA); cbn beta.
  intro a.
  rapply issigmacompact_decidable_hprop.
Defined.

(** The weak limited principle of omniscience. We state this in one form, and then prove it is equivalent to the common form involving the universal quantifier. *)
Definition WLPO
  := forall (P : nat -> Type) (dP : forall n : nat, Decidable (P n)), Decidable (~ sig P).

Instance ishprop_wlpo `{Funext} : IsHProp WLPO := _.

Definition iff_wlpo_ispicompact_nat : WLPO <-> IsPiCompact nat.
Proof.
  split.
  - intros w P dP.
    destruct (w (not o P) _) as [l|r].
    + left. intro n; exact (stable_decidable (P n) (fun u => l (n; u))).
    + right. intro f; exact (r (fun u => u.2 (f u.1))).
  - intros c P dP.
    destruct (c (not o P) _) as [l|r].
    + left. intro u; exact (l u.1 u.2).
    + right. intro nu; exact (r (fun n p => nu (n; p))).
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
