(** * Bar induction *)

Require Import Basics Types.
Require Import Truncations.Core.
Require Import Spaces.Nat.Core.
Require Import Spaces.NatSeq.Core.
Require Import Spaces.List.Core Spaces.List.Theory.
Require Import BoundedSearch.

Local Open Scope nat_scope.
Local Open Scope type_scope.
Local Open Scope list_scope.

(** ** The basic definitions *)

(** A family [B] on a type of lists is a bar if every infinite sequence restricts to a finite sequence satisfying [B]. *)
Definition is_bar {A : Type} (B : list A -> Type)
  := forall (s : nat -> A), {n : nat & B (list_restrict s n)}.

(** A family [B] is a uniform bar if it is a bar such that there is an upper bound for the lengths of the restrictions needed to satisfy the bar condition. *)
Definition is_uniform_bar {A : Type} (B : list A -> Type)
  := {M : nat & forall (s : nat -> A),
                  {n : nat & (n <= M) * B (list_restrict s n)}}.

(** A family [B] on a type of finite sequences is inductive if, for every list [l], if the concatenation of [l] with any term satisfies [B], then the list satisfies [B]. *)
Definition is_inductive {A : Type} (B : list A -> Type)
  := forall (l : list A), (forall (a : A), B (l ++ [a])) -> B l.

(** A family [B] on a type of finite sequences is monotone if for every list satisfying [B], the concatenation with any other list still satisfies [B]. Equivalently, we can just check the concatenations with lists of length one. *)
Definition is_monotone {A : Type} (B : list A -> Type)
  := forall (l1 l2 : list A), B l1 -> B (l1 ++ l2).

Definition is_monotone_singleton {A : Type} (B : list A -> Type)
  := forall (l : list A) (a : A), B l -> B (l ++ [a]).

Definition is_monotone_is_monotone_singleton {A : Type} (B : list A -> Type)
  (mon : is_monotone_singleton B)
  : is_monotone B.
Proof.
  intros l1 l2; induction l2 as [|a l2 IHl2] in l1 |- *.
  - by rewrite app_nil.
  - intro h.
    rewrite (app_assoc l1 [a] l2).
    apply IHl2, mon, h.
Defined.

(** We state three forms of bar induction: (full) bar induction, monotone bar induction and decidable bar induction. *)

Definition decidable_bar_induction (A : Type) :=
  forall (B : list A -> Type)
  (dec : forall (l : list A), Decidable (B l))
  (ind : is_inductive B)
  (bar : is_bar B),
  B nil.

Definition monotone_bar_induction (A : Type) :=
  forall (B : list A -> Type)
  (mon : is_monotone B)
  (ind : is_inductive B)
  (bar : is_bar B),
  B nil.

Definition bar_induction (A : Type) :=
  forall (B : list A -> Type)
  (ind : is_inductive B)
  (bar : is_bar B),
  B nil.

(** The three bar induction principles can be more generally stated for two families. It's clear that the two-family versions imply the one-family versions. We show the reverse implications for full bar induction and monotone bar induction. We do not know if the definitions are equivalent in the decidable case yet. *)

Definition decidable_bar_induction' (A : Type) :=
  forall (B C : list A -> Type)
  (sub : forall l : list A, C l -> B l)
  (dC : forall (l : list A), Decidable (C l))
  (ind : is_inductive B)
  (bar : is_bar C),
  B nil.

Definition monotone_bar_induction' (A : Type) :=
  forall (B C : list A -> Type)
  (sub : forall l : list A, C l -> B l)
  (monC : is_monotone C)
  (indB : is_inductive B)
  (barC : is_bar C),
  B nil.

Definition bar_induction' (A : Type) :=
  forall (B C : list A -> Type)
  (sub : forall l : list A, C l -> B l)
  (indB : is_inductive B)
  (barC : is_bar C),
  B nil.

Definition bar_induction'_bar_induction (A : Type) (BI : bar_induction A)
  : bar_induction' A
  := fun B C sub indB barC => BI B indB (fun s => ((barC s).1; sub _ (barC s).2)).

Definition monotone_bar_induction'_monotone_bar_induction (A : Type)
  (MBI : monotone_bar_induction A)
  : monotone_bar_induction' A.
Proof.
  intros B C sub monC indB barC.
  pose (P := fun v => forall w, B (v ++ w)).
  apply (MBI P).
  - intros u v H w.
    by rewrite <- app_assoc.
  - intros l1 H [|a l2].
    + apply indB.
      intro a.
      specialize (H a nil).
      by rewrite app_nil in *.
    + specialize (H a l2).
      by rewrite <- app_assoc in H.
  - intro s.
    exists (barC s).1.
    intro w.
    apply sub, monC, barC.
Defined.

(** Since decidable bar induction uses decidable predicates, we can state a logically equivalent form based on families of decidable propositions. This form has the advantage of being a proposition. *)

Definition hprop_decidable_bar_induction (A : Type) :=
  forall (B : list A -> Type)
  (prop : forall (l : list A), IsHProp (B l))
  (dec : forall (l : list A), Decidable (B l))
  (ind : is_inductive B)
  (bar : is_bar B),
  B nil.

Definition ishprop_hprop_decidable_bar_induction `{Funext} (A : Type)
  : IsHProp (hprop_decidable_bar_induction A)
  := _.

Definition decidable_bar_induction_hprop_decidable_bar_induction (A : Type)
  (pDBI : hprop_decidable_bar_induction A)
  : decidable_bar_induction A.
Proof.
  intros P dP iP bP.
  apply merely_inhabited_iff_inhabited_stable.
  tapply (pDBI (Tr (-1) o P)).
  - intro l.
    destruct (dP l) as [p | np].
    + left; exact (tr p).
    + right; intro s.
      by strip_truncations.
  - intros l q.
    refine (tr (iP _ _)).
    intro a; apply merely_inhabited_iff_inhabited_stable, (q a).
  - intros s.
    exists (bP s).1.
    exact (tr (bP s).2).
Defined.

(** ** Relations between the three forms of bar induction *)

(** Full bar induction clearly implies the other two. We now show that monotone bar induction implies decidable bar induction, by passing through the two-family versions. *)

Definition decidable_bar_induction'_monotone_bar_induction' (A : Type)
  (MBI : monotone_bar_induction' A)
  : decidable_bar_induction' A.
Proof.
  intros B C sub dC indB barC.
  (* The [n <= length l] part is redundant, but makes it clear that [P l] is decidable, which is used below. *)
  pose (P l := {n : nat & (n <= length l) * C (take n l)}).
  pose (Q l := B l + P l).
  (* First we show that it is enough to prove [Q nil], and then we prove [Q nil]. *)
  enough (Q nil) as [b0 | [n [hn hc]]].
  1: exact b0.
  1: exact (sub _ (take_nil _ # hc)).
  apply (MBI Q P (fun l pl => inr pl)).
  - intros l1 l2 [n (cn1, cn2)].
    exists n; split.
    + rewrite length_app; exact _.
    + exact (take_app l1 l2 cn1 # cn2).
  - intros l hl.
    assert (dP : Decidable (P l)) by rapply decidable_search.
    destruct dP as [t|f].
    1: exact (inr t).
    left. apply indB.
    intro a; destruct (hl a) as [b | [n [hn hc]]].
    1: exact b.
    destruct (equiv_leq_lt_or_eq hn) as [hn1 | hn2]; clear hn.
    + contradiction f.
      assert (hln : n <= length l).
      { rewrite length_app, nat_add_comm in hn1. cbn in hn1; unfold "<" in hn1.
        exact (leq_pred' hn1). }
      exists n; constructor.
      * exact hln.
      * exact ((take_app l [a] hln)^ # hc).
    + refine (sub _ ((take_length_leq _ _ _) # hc)).
      by destruct hn2^.
  - intro s.
    pose (n := (barC s).1).
    exists n; exists n.
    split.
    + by rewrite length_list_restrict.
    + rewrite take_length_leq.
      1: exact (barC s).2.
      by rewrite length_list_restrict.
Defined.

Definition decidable_bar_induction_monotone_bar_induction (A : Type)
  (MBI : monotone_bar_induction A)
  : decidable_bar_induction A
  := fun B dec ind bar =>
      (decidable_bar_induction'_monotone_bar_induction' A
        (monotone_bar_induction'_monotone_bar_induction A MBI))
      B B (fun _ => idmap) dec ind bar.

(** ** Examples of types that satisfy forms of bar induction *)

(** The empty type and all contractible types satisfy full bar induction. *)

Definition bar_induction_empty : bar_induction Empty.
Proof.
  intros B iB _.
  rapply iB.
  intro a; contradiction a.
Defined.

Definition bar_induction_contr (A : Type) `{Contr A} : bar_induction A.
Proof.
  intros B iB bB.
  pose (c := fun (n : nat) => center A).
  specialize (bB c) as [n hn]; induction n.
  1: exact hn.
  apply IHn, iB.
  intro x.
  nrefine (_ # hn).
  rewrite (path_contr x (center A)).
  napply list_restrict_succ.
Defined.

(** If a type satisfies decidable bar induction assuming that it is pointed, then it satisfies decidable bar induction. *)
Definition decidable_bar_induction_pointed_decidable_bar_induction
  (A : Type) (p : A -> decidable_bar_induction A)
  : decidable_bar_induction A.
Proof.
  intros B dB iB bB.
  destruct (dec (B nil)) as [b | n].
  1: exact b.
  apply iB.
  intro a; cbn.
  pose (B' l := B (a :: l)).
  apply (p a B' _).
  - intros l; unfold B'.
    exact (iB (a :: l)).
  - intro s; unfold B'.
    destruct (bB (seq_cons a s)) as [m r].
    destruct m.
    + contradiction (n r).
    + exists m.
      nrefine (_ # r).
      snapply path_list_nth'.
      1: cbn; by rewrite !length_list_restrict.
      intros k hk; destruct k.
      1: cbn; by rewrite nth'_list_restrict.
      assert (hk' : k < length (list_restrict s m)).
      { rewrite length_list_restrict in *.
        exact _. }
      by rewrite (nth'_cons _ _ _ hk'), !nth'_list_restrict.
Defined.

(** The same is true for monotone bar induction. *)
Definition monotone_bar_induction_pointed_monotone_bar_induction
  (A : Type) (p : A -> monotone_bar_induction A)
  : monotone_bar_induction A.
Proof.
  intros B mB iB bB.
  apply iB.
  intro a; cbn.
  by apply (mB nil), (p a).
Defined.

(** Combining [monotone_bar_induction_pointed_monotone_bar_induction] and [bar_induction_contr], we prove that any proposition satisfies monotone bar induction. *)
Definition monotone_bar_induction_hprop (A : Type) `{IsHProp A}
  : monotone_bar_induction A.
Proof.
  apply monotone_bar_induction_pointed_monotone_bar_induction.
  intro a.
  enough (bar_induction A) as BI.
  1: exact (fun B _ iB bB => BI B iB bB).
  apply bar_induction_contr, (contr_inhabited_hprop A a).
Defined.

(** Note that [monotone_bar_induction_pointed_monotone_bar_induction] does not have an analogue for full bar induction. We prove below that every type satisfying full bar induction is Sigma-compact and therefore decidable. Then, as in [monotone_bar_induction_hprop], we would be able to prove that any proposition satisfies bar induction and therefore that every proposition is decidable. *)

(** ** Implications of bar induction *)

(** Full bar induction for a type [A] implies that it is Sigma-compact, in the sense that any decidable family over [A] has a decidable Sigma-type. To prove this, we begin by defining a type family [P] on [list A] so that [P nil] i s our goal. *)

Definition BI_sig_family {A : Type} (P : A -> Type) (l : list A) : Type
  := match l with
      | nil => Decidable {a : A & P a}
      | a :: l' => ~(P a)
     end.

Definition is_bar_BI_sig_family {A : Type} {P : A -> Type}
  (dec : forall n : A, Decidable (P n))
  : is_bar (BI_sig_family P).
Proof.
  intro s.
  destruct (dec (s 0)) as [p|p'].
  - exists 0.
    simpl.
    exact (inl (s 0; p)).
  - exists 1.
    exact p'.
Defined.

Definition is_inductive_BI_sig_family {A : Type} (P : A -> Type)
  : is_inductive (BI_sig_family P).
Proof.
  intros [|a l] h.
  - right. exact (fun pa => h pa.1 pa.2).
  - exact (h a).
Defined.

Definition is_sig_compact_bar_induction {A : Type} (BI : bar_induction A)
  (P : A -> Type) (dec : forall n : A, Decidable (P n))
  : Decidable {a : A & P a}
  := BI (BI_sig_family P)
          (is_inductive_BI_sig_family P) (is_bar_BI_sig_family dec).

(** Full bar induction for [nat] implies the limited principle of omniscience, i.e., for every sequence of natural numbers we can decide whether every term is zero or there exists a non-zero term. *)

Definition LPO_bar_induction {BI : bar_induction nat} (s : nat -> nat)
  : (forall n : nat, s n = 0) + {n : nat & s n <> 0}.
Proof.
  destruct (is_sig_compact_bar_induction BI (fun n => s n <> 0) _) as [l|r].
  - right; exact l.
  - left; exact (fun n => stable (fun z : s n <> 0 => r (n; z))).
Defined.
