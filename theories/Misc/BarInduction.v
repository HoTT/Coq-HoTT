(** * Bar induction *)

From HoTT Require Import Basics Types.
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
Definition IsBar {A : Type} (B : list A -> Type)
  := forall (s : nat -> A), {n : nat & B (list_restrict s n)}.

(** A family [B] is a uniform bar if it is a bar such that there is an upper bound for the lengths of the restrictions needed to satisfy the bar condition. *)
Definition IsUniformBar {A : Type} (B : list A -> Type)
  := {M : nat & forall (s : nat -> A),
                  {n : nat & (n <= M) * B (list_restrict s n)}}.

(** A family [B] on a type of finite sequences is inductive if, for every list [l], if the concatenation of [l] with any term satisfies [B], then the list satisfies [B]. *)
Definition IsInductive {A : Type} (B : list A -> Type)
  := forall (l : list A), (forall (a : A), B (l ++ [a])) -> B l.

(** A family [B] on a type of finite sequences is monotone if for every list satisfying [B], the concatenation with any other list still satisfies [B]. Equivalently, we can just check the concatenations with lists of length one. *)
Definition IsMonotone {A : Type} (B : list A -> Type)
  := forall (l1 l2 : list A), B l1 -> B (l1 ++ l2).

Definition IsMonotoneSingleton {A : Type} (B : list A -> Type)
  := forall (l : list A) (a : A), B l -> B (l ++ [a]).

Definition ismonotone_ismonotonesingleton {A : Type} (B : list A -> Type)
  (mon : IsMonotoneSingleton B)
  : IsMonotone B.
Proof.
  intros l1 l2; induction l2 as [|a l2 IHl2] in l1 |- *.
  - by rewrite app_nil.
  - intro h.
    rewrite (app_assoc l1 [a] l2).
    apply IHl2, mon, h.
Defined.

(** We state three forms of bar induction: (full) bar induction, monotone bar induction and decidable bar induction. *)

Definition DecidableBarInduction (A : Type) :=
  forall (B : list A -> Type)
  (dec : forall (l : list A), Decidable (B l))
  (ind : IsInductive B)
  (bar : IsBar B),
  B nil.

Definition MonotoneBarInduction (A : Type) :=
  forall (B : list A -> Type)
  (mon : IsMonotone B)
  (ind : IsInductive B)
  (bar : IsBar B),
  B nil.

Definition BarInduction (A : Type) :=
  forall (B : list A -> Type)
  (ind : IsInductive B)
  (bar : IsBar B),
  B nil.

(** The three bar induction principles can be more generally stated for two families. It's clear that the two-family versions imply the one-family versions. We show the reverse implications for full bar induction and monotone bar induction. We do not know if the definitions are equivalent in the decidable case yet. *)

Definition DecidableBarInduction' (A : Type) :=
  forall (B C : list A -> Type)
  (sub : forall l : list A, C l -> B l)
  (dC : forall (l : list A), Decidable (C l))
  (ind : IsInductive B)
  (bar : IsBar C),
  B nil.

Definition MonotoneBarInduction' (A : Type) :=
  forall (B C : list A -> Type)
  (sub : forall l : list A, C l -> B l)
  (monC : IsMonotone C)
  (indB : IsInductive B)
  (barC : IsBar C),
  B nil.

Definition BarInduction' (A : Type) :=
  forall (B C : list A -> Type)
  (sub : forall l : list A, C l -> B l)
  (indB : IsInductive B)
  (barC : IsBar C),
  B nil.

Definition barinduction'_barinduction (A : Type) (BI : BarInduction A)
  : BarInduction' A
  := fun B C sub indB barC => BI B indB (fun s => ((barC s).1; sub _ (barC s).2)).

Definition monotonebarinduction'_monotonebarinduction (A : Type)
  (MBI : MonotoneBarInduction A)
  : MonotoneBarInduction' A.
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

Definition HPropDecidableBarInduction (A : Type) :=
  forall (B : list A -> Type)
  (prop : forall (l : list A), IsHProp (B l))
  (dec : forall (l : list A), Decidable (B l))
  (ind : IsInductive B)
  (bar : IsBar B),
  B nil.

Definition ishprop_hpropdecidablebarinduction `{Funext} (A : Type)
  : IsHProp (HPropDecidableBarInduction A)
  := _.

Definition decidablebarinduction_hpropdecidablebarinduction (A : Type)
  (pDBI : HPropDecidableBarInduction A)
  : DecidableBarInduction A.
Proof.
  intros P dP iP bP.
  apply merely_inhabited_iff_inhabited_stable.
  rapply (pDBI (Tr (-1) o P)).
  - intros l q.
    refine (tr (iP _ _)).
    intro a; apply merely_inhabited_iff_inhabited_stable, (q a).
  - intros s.
    exists (bP s).1.
    exact (tr (bP s).2).
Defined.

(** ** Relations between the three forms of bar induction *)

(** Full bar induction clearly implies the other two. We now show that monotone bar induction implies decidable bar induction, by passing through the two-family versions. *)

Definition decidablebarinduction'_monotone_bar_induction' (A : Type)
  (MBI : MonotoneBarInduction' A)
  : DecidableBarInduction' A.
Proof.
  intros B C sub dC indB barC.
  (* The [n <= length l] part is redundant, but makes it clear that [P l] is decidable, which is used below. *)
  pose (P l := {n : nat & (n <= length l) * C (take n l)}).
  pose (Q l := B l + P l).
  (* First we show that it is enough to prove [Q nil] (two cases), and then we prove [Q nil]. *)
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
  (MBI : MonotoneBarInduction A)
  : DecidableBarInduction A
  := fun B dec ind bar =>
      (decidablebarinduction'_monotone_bar_induction' A
        (monotonebarinduction'_monotonebarinduction A MBI))
      B B (fun _ => idmap) dec ind bar.

(** ** Examples of types that satisfy forms of bar induction *)

(** The empty type and all contractible types satisfy full bar induction. *)

Definition barinduction_empty : BarInduction Empty.
Proof.
  intros B iB _.
  rapply iB.
  intro a; contradiction a.
Defined.

Definition barinduction_contr (A : Type) `{Contr A} : BarInduction A.
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
Definition decidablebarinduction_pointed_decidablebarinduction
  (A : Type) (p : A -> DecidableBarInduction A)
  : DecidableBarInduction A.
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
Definition monotonebarinduction_pointed_monotonebarinduction
  (A : Type) (p : A -> MonotoneBarInduction A)
  : MonotoneBarInduction A.
Proof.
  intros B mB iB bB.
  apply iB.
  intro a; cbn.
  by apply (mB nil), (p a).
Defined.

(** Combining [monotonebarinduction_pointed_monotonebarinduction] and [barinduction_contr], we prove that any proposition satisfies monotone bar induction. *)
Definition monotonebarinduction_hprop (A : Type) `{IsHProp A}
  : MonotoneBarInduction A.
Proof.
  apply monotonebarinduction_pointed_monotonebarinduction.
  intro a.
  enough (BarInduction A) as BI.
  1: exact (fun B _ iB bB => BI B iB bB).
  apply barinduction_contr, (contr_inhabited_hprop A a).
Defined.

(** Note that [monotone_bar_induction_pointed_monotone_bar_induction] does not have an analogue for full bar induction. We prove below that every type satisfying full bar induction is Sigma-compact and therefore decidable. Then, as in [monotone_bar_induction_hprop], we would be able to prove that any proposition satisfies bar induction and therefore that every proposition is decidable. *)

(** ** Implications of bar induction *)

(** Full bar induction for a type [A] implies that it is Sigma-compact, in the sense that any decidable family over [A] has a decidable Sigma-type. To prove this, we begin by defining a type family [P] on [list A] so that [P nil] is our goal. *)

Definition BI_sig_family {A : Type} (P : A -> Type) (l : list A) : Type
  := match l with
      | nil => Decidable {a : A & P a}
      | a :: l' => ~(P a)
     end.

Definition is_bar_BI_sig_family {A : Type} {P : A -> Type}
  (dec : forall n : A, Decidable (P n))
  : IsBar (BI_sig_family P).
Proof.
  intro s.
  destruct (dec (s 0)) as [p|p'].
  - exists 0.
    simpl.
    exact (inl (s 0; p)).
  - exists 1.
    exact p'.
Defined.

Definition isinductive_BI_sig_family {A : Type} (P : A -> Type)
  : IsInductive (BI_sig_family P).
Proof.
  intros [|a l] h.
  - right. exact (fun pa => h pa.1 pa.2).
  - exact (h a).
Defined.

Definition issigcompact_barinduction {A : Type} (BI : BarInduction A)
  (P : A -> Type) (dec : forall n : A, Decidable (P n))
  : Decidable {a : A & P a}
  := BI (BI_sig_family P)
          (isinductive_BI_sig_family P) (is_bar_BI_sig_family dec).

(** Full bar induction for [nat] implies the limited principle of omniscience, i.e., for every sequence of natural numbers we can decide whether every term is zero or there exists a non-zero term. *)

Definition LPO_barinduction {BI : BarInduction nat} (s : nat -> nat)
  : (forall n : nat, s n = 0) + {n : nat & s n <> 0}.
Proof.
  destruct (issigcompact_barinduction BI (fun n => s n <> 0) _) as [l|r].
  - right; exact l.
  - left; exact (fun n => stable (fun z : s n <> 0 => r (n; z))).
Defined.
