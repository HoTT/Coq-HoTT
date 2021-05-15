(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics.
Require Import Types.
Require Import HSet.
Require Import DProp.
Require Import Spaces.Nat.
Require Import Equiv.PathSplit.

Local Open Scope path_scope.
Local Open Scope nat_scope.

(** * Finite sets *)

(** ** Canonical finite sets *)

(** A *finite set* is a type that is merely equivalent to the canonical finite set determined by some natural number.  There are many equivalent ways to define the canonical finite sets, such as [{ k : nat & k < n}]; we instead choose a recursive one. *)

Fixpoint Fin (n : nat) : Type0
  := match n with
       | 0 => Empty
       | S n => Fin n + Unit
     end.

Fixpoint fin_to_nat {n} : Fin n -> nat
  := match n with
     | 0 => Empty_rec
     | S n' =>
       fun k =>
         match k with
         | inl k' => fin_to_nat k'
         | inr tt => n'
         end
     end.

Global Instance decidable_fin (n : nat)
: Decidable (Fin n).
Proof.
  destruct n as [|n]; try exact _.
  exact (inl (inr tt)).
Defined.

Global Instance decidablepaths_fin (n : nat)
: DecidablePaths (Fin n).
Proof.
  induction n as [|n IHn]; simpl; exact _.
Defined.

Global Instance contr_fin1 : Contr (Fin 1).
Proof.
  refine (contr_equiv' Unit (sum_empty_l Unit)^-1).
Defined.

Definition fin_empty (n : nat) (f : Fin n -> Empty) : n = 0.
Proof.
  destruct n; [ reflexivity | ].
  elim (f (inr tt)).
Defined.

(** The zeroth element of a non-empty finite set is the left most element. It also happens to be the biggest by termsize. *)
Fixpoint fin_zero {n : nat} : Fin n.+1 :=
  match n with
  | O => inr tt
  | S _ => inl fin_zero
  end.

(** Where `fin_zero` computes the first element of Fin (S n), `fin_last` computes the last. *)
Definition fin_last {n : nat} : Fin (S n) := inr tt.

(** Injection Fin n -> Fin n.+1 mapping the kth element to the kth element. *)
Definition fin_incl {n : nat} (k : Fin n) : Fin (S n) := inl k.

(** There is an injection from Fin n -> Fin n.+1 that maps the kth element to the (k+1)th element. *)
Fixpoint fsucc {n : nat} : Fin n -> Fin n.+1 :=
  match n with
  | O => Empty_rec
  | S n' =>
    fun i : Fin (S n') =>
      match i with
      | inl i' => inl (fsucc i')
      | inr tt => inr tt
      end
  end.

(** This injection is an injection/embedding *)
Lemma isembedding_fsucc {n : nat} : IsEmbedding (@fsucc n).
Proof.
  apply isembedding_isinj_hset.
  induction n.
  - intro i. elim i.
  - intros [] []; intro p.
    + f_ap. apply IHn. eapply path_sum_inl. exact p.
    + destruct u. elim (inl_ne_inr _ _ p).
    + destruct u. elim (inr_ne_inl _ _ p).
    + destruct u, u0; reflexivity.
Qed.

Lemma path_fin_fsucc_incl {n : nat} : forall k : Fin n, fsucc (fin_incl k) = fin_incl (fsucc k).
Proof.
  trivial.
Qed.

Lemma path_nat_fin_incl {n : nat} : forall k : Fin n, fin_to_nat (fin_incl k) = fin_to_nat k.
Proof.
  reflexivity.
Qed.

Lemma path_nat_fsucc {n : nat} : forall k : Fin n, fin_to_nat (fsucc k) = S (fin_to_nat k).
Proof.
  induction n as [|n' IHn].
  - intros [].
  - intros [k'|[]].
    + rewrite path_fin_fsucc_incl, path_nat_fin_incl.
      apply IHn.
    + reflexivity.
Defined.

Lemma path_nat_fin_zero {n} : fin_to_nat (@fin_zero n) = 0.
Proof.
  induction n as [|n' IHn].
  - reflexivity.
  - trivial.
Defined.

Lemma path_nat_fin_last {n} : fin_to_nat (@fin_last n) = n.
Proof.
  reflexivity.
Qed.

(** ** Transposition equivalences *)

(** To prove some basic facts about canonical finite sets, we need some standard automorphisms of them.  Here we define some transpositions and prove that they in fact do the desired things. *)

(** *** Swap the last two elements. *)

Definition fin_transpose_last_two (n : nat)
: Fin n.+2 <~> Fin n.+2
  := ((equiv_sum_assoc _ _ _)^-1)
       oE (1 +E (equiv_sum_symm _ _))
       oE (equiv_sum_assoc _ _ _).

Arguments fin_transpose_last_two : simpl nomatch.

Definition fin_transpose_last_two_last (n : nat)
: fin_transpose_last_two n (inr tt) = (inl (inr tt))
  := 1.

Definition fin_transpose_last_two_nextlast (n : nat)
: fin_transpose_last_two n (inl (inr tt)) = (inr tt)
  := 1.

Definition fin_transpose_last_two_rest (n : nat) (k : Fin n)
: fin_transpose_last_two n (inl (inl k)) = (inl (inl k))
  := 1.

(** *** Swap the last element with [k]. *)

Fixpoint fin_transpose_last_with (n : nat) (k : Fin n.+1)
: Fin n.+1 <~> Fin n.+1.
Proof.
  destruct k as [k|].
  - destruct n as [|n].
    + elim k.
    + destruct k as [k|].
      * refine ((fin_transpose_last_two n)
                  oE _
                  oE (fin_transpose_last_two n)).
        refine ((fin_transpose_last_with n (inl k)) +E 1).
      * apply fin_transpose_last_two.
  - exact (equiv_idmap _).
Defined.

Arguments fin_transpose_last_with : simpl nomatch.

Definition fin_transpose_last_with_last (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n k (inr tt) = k.
Proof.
  destruct k as [k|].
  - induction n as [|n IH]; simpl.
    + elim k.
    + destruct k as [k|].
      * simpl. rewrite IH; reflexivity.
      * simpl. apply ap, ap, path_contr.
  - (** We have to destruct [n] since fixpoints don't reduce unless their argument is a constructor. *)
    destruct n; simpl.
    all:apply ap, path_contr.
Qed.

Definition fin_transpose_last_with_with (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n k k = inr tt.
Proof.
  destruct k as [k|].
  - induction n as [|n IH]; simpl.
    + elim k.
    + destruct k as [|k]; simpl.
      * rewrite IH; reflexivity.
      * apply ap, path_contr.
  - destruct n; simpl.
    all:apply ap, path_contr.
Qed.

Definition fin_transpose_last_with_rest (n : nat)
           (k : Fin n.+1) (l : Fin n)
           (notk : k <> inl l)
: fin_transpose_last_with n k (inl l) = (inl l).
Proof.
  destruct k as [k|].
  - induction n as [|n IH]; simpl.
    1:elim k.
    destruct k as [k|]; simpl.
    { destruct l as [l|]; simpl.
      - rewrite IH.
        + reflexivity.
        + exact (fun p => notk (ap inl p)).
      - reflexivity. }
    { destruct l as [l|]; simpl.
      - reflexivity.
      - elim (notk (ap inl (ap inr (path_unit _ _)))). }
  - destruct n; reflexivity.
Qed.

Definition fin_transpose_last_with_last_other (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n (inr tt) k = k.
Proof.
  destruct n; reflexivity.
Qed.

Definition fin_transpose_last_with_invol (n : nat) (k : Fin n.+1)
: fin_transpose_last_with n k o fin_transpose_last_with n k == idmap.
Proof.
  intros l.
  destruct l as [l|[]].
  - destruct k as [k|[]].
    { destruct (dec_paths k l) as [p|p].
      - rewrite p.
        rewrite fin_transpose_last_with_with.
        apply fin_transpose_last_with_last.
      - rewrite fin_transpose_last_with_rest;
          try apply fin_transpose_last_with_rest;
          exact (fun q => p (path_sum_inl _ q)). }
    + rewrite fin_transpose_last_with_last_other.
      apply fin_transpose_last_with_last_other.
  - rewrite fin_transpose_last_with_last.
    apply fin_transpose_last_with_with.
Qed.

(** ** Equivalences between canonical finite sets *)

(** To give an equivalence [Fin n.+1 <~> Fin m.+1] is equivalent to giving an element of [Fin m.+1] (the image of the last element) together with an equivalence [Fin n <~> Fin m].  More specifically, any such equivalence can be decomposed uniquely as a last-element transposition followed by an equivalence fixing the last element.  *)

(** Here is the uncurried map that constructs an equivalence [Fin n.+1 <~> Fin m.+1]. *)
Definition fin_equiv (n m : nat)
           (k : Fin m.+1) (e : Fin n <~> Fin m)
: Fin n.+1 <~> Fin m.+1
  := (fin_transpose_last_with m k)
       oE (e +E 1).

(** Here is the curried version that we will prove to be an equivalence. *)
Definition fin_equiv' (n m : nat)
: ((Fin m.+1) * (Fin n <~> Fin m)) -> (Fin n.+1 <~> Fin m.+1)
  := fun ke => fin_equiv n m (fst ke) (snd ke).

(** We construct its inverse and the two homotopies first as versions using homotopies without funext (similar to [ExtendableAlong]), then apply funext at the end. *)
Definition fin_equiv_hfiber (n m : nat) (e : Fin n.+1 <~> Fin m.+1)
: { kf : (Fin m.+1) * (Fin n <~> Fin m) & fin_equiv' n m kf == e }.
Proof.
  simpl in e.
  refine (equiv_sigma_prod _ _).
  recall (e (inr tt)) as y eqn:p.
  assert (p' := (moveL_equiv_V _ _ p)^).
  exists y.
  destruct y as [y|[]].
  + simple refine (equiv_unfunctor_sum_l
              (fin_transpose_last_with m (inl y) oE e)
              _ _ ; _).
    { intros a. ev_equiv.
      assert (q : inl y <> e (inl a))
        by exact (fun z => inl_ne_inr _ _ (equiv_inj e (z^ @ p^))).
      set (z := e (inl a)) in *.
      destruct z as [z|[]].
      - rewrite fin_transpose_last_with_rest;
        try exact tt; try assumption.
      - rewrite fin_transpose_last_with_last; exact tt. }
    { intros []. ev_equiv.
      rewrite p.
      rewrite fin_transpose_last_with_with; exact tt. }
    intros x. unfold fst, snd; ev_equiv. simpl.
    destruct x as [x|[]]; simpl.
    * rewrite unfunctor_sum_l_beta.
      apply fin_transpose_last_with_invol.
    * refine (fin_transpose_last_with_last _ _ @ p^).
  + simple refine (equiv_unfunctor_sum_l e _ _ ; _).
    { intros a.
      destruct (is_inl_or_is_inr (e (inl a))) as [l|r].
      - exact l.
      - assert (q := inr_un_inr (e (inl a)) r).
        apply moveR_equiv_V in q.
        assert (s := q^ @ ap (e^-1 o inr) (path_unit _ _) @ p').
        elim (inl_ne_inr _ _ s). }
    { intros []; exact (p^ # tt). }
    intros x. unfold fst, snd; ev_equiv. simpl.
    destruct x as [a|[]].
    * rewrite fin_transpose_last_with_last_other.
      apply unfunctor_sum_l_beta.
    * simpl.
      rewrite fin_transpose_last_with_last.
      symmetry; apply p.
Qed.

Definition fin_equiv_inv (n m : nat) (e : Fin n.+1 <~> Fin m.+1)
: (Fin m.+1) * (Fin n <~> Fin m)
  := (fin_equiv_hfiber n m e).1.

Definition fin_equiv_issect (n m : nat) (e : Fin n.+1 <~> Fin m.+1)
: fin_equiv' n m (fin_equiv_inv n m e) == e
  := (fin_equiv_hfiber n m e).2.

Definition fin_equiv_inj_fst (n m : nat)
           (k l : Fin m.+1) (e f : Fin n <~> Fin m)
: (fin_equiv n m k e == fin_equiv n m l f) -> (k = l).
Proof.
  intros p.
  refine (_ @ p (inr tt) @ _); simpl;
  rewrite fin_transpose_last_with_last; reflexivity.
Qed.

Definition fin_equiv_inj_snd (n m : nat)
           (k l : Fin m.+1) (e f : Fin n <~> Fin m)
: (fin_equiv n m k e == fin_equiv n m l f) -> (e == f).
Proof.
  intros p.
  intros x. assert (q := p (inr tt)); simpl in q.
  rewrite !fin_transpose_last_with_last in q.
  rewrite <- q in p; clear q l.
  exact (path_sum_inl _
           (equiv_inj (fin_transpose_last_with m k) (p (inl x)))).
Qed.

(** Now it's time for funext. *)
Global Instance isequiv_fin_equiv `{Funext} (n m : nat)
: IsEquiv (fin_equiv' n m).
Proof.
  refine (isequiv_pathsplit 0 _); split.
  - intros e; exists (fin_equiv_inv n m e).
    apply path_equiv, path_arrow, fin_equiv_issect.
  - intros [k e] [l f]; simpl.
    refine (_ , fun _ _ => tt).
    intros p; refine (_ ; path_ishprop _ _).
    apply (ap equiv_fun) in p.
    apply ap10 in p.
    apply path_prod'.
    + refine (fin_equiv_inj_fst n m k l e f p).
    + apply path_equiv, path_arrow.
      refine (fin_equiv_inj_snd n m k l e f p).
Qed.

Definition equiv_fin_equiv `{Funext} (n m : nat)
: ((Fin m.+1) * (Fin n <~> Fin m)) <~> (Fin n.+1 <~> Fin m.+1)
  := Build_Equiv _ _ (fin_equiv' n m) _.

(** In particular, this implies that if two canonical finite sets are equivalent, then their cardinalities are equal. *)
Definition nat_eq_fin_equiv (n m : nat)
: (Fin n <~> Fin m) -> (n = m).
Proof.
  revert m; induction n as [|n IHn]; induction m as [|m IHm]; intros e.
  - exact idpath.
  - elim (e^-1 (inr tt)).
  - elim (e (inr tt)).
  - refine (ap S (IHn m _)).
    exact (snd (fin_equiv_inv n m e)).
Qed.

(** ** Initial segments of [nat] *)

Definition nat_fin (n : nat) (k : Fin n) : nat.
Proof.
  induction n as [|n nf].
  - contradiction.
  - destruct k as [k|_].
    + exact (nf k).
    + exact n.
Defined.

Definition nat_fin_inl (n : nat) (k : Fin n)
: nat_fin n.+1 (inl k) = nat_fin n k
  := 1.

Definition nat_fin_compl (n : nat) (k : Fin n) : nat.
Proof.
  induction n as [|n nfc].
  - contradiction.
  - destruct k as [k|_].
    + exact (nfc k).+1.
    + exact 0.
Defined.

Definition nat_fin_compl_compl n k
: (nat_fin n k + nat_fin_compl n k).+1 = n.
Proof.
  induction n as [|n IH].
  - contradiction.
  - destruct k as [k|?]; simpl.
    + rewrite nat_add_comm.
      specialize (IH k).
      rewrite nat_add_comm in IH.
      exact (ap S IH).
    + rewrite nat_add_comm; reflexivity.
Qed.

(** [fsucc_mod] is the successor function mod n *)
Definition fsucc_mod {n : nat} : Fin n -> Fin n.
Proof.
  destruct n.
  1: exact idmap.
  intros [x|].
  - exact (fsucc x).
  - exact fin_zero.
Defined.

(** fsucc allows us to convert a natural number into an element of a finite set. This can be thought of as the modulo map. *)
Fixpoint fin_nat {n : nat} (m : nat) : Fin n.+1
  := match m with
      | 0 => fin_zero
      | S m => fsucc_mod (fin_nat m)
     end.

(** The 1-dimensional version of Sperner's lemma says that given any finite sequence of decidable hProps, where the sequence starts with true and ends with false, we can find a point in the sequence where the sequence changes from true to false. This is like a discrete intermediate value theorem. *)
Fixpoint sperners_lemma_1d {n} :
  forall (f : Fin (n.+2) -> DHProp)
         (left_true : f fin_zero)
         (right_false : ~ f fin_last),
    {k : Fin n.+1 & f (fin_incl k) /\ ~ f (fsucc k)}.
Proof.
  intros ???.
  destruct n as [|n].
  - exists fin_zero. split; assumption.
  - destruct (dec (f (fin_incl fin_last))) as [prev_true|prev_false].
    + exists fin_last. split; assumption.
    + destruct (sperners_lemma_1d _ (f o fin_incl) left_true prev_false) as [k' [fleft fright]].
      exists (fin_incl k').
      split; assumption.
Defined.
