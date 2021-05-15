Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.HSet
  HoTT.DProp
  HoTT.Spaces.Finite.Fin
  HoTT.Spaces.Finite.FinInduction
  HoTT.Spaces.Nat.

Local Open Scope nat_scope.

(** Finite-dimensional sequence. It is often referred to as vector,
    but we call it finite sequence [FinSeq] to avoid confusion with
    vector from linear algebra.

    Note that the induction principle [finseq_]*)

Definition FinSeq@{u} (n : nat) (A : Type@{u}) : Type@{u} := Fin n -> A.

(** The empty finite sequence. *)

Definition fsnil {A : Type} : FinSeq 0 A := Empty_rec.

Definition path_fsnil `{Funext} {A : Type} (v : FinSeq 0 A) : fsnil = v.
Proof.
  apply path_contr.
Defined.

(** Add an element in the end of a finite sequence, [fscons'] and [fscons]. *)

Definition fscons' {A : Type} (n : nat) (a : A) (v : FinSeq (pred n) A)
  : FinSeq n A
  := fun i =>  fin_rec (fun n => FinSeq (pred n) A -> A)
                       (fun _ _ => a) (fun n' i _ v => v i) i v.

Definition fscons {A : Type} {n : nat} : A -> FinSeq n A -> FinSeq n.+1 A
  := fscons' n.+1.

(** Take the first element of a non-empty finite sequence,
    [fshead'] and [fshead]. *)

Definition fshead' {A} (n : nat) : 0 < n -> FinSeq n A -> A
  := match n with
     | 0 => fun N _ => Empty_rec (not_lt_n_0 _ N)
     | n'.+1 => fun _ v => v fin_zero
     end.

Definition fshead {A} {n : nat} : FinSeq n.+1 A -> A := fshead' n.+1 _.

Definition compute_fshead' {A} n (N : n > 0) (a : A) (v : FinSeq (pred n) A)
  : fshead' n N (fscons' n a v) = a.
Proof.
  destruct n; [elim (not_lt_n_n _ N)|].
  exact (apD10 (compute_fin_rec_fin_zero _ _ _ _) v).
Defined.

Definition compute_fshead {A} {n} (a : A) (v : FinSeq n A)
  : fshead (fscons a v) = a.
Proof.
  apply compute_fshead'.
Defined.

(** If the sequence is non-empty, then remove the first element. *)

Definition fstail' {A} (n : nat) : FinSeq n A -> FinSeq (pred n) A
  := match n with
     | 0 => fun _ => Empty_rec
     | n'.+1 => fun v i => v (fsucc i)
     end.

(** Remove the first element from a non-empty sequence. *)

Definition fstail {A} {n : nat} : FinSeq n.+1 A -> FinSeq n A := fstail' n.+1.

Definition compute_fstail' {A} n (a : A) (v : FinSeq (pred n) A)
  : fstail' n (fscons' n a v) == v.
Proof.
  intro i.
  destruct n; [elim i|].
  exact (apD10 (compute_fin_rec_fsucc _ _ _ _) v).
Defined.

Definition compute_fstail `{Funext} {A} {n} (a : A) (v : FinSeq n A)
  : fstail (fscons a v) = v.
Proof.
  funext i.
  apply compute_fstail'.
Defined.

(** A non-empty finite sequence is equal to [fscons] of head and tail,
    [path_expand_fscons'] and [path_expand_fscons]. *)

Lemma path_expand_fscons' {A : Type} (n : nat)
  (i : Fin n) (N : n > 0) (v : FinSeq n A)
  : fscons' n (fshead' n N v) (fstail' n v) i = v i.
Proof.
  induction i using fin_ind.
  - apply compute_fshead.
  - apply (compute_fstail' n.+1 (fshead v) (fstail v)).
Defined.

Lemma path_expand_fscons `{Funext} {A} {n} (v : FinSeq n.+1 A)
  : fscons (fshead v) (fstail v) = v.
Proof.
  funext i.
  apply path_expand_fscons'.
Defined.

(** The following [path_fscons'] and [path_fscons] gives a way to construct
    a path between [fscons] finite sequences. They cooperate nicely with
    [path_expand_fscons'] and [path_expand_fscons]. *)

Definition path_fscons' {A} n {a1 a2 : A} {v1 v2 : FinSeq (pred n) A}
  (p : a1 = a2) (q : forall i, v1 i = v2 i) (i : Fin n)
  : fscons' n a1 v1 i = fscons' n a2 v2 i.
Proof.
  induction i using fin_ind.
  - exact (compute_fshead _ _ @ p @ (compute_fshead _ _)^).
  - refine (_ @ (compute_fstail' n.+1 a2 v2 i)^).
    exact (compute_fstail' n.+1 a1 v1 i @ q i).
Defined.

Definition compute_path_fscons' {A} (n : nat)
    (a : A) (v : FinSeq (pred n) A) (i : Fin n)
    : path_fscons' n (idpath a) (fun j => idpath (v j)) i = idpath.
Proof.
  induction i using fin_ind; unfold path_fscons'.
  - rewrite compute_fin_ind_fin_zero.
    refine (ap (fun p => p @ _) (concat_p1 _) @ _).
    apply concat_pV.
  - rewrite compute_fin_ind_fsucc.
    refine (ap (fun p => p @ _) (concat_p1 _) @ _).
    apply concat_pV.
Qed.

Definition path_fscons `{Funext} {A} {n} {a1 a2 : A} (p : a1 = a2)
  {v1 v2 : FinSeq n A} (q : v1 = v2)
  : fscons a1 v1 = fscons a2 v2.
Proof.
  funext i. apply path_fscons'.
  - assumption.
  - intro j. exact (apD10 q j).
Defined.

Lemma compute_path_fscons `{Funext} {A} {n} (a : A) (v : FinSeq n A)
  : path_fscons (idpath a) (idpath v) = idpath.
Proof.
  refine (ap (path_forall _ _) _ @ eta_path_forall _ _ _).
  funext i. exact (compute_path_fscons' n.+1 a v i).
Defined.

(** The lemmas [path_expand_fscons_fscons'] and [path_expand_fscons_fscons]
    identify [path_expand_fscons'] with [path_fscons'] and
    [path_expand_fscons] with [path_fscons]. *)

Lemma path_expand_fscons_fscons' {A : Type} (n : nat)
  (N : n > 0) (a : A) (v : FinSeq (pred n) A) (i : Fin n)
  : path_expand_fscons' n i N (fscons' n a v) =
    path_fscons' n (compute_fshead' n N a v) (compute_fstail' n a v) i.
Proof.
  induction i using fin_ind; unfold path_fscons', path_expand_fscons'.
  - do 2 rewrite compute_fin_ind_fin_zero.
    refine (_ @ concat_p_pp _ _ _).
    refine (_ @ (ap (fun p => _ @ p) (concat_pV _))^).
    exact (concat_p1 _)^.
  - do 2 rewrite compute_fin_ind_fsucc.
    refine (_ @ concat_p_pp _ _ _).
    refine (_ @ (ap (fun p => _ @ p) (concat_pV _))^).
    exact (concat_p1 _)^.
Qed.

Lemma path_expand_fscons_fscons `{Funext}
  {A : Type} {n : nat} (a : A) (v : FinSeq n A)
  : path_expand_fscons (fscons a v) =
    path_fscons (compute_fshead a v) (compute_fstail a v).
Proof.
  refine (ap (path_forall _ _) _).
  funext i.
  pose (p := eisretr apD10 (compute_fstail' n.+1 a v)).
  refine (_ @ (ap (fun f => _ f i) p)^).
  exact (path_expand_fscons_fscons' n.+1 _ a v i).
Defined.

(** The induction principle for finite sequence, [finseq_ind].
    Note that it uses funext and does not compute. *)

Lemma finseq_ind `{Funext} {A : Type} (P : forall n, FinSeq n A -> Type)
  (z : P 0 fsnil) (s : forall n a (v : FinSeq n A), P n v -> P n.+1 (fscons a v))
  {n : nat} (v : FinSeq n A)
  : P n v.
Proof.
  induction n.
  - exact (transport (P 0) (path_fsnil v) z).
  - refine (transport (P n.+1) (path_expand_fscons v) _).
    apply s. apply IHn.
Defined.

Lemma compute_finseq_ind_fsnil `{Funext} {A : Type}
  (P : forall n, FinSeq n A -> Type) (z : P 0 fsnil)
  (s : forall (n : nat) (a : A) (v : FinSeq n A), P n v -> P n.+1 (fscons a v))
  : finseq_ind P z s fsnil = z.
Proof.
  exact (ap (fun x => _ x z) (hset_path2 1 (path_fsnil fsnil)))^.
Defined.

Lemma compute_finseq_ind_fscons `{Funext} {A : Type}
  (P : forall n, FinSeq n A -> Type) (z : P 0 fsnil)
  (s : forall (n : nat) (a : A) (v : FinSeq n A), P n v -> P n.+1 (fscons a v))
  {n : nat} (a : A) (v : FinSeq n A)
  : finseq_ind P z s (fscons a v) = s n a v (finseq_ind P z s v).
Proof.
  simpl.
  induction (path_expand_fscons_fscons a v)^.
  set (p1 := compute_fshead a v).
  set (p2 := compute_fstail a v).
  induction p1, p2.
  exact (ap (fun p => transport _ p _) (compute_path_fscons _ _)).
Defined.

