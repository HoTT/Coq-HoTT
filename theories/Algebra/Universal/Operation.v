(** This file continues the development of algebra [Operation]. It
    gives a way to construct operations using (conventional) curried
    functions, and shows that such curried operations are equivalent
    to the uncurried operations [Operation]. *)

Require Export HoTT.Algebra.Universal.Algebra.

Require Import
  HoTT.Basics
  HoTT.Types
  HoTT.DProp
  HoTT.Spaces.Finite
  HoTT.Spaces.Nat
  HoTT.Spaces.Finite.FinSeq.

Import notations_algebra.

Local Open Scope nat_scope.

(** Functions [head_dom'] and [head_dom] are used to get the first
    element of a nonempty operation domain [a : forall i, A (ss i)]. *)

Monomorphic Definition head_dom' {σ} (A : Carriers σ) (n : nat)
  : forall (N : n > 0) (ss : FinSeq n (Sort σ)) (a : forall i, A (ss i)),
    A (fshead' n N ss)
  := match n with
     | 0 => fun N ss _ => Empty_rec (not_lt_n_n _ N)
     | n'.+1 => fun N ss a => a fin_zero
     end.

Monomorphic Definition head_dom {σ} (A : Carriers σ) {n : nat}
  (ss : FinSeq n.+1 (Sort σ)) (a : forall i, A (ss i))
  : A (fshead ss)
  := head_dom' A n.+1 _ ss a.

(** Functions [tail_dom'] and [tail_dom] are used to obtain the tail
    of an operation domain [a : forall i, A (ss i)]. *)

Monomorphic Definition tail_dom' {σ} (A : Carriers σ) (n : nat)
  : forall (ss : FinSeq n (Sort σ)) (a : forall i, A (ss i)) (i : Fin (pred n)),
    A (fstail' n ss i)
  := match n with
     | 0 => fun ss _ i => Empty_rec i
     | n'.+1 => fun ss a i => a (fsucc i)
     end.

Monomorphic Definition tail_dom {σ} (A : Carriers σ) {n : nat}
  (ss : FinSeq n.+1 (Sort σ)) (a : forall i, A (ss i))
  : forall i, A (fstail ss i)
  := tail_dom' A n.+1 ss a.

(** Functions [cons_dom'] and [cons_dom] to add an element to
    the front of a given domain [a : forall i, A (ss i)]. *)

Monomorphic Definition cons_dom' {σ} (A : Carriers σ) {n : nat}
  : forall (i : Fin n) (ss : FinSeq n (Sort σ)) (N : n > 0),
    A (fshead' n N ss) -> (forall i, A (fstail' n ss i)) -> A (ss i)
  := fin_ind
      (fun n i =>
        forall (ss : Fin n -> Sort σ) (N : n > 0),
        A (fshead' n N ss) -> (forall i, A (fstail' n ss i)) -> A (ss i))
      (fun n' _ z x _ => x)
      (fun n' i' _ => fun _ _ _ xs => xs i').

Definition cons_dom {σ} (A : Carriers σ)
  {n : nat} (ss : FinSeq n.+1 (Sort σ))
  (x : A (fshead ss)) (xs : forall i, A (fstail ss i))
  : forall i : Fin n.+1, A (ss i)
  := fun i => cons_dom' A i ss _ x xs.

(** The empty domain: *)

Definition nil_dom {σ} (A : Carriers σ) (ss : FinSeq 0 (Sort σ))
  : forall i : Fin 0, A (ss i)
  := Empty_ind (A o ss).

(** A specialization of [Operation] to finite [Fin n] arity. *)

Definition FiniteOperation {σ : Signature} (A : Carriers σ)
  {n : nat} (ss : FinSeq n (Sort σ)) (t : Sort σ) : Type
  := Operation A {| Arity := Fin n; sorts_dom := ss; sort_cod := t |}.

(** A type of curried operations
<<
CurriedOperation A [s1, ..., sn] t := A s1 -> ... -> A sn -> A t.
>> *)

Fixpoint CurriedOperation {σ} (A : Carriers σ) {n : nat}
  : (FinSeq n (Sort σ)) -> Sort σ -> Type
  := match n with
     | 0 => fun ss t => A t
     | n'.+1 =>
        fun ss t => A (fshead ss) -> CurriedOperation A (fstail ss) t
     end.

(** Function [operation_uncurry] is used to uncurry an operation
<<
operation_uncurry A [s1, ..., sn] t (op : CurriedOperation A [s1, ..., sn] t)
  : FiniteOperation A [s1, ..., sn] t
  := fun (x1 : A s1, ..., xn : A xn) => op x1 ... xn
>>
See [equiv_operation_curry] below. *)

Fixpoint operation_uncurry {σ} (A : Carriers σ) {n : nat}
  : forall (ss : FinSeq n (Sort σ)) (t : Sort σ),
    CurriedOperation A ss t -> FiniteOperation A ss t
  := match n with
     | 0 => fun ss t op _ => op
     | n'.+1 =>
        fun ss t op a =>
          operation_uncurry A (fstail ss) t (op (a fin_zero)) (a o fsucc)
     end.

Local Example computation_example_operation_uncurry
  : forall
      (σ : Signature) (A : Carriers σ) (n : nat) (s1 s2 t : Sort σ)
      (ss := (fscons s1 (fscons s2 fsnil)))
      (op : CurriedOperation A ss t) (a : forall i, A (ss i)),
    operation_uncurry A ss t op
    = fun a => op (a fin_zero) (a (fsucc fin_zero)).
Proof.
  reflexivity.
Qed.

(** Function [operation_curry] is used to curry an operation
<<
operation_curry A [s1, ..., sn] t (op : FiniteOperation A [s1, ..., sn] t)
  : CurriedOperation A [s1, ..., sn] t
  := fun (x1 : A s1) ... (xn : A xn) => op (x1, ..., xn)
>>
See [equiv_operation_curry] below. *)

Fixpoint operation_curry {σ} (A : Carriers σ) {n : nat} 
  : forall (ss : FinSeq n (Sort σ)) (t : Sort σ),
    FiniteOperation A ss t -> CurriedOperation A ss t
  := match n with
     | 0 => fun ss t op => op (Empty_ind _)
     | n'.+1 =>
        fun ss t op x =>
          operation_curry A (fstail ss) t (op o cons_dom A ss x)
     end.

Local Example computation_example_operation_curry
  : forall
      (σ : Signature) (A : Carriers σ) (n : nat) (s1 s2 t : Sort σ)
      (ss := (fscons s1 (fscons s2 fsnil)))
      (op : FiniteOperation A ss t)
      (x1 : A s1) (x2 : A s2),
    operation_curry A ss t op
    = fun x1 x2 => op (cons_dom A ss x1 (cons_dom A _ x2 (nil_dom A _))).
Proof.
  reflexivity.
Qed.

Lemma expand_cons_dom' {σ} (A : Carriers σ) (n : nat)
  : forall (i : Fin n) (ss : FinSeq n (Sort σ)) (N : n > 0)
           (a : forall i, A (ss i)),
    cons_dom' A i ss N (head_dom' A n N ss a) (tail_dom' A n ss a) = a i.
Proof.
  intro i.
  induction i using fin_ind; intros ss N a.
  - unfold cons_dom'.
    rewrite compute_fin_ind_fin_zero.
    reflexivity.
  - unfold cons_dom'.
    by rewrite compute_fin_ind_fsucc.
Qed.

Lemma expand_cons_dom `{Funext} {σ} (A : Carriers σ)
  {n : nat} (ss : FinSeq n.+1 (Sort σ)) (a : forall i, A (ss i))
  : cons_dom A ss (head_dom A ss a) (tail_dom A ss a) = a.
Proof.
  funext i.
  apply expand_cons_dom'.
Defined.

Lemma path_operation_curry_to_cunurry `{Funext} {σ} (A : Carriers σ)
  {n : nat} (ss : FinSeq n (Sort σ)) (t : Sort σ)
  : operation_uncurry A ss t o operation_curry A ss t == idmap.
Proof.
  intro a.
  induction n as [| n IHn].
  - funext d. refine (ap a _). apply path_contr.
  - funext a'.
    refine (ap (fun x => x _) (IHn _ _) @ _).
    refine (ap a _).
    apply expand_cons_dom.
Qed.

Lemma path_operation_uncurry_to_curry `{Funext} {σ} (A : Carriers σ)
  {n : nat} (ss : FinSeq n (Sort σ)) (t : Sort σ)
  : operation_curry A ss t o operation_uncurry A ss t == idmap.
Proof.
  intro a.
  induction n; [reflexivity|].
  funext x.
  refine (_ @ IHn (fstail ss) (a x)).
  refine (ap (operation_curry A (fstail ss) t) _).
  funext a'.
  simpl.
  unfold cons_dom, cons_dom'.
  rewrite compute_fin_ind_fin_zero.
  refine (ap (operation_uncurry A (fstail ss) t (a x)) _).
  funext i'.
  now rewrite compute_fin_ind_fsucc.
Qed.

Global Instance isequiv_operation_curry `{Funext} {σ} (A : Carriers σ)
  {n : nat} (ss : FinSeq n (Sort σ)) (t : Sort σ)
  : IsEquiv (operation_curry A ss t).
Proof.
  srapply isequiv_adjointify.
  - apply operation_uncurry.
  - apply path_operation_uncurry_to_curry.
  - apply path_operation_curry_to_cunurry.
Defined.

Definition equiv_operation_curry `{Funext} {σ} (A : Carriers σ)
  {n : nat} (ss : FinSeq n (Sort σ)) (t : Sort σ)
  : FiniteOperation A ss t <~> CurriedOperation A ss t
  := Build_Equiv _ _ (operation_curry A ss t) _.

