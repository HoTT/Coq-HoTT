From HoTT Require Import Basics.
Require Import Nat.Core.
Require Import Spaces.Int.
Require Import Spaces.Finite.Fin.
Require Import WildCat.Core.

Local Set Universe Minimization ToSet.

(** * Successor Structures. *)

(** A successor structure is just a type with a endofunctor on it, called 'successor'. Typical examples include either the integers or natural numbers with the successor (or predecessor) operation. *)

Record SuccStr : Type := {
   ss_carrier :> Type ;
   ss_succ : ss_carrier -> ss_carrier ;
}.

Declare Scope succ_scope.

Local Open Scope nat_scope.
Local Open Scope type_scope.
Local Open Scope succ_scope.

Delimit Scope succ_scope with succ.
Arguments ss_succ {_} _.

Notation "x .+1" := (ss_succ x) : succ_scope.

(** Successor structure of naturals *)
Definition NatSucc : SuccStr := Build_SuccStr nat nat_succ.

(** Successor structure of integers *)
Definition BinIntSucc : SuccStr := Build_SuccStr Int int_succ.

Notation "'+N'" := NatSucc : succ_scope.
Notation "'+Z'" := BinIntSucc : succ_scope.

(** Stratified successor structures *)

(** If [N] has a successor structure, then so does the product [N * Fin n].  The successor operation increases the second factor, and if it wraps around, it also increases the first factor. *)

Definition StratifiedType (N : SuccStr) (n : nat) := N * Fin n.

Definition stratified_succ (N : SuccStr) (n : nat) (x : StratifiedType N n)
  : StratifiedType N n.
Proof.
  constructor.
  + destruct n.
    - exact (Empty_rec _ (snd x)).
    - destruct (dec (snd x = inr tt)).
      * exact (ss_succ (fst x)).
      * exact (fst x).
  + exact (fsucc_mod (snd x)).
Defined.

Definition Stratified (N : SuccStr) (n : nat) : SuccStr
  := Build_SuccStr (StratifiedType N n) (stratified_succ N n).

(** Addition in successor structures *)
Definition ss_add {N : SuccStr} (n : N) (k : nat) : N := nat_iter k ss_succ n.

Infix "+" := ss_add : succ_scope.

Definition ss_add_succ {N : SuccStr} (n : N) (k : nat)
  : n + k.+1 = n.+1 + k
  := nat_iter_succ_r k ss_succ n.

Definition ss_add_sum {N : SuccStr} (n : N) (k l : nat)
  : n + (k + l) = (n + l) + k
  := nat_iter_add k l ss_succ n.

(** Nat and Int segmented by triples *)
Notation "'N3'" := (Stratified (+N) 3) : succ_scope.
Notation "'Z3'" := (Stratified (+Z) 3) : succ_scope.

(** ** Category of successor structures *)

(** Inspired by the construction of the wildcat structure on [pType], we can give [SuccStr] a wildcat structure in a similar manner (all the way up). *)

Record ssFam (A : SuccStr) := {
  ss_fam :> A -> Type;
  dss_succ {x} : ss_fam x -> ss_fam (x.+1);
}.
  
Arguments ss_fam {_ _} _.
Arguments dss_succ {_ _ _}.

Record ssForall {A : SuccStr} (B : ssFam A) := {
  ss_fun :> forall x, B x;
  ss_fun_succ : forall x, ss_fun x.+1 = dss_succ (ss_fun x); 
}.

Arguments ss_fun {_ _} _ _.
Arguments ss_fun_succ {_ _} _ _.

Definition ssfam_const {A : SuccStr} (B : SuccStr) : ssFam A
  := Build_ssFam A (fun _ => B) (fun _ => ss_succ).

Definition ssfam_sshomotopy {A : SuccStr} {P : ssFam A} (f g : ssForall P)
  : ssFam A.
Proof.
  snapply Build_ssFam.
  1: exact (fun x => f x = g x).
  cbn; intros x p.
  exact (ss_fun_succ f x @ ap dss_succ p @ (ss_fun_succ g x)^).
Defined.

Definition ssHomotopy {A : SuccStr} {P : ssFam A} (f g : ssForall P)
  := ssForall (ssfam_sshomotopy f g).

Instance isgraph_ss : IsGraph SuccStr.
Proof.
  snapply Build_IsGraph.
  intros X Y.
  exact (@ssForall X (ssfam_const Y)).
Defined.

Instance isgraph_ssforall {A : SuccStr} (P : ssFam A)
  : IsGraph (ssForall P).
Proof.
  snapply Build_IsGraph.
  exact ssHomotopy.
Defined.

Instance is2graph_ssforall {A : SuccStr} (P : ssFam A)
  : Is2Graph (ssForall P)
  := {}.

Instance is2graph_ss : Is2Graph SuccStr := {}.
Instance is3graph_ss : Is3Graph SuccStr := {}.

Ltac sselim_elim eq x :=
  match type of (eq x) with
  | ?lhs = _ =>
    generalize dependent (eq x);
    generalize dependent lhs
  | _ => fail "sselim: no lhs found"
  end.

Ltac sselim f :=
  let eq := fresh "eq" in
  destruct f as [f eq];
  cbn in *;
  match type of eq with
  | forall x : ?X, _ = _ =>
    multimatch goal with
    | x : X |- _ => sselim_elim eq x
    | f : ?Y -> X |- _ =>
      match goal with
      | y : Y |- _ => sselim_elim eq (f y)
      | g : ?Z -> Y |- _ =>
        match goal with
        | z : Z |- _ => sselim_elim eq (f (g z))
        end
      end
    | _ => fail "sselim: no hyp found"
    end
  | _ => fail "sselim: no eq found"
  end;  
  napply paths_ind_r;
  try clear eq;
  try clear f.

Tactic Notation "sselim" constr(x0) := sselim x0.
Tactic Notation "sselim" constr(x0) constr(x1) := sselim x0; sselim x1.
Tactic Notation "sselim" constr(x0) constr(x1) constr(x2) := sselim x0; sselim x1 x2.
Tactic Notation "sselim" constr(x0) constr(x1) constr(x2) constr(x3) := sselim x0; sselim x1 x2 x3.
Tactic Notation "sselim" constr(x0) constr(x1) constr(x2) constr(x3) constr(x4) := sselim x0; sselim x1 x2 x3 x4.
Tactic Notation "sselim" constr(x0) constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) := sselim x0; sselim x1 x2 x3 x4 x5.
Tactic Notation "sselim" constr(x0) constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) constr(x6) := sselim x0; sselim x1 x2 x3 x4 x5 x6.

Instance is01cat_ss : Is01Cat SuccStr.
Proof.
  snapply Build_Is01Cat.
  - intro X.
    snapply Build_ssForall.
    + exact (fun x => x).
    + reflexivity.
  - intros X Y Z f g.
    snapply Build_ssForall.
    + intro x.
      exact (f (g x)).
    + intro x.
      exact (ap f (ss_fun_succ g x) @ ss_fun_succ f (g x)).
Defined.

Instance is01cat_ssforall {A : SuccStr} (P : ssFam A)
  : Is01Cat (ssForall P).
Proof.
  snapply Build_Is01Cat.
  - intro f.
    snapply Build_ssForall.
    + reflexivity.
    + intro x; simpl.
      by destruct (ss_fun_succ f x).
  - intros f g h p q.
    snapply Build_ssForall.
    + intro x.
      exact (q x @ p x).
    + intro x; cbn.
      sselim p q f g h. simpl.
      by destruct (p x), (q x).
Defined.

Instance is0gpd_ssforall {A : SuccStr} (P : ssFam A)
  : Is0Gpd (ssForall P).
Proof.
  snapply Build_Is0Gpd.
  intros f g p.
  snapply Build_ssForall.
  - intro x.
    exact (p x)^.
  - intro x; cbn.
    sselim p f g.
    by destruct (p x).
Defined.

Instance is1cat_ss : Is1Cat SuccStr.
Proof.
  snapply Build_Is1Cat'.
  1,2: exact _.
  - intros X Y Z g.
    snapply Build_Is0Functor.
    intros f h p.
    snapply Build_ssForall.
    + intro x.
      exact (ap g (p x)).
    + intro x; cbn.
      sselim p f h.
      destruct (p x); clear p; simpl.
      sselim g.
      by destruct (eq (f x)).
  - intros X Y Z g.
    snapply Build_Is0Functor.
    intros f h q.
    snapply Build_ssForall.
    + intros x.
      apply q.
    + intros x; cbn.
      by sselim g q f h.
  - intros X Y Z W f g h.
    srapply Build_ssForall.
    + intro x.
      reflexivity.
    + intro x; cbn.
      by sselim f g h.
  - intros X Y f.
    srapply Build_ssForall.
    1: reflexivity.
    intros x.
    by sselim f.
  - intros X Y f.
    srapply Build_ssForall.
    1: reflexivity.
    intros x.
    by sselim f.
Defined.
