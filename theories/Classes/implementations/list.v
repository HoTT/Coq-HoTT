Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Types.Unit HoTT.Types.Prod.

Generalizable Variables A B C.

Open Scope list_scope.

(** Standard notations for lists. 
In a special module to avoid conflicts. *)
Module ListNotations.
Notation " [] " := nil : list_scope.
Notation " [ x ] " := (cons x nil) : list_scope.
Notation " [ x ; y ; .. ; z ] " :=  (cons x (cons y .. (cons z nil) ..))
  : list_scope.
End ListNotations.

Import ListNotations.

Fixpoint length {A} (l : list A) := match l with
  | [] => O
  | _ :: l => S (length l)
  end.

Fixpoint fold_left {A B} (f : A -> B -> A) (acc : A) (l : list B) :=
  match l with
  | [] => acc
  | x :: l => fold_left f (f acc x) l
  end.

Fixpoint map {A B} (f : A -> B) (l : list A) :=
  match l with
  | [] => []
  | x :: l => (f x) :: (map f l)
  end.

Fixpoint map2 `(f : A -> B -> C)
  (def_l : list A -> list C) (def_r : list B -> list C)
  l1 l2 :=
  match l1, l2 with
  | [], [] => []
  | [], _ => def_r l2
  | _, [] => def_l l1
  | x :: l1, y :: l2 => (f x y) :: (map2 f def_l def_r l1 l2)
  end.

Lemma map2_cons `(f : A -> B -> C) defl defr x l1 y l2 :
  map2 f defl defr (x::l1) (y::l2) = (f x y) :: map2 f defl defr l1 l2.
Proof.
reflexivity.
Qed.

Lemma map_id `(f : A -> A) (Hf : forall x, f x = x) (l : list A) : map f l = l.
Proof.
induction l as [|x l IHl].
- reflexivity.
- simpl. rewrite Hf,IHl. reflexivity.
Qed.

Instance sg_op_app A : SgOp (list A) := @app A.

Instance app_assoc A : Associative (@app A).
Proof.
intros l1. induction l1 as [|x l1 IH];intros l2 l3.
- reflexivity.
- simpl;apply ap;apply IH.
Qed.

Fixpoint for_all {A} (P : A -> Type) l : Type :=
  match l with
  | [] => Unit
  | x :: l => P x /\ for_all P l
  end.

Lemma for_all_trivial {A} (P : A -> Type) : (forall x, P x) ->
  forall l, for_all P l.
Proof.
intros HP l;induction l as [|x l IHl];split;auto.
Qed.

Lemma for_all_map {A B} P Q (f : A -> B) (Hf : forall x, P x -> Q (f x))
 : forall l, for_all P l -> for_all Q (map f l).
Proof.
intros l;induction l as [|x l IHl];simpl.
- auto.
- intros [Hx Hl]. split;auto.
Defined.

Lemma for_all_map2 {A B C} P Q R
  `(f : A -> B -> C) (Hf : forall x y, P x -> Q y -> R (f x y))
  def_l (Hdefl : forall l1, for_all P l1 -> for_all R (def_l l1))
  def_r (Hdefr : forall l2, for_all Q l2 -> for_all R (def_r l2))
  : forall l1 l2, for_all P l1 -> for_all Q l2 ->
    for_all R (map2 f def_l def_r l1 l2).
Proof.
intros l1;induction l1 as [|x l1 IHl1].
- simpl. intros [|y l2] _; auto.
- simpl. intros [|y l2] [Hx Hl1];[intros _|intros [Hy Hl2]];simpl;auto.
  apply Hdefl. simpl;auto.
Qed.

Lemma fold_preserves {A B} P Q (f : A -> B -> A)
  (Hf : forall x y, P x -> Q y -> P (f x y))
  : forall acc (Ha : P acc) l (Hl : for_all Q l), P (fold_left f acc l).
Proof.
intros acc Ha l Hl;revert l Hl acc Ha.
intros l;induction l as [|x l IHl].
- intros _ acc Ha. exact Ha.
- simpl. intros [Hx Hl] acc Ha.
  apply IHl;auto.
Qed.

Instance for_all_trunc {A} {n} (P : A -> Type) : forall l,
  for_all (fun x => IsTrunc n (P x)) l -> IsTrunc n (for_all P l).
Proof.
intros l;induction l as [|x l IHl];simpl.
- intros _. destruct n;apply _.
- intros [Hx Hl].
  apply IHl in Hl. apply _.
Qed.

(* Copy pasted from the Coq library. *)
Definition tl {A} (l:list A) : list A :=
  match l with
    | [] => nil
    | a :: m => m
  end.

(* Modified copy from the Coq library. *)
(** The "In list" predicate *)
Fixpoint InList {A} (a:A) (l:list A) : Type0 :=
  match l with
    | [] => False
    | b :: m => b = a |_| InList a m
  end.

Fixpoint fold_right {A} {B} (f : B -> A -> A) (x : A) (l : list B) : A :=
  match l with
    | nil => x
    | cons b t => f b (fold_right f x t)
  end.
