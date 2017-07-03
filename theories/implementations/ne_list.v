(** This module should be [Require]d but not [Import]ed (except for the notations submodule). *)

Require Import HoTTClasses.misc.stdlib_hints.
Require Export HoTT.Basics.Overture.

Section contents.
  Context {T: Type}.

  Inductive L: Type := one: T -> L | cons: T -> L -> L.

  Fixpoint app (a b: L) {struct a}: L :=
    match a with
    | one x => cons x b
    | cons x y => cons x (app y b)
    end.

  Fixpoint foldr {R} (i: T -> R) (f: T -> R -> R) (a: L): R :=
    match a with
    | one x => i x
    | cons x y => f x (foldr i f y)
    end.

  Fixpoint foldr1 (f: T -> T -> T) (a: L): T :=
    match a with
    | one x => x
    | cons x y => f x (foldr1 f y)
    end.

  Definition head (l: L): T := match l with one x => x | cons x _ => x end.

  Fixpoint to_list (l: L): list T :=
    match l with
    | one x => x :: nil
    | cons x xs => x :: to_list xs
    end.

  Global Coercion to_list: L >-> list.

  Fixpoint from_list (x: T) (xs: list T): L :=
    match xs with
    | nil => one x
    | Datatypes.cons h t => cons x (from_list h t)
    end.

  Definition tail (l: L): list T := match l with one _ => nil | cons _ x => to_list x end.

  Lemma decomp_eq (l: L): l = from_list (head l) (tail l).
  Proof with auto.
    induction l...
    destruct l...
    simpl in *.
    rewrite IHl...
  Qed.  

  Definition last: L -> T := foldr1 (fun x y => y).

  Fixpoint replicate_Sn (x: T) (n: nat): L :=
    match n with
    | 0 => one x
    | S n' => cons x (replicate_Sn x n')
    end.

  Fixpoint take (n: nat) (l: L): L :=
    match l, n with
    | cons x xs, S n' => take n' xs
    | _, _ => one (head l)
    end.

  Lemma two_level_rect (P: L -> Type)
    (Pone: forall x, P (one x))
    (Ptwo: forall x y, P (cons x (one y)))
    (Pmore: forall x y z, P z -> (forall y', P (cons y' z)) -> P (cons x (cons y z))):
      forall l, P l.
  Proof with auto.
   cut (forall l, P l * forall x, P (cons x l)).
    intros. apply X.
   destruct l...
   revert t.
   induction l...
   intros.
   split. apply IHl.
   intro.
   apply Pmore; intros; apply IHl.
  Qed.

(*   Lemma tl_length (l: L): S (length (tl l)) = length l.
  Proof. destruct l; reflexivity. Qed.

  Notation ListPermutation := (@Permutation.Permutation _).

  Definition Permutation (x y: L): Prop := ListPermutation x y.

  Global Instance: Equivalence Permutation.
  Proof with intuition.
   unfold Permutation.
   split; repeat intro...
   transitivity y...
  Qed.

  Global Instance: Proper (Permutation ==> ListPermutation) to_list.
  Proof. firstorder. Qed.

  Lemma Permutation_ne_tl_length (x y: L):
    Permutation x y -> length (tl x) = length (tl y).
  Proof.
   intro H.
   apply eq_add_S.
   do 2 rewrite tl_length.
   rewrite H.
   reflexivity.
  Qed. *)
End contents.

Arguments L : clear implicits.

Fixpoint tails {A} (l: L A): L (L A) :=
  match l with
  | one x => one (one x)
  | cons x y => cons l (tails y)
  end.
(* 
Lemma tails_are_shorter {A} (y x: L A):
  In x (tails y) ->
  length x <= length y.
Proof with auto.
 induction y; simpl.
  intros [[] | ?]; intuition.
 intros [[] | C]...
Qed.
 *)
Fixpoint map {A B} (f: A -> B) (l: L A): L B :=
  match l with
  | one x => one (f x)
  | cons h t => cons (f h) (map f t)
  end.

(* Lemma list_map {A B} (f: A -> B) (l: L A): to_list (map f l) = List.map f (to_list l).
Proof. induction l. reflexivity. simpl. congruence. Qed.
 *)
(* Global Instance: forall {A B} (f: A -> B), Proper (Permutation ==> Permutation) (map f).
Proof with auto.
 intros ????? E.
 unfold Permutation.
 do 2 rewrite list_map.
 rewrite E.
 reflexivity.
Qed.
 *)
Fixpoint inits {A} (l: L A): L (L A) :=
  match l with
  | one x => one (one x)
  | cons h t => cons (one h) (map (cons h) (inits t))
  end.

Module notations.
  Global Notation ne_list := L.
  Global Infix ":::" := cons (at level 60, right associativity).
    (* Todo: Try to get that "[ x ; .. ; y ]" notation working. *)

  Fixpoint ne_zip {A B: Type} (l: ne_list A) (m: ne_list B) {struct l} : ne_list (A * B) :=
    match l with
    | one a => one (a, head m)
    | a ::: l =>
        match m with
        | one b => one (a, b)
        | b ::: m => (a, b) ::: ne_zip l m
        end
    end.
End notations.
