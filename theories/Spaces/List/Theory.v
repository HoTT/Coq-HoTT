Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Trunc
  Basics.Equivalences Basics.Decidable Basics.Iff.
Require Import Types.Paths Types.Unit Types.Prod Types.Sigma Types.Sum
  Types.Empty Types.Option.
Require Export Spaces.List.Core Spaces.Nat.Core.

Local Set Universe Minimization ToSet.
Local Set Polymorphic Inductive Cumulativity.

(** * Theory of Lists and List Operations *)

(** In this file we collect lemmas about lists and their operations. We don't include those in [List.Core] so that file can stay lightweight on dependencies. *)

(** We generally try to keep the order the same as the concepts appeared in [List.Core]. *)

Local Open Scope list_scope.
Local Open Scope nat_scope.
Local Open Scope type_scope.

(** ** Length *)

(** A list of length zero must be the empty list. *)
Definition length_0 {A : Type} (l : list A) (H : length l = 0%nat)
  : l = nil.
Proof.
  destruct l.
  - reflexivity.
  - discriminate.
Defined.

(** ** Concatenation *)

(** Concatenating the empty list on the right is the identity. *)
Definition app_nil {A : Type} (l : list A)
  : l ++ nil = l.
Proof.
  induction l as [|a l IHl].
  1: reflexivity.
  simpl; f_ap.
Defined.

(** Associativity of list concatenation. *)
Definition app_assoc {A : Type} (x y z : list A)
  : app x (app y z) = app (app x y) z.
Proof.
  induction x as [|a x IHx] in |- *.
  - reflexivity.
  - exact (ap (cons a) IHx).
Defined.

(** The type of lists has a monoidal structure given by concatenation. *)
Definition list_pentagon {A : Type} (w x y z : list A)
  : app_assoc w x (y ++ z) @ app_assoc (w ++ x) y z
    = ap (fun l => w ++ l) (app_assoc x y z)
    @ app_assoc w (x ++ y) z
    @ ap (fun l => l ++ z) (app_assoc w x y).
Proof.
  symmetry.
  induction w as [|? w IHw] in x, y, z |- *.
  - simpl.
    apply equiv_p1_1q.
    lhs nrapply concat_p1.
    apply ap_idmap.
  - simpl.
    rhs_V nrapply ap_pp.
    rhs_V nrapply (ap (ap (cons a)) (IHw x y z)).
    rhs nrapply ap_pp.
    f_ap.
    { rhs nrapply ap_pp.
      f_ap.
      apply ap_compose. }
    lhs_V nrapply ap_compose.
    nrapply (ap_compose (fun l => l ++ z)).
Defined.

(** The length of a concatenated list is the sum of the lengths of the two lists. *)
Definition length_app {A : Type} (l l' : list A)
  : length (l ++ l') = (length l + length l')%nat.
Proof.
  induction l as [|a l IHl] using list_ind.
  1: reflexivity.
  simpl.
  exact (ap S IHl).
Defined.

(** An element of a concatenated list is equivalently either in the first list or in the second list. *)
Definition equiv_inlist_app {A : Type} (l l' : list A) (x : A)
  : InList x l + InList x l' <~> InList x (l ++ l').
Proof.
  induction l as [|a l IHl].
  - apply sum_empty_l.
  - cbn; nrefine (_ oE equiv_sum_assoc _ _ _).
    by apply equiv_functor_sum_l.
Defined.

(** ** Folding *)

(** A left fold over a concatenated list is equivalent to folding over the first followed by folding over the second. *)
Lemma fold_left_app {A B : Type} (f : A -> B -> A) (l l' : list B) (i : A)
  : fold_left f (l ++ l') i = fold_left f l' (fold_left f l i).
Proof.
  induction l in i |- *.
  1: reflexivity.
  apply IHl.
Defined.

(** A right fold over a concatenated list is equivalent to folding over the second followed by folding over the first. *)
Lemma fold_right_app {A B : Type} (f : B -> A -> A) (i : A) (l l' : list B)
  : fold_right f i (l ++ l') = fold_right f (fold_right f i l') l.
Proof.
  induction l in i |- *.
  1: reflexivity.
  exact (ap (f a) (IHl _)).
Defined.

(** ** Maps *)

(** The length of a mapped list is the same as the length of the original list. *)
Definition length_list_map {A B : Type} (f : A -> B) (l : list A)
  : length (list_map f l) = length l.
Proof.
  induction l as [|x l IHl] using list_ind.
  - reflexivity.
  - simpl.
    exact (ap S IHl).
Defined.

(** A function applied to an element of a list is an element of the mapped list. *)
Definition inlist_map {A B : Type} (f : A -> B) (l : list A) (x : A)
  : InList x l -> InList (f x) (list_map f l).
Proof.
  simple_list_induction l y l IHl.
  1: contradiction.
  intros [p | i].
  - left.  exact (ap f p).
  - right. exact (IHl i).
Defined.

(** An element of a mapped list is equal to the function applied to some element of the original list. *)
Definition inlist_map' {A B : Type} (f : A -> B) (l : list A) (x : B)
  : InList x (list_map f l) -> { y : A & (f y = x) * InList y l }.
Proof.
  induction l as [|y l IHl].
  1: contradiction.
  intros [p | i].
  - exact (y; (p, inl idpath)).
  - destruct (IHl i) as [y' [p i']].
    exact (y'; (p, inr i')).
Defined.

(** Mapping a function over a concatenated list is the concatenation of the mapped lists. *)
Definition list_map_app {A B : Type} (f : A -> B) (l l' : list A)
  : list_map f (l ++ l') = list_map f l ++ list_map f l'.
Proof.
  induction l as [|a l IHl].
  1: reflexivity.
  simpl; f_ap.
Defined.

(** A function that acts as the identity on the elements of a list is the identity on the mapped list. *)
Lemma list_map_id {A : Type} (f : A -> A) (l : list A)
  (Hf : forall x, InList x l -> f x = x)
  :  list_map f l = l.
Proof.
  induction l as [|x l IHl].
  - reflexivity.
  - simpl.
    nrapply ap011.
    + exact (Hf _ (inl idpath)).
    + apply IHl.
      intros y Hy.
      apply Hf.
      by right.
Defined.

(** A [list_map] of a composition is the composition of the maps. *)
Definition list_map_compose {A B C} (f : A -> B) (g : B -> C) (l : list A)
  : list_map (fun x => g (f x)) l = list_map g (list_map f l).
Proof.
  induction l as [|a l IHl].
  1: reflexivity.
  simpl; f_ap.
Defined.

(** TODO: generalize as max *)
(** The length of a [list_map2] is the same as the length of the original lists. *)
Definition length_list_map2@{i j k|} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  (f : A -> B -> C) defl defr l1 l2
  : length l1 = length l2
    -> length (list_map2 f defl defr l1 l2) = length l1.
Proof.
  intros p.
  induction l1 as [|x l1 IHl1] in l2, p |- * using list_ind@{i j}.
  - destruct l2.
    + reflexivity.
    + inversion p.
  - destruct l2.
    + inversion p.
    + cbn; f_ap.
      by apply IHl1, path_nat_succ.
Defined.

(** An element of a [list_map2] is the result of applying the function to some elements of the original lists. *)
Definition inlist_map2@{i j k u | i <= u, j <= u, k <= u}
  {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  (f : A -> B -> C) defl defr l1 l2 x
  : InList x (list_map2 f defl defr l1 l2) -> length l1 = length l2
    -> { y : A & { z : B &
                        prod@{k u} ((f y z) = x) (InList y l1 * InList z l2) } }.
Proof.
  intros H p.
  induction l1 as [|y l1 IHl1] in l2, x, H, p |- * using list_ind@{i u}.
  - destruct l2.
    1: contradiction.
    inversion p.
  - destruct l2 as [| z].
    1: inversion p.
    destruct H as [q | i].
    1: exact (y; z; (q, (inl idpath, inl idpath))).
    destruct (IHl1 l2 x i) as [y' [z' [q [r s]]]].
    1: apply path_nat_succ, p.
    exact (y'; z'; (q, (inr r, inr s))).
Defined.

(** [list_map2] is a [list_map] if the first list is a repeated value. *)
Definition list_map2_repeat_l {A B C} (f : A -> B -> C) (x : A) l {defl defr}
  : list_map2 f defl defr (repeat x (length l)) l = list_map (f x) l.
Proof.
  induction l as [|y l IHl].
  - reflexivity.
  - cbn; f_ap.
Defined.

(** [list_map2] is a [list_map] if the second list is a repeated value. *)
Definition list_map2_repeat_r {A B C} (f : A -> B -> C) (y : B) l {defl defr}
  : list_map2 f defl defr l (repeat y (length l)) = list_map (fun x => f x y) l.
Proof.
  induction l as [|x l IHl].
  - reflexivity.
  - cbn; f_ap.
Defined.

(** ** Reversal *)

(** The length of [reverse_acc] is the sum of the lengths of the two lists. *)
Definition length_reverse_acc@{i|} {A : Type@{i}} (acc l : list A)
  : length (reverse_acc acc l) = (length acc + length l)%nat.
Proof.
  symmetry.
  induction l as [|x l IHl] in acc |- * using list_ind@{i i}.
  - apply nat_add_zero_r.
  - rhs_V nrapply IHl.
    apply nat_add_succ_r.
Defined.

(** The length of [reverse] is the same as the length of the original list. *)
Definition length_reverse {A : Type} (l : list A)
  : length (reverse l) = length l.
Proof.
  rapply length_reverse_acc.
Defined.

(** The [list_map] of a [reverse_acc] is the [reverse_acc] of the [list_map] of the two lists. *)
Definition list_map_reverse_acc {A B : Type}
  (f : A -> B) (l l' : list A)
  : list_map f (reverse_acc l' l) = reverse_acc (list_map f l') (list_map f l).
Proof.
  revert l'; simple_list_induction l a l IHl; intro l'.
  1: reflexivity.
  apply IHl.
Defined.

(** The [list_map] of a reversed list is the reversed [list_map]. *)
Definition list_map_reverse {A B} (f : A -> B) (l : list A)
  : list_map f (reverse l) = reverse (list_map f l).
Proof.
  nrapply list_map_reverse_acc.
Defined.

(** [reverse_acc] is the same as concatenating the reversed list with the accumulator. *)
Definition reverse_acc_cons {A : Type} (l l' : list A)
  : reverse_acc l' l = reverse l ++ l'.
Proof.
  induction l as [|a l IHl] in l' |- *.
  1: reflexivity.
  lhs nrapply IHl.
  lhs nrapply (app_assoc _ [a]).
  f_ap; symmetry.
  apply IHl.
Defined.

(** The [reverse] of a [cons] is the concatenation of the [reverse] with the head. *) 
Definition reverse_cons {A : Type} (a : A) (l : list A)
  : reverse (a :: l) = reverse l ++ [a].
Proof.
  induction l as [|b l IHl] in a |- *.
  1: reflexivity.
  rewrite IHl.
  rewrite <- app_assoc.
  cbn; apply reverse_acc_cons.
Defined.

(** The [reverse] of a concatenated list is the concatenation of the reversed lists in reverse order. *)
Definition reverse_app {A : Type} (l l' : list A)
  : reverse (l ++ l') = reverse l' ++ reverse l.
Proof.
  induction l as [|a l IHl] in l' |- *.
  1: symmetry; apply app_nil.
  simpl.
  lhs nrapply reverse_cons.
  rhs nrapply ap.
  2: nrapply reverse_cons.
  rhs nrapply app_assoc.
  nrapply (ap (fun l => l ++ [a])).
  exact (IHl l').
Defined.

(** [reverse] is involutive. *)
Definition reverse_reverse {A : Type} (l : list A)
  : reverse (reverse l) = l.
Proof.
  induction l.
  1: reflexivity.
  lhs nrapply ap.
  1: nrapply reverse_cons.
  lhs nrapply reverse_app.
  exact (ap _ IHl).
Defined.

(** ** Getting elements *)

(** A variant of [nth] that returns an element of the list and a proof that it is the [n]-th element. *)
Definition nth_lt@{i|} {A : Type@{i}} (l : list A) (n : nat)
  (H : (n < length l)%nat)
  : { x : A & nth l n = Some x }.
Proof.
  induction l as [|a l IHa] in n, H |- * using list_ind@{i i}.
  1: destruct (not_lt_zero_r _ H).
  destruct n.
  1: by exists a.
  apply IHa.
  apply leq_pred'.
  exact H.
Defined.

(** A variant of [nth] that always returns an element when we know that the index is in the list. *)
Definition nth' {A : Type} (l : list A) (n : nat) (H : (n < length l)%nat) : A
  := pr1 (nth_lt l n H).

(** The [nth'] element doesn't depend on the proof that [n < length l]. *)
Definition nth'_nth' {A} (l : list A) (n : nat) (H H' : (n < length l)%nat)
  : nth' l n H = nth' l n H'.
Proof.
  apply ap, path_ishprop.
Defined.

(** Two equal lists have the same elements in the same positions. *)
Definition nth'_path_list {A : Type} {l1 l2 : list A}
  (p : l1 = l2) {n : nat} (Hn1 : n < length l1) (Hn2 : n < length l2)
  : nth' l1 n Hn1 = nth' l2 n Hn2.
Proof.
  destruct p.
  by apply nth'_nth'.
Defined.

(** The [nth'] element of a list is in the list. *)
Definition inlist_nth'@{i|} {A : Type@{i}} (l : list A) (n : nat)
  (H : (n < length l)%nat)
  : InList (nth' l n H) l.
Proof.
  induction l as [|a l IHa] in n, H |- * using list_ind@{i i}.
  1: destruct (not_lt_zero_r _ H).
  destruct n.
  1: by left.
  right.
  apply IHa.
Defined.

(** The [nth'] element of a list is the same as the one given by [nth]. *)
Definition nth_nth' {A} (l : list A) (n : nat) (H : (n < length l)%nat)
  : nth l n = Some (nth' l n H).
Proof.
  exact (nth_lt l n H).2.
Defined.

(** The [nth'] element of a [cons] indexed at [n.+1] is the same as the [nth'] element of the tail indexed at [n]. *)
Definition nth'_cons {A : Type} (l : list A) (n : nat) (x : A)
  (H : (n < length l)%nat) (H' : (n.+1 < length (x :: l))%nat)
  : nth' (x :: l) n.+1 H' = nth' l n H.
Proof.
  apply isinj_some.
  nrefine (_^ @ _ @ _).  
  1,3: rapply nth_nth'.
  reflexivity.
Defined.

(** The index of an element in a list is the [n] such that the [nth'] element is the element. *)
Definition index_of@{i|} {A : Type@{i}} (l : list A) (x : A)
  : InList x l
    -> sig@{Set i} (fun n : nat => { H : (n < length l)%nat & nth' l n H = x }).
Proof.
  induction l as [|a l IHl] using list_ind@{i i}.
  1: intros x'; destruct x'.
  intros [| i].
  - revert a p.
    snrapply paths_ind_r@{i i}.
    snrefine (exist@{i i} _ 0%nat _).
    snrefine (exist _ _ idpath).
    apply leq_succ.
    exact _.
  - destruct (IHl i) as [n [H H']].
    snrefine (exist@{i i} _ n.+1%nat _).
    snrefine (_; _); cbn.
    1: apply leq_succ, H.
    refine (_ @ H').
    apply nth'_cons.
Defined.

(** The [nth] element of a map is the function applied optionally to the [nth] element of the original list. *)
Definition nth_list_map@{i j|} {A : Type@{i}} {B : Type@{j}}
  (f : A -> B) (l : list A) (n : nat)
  : nth (list_map f l) n = functor_option f (nth l n).
Proof.
  induction l as [|a l IHl] in n |- * using list_ind@{i j}.
  1: by destruct n.
  destruct n.
  1: reflexivity.
  apply IHl.
Defined.

(** The [nth'] element of a [list_map] is the function applied to the [nth'] element of the original list. *)
Definition nth'_list_map@{i j|} {A : Type@{i}} {B : Type@{j}}
  (f : A -> B) (l : list A) (n : nat) (H : (n < length l)%nat)
  (H' : (n < length (list_map f l))%nat)
  : nth' (list_map f l) n H' = f (nth' l n H).
Proof.
  induction l as [|a l IHl] in n, H, H' |- * using list_ind@{i j}.
  1: destruct (not_lt_zero_r _ H).
  destruct n.
  1: reflexivity.
  apply IHl.
Defined.

(** The [nth'] element of a [list_map2] is the function applied to the [nth'] elements of the original lists. The length of the two lists is required to be the same. *)
Definition nth'_list_map2 {A B C : Type}
  (f : A -> B -> C) (l1 : list A) (l2 : list B)
  (n : nat) defl defr (H : (n < length l1)%nat) (H' : (n < length l2)%nat)
  (H'' : (n < length (list_map2 f defl defr l1 l2))%nat)
  (p : length l1 = length l2)
  : f (nth' l1 n H) (nth' l2 n H') = nth' (list_map2 f defl defr l1 l2) n H''.
Proof.
  revert l2 n defl defr H H' H'' p;
    simple_list_induction l1 a l1 IHl1;
    intros l2 n defl defr H H' H'' p.
  - destruct l2 as [|b l2].
    + destruct (not_lt_zero_r _ H).
    + inversion p.
  - destruct l2 as [|b l2].
    + inversion p.
    + destruct n.
      * reflexivity.
      * erewrite 3 nth'_cons.
        apply IHl1.
        by apply path_nat_succ.
Defined.

(** The [nth'] element of a [repeat] is the repeated value. *)
Definition nth'_repeat@{i|} {A : Type@{i}} (x : A) (i n : nat)
  (H : (i < length (repeat x n))%nat)
  : nth' (repeat x n) i H = x.
Proof.
  induction n as [|n IHn] in i, H |- * using nat_ind@{i}.
  1: destruct (not_lt_zero_r _ H).
  destruct i.
  1: reflexivity.
  apply IHn.
Defined.

(** Two lists are equal if their [nth'] elements are equal. *)
Definition path_list_nth'@{i|} {A : Type@{i}} (l l' : list A)
  (p : length l = length l')
  : (forall n (H : (n < length l)%nat), nth' l n H = nth' l' n (p # H))
    -> l = l'.
Proof.
  intros H.
  induction l as [|a l IHl] in l', p, H |- * using list_ind@{i i}.
  { destruct l'.
    - reflexivity.
    - discriminate. }
  destruct l' as [|a' l'].
  1: discriminate.
  f_ap.
  - exact (H 0%nat _).
  - snrapply IHl.
    1: by apply path_nat_succ.
    intros n Hn.
    snrefine ((nth'_cons l n a Hn _)^ @ _).
    1: apply leq_succ, Hn.
    lhs nrapply H.
    nrapply nth'_cons.
Defined.

(** The [nth n] element of a concatenated list [l ++ l'] where [n < length l] is the [nth] element of [l]. *)
Definition nth_app@{i|} {A : Type@{i}} (l l' : list A) (n : nat)
  (H : (n < length l)%nat)
  : nth (l ++ l') n = nth l n.
Proof.
  induction l as [|a l IHl] in l', n, H |- * using list_ind@{i i}.
  1: destruct (not_lt_zero_r _ H).
  destruct n.
  1: reflexivity.
  by apply IHl, leq_pred'.
Defined.

(** The [nth i] element where [pred (length l) = i] is the last element of the list. *)
Definition nth_last {A : Type} (l : list A) (i : nat) (p : nat_pred (length l) = i)
  : nth l i = last l. 
Proof.
  destruct p.
  induction l as [|a l IHl].
  1: reflexivity.
  destruct l as [|b l].
  1: reflexivity.
  cbn; apply IHl.
Defined.

(** The last element of a list with an element appended is the appended element. *)
Definition last_app {A : Type} (l : list A) (x : A)
  : last (l ++ [x]) = Some x.
Proof.
  induction l as [|a l IHl] in x |- *.
  1: reflexivity.
  destruct l.
  1: reflexivity.
  cbn; apply IHl.
Defined.

(** ** Removing elements *)

(** These functions allow surgery to be perfomed on a given list. *)

(** *** Drop *)

(** [drop n l] removes the first [n] elements of [l]. *)
Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
  match l, n with
  | _ :: l, n.+1%nat => drop n l
  | _, _ => l
  end.

(** A [drop] of zero elements is the identity. *)
Definition drop_0 {A : Type} (l : list A)
  : drop 0 l = l.
Proof.
  by destruct l.
Defined.

(** A [drop] of one element is the tail of the list. *)
Definition drop_1 {A : Type} (l : list A)
  : drop 1 l = tail l.
Proof.
  induction l.
  1: reflexivity.
  by destruct l.
Defined.

(** A [drop] of the empty list is the empty list. *)
Definition drop_nil {A : Type} (n : nat)
  : drop n (@nil A) = nil.
Proof.
  by destruct n.
Defined.

(** A [drop] of [n] elements with [length l <= n] is the empty list. *)
Definition drop_length_leq@{i|} {A : Type@{i}} (n : nat) (l : list A)
  (H : (length l <= n)%nat)
  : drop n l = nil.
Proof.
  induction l as [|a l IHl] in H, n |- * using list_ind@{i i}.
  1: apply drop_nil.
  destruct n.
  1: destruct (not_lt_zero_r _ H).
  cbn; apply IHl.
  apply leq_pred'.
  exact H.
Defined.

(** The length of a [drop n] is the length of the original list minus [n]. *)
Definition length_drop@{i|} {A : Type@{i}} (n : nat) (l : list A)
  : length (drop n l) = (length l - n)%nat.
Proof.
  induction l as [|a l IHl] in n |- * using list_ind@{i i}.
  1: by rewrite drop_nil.
  destruct n.
  1: reflexivity.
  exact (IHl n).
Defined.

(** An element of a [drop] is an element of the original list. *)
Definition drop_inlist@{i|} {A : Type@{i}} (n : nat) (l : list A) (x : A)
  : InList x (drop n l) -> InList x l.
Proof.
  intros H.
  induction l as [|a l IHl] in n, H, x |- * using list_ind@{i i}.
  1: rewrite drop_nil in H; contradiction.
  destruct n.
  1: rewrite drop_0 in H; assumption.
  right; nrapply (IHl _ _ H).
Defined.

(** *** Take *)

(** [take n l] keeps the first [n] elements of [l] and returns [l] if [n >= length l]. *)
Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
  match l, n with
  | x :: l, n.+1%nat => x :: take n l
  | _, _ => nil
  end.

(** A [take] of zero elements is the empty list. *)
Definition take_0 {A : Type} (l : list A) : take 0 l = nil.
Proof.
  by destruct l.
Defined.

(** A [take] of the empty list is the empty list. *)
Definition take_nil {A : Type} (n : nat) : take n (@nil A) = nil.
Proof.
  by destruct n.
Defined.

(** A [take] of [n] elements with [length l <= n] is the original list. *)
Definition take_length_leq@{i|} {A : Type@{i}} (n : nat) (l : list A)
  (H : (length l <= n)%nat)
  : take n l = l.
Proof.
  induction l as [|a l IHl] in H, n |- * using list_ind@{i i}.
  1: apply take_nil.
  destruct n.
  1: destruct (not_lt_zero_r _ H).
  cbn; f_ap.
  by apply IHl, leq_pred'.
Defined.

(** The length of a [take n] is the minimum of [n] and the length of the original list. *)
Definition length_take@{i|} {A : Type@{i}} (n : nat) (l : list A)
  : length (take n l) = nat_min n (length l).
Proof.
  induction l as [|a l IHl] in n |- * using list_ind@{i i}.
  { rewrite take_nil.
    rewrite nat_min_r.
    1: reflexivity.
    cbn; exact _. }
  destruct n.
  1: reflexivity.
  cbn; f_ap.
Defined.

(** The length of a [take] is less than or equal to the length of the list. *)
Definition length_take_leq {A : Type} {n : nat} (l : list A)
  : length (take n l) <= length l
  := transport (fun x => x <= length l) (length_take n l)^ (nat_min_leq_r _ _).

(** An element of a [take] is an element of the original list. *)
Definition take_inlist@{i|} {A : Type@{i}} (n : nat) (l : list A) (x : A)
  : InList x (take n l) -> InList x l.
Proof.
  intros H.
  induction l as [|a l IHl] in n, H, x |- * using list_ind@{i i}.
  1: rewrite take_nil in H; contradiction.
  destruct n.
  1: rewrite take_0 in H; contradiction.
  destruct H as [-> | H].
  - left; reflexivity.
  - right; exact (IHl _ _ H).
Defined.

(** Applying a [take] twice with [m] and [n] is the same as applying it once with [nat_min m n]. *)
Definition take_take_min {A : Type} {m n : nat} (l : list A)
  : take n (take m l) = take (nat_min n m) l.
Proof.
  revert n m l; induction n, m.
  1-3: intro l; by rewrite !take_0.
  destruct l as [|a l'].
  1: by rewrite !take_nil.
  cbn. apply ap, IHn.
Defined.

(** [take] is commutative in [n]. *)
Definition take_comm {A : Type} {m n : nat} (l : list A)
  : take n (take m l) = take m (take n l).
Proof.
  by rewrite !take_take_min, nat_min_comm.
Defined.

(** A [take n] does not change under concatenation if [n] is less than or equal to the length of the first list. *)
Definition take_app {A : Type} {n : nat} (l1 l2 : list A) (hn : n <= length l1)
  : take n l1 = take n (l1++l2).
Proof.
  induction n in l1, l2, hn |- *.
  - by rewrite !take_0.
  - induction l1 as [|a l1 IHl1].
    + contradiction (not_lt_zero_r _ hn).
    + cbn.
      apply ap, IHn, (_ hn).
Defined.

(** *** Remove *)

(** [remove n l] removes the [n]-th element of [l]. *)
Definition remove {A : Type} (n : nat) (l : list A) : list A
  := take n l ++ drop n.+1 l.

(** Removing the first element of a list is the tail of the list. *)
Definition remove_0 {A : Type} (l : list A) : remove 0 l = tail l.
Proof.
  unfold remove.
  by rewrite take_0, drop_1.
Defined.

(** Removing the [n]-th element of a list with [length l <= n] is the original list. *)
Definition remove_length_leq {A : Type} (n : nat) (l : list A)
  (H : (length l <= n)%nat)
  : remove n l = l.
Proof.
  unfold remove.
  rewrite take_length_leq.
  2: exact _.
  rewrite drop_length_leq.
  2: exact _.
  apply app_nil.
Defined.

(** The length of a [remove n] is the length of the original list minus one. *)
Definition length_remove@{i|} {A : Type@{i}} (n : nat) (l : list A)
  (H : (n < length l)%nat)
  : length (remove n l) = nat_pred (length l)%nat.
Proof.
  unfold remove.
  rewrite length_app@{i}.
  rewrite length_take.
  rewrite length_drop.
  rewrite nat_min_l.
  2: exact (leq_trans _ H).
  rewrite <- nat_sub_l_add_r.
  2: exact _.
  lhs nrapply nat_sub_succ_r.
  apply ap.
  apply nat_add_sub_cancel_l.
Defined. 

(** An element of a [remove] is an element of the original list. *)
Definition remove_inlist {A : Type} (n : nat) (l : list A) (x : A)
  : InList x (remove n l) -> InList x l.
Proof.
  unfold remove.
  intros p.
  apply equiv_inlist_app in p.
  revert p.
  snrapply sum_rec.
  - apply take_inlist.
  - apply drop_inlist.
Defined.

(** *** Filter *)

(** Produce the list of elements of a list that satisfy a decidable predicate. *)
Fixpoint list_filter@{u v|} {A : Type@{u}} (l : list A) (P : A -> Type@{v})
  (dec : forall x, Decidable (P x))
  : list A
  := match l with
    | nil => nil
    | x :: l =>
      if dec x then x :: list_filter l P dec
        else list_filter l P dec
    end.

Definition inlist_filter@{u v k | u <= k, v <= k} {A : Type@{u}} (l : list A)
  (P : A -> Type@{v}) (dec : forall x, Decidable (P x)) (x : A)
  : iff@{u k k} (InList x (list_filter l P dec)) (InList x l /\ P x).
Proof.
  simple_list_induction l a l IHl.
  - simpl.
    apply iff_inverse.
    apply iff_equiv.
    snrapply prod_empty_l@{v}.
  - simpl.
    nrapply iff_compose.
    2: { apply iff_inverse.
         apply iff_equiv.
         exact (sum_distrib_r@{k k k _ _ _ k k} _ _ _). }
    destruct (dec a) as [p|p].
    + simpl.
      snrapply iff_compose.
      1: exact (sum (a = x) (prod (InList@{u} x l) (P x))).
      1: split; apply functor_sum; only 1,3: exact idmap; apply IHl.
      split; apply functor_sum@{k k k k}; only 2,4: apply idmap.
      * intros [].
        exact (idpath, p).
      * exact fst.
    + nrapply iff_compose.
      1: apply IHl.
      apply iff_inverse.
      apply iff_equiv.
      nrefine (equiv_compose'@{k k k} (sum_empty_l@{k} _) _).
      snrapply equiv_functor_sum'@{k k k k k k}.
      2: exact equiv_idmap.
      apply equiv_to_empty.
      by intros [[] r].
Defined.

Definition list_filter_app {A : Type} (l l' : list A) (P : A -> Type)
  (dec : forall x, Decidable (P x))
  : list_filter (l ++ l') P dec = list_filter l P dec ++ list_filter l' P dec.
Proof.
  simple_list_induction l a l IHl.
  - reflexivity.
  - simpl; destruct (dec a); trivial.
    simpl; f_ap.
Defined.

(** ** Sequences *)

(** The length of a reverse sequence of [n] numbers is [n]. *)
Definition length_seq_rev@{} (n : nat)
  : length (seq_rev n) = n.
Proof.
  induction n as [|n IHn].
  1: reflexivity.
  cbn; f_ap.
Defined.

(** The length of a sequence of [n] numbers is [n]. *)
Definition length_seq@{} (n : nat)
  : length (seq n) = n.
Proof.
  lhs nrapply length_reverse.
  apply length_seq_rev.
Defined.

(** The reversed sequence of [n.+1] numbers is the [n] followed by the rest of the reversed sequence. *)
Definition seq_rev_cons@{} (n : nat)
  : seq_rev n.+1 = n :: seq_rev n
  := idpath.

(** The sequence of [n.+1] numbers is the sequence of [n] numbers concatenated with [[n]]. *)
Definition seq_succ@{} (n : nat)
  : seq n.+1 = seq n ++ [n].
Proof.
  apply reverse_cons.
Defined.

(** Alternate definition of [seq_rev] that keeps the proofs of the entries being [< n]. *)
Definition seq_rev'@{} (n : nat) : list {k : nat & (k < n)%nat}.
Proof.
  transparent assert (f : (forall n, {k : nat & (k < n)%nat}
    -> {k : nat & (k < n.+1)%nat})).
  { intros m.
    snrapply (functor_sigma idmap).
    intros k H.
    exact (leq_succ_r H). }
  induction n as [|n IHn].
  1: exact nil.
  nrefine ((n; _) :: list_map (f n) IHn).
  exact _.
Defined.

(** Alternate definition of [seq] that keeps the proofs of the entries being [< n]. *)
Definition seq'@{} (n : nat) : list {k : nat & (k < n)%nat}
  := reverse (seq_rev' n).

(** The length of [seq_rev' n] is [n]. *) 
Definition length_seq_rev'@{} (n : nat)
  : length (seq_rev' n) = n.
Proof.
  induction n as [|n IHn].
  1: reflexivity.
  cbn; f_ap.
  lhs nrapply length_list_map.
  exact IHn.
Defined.

(** The length of [seq' n] is [n]. *)
Definition length_seq'@{} (n : nat)
  : length (seq' n) = n.
Proof.
  lhs nrapply length_reverse.
  apply length_seq_rev'.
Defined.

(** The [list_map] of first projections on [seq_rev' n] is [seq_rev n]. *)
Definition seq_rev_seq_rev'@{} (n : nat)
  : list_map pr1 (seq_rev' n) = seq_rev n.
Proof.
  induction n as [|n IHn].
  1: reflexivity.
  simpl; f_ap.
  lhs_V nrapply list_map_compose.
  apply IHn.
Defined.

(** The [list_map] of first projections on [seq' n] is [seq n]. *)
Definition seq_seq'@{} (n : nat)
  : list_map pr1 (seq' n) = seq n.
Proof.
  lhs nrapply list_map_reverse_acc.
  apply (ap reverse).
  apply seq_rev_seq_rev'.
Defined.

(** The [nth] element of a [seq_rev] is [n - i.+1]. *)
Definition nth_seq_rev@{} {n i} (H : (i < n)%nat)
  : nth (seq_rev n) i = Some (n - i.+1)%nat.
Proof.
  induction i as [|i IHi] in n, H |- *.
  - induction n.
    1: destruct (not_lt_zero_r _ H).
    cbn; by rewrite nat_sub_zero_r.
  - induction n as [|n IHn].
    1: destruct (not_lt_zero_r _ H).
    by apply IHi, leq_pred'.
Defined.

(** The [nth] element of a [seq] is [i]. *)
Definition nth_seq@{} {n i} (H : (i < n)%nat)
  : nth (seq n) i = Some i.
Proof.
  induction n.
  1: destruct (not_lt_zero_r _ H).
  rewrite seq_succ.
  destruct (dec (i < n)%nat) as [H'|H'].
  - lhs nrapply nth_app.
    1: by rewrite length_seq.
    by apply IHn.
  - apply geq_iff_not_lt in H'.
    apply leq_pred' in H.
    destruct (leq_antisym H H').
    lhs nrapply nth_last.
    { rewrite length_app.
      rewrite nat_add_comm.
      apply length_seq. }
    nrapply last_app.
Defined.

(** The [nth'] element of a [seq'] is [i]. *)
Definition nth'_seq'@{} (n i : nat) (H : (i < length (seq' n))%nat)
  : (nth' (seq' n) i H).1 = i.
Proof.
  unshelve lhs_V nrapply nth'_list_map.
  1: by rewrite length_list_map.
  unshelve lhs nrapply (ap011D (fun x y => nth' x _ y) _ idpath).
  2: apply seq_seq'.
  apply isinj_some.
  lhs_V nrapply nth_nth'.
  apply nth_seq.
  by rewrite length_seq' in H.
Defined.

Definition inlist_seq@{} (n : nat) x
  : InList x (seq n) <~> (x < n)%nat.
Proof.
  simple_induction n n IHn.
  { symmetry; apply equiv_to_empty.
    apply not_lt_zero_r. }
  refine (_ oE equiv_transport _ (seq_succ _)).
  nrefine (_ oE (equiv_inlist_app _ _ _)^-1).
  nrefine (_ oE equiv_functor_sum' (B':=x = n) IHn _).
  2: { simpl.
       exact (equiv_path_inverse _ _ oE sum_empty_r@{Set} _). }
  nrefine (_ oE equiv_leq_lt_or_eq^-1).
  rapply equiv_iff_hprop.
Defined.

(** Turning a finite sequence into a list. This is taken from [Build_Vector]. *)
Definition Build_list {A : Type} (n : nat)
  (f : forall (i : nat), (i < n) -> A)
  : list A
  := list_map (fun '(i; Hi) => f i Hi) (seq' n).

Definition length_Build_list {A : Type} (n : nat)
  (f : forall (i : nat), (i < n) -> A)
  : length (Build_list n f) = n.
Proof.
  lhs nrapply length_list_map.
  apply length_seq'.
Defined.

(** Restriction of an infinite sequence to a list of specified length. *)
Definition list_restrict {A : Type} (s : nat -> A) (n : nat) : list A
  := Build_list n (fun m _ => s m).

Definition list_restrict_length {A : Type} (s : nat -> A) (n : nat)
  : length (list_restrict s n) = n
  := length_Build_list _ _.

(** [nth'] of the restriction of a sequence is the corresponding term of the sequence.  *)
Definition entry_list_restrict {A : Type} (s : nat -> A) (n : nat)
  {i : nat} (Hi : i < n)
  : nth' (list_restrict s n) i ((list_restrict_length s n)^ # Hi) = s i.
Proof.
  lhs snrefine (nth'_list_map _ _ _ (_^ # Hi) _).
  - exact (ap s (nth'_seq' _ _ _)).
  Unshelve. nrapply length_seq'.
Defined.

(** ** Repeat *)

(** The length of a repeated list is the number of repetitions. *)
Definition length_repeat@{i|} {A : Type@{i}} (n : nat) (x : A)
  : length (repeat x n) = n.
Proof.
  induction n using nat_ind@{i}.
  - reflexivity.
  - exact (ap S IHn).
Defined.

(** An element of a repeated list is equal to the repeated element. *)
Definition inlist_repeat@{i|} {A : Type@{i}} (n : nat) (x y : A)
  : InList y (repeat x n) -> y = x.
Proof.
  induction n as [|n IHn].
  1:contradiction.
  intros [p | i].
  - by symmetry.
  - by apply IHn.
Defined.

(** ** Forall *)

(** If a predicate holds for all elements of a list, the the [for_all] predicate holds for the list. *)
Definition for_all_inlist {A : Type} (P : A -> Type) l
  : (forall x, InList x l -> P x) -> for_all P l.
Proof.
  simple_list_induction l h t IHl; intros H; cbn; trivial; split.
  - apply H.
    by left.
  - apply IHl.
    intros y i.
    apply H.
    by right.
Defined.

(** Conversely, if [for_all P l] then each element of the list satisfies [P]. *)
Definition inlist_for_all {A : Type} {P : A -> Type}
  (l : list A)
  : for_all P l -> forall x, InList x l -> P x.
Proof.
  simple_list_induction l x l IHl.
  - contradiction.
  - intros [Hx Hl] y [-> | i].
    + exact Hx.
    + apply IHl.
      1: exact Hl.
      exact i.
Defined.

(** If a predicate [P] implies a predicate [Q] composed with a function [f], then [for_all P l] implies [for_all Q (list_map f l)]. *)
Definition for_all_list_map {A B : Type} (P : A -> Type) (Q : B -> Type)
  (f : A -> B) (Hf : forall x, P x -> Q (f x))
  : forall l, for_all P l -> for_all Q (list_map f l).
Proof.
  simple_list_induction l x l IHl; simpl; trivial.
  intros [Hx Hl].
  split; auto.
Defined.

(** A variant of [for_all_map P Q f] where [Q] is [P o f]. *)
Definition for_all_list_map' {A B : Type} (P : B -> Type) (f : A -> B)
  : forall l, for_all (P o f) l -> for_all P (list_map f l).
Proof.
  by apply for_all_list_map.
Defined.

(** If a predicate [P] and a predicate [Q] together imply a predicate [R], then [for_all P l] and [for_all Q l] together imply [for_all R l]. There are also some side conditions for the default elements. *)
Lemma for_all_list_map2 {A B C : Type}
  (P : A -> Type) (Q : B -> Type) (R : C -> Type)
  (f : A -> B -> C) (Hf : forall x y, P x -> Q y -> R (f x y))
  def_l (Hdefl : forall l1, for_all P l1 -> for_all R (def_l l1))
  def_r (Hdefr : forall l2, for_all Q l2 -> for_all R (def_r l2))
  (l1 : list A) (l2 : list B)
  : for_all P l1 -> for_all Q l2
    -> for_all R (list_map2 f def_l def_r l1 l2).
Proof.
  revert l2;
    simple_list_induction l1 x l1 IHl1;
    intro l2.
  - destruct l2 as [|y l2]; cbn; auto.
  - simpl. destruct l2 as [|y l2]; intros [Hx Hl1];
      [intros _ | intros [Hy Hl2] ]; simpl; auto.
    apply Hdefl.
    simpl; auto.
Defined.

(** A simpler variant of [for_all_map2] where both lists have the same length and the side conditions on the default elements can be avoided. *)
Definition for_all_list_map2' {A B C : Type}
  (P : A -> Type) (Q : B -> Type) (R : C -> Type)
  (f : A -> B -> C) (Hf : forall x y, P x -> Q y -> R (f x y))
  {def_l def_r} {l1 : list A} {l2 : list B}
  (p : length l1 = length l2)
  : for_all P l1 -> for_all Q l2
    -> for_all R (list_map2 f def_l def_r l1 l2).
Proof.
  revert l2 p;
    simple_list_induction l1 x l1 IHl1;
    intros l2 p.
  - destruct l2.
    + reflexivity.
    + discriminate.
  - destruct l2 as [|y l2].
    + discriminate.
    + intros [Hx Hl1] [Hy Hl2].
      split.
      * by apply Hf.
      * apply IHl1; trivial.
        apply path_nat_succ.
        exact p.
Defined.

(** The left fold of [f] on a list [l] for which [for_all Q l] satisfies [P] if [P] and [Q] imply [P] composed with [f]. *)
Lemma fold_left_preserves {A B : Type}
  (P : A -> Type) (Q : B -> Type) (f : A -> B -> A)
  (Hf : forall x y, P x -> Q y -> P (f x y))
  (acc : A) (Ha : P acc) (l : list B) (Hl : for_all Q l)
  : P (fold_left f l acc).
Proof.
  revert acc Ha Hl;
    simple_list_induction l x l IHl;
    intros acc Ha Hl.
  - exact Ha.
  - simpl.
    destruct Hl as [Qx Hl].
    apply IHl; auto.
Defined.

(** [for_all] preserves the truncation predicate. *)
Definition istrunc_for_all {A : Type}
  {n : trunc_index} (P : A -> Type) (l : list A)
  : for_all (fun x => IsTrunc n (P x)) l -> IsTrunc n (for_all P l).
Proof.
  induction l as [|x l IHl]; simpl.
  - destruct n; exact _.
  - intros [Hx Hl].
    apply IHl in Hl.
    exact _.
Defined.

Global Instance istrunc_for_all' {A : Type} {n : trunc_index}
  (P : A -> Type) (l : list A)
  `{forall x, IsTrunc n (P x)}
  : IsTrunc n (for_all P l).
Proof.
  by apply istrunc_for_all, for_all_inlist.
Defined.

(** If a predicate holds for an element, then it holds [for_all] the elements of the repeated list. *)
Definition for_all_repeat {A : Type} {n : nat}
  (P : A -> Type) (x : A)
  : P x -> for_all P (repeat x n).
Proof.
  intros H.
  induction n as [|n IHn].
  1: exact tt.
  exact (H, IHn).
Defined.

(** We can form a list of pairs of a sigma type given a list and a for_all predicate over it. *)
Definition list_sigma {A : Type} (P : A -> Type) (l : list A) (p : for_all P l)
  : list {x : A & P x}.
Proof.
  induction l as [|x l IHl] in p |- *.
  1: exact nil.
  destruct p as [Hx Hl].
  exact ((x; Hx) :: IHl Hl).
Defined.

(** The length of a list of sigma types is the same as the original list. *)
Definition length_list_sigma {A : Type} {P : A -> Type} {l : list A} {p : for_all P l}
  : length (list_sigma P l p) = length l.
Proof.
  revert p; simple_list_induction l x l IHl; intro p.
  1: reflexivity.
  destruct p as [Hx Hl].
  cbn; f_ap.
  apply IHl.
Defined.

(** If a predicate [P] is decidable then so is [for_all P]. *)
Global Instance decidable_for_all {A : Type} (P : A -> Type)
  `{forall x, Decidable (P x)} (l : list A)
  : Decidable (for_all P l).
Proof.
  simple_list_induction l x l IHl; exact _.
Defined.

(** If a predicate [P] is decidable then so is [list_exists P]. *)
Global Instance decidable_list_exists {A : Type} (P : A -> Type)
  `{forall x, Decidable (P x)} (l : list A)
  : Decidable (list_exists P l).
Proof.
  simple_list_induction l x l IHl; exact _.
Defined.

Definition inlist_list_exists {A : Type} (P : A -> Type) (l : list A)
  : list_exists P l -> exists (x : A), InList x l /\ P x.
Proof.
  simple_list_induction l x l IHl.
  1: done.
  simpl.
  intros [Px | ex].
  - exists x.
    by split; [left|].
  - destruct (IHl ex) as [x' [H Px']].
    exists x'.
    by split; [right|].
Defined.

Definition list_exists_inlist {A : Type} (P : A -> Type) (l : list A)
  : forall (x : A), InList x l -> P x -> list_exists P l.
Proof.
  simple_list_induction l x l IHl.
  1: trivial.
  simpl; intros y H p; revert H.
  apply functor_sum.
  - exact (fun r => r^ # p).
  - intros H.
    by apply (IHl y).
Defined.

Definition list_exists_seq {n : nat} (P : nat -> Type)
  (H : forall k, P k -> (k < n)%nat)
  : (exists k, P k) <-> list_exists P (seq n).
Proof.
  split.
  - intros [k p].
    snrapply (list_exists_inlist P _ k _ p).
    apply inlist_seq, H.
    exact p.
  - intros H1.
    apply inlist_list_exists in H1.
    destruct H1 as [k [Hk p]].
    exists k.
    exact p.
Defined.

(** An upper bound on witnesses of a decidable predicate makes the sigma type decidable. *)
Definition decidable_exists_nat (n : nat) (P : nat -> Type)
  (H1 : forall k, P k -> (k < n)%nat)
  (H2 : forall k, Decidable (P k))
  : Decidable (exists k, P k).
Proof.
  nrapply decidable_iff.
  1: apply iff_inverse; nrapply list_exists_seq.
  1: exact H1.
  exact _.
Defined.
