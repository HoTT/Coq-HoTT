Require Import Basics.Overture Spaces.List.Core.
Require Import canonical_names.

(** * Theory of Lists and List Operations *)

(** In this file we collect lemmas about lists and their operations. We don't include those in [List.Core] so that file can stay lightweight on dependencies. *)

(** We generally try to keep the order the same as the concepts appeared in [List.Core]. *)

Local Open Scope list_scope.

(** ** Concatenation *)

(** TODO: is this needed? *)
Global Instance sg_op_app A : SgOp (list A) := @app A.

Global Instance app_assoc {A} : Associative (@app A).
Proof.
  intros l1 l2 l3.
  induction l1 as [|a l IHl] in |- *.
  - reflexivity.
  - exact (ap (cons a) IHl).
Defined.

(** The type of lists has a monoidal structure given by concatenation. *)
Definition list_pentagon {A} (w x y z : list A)
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

(** ** Folding *)

Lemma fold_left_app {A B} (f : A -> B -> A) (l l' : list B) (i : A)
  : fold_left f (l ++ l') i = fold_left f l' (fold_left f l i).
Proof.
  induction l in i |- *.
  1: reflexivity.
  apply IHl.
Defined.

Lemma fold_right_app {A B} (f : B -> A -> A) (i : A) (l l' : list B)
  : fold_right f i (l ++ l') = fold_right f (fold_right f i l') l.
Proof.
  induction l in i |- *.
  1: reflexivity.
  exact (ap (f a) (IHl _)).
Defined.

(** ** Maps *)

Lemma map_id {A} (f : A -> A) (Hf : forall x, f x = x) (l : list A)
  :  map f l = l.
Proof.
  induction l as [|x l IHl].
  - reflexivity.
  - simpl.
    nrapply ap011.
    + exact (Hf _).
    + exact IHl.
Defined.

Lemma map2_cons {A B C} (f : A -> B -> C) defl defr x l1 y l2
  :  map2 f defl defr (x :: l1) (y :: l2)
    = (f x y) :: map2 f defl defr l1 l2.
Proof.
  reflexivity.
Defined.

(** ** Forall *)

Lemma for_all_trivial {A} (P : A -> Type) : (forall x, P x) ->
  forall l, for_all P l.
Proof.
  intros HP l; induction l as [|x l IHl]; split; auto.
Defined.

Lemma for_all_map {A B} P Q (f : A -> B) (Hf : forall x, P x -> Q (f x))
 : forall l, for_all P l -> for_all Q (map f l).
Proof.
  intros l;induction l as [|x l IHl];simpl.
  - auto.
  - intros [Hx Hl]. split; auto.
Defined.

Lemma for_all_map2 {A B C}
  (P : A -> Type) (Q : B -> Type) (R : C -> Type)
  (f : A -> B -> C) (Hf : forall x y, P x -> Q y -> R (f x y))
  def_l (Hdefl : forall l1, for_all P l1 -> for_all R (def_l l1))
  def_r (Hdefr : forall l2, for_all Q l2 -> for_all R (def_r l2))
  (l1 : list A) (l2 : list B)
  : for_all P l1 -> for_all Q l2
    -> for_all R (map2 f def_l def_r l1 l2).
Proof.
  induction l1 as [|x l1 IHl1] in l2 |- *.
  - destruct l2 as [|y l2]; cbn; auto.
  - simpl. destruct l2 as [|y l2]; intros [Hx Hl1];
      [intros _ | intros [Hy Hl2] ]; simpl; auto.
    apply Hdefl.
    simpl; auto.
Defined.

Lemma fold_preserves {A B} P Q (f : A -> B -> A)
  (Hf : forall x y, P x -> Q y -> P (f x y))
  (acc : A) (Ha : P acc) (l : list B) (Hl : for_all Q l)
  : P (fold_left f l acc).
Proof.
  induction l as [|x l IHl] in acc, Ha, Hl |- *.
  - exact Ha.
  - simpl.
    destruct Hl as [Qx Hl].
    apply IHl; auto.
Defined.

Global Instance for_all_trunc {A} {n} (P : A -> Type) (l : list A)
  : for_all (fun x => IsTrunc n (P x)) l -> IsTrunc n (for_all P l).
Proof.
  induction l as [|x l IHl]; simpl.
  - destruct n; exact _.
  - intros [Hx Hl].
    apply IHl in Hl.
    exact _.
Defined.


