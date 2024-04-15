Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Trunc.
Require Import Classes.implementations.list Types.Unit Types.Empty Types.Prod.
Require Import Modalities.ReflectiveSubuniverse Truncations.Core.

Local Open Scope list_scope.

(** Note that [list] is currently defined in Basics.Datatypes. *)

(** ** Lemmas about lists *)

Section Fold_Left_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : A -> B -> A.

  Fixpoint fold_left (l : list B) (a0 : A) : A :=
    match l with
      | nil => a0
      | cons b t => fold_left t (f a0 b)
    end.

  Lemma fold_left_app : forall (l l' : list B) (i : A),
    fold_left (l ++ l') i = fold_left l' (fold_left l i).
  Proof.
    induction l; simpl; auto.
  Qed.

End Fold_Left_Recursor.

Section Fold_Right_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : B -> A -> A.

  Fixpoint fold_right (a0 : A) (l : list B) : A :=
    match l with
      | nil => a0
      | cons b t => f b (fold_right a0 t)
    end.

  Lemma fold_right_app : forall l l' i,
    fold_right i (l ++ l') = fold_right (fold_right i l') l.
  Proof.
    induction l; simpl; auto.
    intros; f_ap.
  Qed.

End Fold_Right_Recursor.

(** The type of lists has a monoidal structure given by concatenation. *)
Definition list_pentagon {A} (w x y z : list A)
  : app_assoc _ w x (y ++ z) @ app_assoc _ (w ++ x) y z
    = ap (fun l => w ++ l) (app_assoc _ x y z)
    @ app_assoc _ w (x ++ y) z
    @ ap (fun l => l ++ z) (app_assoc _ w x y).
Proof.
  symmetry.
  induction w as [|? w IHw] in x, y, z |- *.
  - simpl.
    rhs nrapply concat_1p.
    lhs nrapply concat_p1.
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

(** ** Path spaces of lists *)

(** This proof was adapted from a proof given in agda/cubical by Evan Cavallo. *)

Section PathList.
  Context {A : Type}.
  
  (** This type is equivalent to the path space of lists. We don't actually show that it is equivalent to the type of paths but rather that the path type is a retract of this type. This is sufficient to determine the h-level of the type of lists. *)
  Fixpoint ListEq (l l' : list A) : Type :=
    match l, l' with
      | nil, nil => Unit
      | cons x xs, cons x' xs' => (x = x') * ListEq xs xs'
      | _, _ => Empty
    end.

  Global Instance reflexive_listeq : Reflexive ListEq. 
  Proof.
    intros l.
    induction l as [| a l IHl].
    - exact tt.
    - exact (idpath, IHl).
  Defined.

  Local Definition encode {l1 l2} (p : l1 = l2) : ListEq l1 l2.
  Proof.
    by destruct p.
  Defined.

  Local Definition decode {l1 l2} (q : ListEq l1 l2) : l1 = l2.
  Proof.
    induction l1 as [| a l1 IHl1 ] in l2, q |- *.
    1: by destruct l2.
    destruct l2.
    1: contradiction.
    destruct q as [p q].
    exact (ap011 (cons (A:=_)) p (IHl1 _ q)).
  Defined.

  Local Definition decode_refl {l} : decode (reflexivity l) = idpath.
  Proof.
    induction l.
    1: reflexivity.
    exact (ap02 (cons a) IHl).
  Defined.

  Local Definition decode_encode {l1 l2} (p : l1 = l2)
    : decode (encode p) = p.
  Proof.
    destruct p.
    apply decode_refl.
  Defined.

  (** By case analysis on both lists, it's easy to show that [ListEq] is [n.+1]-truncated if [A] is [n.+2]-truncated. *)
  Global Instance istrunc_listeq n {l1 l2} {H : IsTrunc n.+2 A}
    : IsTrunc n.+1 (ListEq l1 l2).
  Proof.
    induction l1 in l2 |- *.
    - destruct l2.
      1,2: exact _.
    - destruct l2.
      1: exact _.
      rapply istrunc_prod.
  Defined.

  (** The path space of lists is a retract of [ListEq], therefore it is [n.+1]-truncated if [ListEq] is [n.+1]-truncated. By the previous result, this holds when [A] is [n.+2]-truncated. *) 
  Global Instance istrunc_list n {H : IsTrunc n.+2 A} : IsTrunc n.+2 (list A).
  Proof.
    apply istrunc_S.
    intros x y.
    rapply (inO_retract_inO n.+1 _ _ encode decode decode_encode).
  Defined.

End PathList.
