Require Import Basics Types.

Local Open Scope list_scope.

(** ** Lemmas about lists *)

(** Note that [list] is currently defined in the coq stdlib. *)

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

