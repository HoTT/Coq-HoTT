Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids.
Require Import Classes.implementations.list.

Local Open Scope list_scope.

(** ** Lemmas about lists *)

(** Note that [list] is currently defined in Basics.Datatypes. *)

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
