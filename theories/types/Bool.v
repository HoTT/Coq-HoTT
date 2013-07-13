(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the booleans *)

Require Import Overture Contractible Equivalences types.Prod HSet.
Local Open Scope equiv_scope.

(* coq calls it "bool", we call it "Bool" *)
Inductive Bool : Type :=
  | true : Bool
  | false : Bool.

Add Printing If Bool.

Delimit Scope bool_scope with Bool.

Bind Scope bool_scope with Bool.

Definition andb (b1 b2 : Bool) : Bool := if b1 then b2 else false.

Definition orb (b1 b2 : Bool) : Bool := if b1 then true else b2.

Definition negb (b : Bool) := if b then false else true.

Definition implb (b1 b2 : Bool) : Bool := if b1 then b2 else true.

Infix "||" := orb : bool_scope.
Infix "&&" := andb : bool_scope.

Instance trunc_if n A B `{IsTrunc n A, IsTrunc n B} (b : Bool)
: IsTrunc n (if b then A else B) | 100
  := if b as b return (IsTrunc n (if b then A else B)) then _ else _.

Section BoolDecidable.
  Definition false_ne_true : ~false = true
    := fun H => match H in (_ = y) return (if y then Empty else Bool) with
                  | 1%path => true
                end.

  Definition true_ne_false : ~true = false
    := fun H => false_ne_true (symmetry _ _ H).

  Definition decidable_paths_bool : decidable_paths Bool
    := fun x y => match x as x, y as y return ((x = y) + (~x = y)) with
                    | true, true => inl idpath
                    | false, false => inl idpath
                    | true, false => inr true_ne_false
                    | false, true => inr false_ne_true
                  end.

  Global Instance trunc_bool : IsHSet Bool
    := hset_decidable decidable_paths_bool.
End BoolDecidable.

Section BoolForall.
  Variable P : Bool -> Type.

  Let f (s : forall b, P b) := (s false, s true).

  Let g (u : P false * P true) (b : Bool) : P b :=
    match b with
      | false => fst u
      | true => snd u
    end.

  Definition equiv_bool_forall_prod `{Funext} :
    (forall b, P b) <~> P false * P true.
  Proof.
    apply (equiv_adjointify f g);
    repeat (reflexivity
              || intros []
              || intro
              || apply path_forall).
  Defined.
End BoolForall.
