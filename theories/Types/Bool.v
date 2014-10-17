(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the booleans *)

Require Import HoTT.Basics.
Require Import Types.Prod Types.Equiv.
Local Open Scope equiv_scope.

(* coq calls it "bool", we call it "Bool" *)
Local Unset Elimination Schemes.
Inductive Bool : Type1 :=
  | true : Bool
  | false : Bool.
Scheme Bool_ind := Induction for Bool Sort Type.
Scheme Bool_rec := Minimality for Bool Sort Type.

Add Printing If Bool.

Delimit Scope bool_scope with Bool.

Bind Scope bool_scope with Bool.

Definition andb (b1 b2 : Bool) : Bool := if b1 then b2 else false.

Definition orb (b1 b2 : Bool) : Bool := if b1 then true else b2.

Definition negb (b : Bool) := if b then false else true.

Definition implb (b1 b2 : Bool) : Bool := if b1 then b2 else true.

Infix "||" := orb : bool_scope.
Infix "&&" := andb : bool_scope.

Global Instance trunc_if n A B `{IsTrunc n A, IsTrunc n B} (b : Bool)
: IsTrunc n (if b then A else B) | 100
  := if b as b return (IsTrunc n (if b then A else B)) then _ else _.

Section BoolDecidable.
  Definition false_ne_true : ~false = true
    := fun H => match H in (_ = y) return (if y then Empty else Bool) with
                  | 1%path => true
                end.

  Definition true_ne_false : ~true = false
    := fun H => false_ne_true (symmetry _ _ H).

  Global Instance decidable_paths_bool : DecidablePaths Bool
    := fun x y => match x as x, y as y return ((x = y) + (~x = y)) with
                    | true, true => inl idpath
                    | false, false => inl idpath
                    | true, false => inr true_ne_false
                    | false, true => inr false_ne_true
                  end.

  Corollary hset_bool : IsHSet Bool.
  Proof.
    exact _.
  Defined.
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

(** ** The type [Bool <~> Bool] is equivalent to [Bool]. *)

(** The nonidentity equivalence is negation (the flip). *)
Global Instance isequiv_negb : IsEquiv negb.
Proof.
  refine (@BuildIsEquiv
            _ _
            negb negb
            (fun b => if b as b return negb (negb b) = b then idpath else idpath)
            (fun b => if b as b return negb (negb b) = b then idpath else idpath)
            _).
  intros []; simpl; exact idpath.
Defined.

Definition equiv_negb : Bool <~> Bool
  := BuildEquiv Bool Bool negb _.

(** Any equivalence [Bool <~> Bool] sends [true] and [false] to different things. *)
Lemma eval_bool_isequiv (f : Bool -> Bool) `{IsEquiv Bool Bool f}
: f false = negb (f true).
Proof.
  pose proof (eissect f true).
  pose proof (eissect f false).
  destruct (f true), (f false).
  - etransitivity; try (eassumption || (symmetry; eassumption)).
  - simpl. reflexivity.
  - simpl. reflexivity.
  - etransitivity; try (eassumption || (symmetry; eassumption)).
Defined.

Section EquivBoolEquiv.

  (** We will identify the constant equivalence with [true] and the flip equivalence with [false], and do this by evaluating the equivalence function on [true]. *)
  Let f : (Bool <~> Bool) -> Bool := fun e => e true.
  Let g : Bool -> (Bool <~> Bool) := fun b => if b
                                              then (equiv_idmap Bool)
                                              else equiv_negb.

  Lemma equiv_bool_equiv_bool_bool `{Funext} : Bool <~> (Bool <~> Bool).
  Proof.
    refine (equiv_adjointify g f _ _);
    unfold f, g; clear f g;
    hnf; simpl.
    - intro e.
      destruct e as [e ?].
      apply path_equiv; try assumption.
      apply path_forall.
      intros []; simpl.
      * destruct (e true); reflexivity.
      * etransitivity; [ | symmetry; apply eval_bool_isequiv; trivial ].
        destruct (e true); reflexivity.
    - intros []; reflexivity.
  Defined.

End EquivBoolEquiv.
