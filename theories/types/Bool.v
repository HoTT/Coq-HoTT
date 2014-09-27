(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the booleans *)

Require Import Basics.
Require Import types.Prod HSet HProp.
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

  Global Instance trunc_bool : IsHSet Bool | 0
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

Section EquivBoolEquiv.
  (** We prove that the type [Bool <~> Bool] is equivalent to [Bool].  We first define the functions in both directoins, which identify [true] with the identity equivalence and [false] with the flip equivalence. *)

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

  (** We prove that equivalences [Bool <~> Bool] send [true] and [false] to different things. *)
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

  (** We identify the constant equivalence with [true] and the flip equivalence with [false], and do this by evaluating the equivalence function on [true]. *)
  Let f : Bool <~> Bool -> Bool := fun e => e true.
  Let g : Bool -> Bool <~> Bool := fun b => if b
                                            then {| equiv_fun := idmap |}
                                            else {| equiv_fun := negb |}.

  (** We can't depend on [EquivalenceVarieties] nor [Misc] here, so we take the necessary lemma as a hypothesis, and put the theorem in [Misc.v] *)
  Context `{Funext}.
  Hypothesis path_equiv : forall e1 e2 : Bool <~> Bool,
                            (e1 = e2 :> (Bool -> Bool)) -> (e1 = e2 :> (Bool <~> Bool)).
  Lemma equiv_bool_equiv_bool_bool_helper : Bool <~> (Bool <~> Bool).
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

(** canonical map from Bool to hProp *)
Definition is_true (b : Bool) : hProp
  := if b then Unit_hp else False_hp.
