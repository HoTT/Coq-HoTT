(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the booleans *)

Require Import HoTT.Basics.
Require Import Types.Prod Types.Equiv.

Local Open Scope path_scope.

(* coq calls it "bool", we call it "Bool" *)
Local Unset Elimination Schemes.
Inductive Bool : Type0 :=
  | true : Bool
  | false : Bool.
Scheme Bool_ind := Induction for Bool Sort Type.
Scheme Bool_rec := Minimality for Bool Sort Type.

Add Printing If Bool.

Declare Scope bool_scope.

Delimit Scope bool_scope with Bool.

Bind Scope bool_scope with Bool.

Definition andb (b1 b2 : Bool) : Bool := if b1 then b2 else false.

Definition orb (b1 b2 : Bool) : Bool := if b1 then true else b2.

Definition negb (b : Bool) := if b then false else true.

Definition implb (b1 b2 : Bool) : Bool := if b1 then b2 else true.

Infix "||" := orb : bool_scope.
Infix "&&" := andb : bool_scope.
Infix "->" := implb : bool_scope.

Definition implb_true {b} : implb b true = true
  := if b as b return implb b true = true then idpath else idpath.

Definition implb_impl {a b} : (a -> b)%Bool = true <-> (a = true -> b = true).
Proof.
  destruct a; simpl; split; trivial using idpath with nocore;
  destruct b; simpl; auto using idpath with nocore.
Defined.

Global Instance trunc_if n A B `{IsTrunc n A, IsTrunc n B} (b : Bool)
: IsTrunc n (if b then A else B) | 100
  := if b as b return (IsTrunc n (if b then A else B)) then _ else _.

(** ** Decidability *)

Section BoolDecidable.
  Definition false_ne_true : ~false = true
    := fun H => match H in (_ = y) return (if y return Set then Empty else Bool) with
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

(** In particular, [negb] has no fixed points *)
Definition not_fixed_negb (b : Bool) : negb b <> b
  := match b return negb b <> b with
       | true => false_ne_true
       | false => true_ne_false
     end.

(** And conversely, if two elements of [Bool] are unequal, they must be related by [negb]. *)
Definition negb_ne {b1 b2 : Bool}
: (b1 <> b2) -> (b1 = negb b2).
Proof.
  destruct b1, b2.
  - intros oops; case (oops idpath).
  - reflexivity.
  - reflexivity.
  - intros oops; case (oops idpath).
Defined.

(** ** Products as [forall] over [Bool] *)

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

  Definition aut_bool_canonical (e : Bool <~> Bool)
  : e == g (f e).
  Proof.
    unfold f, g; clear f g; intros []; simpl.
    - destruct (e true); reflexivity.
    - refine (eval_bool_isequiv e @ _).
      destruct (e true); reflexivity.
  Defined.

  Lemma equiv_bool_aut_bool `{Funext} : Bool <~> (Bool <~> Bool).
  Proof.
    refine (equiv_adjointify g f _ _).
    - intro e.
      apply path_equiv, path_forall.
      intros b; symmetry; apply aut_bool_canonical.
    - intros []; reflexivity.
  Defined.

  (** It follows that every automorphism of [Bool] is either [idmap] or [negb]. *)
  Definition aut_bool_idmap_or_negb `{Funext} (e : Bool <~> Bool)
  : (e = equiv_idmap Bool) + (e = equiv_negb).
  Proof.
    revert e. equiv_intro equiv_bool_aut_bool e.
    destruct e; simpl.
    - exact (inl idpath).
    - exact (inr idpath).
  Defined.

  (** But, obviously, not both. *)
  Definition idmap_bool_ne_negb : equiv_idmap Bool <> equiv_negb.
  Proof.
    intros oops.
    exact (true_ne_false (ap10_equiv oops true)).
  Defined.

  (** In particular, every pair of automorphisms of [Bool] commute with each other. *)
  Definition abelian_aut_bool (e1 e2 : Bool <~> Bool)
  : e1 o e2 == e2 o e1.
  Proof.
    intro b.
    refine (ap e1 (aut_bool_canonical e2 b) @ _).
    refine (aut_bool_canonical e1 _ @ _).
    refine (_ @ ap e2 (aut_bool_canonical e1 b)^).
    refine (_ @ (aut_bool_canonical e2 _)^).
    unfold f, g.
    destruct (e1 true), (e2 true), b; reflexivity.
  Defined.

End EquivBoolEquiv.
