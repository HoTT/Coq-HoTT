(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool.

(******************************************************************************)
(* This file defines two "base" combinatorial interfaces:                     *)
(*    eqType == the structure for types with a decidable equality.            *)
(*              Equality mixins can be made Canonical to allow generic        *)
(*              folding of equality predicates.                               *)
(* subType p == the structure for types isomorphic to {x : T | p x} with      *)
(*              p : pred T for some type T.                                   *)
(* The eqType interface supports the following operations:                    *)
(*          x == y <=> x compares equal to y (this is a boolean test).        *)
(*     x == y :> T <=> x == y at type T.                                      *)
(*          x != y <=> x and y compare unequal.                               *)
(*     x != y :> T <=>  "    "      "    "     at type T.                     *)
(*         x =P y  :: a proof of reflect (x = y) (x == y); this coerces       *)
(*                     to x == y -> x = y.                                    *)
(*    comparable T <-> equality on T is decidable                             *)
(*                    := forall x y : T, decidable (x = y)                    *)
(*  comparableClass compT == eqType mixin/class for compT : comparable T.     *)
(*             pred1 a == the singleton predicate [pred x | x == a].          *)
(* pred2, pred3, pred4 == pair, triple, quad predicates.                      *)
(*            predC1 a == [pred x | x != a].                                  *)
(*      [predU1 a & A] == [pred x | (x == a) || (x \in A)].                   *)
(*      [predD1 A & a] == [pred x | x != a & x \in A].                        *)
(*  predU1 a P, predD1 P a == applicative versions of the above.              *)
(*              frel f == the relation associated with f : T -> T.            *)
(*                     := [rel x y | f x == y].                               *)
(*       invariant k f == elements of T whose k-class is f-invariant.         *)
(*                     := [pred x | k (f x) == k x] with f : T -> T.          *)
(*  [fun x : T => e0 with a1 |-> e1, .., a_n |-> e_n]                         *)
(*  [eta f with a1 |-> e1, .., a_n |-> e_n] ==                                *)
(*    the auto-expanding function that maps x = a_i to e_i, and other values  *)
(*    of x to e0 (resp. f x). In the first form the `: T' is optional and x   *)
(*    can occur in a_i or e_i.                                                *)
(* Equality on an eqType is proof-irrelevant (lemma eq_irrelevance).          *)
(*   The eqType interface is implemented for most standard datatypes:         *)
(*  bool, unit, void, option, prod (denoted A * B), sum (denoted A + B),      *)
(*  sig (denoted {x | P}), sigT (denoted {i : I & T}).                        *)
(*   The fields of sig, sig2, and sigT are renamed sval, svalP, s2val,        *)
(* s2valP, s2valP', tag, and tagged, respectively. We also define             *)
(*   Tagged T_ x == eta-friendly constructor for {i : I | T_ i}, x : T_ i.    *)
(*   tagged_as u v == v cast as T_(tag u) if tag v == tag u, else u.          *)
(*  -> We have u == v <=> (tag u == tag v) && (tagged u == tagged_as u v).    *)
(* The subType interface supports the following operations:                   *)
(*      val == the generic injection from a subType S of T into T.            *)
(*             For example, if u : {x : T | P}, then val u : T.               *)
(*             val is injective because P is proof-irrelevant (P is in bool,  *)
(*             and the is_true coercion expands to P = true).                 *)
(*     valP == the generic proof of P (val u) for u : subType P.              *)
(* Sub x Px == the generic constructor for a subType P; Px is a proof of P x  *)
(*             and P should be inferred from the expected return type.        *)
(*  insub x == the generic partial projection of T into a subType S of T.     *)
(*             This returns an option S; if S : subType P then                *)
(*                insub x = Some u with val u = x if P x,                     *)
(*                          None if ~~ P x                                    *)
(*             The insubP lemma encapsulates this dichotomy.                  *)
(*             P should be infered from the expected return type.             *)
(*  innew x == total (non-option) variant of insub when P = predT.            *)
(* {? x | P} == option {x | P} (syntax for casting insub x).                  *)
(* insubd u0 x == the generic projection with default value u0.               *)
(*             := odflt u0 (insub x).                                         *)
(* insigd A0 x == special case of insubd for S == {x | x \in A}, where A0 is  *)
(*                a proof of x0 \in A.                                        *)
(* insub_eq x == transparent version of insub x that expands to Some/None     *)
(*               when P x can evaluate.                                       *)
(*  The subType P interface is most often implemented using one of:           *)
(*   [subType for S_val]                                                      *)
(*     where S_val : S -> T is the first projection of a type S isomorphic to *)
(*     {x : T | P}.                                                           *)
(*   [newType for S_val]                                                      *)
(*     where S_val : S -> T is the projection of a type S isomorphic to       *)
(*     wrapped T; in this case P must be predT.                               *)
(*   [subType for S_val by Srect], [newType for S_val by Srect]               *)
(*     variants of the above where the eliminator is explicitly provided.     *)
(*     Here S no longer needs to be syntactically identical to {x | P x} or   *)
(*     wrapped T, but it must have a derived constructor S_Sub statisfying an *)
(*     eliminator Srect identical to the one the Coq Inductive command would  *)
(*     have generated, and S_val (S_Sub x Px) (resp. S_val (S_sub x) for the  *)
(*     newType form) must be convertible to x.                                *)
(*     variant of the above when S is a wrapper type for T (so P = predT).    *)
(*   [subType of S], [subType of S for S_val]                                 *)
(*     clones the canonical subType structure for S; if S_val is specified,   *)
(*     then it replaces the inferred projector.                               *)
(* Subtypes inherit the eqType structure of their base types; the generic     *)
(* structure should be explicitly instantiated using the                      *)
(*   [eqMixin of S by <:]                                                     *)
(* construct to declare the Equality mixin; this pattern is repeated for all  *)
(* the combinatorial interfaces (Choice, Countable, Finite).                  *)
(*   More generally, the eqType structure can be transfered by (partial)      *)
(* injections, using:                                                         *)
(*   InjEqMixin injf == an Equality mixin for T, using an f : T -> eT where   *)
(*                      eT has an eqType structure and injf : injective f.    *)
(*    PcanEqMixin fK == an Equality mixin similarly derived from f and a left *)
(*                      inverse partial function g and fK : pcancel f g.      *)
(*     CanEqMixin fK == an Equality mixin similarly derived from f and a left *)
(*                      inverse function g and fK : cancel f g.               *)
(*   We add the following to the standard suffixes documented in ssrbool.v:   *)
(*  1, 2, 3, 4 -- explicit enumeration predicate for 1 (singleton), 2, 3, or  *)
(*                4 values.                                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Equality.

Definition axiom T (e : rel T) := forall x y, reflect (x = y) (e x y).

Structure mixin_of T := Mixin {op : rel T; _ : axiom op}.
Notation class_of := mixin_of (only parsing).

Section ClassDef.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition pack c := @Pack T c T.
Definition clone := fun c & cT -> T & phant_id (pack c) cT => pack c.

End ClassDef.

Module Exports.
Coercion sort : type >-> Sortclass.
Notation eqType := type.
Notation EqMixin := Mixin.
Notation EqType T m := (@pack T m).
Notation "[ 'eqMixin' 'of' T ]" := (class _ : mixin_of T)
  (at level 0, format "[ 'eqMixin'  'of'  T ]") : form_scope.
Notation "[ 'eqType' 'of' T 'for' C ]" := (@clone T C _ idfun id)
  (at level 0, format "[ 'eqType'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'eqType' 'of' T ]" := (@clone T _ _ id id)
  (at level 0, format "[ 'eqType'  'of'  T ]") : form_scope.
End Exports.

End Equality.
Export Equality.Exports.

Definition eq_op T := Equality.op (Equality.class T).

Lemma eqE T x : eq_op x = Equality.op (Equality.class T) x.
Proof. by []. Qed.

Lemma eqP T : Equality.axiom (@eq_op T).
Proof. by case: T => ? []. Qed.
Implicit Arguments eqP [T x y].

Delimit Scope eq_scope with EQ.
Open Scope eq_scope.

Notation "x == y" := (eq_op x y)
  (at level 70, no associativity) : bool_scope.
Notation "x == y :> T" := ((x : T) == (y : T))
  (at level 70, y at next level) : bool_scope.
Notation "x != y" := (~~ (x == y))
  (at level 70, no associativity) : bool_scope.
Notation "x != y :> T" := (~~ (x == y :> T))
  (at level 70, y at next level) : bool_scope.
Notation "x =P y" := (eqP : reflect (x = y) (x == y))
  (at level 70, no associativity) : eq_scope.
Notation "x =P y :> T" := (eqP : reflect (x = y :> T) (x == y :> T))
  (at level 70, y at next level, no associativity) : eq_scope.

Prenex Implicits eq_op eqP.

Lemma eq_refl (T : eqType) (x : T) : x == x. Proof. exact/eqP. Qed.
Notation eqxx := eq_refl.

Lemma eq_sym (T : eqType) (x y : T) : (x == y) = (y == x).
Proof. exact/eqP/eqP. Qed.

Hint Resolve eq_refl eq_sym.

Section Contrapositives.

Variable T : eqType.
Implicit Types (A : pred T) (b : bool) (x : T).

Lemma contraTeq b x y : (x != y -> ~~ b) -> b -> x = y.
Proof. by move=> imp hyp; apply/eqP; apply: contraTT hyp. Qed.

Lemma contraNeq b x y : (x != y -> b) -> ~~ b -> x = y.
Proof. by move=> imp hyp; apply/eqP; apply: contraNT hyp. Qed.

Lemma contraFeq b x y : (x != y -> b) -> b = false -> x = y.
Proof. by move=> imp /negbT; apply: contraNeq. Qed.

Lemma contraTneq b x y : (x = y -> ~~ b) -> b -> x != y.
Proof. by move=> imp; apply: contraTN => /eqP. Qed.

Lemma contraNneq b x y : (x = y -> b) -> ~~ b -> x != y.
Proof. by move=> imp; apply: contraNN => /eqP. Qed.

Lemma contraFneq b x y : (x = y -> b) -> b = false -> x != y.
Proof. by move=> imp /negbT; apply: contraNneq. Qed.

Lemma contra_eqN b x y : (b -> x != y) -> x = y -> ~~ b.
Proof. by move=> imp /eqP; apply: contraL. Qed.

Lemma contra_eqF b x y : (b -> x != y) -> x = y -> b = false.
Proof. by move=> imp /eqP; apply: contraTF. Qed.

Lemma contra_eqT b x y : (~~ b -> x != y) -> x = y -> b.
Proof. by move=> imp /eqP; apply: contraLR. Qed.

Lemma contra_eq x1 y1 x2 y2 : (x2 != y2 -> x1 != y1) -> x1 = y1 -> x2 = y2.
Proof. by move=> imp /eqP; apply: contraTeq. Qed.

Lemma contra_neq x1 y1 x2 y2 : (x2 = y2 -> x1 = y1) -> x1 != y1 -> x2 != y2.
Proof. by move=> imp; apply: contraNneq => /imp->. Qed.

Lemma memPn A x : reflect {in A, forall y, y != x} (x \notin A).
Proof.
apply: (iffP idP) => [notDx y | notDx]; first by apply: contraTneq => ->.
exact: contraL (notDx x) _.
Qed.

Lemma ifN_eq R x y vT vF : x != y -> (if x == y then vT else vF) = vF :> R.
Proof. exact: ifN. Qed.

Lemma ifN_eqC R x y vT vF : x != y -> (if y == x then vT else vF) = vF :> R.
Proof. by rewrite eq_sym; apply: ifN. Qed.

End Contrapositives.

Implicit Arguments memPn [T A x].

Theorem eq_irrelevance (T : eqType) x y : forall e1 e2 : x = y :> T, e1 = e2.
Proof.
pose proj z e := if x =P z is ReflectT e0 then e0 else e.
suff: injective (proj y) by rewrite /proj => injp e e'; apply: injp; case: eqP.
pose join (e : x = _) := etrans (esym e).
apply: can_inj (join x y (proj x (erefl x))) _.
by case: y /; case: _ / (proj x _).
Qed.

Corollary eq_axiomK (T : eqType) (x : T) : all_equal_to (erefl x).
Proof. move=> eq_x_x; exact: eq_irrelevance. Qed.

(* We use the module system to circumvent a silly limitation that  *)
(* forbids using the same constant to coerce to different targets. *)
Module Type EqTypePredSig.
Parameter sort : eqType -> predArgType.
End EqTypePredSig.
Module MakeEqTypePred (eqmod : EqTypePredSig).
Coercion eqmod.sort : eqType >-> predArgType.
End MakeEqTypePred.
Module Export EqTypePred := MakeEqTypePred Equality.

Lemma unit_eqP : Equality.axiom (fun _ _ : unit => true).
Proof. by do 2!case; left. Qed.

Definition unit_eqMixin := EqMixin unit_eqP.
Canonical unit_eqType := Eval hnf in EqType unit unit_eqMixin.

(* Comparison for booleans. *)

(* This is extensionally equal, but not convertible to Bool.eqb. *)
Definition eqb b := addb (~~ b).

Lemma eqbP : Equality.axiom eqb.
Proof. by do 2!case; constructor. Qed.

Canonical bool_eqMixin := EqMixin eqbP.
Canonical bool_eqType := Eval hnf in EqType bool bool_eqMixin.

Lemma eqbE : eqb = eq_op. Proof. by []. Qed.

Lemma bool_irrelevance (x y : bool) (E E' : x = y) : E = E'.
Proof. exact: eq_irrelevance. Qed.

Lemma negb_add b1 b2 : ~~ (b1 (+) b2) = (b1 == b2).
Proof. by rewrite -addNb. Qed.

Lemma negb_eqb b1 b2 : (b1 != b2) = b1 (+) b2.
Proof. by rewrite -addNb negbK. Qed.

Lemma eqb_id b : (b == true) = b.
Proof. by case: b. Qed.

Lemma eqbF_neg b : (b == false) = ~~ b.
Proof. by case: b. Qed.

Lemma eqb_negLR b1 b2 : (~~ b1 == b2) = (b1 == ~~ b2).
Proof. by case: b1; case: b2. Qed.

(* Equality-based predicates.       *)

Notation xpred1 := (fun a1 x => x == a1).
Notation xpred2 := (fun a1 a2 x => (x == a1) || (x == a2)).
Notation xpred3 := (fun a1 a2 a3 x => [|| x == a1, x == a2 | x == a3]).
Notation xpred4 :=
  (fun a1 a2 a3 a4 x => [|| x == a1, x == a2, x == a3 | x == a4]).
Notation xpredU1 := (fun a1 (p : pred _) x => (x == a1) || p x).
Notation xpredC1 := (fun a1 x => x != a1).
Notation xpredD1 := (fun (p : pred _) a1 x => (x != a1) && p x).

Section EqPred.

Variable T : eqType.

Definition pred1 (a1 : T) := SimplPred (xpred1 a1).
Definition pred2 (a1 a2 : T) := SimplPred (xpred2 a1 a2).
Definition pred3 (a1 a2 a3 : T) := SimplPred (xpred3 a1 a2 a3).
Definition pred4 (a1 a2 a3 a4 : T) := SimplPred (xpred4 a1 a2 a3 a4).
Definition predU1 (a1 : T) p := SimplPred (xpredU1 a1 p).
Definition predC1 (a1 : T) := SimplPred (xpredC1 a1).
Definition predD1 p (a1 : T) := SimplPred (xpredD1 p a1).

Lemma pred1E : pred1 =2 eq_op. Proof. move=> x y; exact: eq_sym. Qed.

Variables (T2 : eqType) (x y : T) (z u : T2) (b : bool).

Lemma predU1P : reflect (x = y \/ b) ((x == y) || b).
Proof. apply: (iffP orP) => [] []; by [right | move/eqP; left]. Qed.

Lemma pred2P : reflect (x = y \/ z = u) ((x == y) || (z == u)).
Proof. by apply: (iffP orP) => [] [] /eqP; by [left | right]. Qed.

Lemma predD1P : reflect (x <> y /\ b) ((x != y) && b).
Proof. by apply: (iffP andP)=> [] [] // /eqP. Qed.

Lemma predU1l : x = y -> (x == y) || b.
Proof. by move->; rewrite eqxx. Qed.

Lemma predU1r : b -> (x == y) || b.
Proof. by move->; rewrite orbT. Qed.

Lemma eqVneq : {x = y} + {x != y}.
Proof. by case: eqP; [left | right]. Qed.

End EqPred.

Implicit Arguments predU1P [T x y b].
Implicit Arguments pred2P [T T2 x y z u].
Implicit Arguments predD1P [T x y b].
Prenex Implicits pred1 pred2 pred3 pred4 predU1 predC1 predD1 predU1P.

Notation "[ 'predU1' x & A ]" := (predU1 x [mem A])
  (at level 0, format "[ 'predU1'  x  &  A ]") : fun_scope.
Notation "[ 'predD1' A & x ]" := (predD1 [mem A] x)
  (at level 0, format "[ 'predD1'  A  &  x ]") : fun_scope.

(* Lemmas for reflected equality and functions.   *)

Section EqFun.

Section Exo.

Variables (aT rT : eqType) (D : pred aT) (f : aT -> rT) (g : rT -> aT).

Lemma inj_eq : injective f -> forall x y, (f x == f y) = (x == y).
Proof. by move=> inj_f x y; apply/eqP/eqP=> [|-> //]; exact: inj_f. Qed.

Lemma can_eq : cancel f g -> forall x y, (f x == f y) = (x == y).
Proof. move/can_inj; exact: inj_eq. Qed.

Lemma bij_eq : bijective f -> forall x y, (f x == f y) = (x == y).
Proof. move/bij_inj; apply: inj_eq. Qed.

Lemma can2_eq : cancel f g -> cancel g f -> forall x y, (f x == y) = (x == g y).
Proof. by move=> fK gK x y; rewrite -{1}[y]gK; exact: can_eq. Qed.

Lemma inj_in_eq :
  {in D &, injective f} -> {in D &, forall x y, (f x == f y) = (x == y)}.
Proof. by move=> inj_f x y Dx Dy; apply/eqP/eqP=> [|-> //]; exact: inj_f. Qed.

Lemma can_in_eq :
  {in D, cancel f g} -> {in D &, forall x y, (f x == f y) = (x == y)}.
Proof. by move/can_in_inj; exact: inj_in_eq. Qed.

End Exo.

Section Endo.

Variable T : eqType.

Definition frel f := [rel x y : T | f x == y].

Lemma inv_eq f : involutive f -> forall x y : T, (f x == y) = (x == f y).
Proof. by move=> fK; exact: can2_eq. Qed.

Lemma eq_frel f f' : f =1 f' -> frel f =2 frel f'.
Proof. by move=> eq_f x y; rewrite /= eq_f. Qed.

End Endo.

Variable aT : Type.

(* The invariant of an function f wrt a projection k is the pred of points *)
(* that have the same projection as their image.                           *)

Definition invariant (rT : eqType) f (k : aT -> rT) :=
  [pred x | k (f x) == k x].

Variables (rT1 rT2 : eqType) (f : aT -> aT) (h : rT1 -> rT2) (k : aT -> rT1).

Lemma invariant_comp : subpred (invariant f k) (invariant f (h \o k)).
Proof. by move=> x eq_kfx; rewrite /= (eqP eq_kfx). Qed.

Lemma invariant_inj : injective h -> invariant f (h \o k) =1 invariant f k.
Proof. move=> inj_h x; exact: (inj_eq inj_h). Qed.

End EqFun.

Prenex Implicits frel.

(* The coercion to rel must be explicit for derived Notations to unparse. *)
Notation coerced_frel f := (rel_of_simpl_rel (frel f)) (only parsing).

Section FunWith.

Variables (aT : eqType) (rT : Type).

CoInductive fun_delta : Type := FunDelta of aT & rT.

Definition fwith x y (f : aT -> rT) := [fun z => if z == x then y else f z].

Definition app_fdelta df f z :=
  let: FunDelta x y := df in if z == x then y else f z.

End FunWith.

Prenex Implicits fwith.

Notation "x |-> y" := (FunDelta x y)
  (at level 190, no associativity,
   format "'[hv' x '/ '  |->  y ']'") : fun_delta_scope.

Delimit Scope fun_delta_scope with FUN_DELTA.
Arguments Scope app_fdelta [_ type_scope fun_delta_scope _ _].

Notation "[ 'fun' z : T => F 'with' d1 , .. , dn ]" :=
  (SimplFunDelta (fun z : T =>
     app_fdelta d1%FUN_DELTA .. (app_fdelta dn%FUN_DELTA  (fun _ => F)) ..))
  (at level 0, z ident, only parsing) : fun_scope.

Notation "[ 'fun' z => F 'with' d1 , .. , dn ]" :=
  (SimplFunDelta (fun z =>
     app_fdelta d1%FUN_DELTA .. (app_fdelta dn%FUN_DELTA (fun _ => F)) ..))
  (at level 0, z ident, format
   "'[hv' [ '[' 'fun'  z  => '/ '  F ']' '/'  'with'  '[' d1 , '/'  .. , '/'  dn ']' ] ']'"
   ) : fun_scope.

Notation "[ 'eta' f 'with' d1 , .. , dn ]" :=
  (SimplFunDelta (fun _ =>
     app_fdelta d1%FUN_DELTA .. (app_fdelta dn%FUN_DELTA f) ..))
  (at level 0, z ident, format
  "'[hv' [ '[' 'eta' '/ '  f ']' '/'  'with'  '[' d1 , '/'  .. , '/'  dn ']' ] ']'"
  ) : fun_scope.

(* Various EqType constructions.                                         *)

Section ComparableType.

Variable T : Type.

Definition comparable := forall x y : T, decidable (x = y).

Hypothesis Hcompare : comparable.

Definition compareb x y : bool := Hcompare x y.

Lemma compareP : Equality.axiom compareb.
Proof. by move=> x y; exact: sumboolP. Qed.

Definition comparableClass := EqMixin compareP.

End ComparableType.

Definition eq_comparable (T : eqType) : comparable T :=
  fun x y => decP (x =P y).

Section SubType.

Variables (T : Type) (P : pred T).

Structure subType : Type := SubType {
  sub_sort :> Type;
  val : sub_sort -> T;
  Sub : forall x, P x -> sub_sort;
  _ : forall K (_ : forall x Px, K (@Sub x Px)) u, K u;
  _ : forall x Px, val (@Sub x Px) = x
}.

Implicit Arguments Sub [s].
Lemma vrefl : forall x, P x -> x = x. Proof. by []. Qed.
Definition vrefl_rect := vrefl.

Definition clone_subType U v :=
  fun sT & sub_sort sT -> U =>
  fun c Urec cK (sT' := @SubType U v c Urec cK) & phant_id sT' sT => sT'.

Variable sT : subType.

CoInductive Sub_spec : sT -> Type := SubSpec x Px : Sub_spec (Sub x Px).

Lemma SubP u : Sub_spec u.
Proof. by case: sT Sub_spec SubSpec u => T' _ C rec /= _. Qed.

Lemma SubK x Px : @val sT (Sub x Px) = x.
Proof. by case: sT. Qed.

Definition insub x :=
  if @idP (P x) is ReflectT Px then @Some sT (Sub x Px) else None.

Definition insubd u0 x := odflt u0 (insub x).

CoInductive insub_spec x : option sT -> Type :=
  | InsubSome u of P x & val u = x : insub_spec x (Some u)
  | InsubNone   of ~~ P x          : insub_spec x None.

Lemma insubP x : insub_spec x (insub x).
Proof.
by rewrite /insub; case: {-}_ / idP; [left; rewrite ?SubK | right; exact/negP].
Qed.

Lemma insubT x Px : insub x = Some (Sub x Px).
Proof.
case: insubP; last by case/negP.
case/SubP=> y Py _ def_x; rewrite -def_x SubK in Px *.
congr (Some (Sub _ _)); exact: bool_irrelevance.
Qed.

Lemma insubF x : P x = false -> insub x = None.
Proof. by move/idP; case: insubP. Qed.

Lemma insubN x : ~~ P x -> insub x = None.
Proof. by move/negPf/insubF. Qed.

Lemma isSome_insub : ([eta insub] : pred T) =1 P.
Proof. by apply: fsym => x; case: insubP => // /negPf. Qed.

Lemma insubK : ocancel insub (@val _).
Proof. by move=> x; case: insubP. Qed.

Lemma valP (u : sT) : P (val u).
Proof. by case/SubP: u => x Px; rewrite SubK. Qed.

Lemma valK : pcancel (@val _) insub.
Proof. case/SubP=> x Px; rewrite SubK; exact: insubT. Qed.

Lemma val_inj : injective (@val sT).
Proof. exact: pcan_inj valK. Qed.

Lemma valKd u0 : cancel (@val _) (insubd u0).
Proof. by move=> u; rewrite /insubd valK. Qed.

Lemma val_insubd u0 x : val (insubd u0 x) = if P x then x else val u0.
Proof. by rewrite /insubd; case: insubP => [u -> | /negPf->]. Qed.

Lemma insubdK u0 : {in P, cancel (insubd u0) (@val _)}.
Proof. by move=> x Px; rewrite /= val_insubd [P x]Px. Qed.

Definition insub_eq x :=
  let Some_sub Px := Some (Sub x Px : sT) in
  let None_sub _ := None in
  (if P x as Px return P x = Px -> _ then Some_sub else None_sub) (erefl _).

Lemma insub_eqE : insub_eq =1 insub.
Proof.
rewrite /insub_eq /insub => x; case: {2 3}_ / idP (erefl _) => // Px Px'.
by congr (Some _); apply: val_inj; rewrite !SubK.
Qed.

End SubType.

Implicit Arguments SubType [T P].
Implicit Arguments Sub [T P s].
Implicit Arguments vrefl [T P].
Implicit Arguments vrefl_rect [T P].
Implicit Arguments clone_subType [T P sT c Urec cK].
Implicit Arguments insub [T P sT].
Implicit Arguments insubT [T sT x].
Implicit Arguments val_inj [T P sT].
Prenex Implicits val Sub vrefl vrefl_rect insub insubd val_inj.

Local Notation inlined_sub_rect :=
  (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px).

Local Notation inlined_new_rect :=
  (fun K K_S u => let (x) as u return K u := u in K_S x).

Notation "[ 'subType' 'for' v ]" := (SubType _ v _ inlined_sub_rect vrefl_rect)
 (at level 0, only parsing) : form_scope.

Notation "[ 'sub' 'Type' 'for' v ]" := (SubType _ v _ _ vrefl_rect)
 (at level 0, format "[ 'sub' 'Type'  'for'  v ]") : form_scope.

Notation "[ 'subType' 'for' v 'by' rec ]" := (SubType _ v _ rec vrefl)
 (at level 0, format "[ 'subType'  'for'  v  'by'  rec ]") : form_scope.

Notation "[ 'subType' 'of' U 'for' v ]" := (clone_subType U v id idfun)
 (at level 0, format "[ 'subType'  'of'  U  'for'  v ]") : form_scope.

(*
Notation "[ 'subType' 'for' v ]" := (clone_subType _ v id idfun)
 (at level 0, format "[ 'subType'  'for'  v ]") : form_scope.
*)
Notation "[ 'subType' 'of' U ]" := (clone_subType U _ id id)
 (at level 0, format "[ 'subType'  'of'  U ]") : form_scope.

Definition NewType T U v c Urec :=
  let Urec' P IH := Urec P (fun x : T => IH x isT : P _) in
  SubType U v (fun x _ => c x) Urec'.
Implicit Arguments NewType [T U].

Notation "[ 'newType' 'for' v ]" := (NewType v _ inlined_new_rect vrefl_rect)
 (at level 0, only parsing) : form_scope.

Notation "[ 'new' 'Type' 'for' v ]" := (NewType v _ _ vrefl_rect)
 (at level 0, format "[ 'new' 'Type'  'for'  v ]") : form_scope.

Notation "[ 'newType' 'for' v 'by' rec ]" := (NewType v _ rec vrefl)
 (at level 0, format "[ 'newType'  'for'  v  'by'  rec ]") : form_scope.

Definition innew T nT x := @Sub T predT nT x (erefl true).
Implicit Arguments innew [T nT].
Prenex Implicits innew.

Lemma innew_val T nT : cancel val (@innew T nT).
Proof. by move=> u; apply: val_inj; exact: SubK. Qed.

(* Prenex Implicits and renaming. *)
Notation sval := (@proj1_sig _ _).
Notation "@ 'sval'" := (@proj1_sig) (at level 10, format "@ 'sval'").

Section SigProj.

Variables (T : Type) (P Q : T -> Prop).

Lemma svalP : forall u : sig P, P (sval u). Proof. by case. Qed.

Definition s2val (u : sig2 P Q) := let: exist2 x _ _ := u in x.

Lemma s2valP u : P (s2val u). Proof. by case: u. Qed.

Lemma s2valP' u : Q (s2val u). Proof. by case: u. Qed.

End SigProj.

Prenex Implicits svalP s2val s2valP s2valP'.

Canonical sig_subType T (P : pred T) : subType [eta P] :=
  Eval hnf in [subType for @sval T [eta [eta P]]].

(* Shorthand for sigma types over collective predicates. *)
Notation "{ x 'in' A }" := {x | x \in A}
  (at level 0, x at level 99, format  "{ x  'in'  A }") : type_scope.
Notation "{ x 'in' A | P }" := {x | (x \in A) && P}
  (at level 0, x at level 99, format  "{ x  'in'  A  |  P }") : type_scope.

(* Shorthand for the return type of insub. *)
Notation "{ ? x : T | P }" := (option {x : T | is_true P})
  (at level 0, x at level 99, only parsing) : type_scope.
Notation "{ ? x | P }" := {? x : _ | P}
  (at level 0, x at level 99, format  "{ ?  x  |  P }") : type_scope.
Notation "{ ? x 'in' A }" := {? x | x \in A}
  (at level 0, x at level 99, format  "{ ?  x  'in'  A }") : type_scope.
Notation "{ ? x 'in' A | P }" := {? x | (x \in A) && P}
  (at level 0, x at level 99, format  "{ ?  x  'in'  A  |  P }") : type_scope.

(* A variant of injection with default that infers a collective predicate *)
(* from the membership proof for the default value.                       *)
Definition insigd T (A : mem_pred T) x (Ax : in_mem x A) :=
  insubd (exist [eta A] x Ax).

(* There should be a rel definition for the subType equality op, but this *)
(* seems to cause the simpl tactic to diverge on expressions involving == *)
(* on 4+ nested subTypes in a "strict" position (e.g., after ~~).         *)
(* Definition feq f := [rel x y | f x == f y].                            *)

Section TransferEqType.

Variables (T : Type) (eT : eqType) (f : T -> eT).

Lemma inj_eqAxiom : injective f -> Equality.axiom (fun x y => f x == f y).
Proof. by move=> f_inj x y; apply: (iffP eqP) => [|-> //]; exact: f_inj. Qed.

Definition InjEqMixin f_inj := EqMixin (inj_eqAxiom f_inj).

Definition PcanEqMixin g (fK : pcancel f g) := InjEqMixin (pcan_inj fK).

Definition CanEqMixin g (fK : cancel f g) := InjEqMixin (can_inj fK).

End TransferEqType.

Section SubEqType.

Variables (T : eqType) (P : pred T) (sT : subType P).

Notation Local ev_ax := (fun T v => @Equality.axiom T (fun x y => v x == v y)).
Lemma val_eqP : ev_ax sT val. Proof. exact: inj_eqAxiom val_inj. Qed.

Definition sub_eqMixin := EqMixin val_eqP.
Canonical sub_eqType := Eval hnf in EqType sT sub_eqMixin.

Definition SubEqMixin :=
  (let: SubType _ v _ _ _ as sT' := sT
     return ev_ax sT' val -> Equality.class_of sT' in
   fun vP : ev_ax _ v => EqMixin vP
   ) val_eqP.

Lemma val_eqE (u v : sT) : (val u == val v) = (u == v).
Proof. by []. Qed.

End SubEqType.

Implicit Arguments val_eqP [T P sT x y].
Prenex Implicits val_eqP.

Notation "[ 'eqMixin' 'of' T 'by' <: ]" := (SubEqMixin _ : Equality.class_of T)
  (at level 0, format "[ 'eqMixin'  'of'  T  'by'  <: ]") : form_scope.

Section SigEqType.

Variables (T : eqType) (P : pred T).

Definition sig_eqMixin := Eval hnf in [eqMixin of {x | P x} by <:].
Canonical sig_eqType := Eval hnf in EqType {x | P x} sig_eqMixin.

End SigEqType.

Section ProdEqType.

Variable T1 T2 : eqType.

Definition pair_eq := [rel u v : T1 * T2 | (u.1 == v.1) && (u.2 == v.2)].

Lemma pair_eqP : Equality.axiom pair_eq.
Proof.
move=> [x1 x2] [y1 y2] /=; apply: (iffP andP) => [[]|[<- <-]] //=.
by do 2!move/eqP->.
Qed.

Definition prod_eqMixin := EqMixin pair_eqP.
Canonical prod_eqType := Eval hnf in EqType (T1 * T2) prod_eqMixin.

Lemma pair_eqE : pair_eq = eq_op :> rel _. Proof. by []. Qed.

Lemma xpair_eqE (x1 y1 : T1) (x2 y2 : T2) :
  ((x1, x2) == (y1, y2)) = ((x1 == y1) && (x2 == y2)).
Proof. by []. Qed.

Lemma pair_eq1 (u v : T1 * T2) : u == v -> u.1 == v.1.
Proof. by case/andP. Qed.

Lemma pair_eq2 (u v : T1 * T2) : u == v -> u.2 == v.2.
Proof. by case/andP. Qed.

End ProdEqType.

Implicit Arguments pair_eqP [T1 T2].

Prenex Implicits pair_eqP.

Definition predX T1 T2 (p1 : pred T1) (p2 : pred T2) :=
  [pred z | p1 z.1 & p2 z.2].

Notation "[ 'predX' A1 & A2 ]" := (predX [mem A1] [mem A2])
  (at level 0, format "[ 'predX'  A1  &  A2 ]") : fun_scope.

Section OptionEqType.

Variable T : eqType.

Definition opt_eq (u v : option T) : bool :=
  oapp (fun x => oapp (eq_op x) false v) (~~ v) u.

Lemma opt_eqP : Equality.axiom opt_eq.
Proof.
case=> [x|] [y|] /=; by [constructor | apply: (iffP eqP) => [|[]] ->].
Qed.

Canonical option_eqMixin := EqMixin opt_eqP.
Canonical option_eqType := Eval hnf in EqType (option T) option_eqMixin.

End OptionEqType.

Definition tag := projS1.
Definition tagged I T_ :  forall u, T_(tag u) := @projS2 I [eta T_].
Definition Tagged I i T_ x := @existS I [eta T_] i x.
Implicit Arguments Tagged [I i].
Prenex Implicits tag tagged Tagged.

Section TaggedAs.

Variables (I : eqType) (T_ : I -> Type).
Implicit Types u v : {i : I & T_ i}.

Definition tagged_as u v :=
  if tag u =P tag v is ReflectT eq_uv then
    eq_rect_r T_ (tagged v) eq_uv
  else tagged u.

Lemma tagged_asE u x : tagged_as u (Tagged T_ x) = x.
Proof.
by rewrite /tagged_as /=; case: eqP => // eq_uu; rewrite [eq_uu]eq_axiomK.
Qed.

End TaggedAs.

Section TagEqType.

Variables (I : eqType) (T_ : I -> eqType).
Implicit Types u v : {i : I & T_ i}.

Definition tag_eq u v := (tag u == tag v) && (tagged u == tagged_as u v).

Lemma tag_eqP : Equality.axiom tag_eq.
Proof.
rewrite /tag_eq => [] [i x] [j] /=.
case: eqP => [<-|Hij] y; last by right; case.
by apply: (iffP eqP) => [->|<-]; rewrite tagged_asE.
Qed.

Canonical tag_eqMixin := EqMixin tag_eqP.
Canonical tag_eqType := Eval hnf in EqType {i : I & T_ i} tag_eqMixin.

Lemma tag_eqE : tag_eq = eq_op. Proof. by []. Qed.

Lemma eq_tag u v : u == v -> tag u = tag v.
Proof. by move/eqP->. Qed.

Lemma eq_Tagged u x :(u == Tagged _ x) = (tagged u == x).
Proof. by rewrite -tag_eqE /tag_eq eqxx tagged_asE. Qed.

End TagEqType.

Implicit Arguments tag_eqP [I T_ x y].
Prenex Implicits tag_eqP.

Section SumEqType.

Variables T1 T2 : eqType.
Implicit Types u v : T1 + T2.

Definition sum_eq u v :=
  match u, v with
  | inl x, inl y | inr x, inr y => x == y
  | _, _ => false
  end.

Lemma sum_eqP : Equality.axiom sum_eq.
Proof. case=> x [] y /=; by [right | apply: (iffP eqP) => [->|[->]]]. Qed.

Canonical sum_eqMixin := EqMixin sum_eqP.
Canonical sum_eqType := Eval hnf in EqType (T1 + T2) sum_eqMixin.

Lemma sum_eqE : sum_eq = eq_op. Proof. by []. Qed.

End SumEqType.

Implicit Arguments sum_eqP [T1 T2 x y].
Prenex Implicits sum_eqP.
