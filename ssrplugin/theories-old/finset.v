(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq choice fintype.
Require Import finfun bigop.

(******************************************************************************)
(* This file defines a type for sets over a finite Type, similar to the type  *)
(* of functions over a finite Type defined in finfun.v (indeed, based in it): *)
(*  {set T} where T must have a finType structure                             *)
(* We equip {set T} itself with a finType structure, hence Leibnitz and       *)
(* extensional equalities coincide on {set T}, and we can form {set {set T}}  *)
(*   If A, B : {set T} and P : {set {set T}}, we define:                      *)
(*           x \in A == x belongs to A (i.e., {set T} implements predType,    *)
(*                      by coercion to pred_sort).                            *)
(*             mem A == the predicate corresponding to A.                     *)
(*          finset p == the set corresponding to a predicate p.               *)
(*       [set x | P] == the set containing the x such that P is true (x may   *)
(*                      appear in P).                                         *)
(*   [set x | P & Q] := [set x | P && Q].                                     *)
(*      [set x in A] == the set containing the x in a collective predicate A. *)
(*  [set x in A | P] == the set containing the x in A such that P is true.    *)
(* [set x in A | P & Q] := [set x in A | P && Q].                             *)
(*  All these have typed variants [set x : T | P], [set x : T in A], etc.     *)
(*              set0 == the empty set.                                        *)
(*  [set: T] or setT == the full set (the A containing all x : T).            *)
(*           A :|: B == the union of A and B.                                 *)
(*            x |: A == A with the element x added (:= [set x] :| A).         *)
(*           A :&: B == the intersection of A and B.                          *)
(*              ~: A == the complement of A.                                  *)
(*           A :\: B == the difference A minus B.                             *)
(*            A :\ x == A with the element x removed (:= A :\: [set x]).      *)
(* \bigcup_<range> A == the union of all A, for i in <range> (i is bound in   *)
(*                      A, see bigop.v).                                      *)
(* \bigcap_<range> A == the intersection of all A, for i in <range>.          *)
(*           cover P == the union of the set of sets P.                       *)
(*        trivIset P <=> the elements of P are pairwise disjoint.             *)
(*     partition P A <=> P is a partition of A.                               *)
(*        pblock P x == a block of P containing x, or else set0.              *)
(* equivalence_partition R D == the partition induced on D by the relation R  *)
(*                       (provided R is an equivalence relation in D).        *)
(*       preim_partition f D == the partition induced on D by the equivalence *)
(*                              [rel x y | f x == f y].                       *)
(*    is_transversal X P D <=> X is a transversal of the partition P of D.    *)
(*   transversal P D == a transversal of P, provided P is a partition of D.   *)
(*  transversal_repr x0 X B == a representative of B \in P selected by the    *)
(*                      tranversal X of P, or else x0.                        *)
(*        powerset A == the set of all subset of the set A.                   *)
(*          P ::&: A == those sets in P that are subsets of the set A.        *)
(*         f @^-1: A == the preimage of the collective predicate A under f.   *)
(*            f @: A == the image set of the collective predicate A by f.     *)
(*       f @2:(A, B) == the image set of A x B by the binary function f.      *)
(*  [set E | x in A] == the set of all the values of the expression E, for x  *)
(*                      drawn from the collective predicate A.                *)
(*  [set E | x in A & P] == the set of values of E for x drawn from A, such   *)
(*                      that P is true.                                       *)
(*  [set E | x in A, y in B] == the set of values of E for x drawn from A and *)
(*                      and y drawn from B; B may depend on x.                *)
(*  [set E | x <- A, y <- B & P] == the set of values of E for x drawn from A *)
(*                      y drawn from B, such that P is trye.                  *)
(*  [set E | x : T] == the set of all values of E, with x in type T.          *)
(*  [set E | x : T & P] == the set of values of E for x : T s.t. P is true.   *)
(*  [set E | x : T, y : U in B], [set E | x : T, y : U in B & P],             *)
(*  [set E | x : T in A, y : U], [set E | x : T in A, y : U & P],             *)
(*  [set E | x : T, y : U], [set E | x : T, y : U & P]                        *)
(*             == type-ranging versions of the binary comprehensions.         *)
(*   [set E | x : T in A], [set E | x in A, y], [set E | x, y & P], etc.      *)
(*             == typed and untyped variants of the comprehensions above.     *)
(*                The types may be required as type inference processes E     *)
(*                before considering A or B. Note that type casts in the      *)
(*                binary comprehension must either be both present or absent  *)
(*                and that there are no untyped variants for single-type      *)
(*                comprehension as Coq parsing confuses [x | P] and [E | x].  *)
(*        minset p A == A is a minimal set satisfying p.                      *)
(*        maxset p A == A is a maximal set satisfying p.                      *)
(* We also provide notations A :=: B, A :<>: B, A :==: B, A :!=: B, A :=P: B  *)
(* that specialize A = B, A <> B, A == B, etc., to {set _}. This is useful    *)
(* for subtypes of {set T}, such as {group T}, that coerce to {set T}.        *)
(*   We give many lemmas on these operations, on card, and on set inclusion.  *)
(* In addition to the standard suffixes described in ssrbool.v, we associate  *)
(* the following suffixes to set operations:                                  *)
(*  0 -- the empty set, as in in_set0 : (x \in set0) = false.                 *)
(*  T -- the full set, as in in_setT : x \in [set: T].                        *)
(*  1 -- a singleton set, as in in_set1 : (x \in [set a]) = (x == a).         *)
(*  2 -- an unordered pair, as in                                             *)
(*          in_set2 : (x \in [set a; b]) = (x == a) || (x == b).              *)
(*  C -- complement, as in setCK : ~: ~: A = A.                               *)
(*  I -- intersection, as in setIid : A :&: A = A.                            *)
(*  U -- union, as in setUid : A :|: A = A.                                   *)
(*  D -- difference, as in setDv : A :\: A = set0.                            *)
(*  S -- a subset argument, as in                                             *)
(*         setIS: B \subset C -> A :&: B \subset A :&: C                      *)
(* These suffixes are sometimes preceded with an `s' to distinguish them from *)
(* their basic ssrbool interpretation, e.g.,                                  *)
(*  card1 : #|pred1 x| = 1 and cards1 : #|[set x]| = 1                        *)
(* We also use a trailling `r' to distinguish a right-hand complement from    *)
(* commutativity, e.g.,                                                       *)
(*  setIC : A :&: B = B :&: A and setICr : A :&: ~: A = set0.                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section SetType.

Variable T : finType.

Inductive set_type : predArgType := FinSet of {ffun pred T}.
Definition finfun_of_set A := let: FinSet f := A in f.
Definition set_of of phant T := set_type.
Identity Coercion type_of_set_of : set_of >-> set_type.

Canonical set_subType := Eval hnf in [newType for finfun_of_set].
Definition set_eqMixin := Eval hnf in [eqMixin of set_type by <:].
Canonical set_eqType := Eval hnf in EqType set_type set_eqMixin.
Definition set_choiceMixin := [choiceMixin of set_type by <:].
Canonical set_choiceType := Eval hnf in ChoiceType set_type set_choiceMixin.
Definition set_countMixin := [countMixin of set_type by <:].
Canonical set_countType := Eval hnf in CountType set_type set_countMixin.
Canonical set_subCountType := Eval hnf in [subCountType of set_type].
Definition set_finMixin := [finMixin of set_type by <:].
Canonical set_finType := Eval hnf in FinType set_type set_finMixin.
Canonical set_subFinType := Eval hnf in [subFinType of set_type].

End SetType.

Delimit Scope set_scope with SET.
Bind Scope set_scope with set_type.
Bind Scope set_scope with set_of.
Open Scope set_scope.
Arguments Scope finfun_of_set [_ set_scope].

Notation "{ 'set' T }" := (set_of (Phant T))
  (at level 0, format "{ 'set'  T }") : type_scope.

(* We later define several subtypes that coerce to set; for these it is       *)
(* preferable to state equalities at the {set _} level, even when comparing   *)
(* subtype values, because the primitive "injection" tactic tends to diverge  *)
(* on complex types (e.g., quotient groups). We provide some parse-only       *)
(* notation to make this technicality less obstrusive.                        *)
Notation "A :=: B" := (A = B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :<>: B" := (A <> B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :==: B" := (A == B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :!=: B" := (A != B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.
Notation "A :=P: B" := (A =P B :> {set _})
  (at level 70, no associativity, only parsing) : set_scope.

Notation Local finset_def := (fun T P => @FinSet T (finfun P)).

Notation Local pred_of_set_def := (fun T (A : set_type T) => val A : _ -> _).

Module Type SetDefSig.
Parameter finset : forall T : finType, pred T -> {set T}.
Parameter pred_of_set : forall T, set_type T -> fin_pred_sort (predPredType T).
(* The weird type of pred_of_set is imposed by the syntactic restrictions on  *)
(* coercion declarations; it is unfortunately not possible to use a functor   *)
(* to retype the declaration, because this triggers an ugly bug in the Coq    *)
(* coercion chaining code.                                                    *)
Axiom finsetE : finset = finset_def.
Axiom pred_of_setE : pred_of_set = pred_of_set_def.
End SetDefSig.

Module SetDef : SetDefSig.
Definition finset := finset_def.
Definition pred_of_set := pred_of_set_def.
Lemma finsetE : finset = finset_def. Proof. by []. Qed.
Lemma pred_of_setE : pred_of_set = pred_of_set_def. Proof. by []. Qed.
End SetDef.

Notation finset := SetDef.finset.
Notation pred_of_set := SetDef.pred_of_set.
Canonical finset_unlock := Unlockable SetDef.finsetE.
Canonical pred_of_set_unlock := Unlockable SetDef.pred_of_setE.

Notation "[ 'set' x : T | P ]" := (finset (fun x : T => P%B))
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]") : set_scope.
Notation "[ 'set' x 'in' A ]" := [set x | x \in A]
  (at level 0, x at level 99, format "[ 'set'  x  'in'  A ]") : set_scope.
Notation "[ 'set' x : T 'in' A ]" := [set x : T | x \in A]
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x : T | P & Q ]" := [set x : T | P && Q]
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x | P & Q ]" := [set x | P && Q ]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P  &  Q ]") : set_scope.
Notation "[ 'set' x : T 'in' A | P ]" := [set x : T | x \in A & P]
  (at level 0, x at level 99, only parsing) : set_scope.
Notation "[ 'set' x 'in' A | P ]" := [set x | x \in A & P]
  (at level 0, x at level 99, format "[ 'set'  x  'in'  A  |  P ]") : set_scope.
Notation "[ 'set' x 'in' A | P & Q ]" := [set x in A | P && Q]
  (at level 0, x at level 99,
   format "[ 'set'  x  'in'  A  |  P  &  Q ]") : set_scope.
Notation "[ 'set' x : T 'in' A | P & Q ]" := [set x : T in A | P && Q]
  (at level 0, x at level 99, only parsing) : set_scope.

(* This lets us use set and subtypes of set, like group or coset_of, both as  *)
(* collective predicates and as arguments of the \pi(_) notation.             *)
Coercion pred_of_set: set_type >-> fin_pred_sort.

(* Declare pred_of_set as a canonical instance of topred, but use the         *)
(* coercion to resolve mem A to @mem (predPredType T) (pred_of_set A).        *)
Canonical set_predType T :=
  Eval hnf in @mkPredType _ (unkeyed (set_type T)) (@pred_of_set T).

Section BasicSetTheory.

Variable T : finType.
Implicit Types (x : T) (A B : {set T}) (pA : pred T).

Canonical set_of_subType := Eval hnf in [subType of {set T}].
Canonical set_of_eqType := Eval hnf in [eqType of {set T}].
Canonical set_of_choiceType := Eval hnf in [choiceType of {set T}].
Canonical set_of_countType := Eval hnf in [countType of {set T}].
Canonical set_of_subCountType := Eval hnf in [subCountType of {set T}].
Canonical set_of_finType := Eval hnf in [finType of {set T}].
Canonical set_of_subFinType := Eval hnf in [subFinType of {set T}].

Lemma in_set pA x : x \in finset pA = pA x.
Proof. by rewrite [@finset]unlock unlock [x \in _]ffunE. Qed.

Lemma setP A B : A =i B <-> A = B.
Proof.
by split=> [eqAB|-> //]; apply/val_inj/ffunP=> x; have:= eqAB x; rewrite unlock.
Qed.

Definition set0 := [set x : T | false].
Definition setTfor (phT : phant T) := [set x : T | true].

Lemma in_setT x : x \in setTfor (Phant T).
Proof. by rewrite in_set. Qed.

Lemma eqsVneq A B : (A = B) + (A != B).
Proof. exact: eqVneq. Qed.

End BasicSetTheory.

Definition inE := (in_set, inE).

Implicit Arguments set0 [T].
Prenex Implicits set0.
Hint Resolve in_setT.

Notation "[ 'set' : T ]" := (setTfor (Phant T))
  (at level 0, format "[ 'set' :  T ]") : set_scope.

Notation setT := [set: _] (only parsing).

Section setOpsDefs.

Variable T : finType.
Implicit Types (a x : T) (A B D : {set T}) (P : {set {set T}}).

Definition set1 a := [set x | x == a].
Definition setU A B := [set x | (x \in A) || (x \in B)].
Definition setI A B := [set x in A | x \in B].
Definition setC A := [set x | x \notin A].
Definition setD A B := [set x | x \notin B & x \in A].
Definition ssetI P D := [set A in P | A \subset D].
Definition powerset D := [set A : {set T} | A \subset D].

End setOpsDefs.

Notation "[ 'set' a ]" := (set1 a)
  (at level 0, a at level 99, format "[ 'set'  a ]") : set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)]
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]") : set_scope.
Notation "A :|: B" := (setU A B) : set_scope.
Notation "a |: A" := ([set a] :|: A) : set_scope.
(* This is left-associative due to historical limitations of the .. Notation. *)
Notation "[ 'set' a1 ; a2 ; .. ; an ]" := (setU .. (a1 |: [set a2]) .. [set an])
  (at level 0, a1 at level 99,
   format "[ 'set'  a1 ;  a2 ;  .. ;  an ]") : set_scope.
Notation "A :&: B" := (setI A B) : set_scope.
Notation "~: A" := (setC A) (at level 35, right associativity) : set_scope.
Notation "[ 'set' ~ a ]" := (~: [set a])
  (at level 0, format "[ 'set' ~  a ]") : set_scope.
Notation "A :\: B" := (setD A B) : set_scope.
Notation "A :\ a" := (A :\: [set a]) : set_scope.
Notation "P ::&: D" := (ssetI P D) (at level 48) : set_scope.

Section setOps.

Variable T : finType.
Implicit Types (a x : T) (A B C D : {set T}) (pA pB pC : pred T).

Lemma eqEsubset A B : (A == B) = (A \subset B) && (B \subset A).
Proof. by apply/eqP/subset_eqP=> /setP. Qed.

Lemma subEproper A B : A \subset B = (A == B) || (A \proper B).
Proof. by rewrite eqEsubset -andb_orr orbN andbT. Qed.

Lemma eqVproper A B : A \subset B -> A = B \/ A \proper B.
Proof. by rewrite subEproper => /predU1P. Qed.

Lemma properEneq A B : A \proper B = (A != B) && (A \subset B).
Proof. by rewrite andbC eqEsubset negb_and andb_orr andbN. Qed.

Lemma proper_neq A B : A \proper B -> A != B.
Proof. by rewrite properEneq; case/andP. Qed.

Lemma eqEproper A B : (A == B) = (A \subset B) && ~~ (A \proper B).
Proof. by rewrite negb_and negbK andb_orr andbN eqEsubset. Qed.

Lemma eqEcard A B : (A == B) = (A \subset B) && (#|B| <= #|A|).
Proof.
rewrite eqEsubset; apply: andb_id2l => sAB.
by rewrite (geq_leqif (subset_leqif_card sAB)).
Qed.

Lemma properEcard A B : (A \proper B) = (A \subset B) && (#|A| < #|B|).
Proof. by rewrite properEneq ltnNge andbC eqEcard; case: (A \subset B). Qed.

Lemma subset_leqif_cards A B : A \subset B -> (#|A| <= #|B| ?= iff (A == B)).
Proof. by move=> sAB; rewrite eqEsubset sAB; exact: subset_leqif_card. Qed.

Lemma in_set0 x : x \in set0 = false.
Proof. by rewrite inE. Qed.

Lemma sub0set A : set0 \subset A.
Proof. by apply/subsetP=> x; rewrite inE. Qed.

Lemma subset0 A : (A \subset set0) = (A == set0).
Proof. by rewrite eqEsubset sub0set andbT. Qed.

Lemma proper0 A : (set0 \proper A) = (A != set0).
Proof. by rewrite properE sub0set subset0. Qed.

Lemma subset_neq0 A B : A \subset B -> A != set0 -> B != set0.
Proof. by rewrite -!proper0 => sAB /proper_sub_trans->. Qed.

Lemma set_0Vmem A : (A = set0) + {x : T | x \in A}.
Proof.
case: (pickP (mem A)) => [x Ax | A0]; [by right; exists x | left].
apply/setP=> x; rewrite inE; exact: A0.
Qed.

Lemma enum_set0 : enum set0 = [::] :> seq T.
Proof. by rewrite (eq_enum (in_set _)) enum0. Qed.

Lemma subsetT A : A \subset setT.
Proof. by apply/subsetP=> x; rewrite inE. Qed.

Lemma subsetT_hint mA : subset mA (mem [set: T]).
Proof. by rewrite unlock; apply/pred0P=> x; rewrite !inE. Qed.
Hint Resolve subsetT_hint.

Lemma subTset A : (setT \subset A) = (A == setT).
Proof. by rewrite eqEsubset subsetT. Qed.

Lemma properT A : (A \proper setT) = (A != setT).
Proof. by rewrite properEneq subsetT andbT. Qed.

Lemma set1P x a : reflect (x = a) (x \in [set a]).
Proof. by rewrite inE; exact: eqP. Qed.

Lemma enum_setT : enum [set: T] = Finite.enum T.
Proof. by rewrite (eq_enum (in_set _)) enumT. Qed.

Lemma in_set1 x a : (x \in [set a]) = (x == a).
Proof. exact: in_set. Qed.

Lemma set11 x : x \in [set x].
Proof. by rewrite inE. Qed.

Lemma set1_inj : injective (@set1 T).
Proof. by move=> a b eqsab; apply/set1P; rewrite -eqsab set11. Qed.

Lemma enum_set1 a : enum [set a] = [:: a].
Proof. by rewrite (eq_enum (in_set _)) enum1. Qed.

Lemma setU1P x a B : reflect (x = a \/ x \in B) (x \in a |: B).
Proof. by rewrite !inE; exact: predU1P. Qed.

Lemma in_setU1 x a B : (x \in a |: B) = (x == a) || (x \in B).
Proof. by rewrite !inE. Qed.

Lemma set_cons a s : [set x in a :: s] = a |: [set x in s].
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma setU11 x B : x \in x |: B.
Proof. by rewrite !inE eqxx. Qed.

Lemma setU1r x a B : x \in B -> x \in a |: B.
Proof. by move=> Bx; rewrite !inE predU1r. Qed.

(* We need separate lemmas for the explicit enumerations since they *)
(* associate on the left.                                           *)
Lemma set1Ul x A b : x \in A -> x \in A :|: [set b].
Proof. by move=> Ax; rewrite !inE Ax. Qed.

Lemma set1Ur A b : b \in A :|: [set b].
Proof. by rewrite !inE eqxx orbT. Qed.

Lemma in_setC1 x a : (x \in [set~ a]) = (x != a).
Proof. by rewrite !inE. Qed.

Lemma setC11 x : (x \in [set~ x]) = false.
Proof. by rewrite !inE eqxx. Qed.

Lemma setD1P x A b : reflect (x != b /\ x \in A) (x \in A :\ b).
Proof. rewrite !inE; exact: andP. Qed.

Lemma in_setD1 x A b : (x \in A :\ b) = (x != b) && (x \in A) .
Proof. by rewrite !inE. Qed.

Lemma setD11 b A : (b \in A :\ b) = false.
Proof. by rewrite !inE eqxx. Qed.

Lemma setD1K a A : a \in A -> a |: (A :\ a) = A.
Proof. by move=> Aa; apply/setP=> x; rewrite !inE; case: eqP => // ->. Qed.

Lemma setU1K a B : a \notin B -> (a |: B) :\ a = B.
Proof.
by move/negPf=> nBa; apply/setP=> x; rewrite !inE; case: eqP => // ->.
Qed.

Lemma set2P x a b : reflect (x = a \/ x = b) (x \in [set a; b]).
Proof. rewrite !inE; exact: pred2P. Qed.

Lemma in_set2 x a b : (x \in [set a; b]) = (x == a) || (x == b).
Proof. by rewrite !inE. Qed.

Lemma set21 a b : a \in [set a; b].
Proof. by rewrite !inE eqxx. Qed.

Lemma set22 a b : b \in [set a; b].
Proof. by rewrite !inE eqxx orbT. Qed.

Lemma setUP x A B : reflect (x \in A \/ x \in B) (x \in A :|: B).
Proof. by rewrite !inE; exact: orP. Qed.

Lemma in_setU x A B : (x \in A :|: B) = (x \in A) || (x \in B).
Proof. exact: in_set. Qed.

Lemma setUC A B : A :|: B = B :|: A.
Proof. by apply/setP => x; rewrite !inE orbC. Qed.

Lemma setUS A B C : A \subset B -> C :|: A \subset C :|: B.
Proof.
move=> sAB; apply/subsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (subsetP sAB).
Qed.

Lemma setSU A B C : A \subset B -> A :|: C \subset B :|: C.
Proof. by move=> sAB; rewrite -!(setUC C) setUS. Qed.

Lemma setUSS A B C D : A \subset C -> B \subset D -> A :|: B \subset C :|: D.
Proof. by move=> /(setSU B) /subset_trans sAC /(setUS C)/sAC. Qed.

Lemma set0U A : set0 :|: A = A.
Proof. by apply/setP => x; rewrite !inE orFb. Qed.

Lemma setU0 A : A :|: set0 = A.
Proof. by rewrite setUC set0U. Qed.

Lemma setUA A B C : A :|: (B :|: C) = A :|: B :|: C.
Proof. by apply/setP => x; rewrite !inE orbA. Qed.

Lemma setUCA A B C : A :|: (B :|: C) = B :|: (A :|: C).
Proof. by rewrite !setUA (setUC B). Qed.

Lemma setUAC A B C : A :|: B :|: C = A :|: C :|: B.
Proof. by rewrite -!setUA (setUC B). Qed.

Lemma setUACA A B C D : (A :|: B) :|: (C :|: D) = (A :|: C) :|: (B :|: D).
Proof. by rewrite -!setUA (setUCA B). Qed.

Lemma setTU A : setT :|: A = setT.
Proof. by apply/setP => x; rewrite !inE orTb. Qed.

Lemma setUT A : A :|: setT = setT.
Proof. by rewrite setUC setTU. Qed.

Lemma setUid A : A :|: A = A.
Proof. by apply/setP=> x; rewrite inE orbb. Qed.

Lemma setUUl A B C : A :|: B :|: C = (A :|: C) :|: (B :|: C).
Proof. by rewrite setUA !(setUAC _ C) -(setUA _ C) setUid. Qed.

Lemma setUUr A B C : A :|: (B :|: C) = (A :|: B) :|: (A :|: C).
Proof. by rewrite !(setUC A) setUUl. Qed.

(* intersection *)

(* setIdP is a generalisation of setIP that applies to comprehensions. *)
Lemma setIdP x pA pB : reflect (pA x /\ pB x) (x \in [set y | pA y & pB y]).
Proof. by rewrite !inE; exact: andP. Qed.

Lemma setId2P x pA pB pC :
  reflect [/\ pA x, pB x & pC x] (x \in [set y | pA y & pB y && pC y]).
Proof. by rewrite !inE; exact: and3P. Qed.

Lemma setIdE A pB : [set x in A | pB x] = A :&: [set x | pB x].
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma setIP x A B : reflect (x \in A /\ x \in B) (x \in A :&: B).
Proof. exact: (iffP (@setIdP _ _ _)). Qed.

Lemma in_setI x A B : (x \in A :&: B) = (x \in A) && (x \in B).
Proof. exact: in_set. Qed.

Lemma setIC A B : A :&: B = B :&: A.
Proof. by apply/setP => x; rewrite !inE andbC. Qed.

Lemma setIS A B C : A \subset B -> C :&: A \subset C :&: B.
Proof.
move=> sAB; apply/subsetP=> x; rewrite !inE.
by case: (x \in C) => //; exact: (subsetP sAB).
Qed.

Lemma setSI A B C : A \subset B -> A :&: C \subset B :&: C.
Proof. by move=> sAB; rewrite -!(setIC C) setIS. Qed.

Lemma setISS A B C D : A \subset C -> B \subset D -> A :&: B \subset C :&: D.
Proof. by move=> /(setSI B) /subset_trans sAC /(setIS C) /sAC. Qed.

Lemma setTI A : setT :&: A = A.
Proof. by apply/setP => x; rewrite !inE andTb. Qed.

Lemma setIT A : A :&: setT = A.
Proof. by rewrite setIC setTI. Qed.

Lemma set0I A : set0 :&: A = set0.
Proof. by apply/setP => x; rewrite !inE andFb. Qed.

Lemma setI0 A : A :&: set0 = set0.

Proof. by rewrite setIC set0I. Qed.

Lemma setIA A B C : A :&: (B :&: C) = A :&: B :&: C.
Proof. by apply/setP=> x; rewrite !inE andbA. Qed.

Lemma setICA A B C : A :&: (B :&: C) = B :&: (A :&: C).
Proof. by rewrite !setIA (setIC A). Qed.

Lemma setIAC A B C : A :&: B :&: C = A :&: C :&: B.
Proof. by rewrite -!setIA (setIC B). Qed.

Lemma setIACA A B C D : (A :&: B) :&: (C :&: D) = (A :&: C) :&: (B :&: D).
Proof. by rewrite -!setIA (setICA B). Qed.

Lemma setIid A : A :&: A = A.
Proof. by apply/setP=> x; rewrite inE andbb. Qed.

Lemma setIIl A B C : A :&: B :&: C = (A :&: C) :&: (B :&: C).
Proof. by rewrite setIA !(setIAC _ C) -(setIA _ C) setIid. Qed.

Lemma setIIr A B C : A :&: (B :&: C) = (A :&: B) :&: (A :&: C).
Proof. by rewrite !(setIC A) setIIl. Qed.

(* distribute /cancel *)

Lemma setIUr A B C : A :&: (B :|: C) = (A :&: B) :|: (A :&: C).
Proof. by apply/setP=> x; rewrite !inE andb_orr. Qed.

Lemma setIUl A B C : (A :|: B) :&: C = (A :&: C) :|: (B :&: C).
Proof. by apply/setP=> x; rewrite !inE andb_orl. Qed.

Lemma setUIr A B C : A :|: (B :&: C) = (A :|: B) :&: (A :|: C).
Proof. by apply/setP=> x; rewrite !inE orb_andr. Qed.

Lemma setUIl A B C : (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
Proof. by apply/setP=> x; rewrite !inE orb_andl. Qed.

Lemma setUK A B : (A :|: B) :&: A = A.
Proof. by apply/setP=> x; rewrite !inE orbK. Qed.

Lemma setKU A B : A :&: (B :|: A) = A.
Proof. by apply/setP=> x; rewrite !inE orKb. Qed.

Lemma setIK A B : (A :&: B) :|: A = A.
Proof. by apply/setP=> x; rewrite !inE andbK. Qed.

Lemma setKI A B : A :|: (B :&: A) = A.
Proof. by apply/setP=> x; rewrite !inE andKb. Qed.

(* complement *)

Lemma setCP x A : reflect (~ x \in A) (x \in ~: A).
Proof. by rewrite !inE; exact: negP. Qed.

Lemma in_setC x A : (x \in ~: A) = (x \notin A).
Proof. exact: in_set. Qed.

Lemma setCK : involutive (@setC T).
Proof. by move=> A; apply/setP=> x; rewrite !inE negbK. Qed.

Lemma setC_inj : injective (@setC T).
Proof. exact: can_inj setCK. Qed.

Lemma subsets_disjoint A B : (A \subset B) = [disjoint A & ~: B].
Proof. by rewrite subset_disjoint; apply: eq_disjoint_r => x; rewrite !inE. Qed.

Lemma disjoints_subset A B : [disjoint A & B] = (A \subset ~: B).
Proof. by rewrite subsets_disjoint setCK. Qed.

Lemma powersetCE A B : (A \in powerset (~: B)) = [disjoint A & B].
Proof. by rewrite inE disjoints_subset. Qed.

Lemma setCS A B : (~: A \subset ~: B) = (B \subset A).
Proof. by rewrite !subsets_disjoint setCK disjoint_sym. Qed.

Lemma setCU A B : ~: (A :|: B) = ~: A :&: ~: B.
Proof. by apply/setP=> x; rewrite !inE negb_or. Qed.

Lemma setCI A B : ~: (A :&: B) = ~: A :|: ~: B.
Proof. by apply/setP=> x; rewrite !inE negb_and. Qed.

Lemma setUCr A : A :|: ~: A = setT.
Proof. by apply/setP=> x; rewrite !inE orbN. Qed.

Lemma setICr A : A :&: ~: A = set0.
Proof. by apply/setP=> x; rewrite !inE andbN. Qed.

Lemma setC0 : ~: set0 = [set: T].
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma setCT : ~: [set: T] = set0.
Proof. by rewrite -setC0 setCK. Qed.

(* difference *)

Lemma setDP A B x : reflect (x \in A /\ x \notin B) (x \in A :\: B).
Proof. by rewrite inE andbC; exact: andP. Qed.

Lemma in_setD A B x : (x \in A :\: B) = (x \notin B) && (x \in A).
Proof. exact: in_set. Qed.

Lemma setDE A B : A :\: B = A :&: ~: B.
Proof. by apply/setP => x; rewrite !inE andbC. Qed.

Lemma setSD A B C : A \subset B -> A :\: C \subset B :\: C.
Proof. by rewrite !setDE; exact: setSI. Qed.

Lemma setDS A B C : A \subset B -> C :\: B \subset C :\: A.
Proof. by rewrite !setDE -setCS; exact: setIS. Qed.

Lemma setDSS A B C D : A \subset C -> D \subset B -> A :\: B \subset C :\: D.
Proof. by move=> /(setSD B) /subset_trans sAC /(setDS C) /sAC. Qed.

Lemma setD0 A : A :\: set0 = A.
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma set0D A : set0 :\: A = set0.
Proof. by apply/setP=> x; rewrite !inE andbF. Qed.

Lemma setDT A : A :\: setT = set0.
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma setTD A : setT :\: A = ~: A.
Proof. by apply/setP=> x; rewrite !inE andbT. Qed.

Lemma setDv A : A :\: A = set0.
Proof. by apply/setP=> x; rewrite !inE andNb. Qed.

Lemma setCD A B : ~: (A :\: B) = ~: A :|: B.
Proof. by rewrite !setDE setCI setCK. Qed.

Lemma setID A B : A :&: B :|: A :\: B = A.
Proof. by rewrite setDE -setIUr setUCr setIT. Qed.

Lemma setDUl A B C : (A :|: B) :\: C = (A :\: C) :|: (B :\: C).
Proof. by rewrite !setDE setIUl. Qed.

Lemma setDUr A B C : A :\: (B :|: C) = (A :\: B) :&: (A :\: C).
Proof. by rewrite !setDE setCU setIIr. Qed.

Lemma setDIl A B C : (A :&: B) :\: C = (A :\: C) :&: (B :\: C).
Proof. by rewrite !setDE setIIl. Qed.

Lemma setDIr A B C : A :\: (B :&: C) = (A :\: B) :|: (A :\: C).
Proof. by rewrite !setDE setCI setIUr. Qed.

Lemma setDDl A B C : (A :\: B) :\: C = A :\: (B :|: C).
Proof. by rewrite !setDE setCU setIA. Qed.

Lemma setDDr A B C : A :\: (B :\: C) = (A :\: B) :|: (A :&: C).
Proof. by rewrite !setDE setCI setIUr setCK. Qed.

(* powerset *)

Lemma powersetE A B : (A \in powerset B) = (A \subset B).
Proof. by rewrite inE. Qed.

Lemma powersetS A B : (powerset A \subset powerset B) = (A \subset B).
Proof.
apply/subsetP/idP=> [sAB | sAB C]; last by rewrite !inE => /subset_trans ->.
by rewrite -powersetE sAB // inE.
Qed.

Lemma powerset0 : powerset set0 = [set set0] :> {set {set T}}.
Proof. by apply/setP=> A; rewrite !inE subset0. Qed.

Lemma powersetT : powerset [set: T] = [set: {set T}].
Proof. by apply/setP=> A; rewrite !inE subsetT. Qed.

Lemma setI_powerset P A : P :&: powerset A = P ::&: A.
Proof. by apply/setP=> B; rewrite !inE. Qed.

(* cardinal lemmas for sets *)

Lemma cardsE pA : #|[set x in pA]| = #|pA|.
Proof. by apply: eq_card; exact: in_set. Qed.

Lemma sum1dep_card pA : \sum_(x | pA x) 1 = #|[set x | pA x]|.
Proof. by rewrite sum1_card cardsE. Qed.

Lemma sum_nat_dep_const pA n : \sum_(x | pA x) n = #|[set x | pA x]| * n.
Proof. by rewrite sum_nat_const cardsE. Qed.

Lemma cards0 : #|@set0 T| = 0.
Proof. by rewrite cardsE card0. Qed.

Lemma cards_eq0 A : (#|A| == 0) = (A == set0).
Proof. by rewrite (eq_sym A) eqEcard sub0set cards0 leqn0. Qed.

Lemma set0Pn A : reflect (exists x, x \in A) (A != set0).
Proof. by rewrite -cards_eq0; exact: existsP. Qed.

Lemma card_gt0 A : (0 < #|A|) = (A != set0).
Proof. by rewrite lt0n cards_eq0. Qed.

Lemma cards0_eq A : #|A| = 0 -> A = set0.
Proof. by move=> A_0; apply/setP=> x; rewrite inE (card0_eq A_0). Qed.

Lemma cards1 x : #|[set x]| = 1.
Proof. by rewrite cardsE card1. Qed.

Lemma cardsUI A B : #|A :|: B| + #|A :&: B| = #|A| + #|B|.
Proof. by rewrite !cardsE cardUI. Qed.

Lemma cardsU A B : #|A :|: B| = (#|A| + #|B| - #|A :&: B|)%N.
Proof. by rewrite -cardsUI addnK. Qed.

Lemma cardsI A B : #|A :&: B| = (#|A| + #|B| - #|A :|: B|)%N.
Proof. by rewrite  -cardsUI addKn. Qed.

Lemma cardsT : #|[set: T]| = #|T|.
Proof. by rewrite cardsE. Qed.

Lemma cardsID B A : #|A :&: B| + #|A :\: B| = #|A|.
Proof. by rewrite !cardsE cardID. Qed.

Lemma cardsD A B : #|A :\: B| = (#|A| - #|A :&: B|)%N.
Proof. by rewrite -(cardsID B A) addKn. Qed.

Lemma cardsC A : #|A| + #|~: A| = #|T|.
Proof. by rewrite cardsE cardC. Qed.

Lemma cardsCs A : #|A| = #|T| - #|~: A|.
Proof. by rewrite -(cardsC A) addnK. Qed.

Lemma cardsU1 a A : #|a |: A| = (a \notin A) + #|A|.
Proof. by rewrite -cardU1; apply: eq_card=> x; rewrite !inE. Qed.

Lemma cards2 a b : #|[set a; b]| = (a != b).+1.
Proof. by rewrite -card2; apply: eq_card=> x; rewrite !inE. Qed.

Lemma cardsC1 a : #|[set~ a]| = #|T|.-1.
Proof. by rewrite -(cardC1 a); apply: eq_card=> x; rewrite !inE. Qed.

Lemma cardsD1 a A : #|A| = (a \in A) + #|A :\ a|.
Proof.
by rewrite (cardD1 a); congr (_ + _); apply: eq_card => x; rewrite !inE.
Qed.

(* other inclusions *)

Lemma subsetIl A B : A :&: B \subset A.
Proof. by apply/subsetP=> x; rewrite inE; case/andP. Qed.

Lemma subsetIr A B : A :&: B \subset B.
Proof. by apply/subsetP=> x; rewrite inE; case/andP. Qed.

Lemma subsetUl A B : A \subset A :|: B.
Proof. by apply/subsetP=> x; rewrite inE => ->. Qed.

Lemma subsetUr A B : B \subset A :|: B.
Proof. by apply/subsetP=> x; rewrite inE orbC => ->. Qed.

Lemma subsetU1 x A : A \subset x |: A.
Proof. exact: subsetUr. Qed.

Lemma subsetDl A B : A :\: B \subset A.
Proof. by rewrite setDE subsetIl. Qed.

Lemma subD1set A x : A :\ x \subset A.
Proof. by rewrite subsetDl. Qed.

Lemma subsetDr A B : A :\: B \subset ~: B.
Proof. by rewrite setDE subsetIr. Qed.

Lemma sub1set A x : ([set x] \subset A) = (x \in A).
Proof. by rewrite -subset_pred1; apply: eq_subset=> y; rewrite !inE. Qed.

Lemma cards1P A : reflect (exists x, A = [set x]) (#|A| == 1).
Proof.
apply: (iffP idP) => [|[x ->]]; last by rewrite cards1.
rewrite eq_sym eqn_leq card_gt0 => /andP[/set0Pn[x Ax] leA1].
by exists x; apply/eqP; rewrite eq_sym eqEcard sub1set Ax cards1 leA1.
Qed.

Lemma subset1 A x : (A \subset [set x]) = (A == [set x]) || (A == set0).
Proof.
rewrite eqEcard cards1 -cards_eq0 orbC andbC.
by case: posnP => // A0; rewrite (cards0_eq A0) sub0set.
Qed.

Lemma powerset1 x : powerset [set x] = [set set0; [set x]].
Proof. by apply/setP=> A; rewrite !inE subset1 orbC. Qed.

Lemma setIidPl A B : reflect (A :&: B = A) (A \subset B).
Proof.
apply: (iffP subsetP) => [sAB | <- x /setIP[] //].
by apply/setP=> x; rewrite inE; apply: andb_idr; exact: sAB.
Qed.
Implicit Arguments setIidPl [A B].

Lemma setIidPr A B : reflect (A :&: B = B) (B \subset A).
Proof. rewrite setIC; exact: setIidPl. Qed.

Lemma cardsDS A B : B \subset A -> #|A :\: B| = (#|A| - #|B|)%N.
Proof. by rewrite cardsD => /setIidPr->. Qed.

Lemma setUidPl A B : reflect (A :|: B = A) (B \subset A).
Proof.
by rewrite -setCS (sameP setIidPl eqP) -setCU (inj_eq setC_inj); exact: eqP.
Qed.

Lemma setUidPr A B : reflect (A :|: B = B) (A \subset B).
Proof. rewrite setUC; exact: setUidPl. Qed.

Lemma setDidPl A B : reflect (A :\: B = A) [disjoint A & B].
Proof. rewrite setDE disjoints_subset; exact: setIidPl. Qed.

Lemma subIset A B C : (B \subset A) || (C \subset A) -> (B :&: C \subset A).
Proof. by case/orP; apply: subset_trans; rewrite (subsetIl, subsetIr). Qed.

Lemma subsetI A B C : (A \subset B :&: C) = (A \subset B) && (A \subset C).
Proof.
rewrite !(sameP setIidPl eqP) setIA; have [-> //| ] := altP (A :&: B =P A).
by apply: contraNF => /eqP <-; rewrite -setIA -setIIl setIAC.
Qed.

Lemma subsetIP A B C : reflect (A \subset B /\ A \subset C) (A \subset B :&: C).
Proof. by rewrite subsetI; exact: andP. Qed.

Lemma subsetIidl A B : (A \subset A :&: B) = (A \subset B).
Proof. by rewrite subsetI subxx. Qed.

Lemma subsetIidr A B : (B \subset A :&: B) = (B \subset A).
Proof. by rewrite setIC subsetIidl. Qed.

Lemma powersetI A B : powerset (A :&: B) = powerset A :&: powerset B.
Proof. by apply/setP=> C; rewrite !inE subsetI. Qed.

Lemma subUset A B C : (B :|: C \subset A) = (B \subset A) && (C \subset A).
Proof. by rewrite -setCS setCU subsetI !setCS. Qed.

Lemma subsetU A B C : (A \subset B) || (A \subset C) -> A \subset B :|: C.
Proof. by rewrite -!(setCS _ A) setCU; exact: subIset. Qed.

Lemma subUsetP A B C : reflect (A \subset C /\ B \subset C) (A :|: B \subset C).
Proof. by rewrite subUset; exact: andP. Qed.

Lemma subsetC A B : (A \subset ~: B) = (B \subset ~: A).
Proof. by rewrite -setCS setCK. Qed.

Lemma subCset A B : (~: A \subset B) = (~: B \subset A).
Proof. by rewrite -setCS setCK. Qed.

Lemma subsetD A B C : (A \subset B :\: C) = (A \subset B) && [disjoint A & C].
Proof. by rewrite setDE subsetI -disjoints_subset. Qed.

Lemma subDset A B C : (A :\: B \subset C) = (A \subset B :|: C).
Proof.
apply/subsetP/subsetP=> sABC x; rewrite !inE.
  by case Bx: (x \in B) => // Ax; rewrite sABC ?inE ?Bx.
by case Bx: (x \in B) => //; move/sABC; rewrite inE Bx.
Qed.

Lemma subsetDP A B C :
  reflect (A \subset B /\ [disjoint A & C]) (A \subset B :\: C).
Proof. by rewrite subsetD; exact: andP. Qed.

Lemma setU_eq0 A B : (A :|: B == set0) = (A == set0) && (B == set0).
Proof. by rewrite -!subset0 subUset. Qed.

Lemma setD_eq0 A B : (A :\: B == set0) = (A \subset B).
Proof. by rewrite -subset0 subDset setU0. Qed.

Lemma setI_eq0 A B : (A :&: B == set0) = [disjoint A & B].
Proof. by rewrite disjoints_subset -setD_eq0 setDE setCK. Qed.

Lemma disjoint_setI0 A B : [disjoint A & B] -> A :&: B = set0.
Proof. by rewrite -setI_eq0; move/eqP. Qed.

Lemma subsetD1 A B x : (A \subset B :\ x) = (A \subset B) && (x \notin A).
Proof. by rewrite setDE subsetI subsetC sub1set inE. Qed.

Lemma subsetD1P A B x : reflect (A \subset B /\ x \notin A) (A \subset B :\ x).
Proof. by rewrite subsetD1; exact: andP. Qed.

Lemma properD1 A x : x \in A -> A :\ x \proper A.
Proof.
move=> Ax; rewrite properE subsetDl; apply/subsetPn; exists x=> //.
by rewrite in_setD1 Ax eqxx.
Qed.

Lemma properIr A B : ~~ (B \subset A) -> A :&: B \proper B.
Proof. by move=> nsAB; rewrite properE subsetIr subsetI negb_and nsAB. Qed.

Lemma properIl A B : ~~ (A \subset B) -> A :&: B \proper A.
Proof. by move=> nsBA; rewrite properE subsetIl subsetI negb_and nsBA orbT. Qed.

Lemma properUr A B : ~~ (A \subset B) ->  B \proper A :|: B.
Proof. by rewrite properE subsetUr subUset subxx /= andbT. Qed.

Lemma properUl A B : ~~ (B \subset A) ->  A \proper A :|: B.
Proof. by move=> not_sBA; rewrite setUC properUr. Qed.

Lemma proper1set A x : ([set x] \proper A) -> (x \in A).
Proof. by move/proper_sub; rewrite sub1set. Qed.

Lemma properIset A B C : (B \proper A) || (C \proper A) -> (B :&: C \proper A).
Proof. by case/orP; apply: sub_proper_trans; rewrite (subsetIl, subsetIr). Qed.

Lemma properI A B C : (A \proper B :&: C) -> (A \proper B) && (A \proper C).
Proof.
move=> pAI; apply/andP.
by split; apply: (proper_sub_trans pAI); rewrite (subsetIl, subsetIr).
Qed.

Lemma properU A B C : (B :|: C \proper A) -> (B \proper A) && (C \proper A).
Proof.
move=> pUA; apply/andP.
by split; apply: sub_proper_trans pUA; rewrite (subsetUr, subsetUl).
Qed.

Lemma properD A B C : (A \proper B :\: C) -> (A \proper B) && [disjoint A & C].
Proof. by rewrite setDE disjoints_subset => /properI/andP[-> /proper_sub]. Qed.

End setOps.

Implicit Arguments set1P [T x a].
Implicit Arguments set1_inj [T].
Implicit Arguments set2P [T x a b].
Implicit Arguments setIdP [T x pA pB].
Implicit Arguments setIP [T x A B].
Implicit Arguments setU1P [T x a B].
Implicit Arguments setD1P [T x A b].
Implicit Arguments setUP [T x A B].
Implicit Arguments setDP [T x A B].
Implicit Arguments cards1P [T A].
Implicit Arguments setCP [T x A].
Implicit Arguments setIidPl [T A B].
Implicit Arguments setIidPr [T A B].
Implicit Arguments setUidPl [T A B].
Implicit Arguments setUidPr [T A B].
Implicit Arguments setDidPl [T A B].
Implicit Arguments subsetIP [T A B C].
Implicit Arguments subUsetP [T A B C].
Implicit Arguments subsetDP [T A B C].
Implicit Arguments subsetD1P [T A B x].
Prenex Implicits set1 set1_inj.
Prenex Implicits set1P set2P setU1P setD1P setIdP setIP setUP setDP.
Prenex Implicits cards1P setCP setIidPl setIidPr setUidPl setUidPr setDidPl.
Hint Resolve subsetT_hint.

Section setOpsAlgebra.

Import Monoid.

Variable T : finType.

Canonical setI_monoid := Law (@setIA T) (@setTI T) (@setIT T).

Canonical setI_comoid := ComLaw (@setIC T).
Canonical setI_muloid := MulLaw (@set0I T) (@setI0 T).

Canonical setU_monoid := Law (@setUA T) (@set0U T) (@setU0 T).
Canonical setU_comoid := ComLaw (@setUC T).
Canonical setU_muloid := MulLaw (@setTU T) (@setUT T).

Canonical setI_addoid := AddLaw (@setUIl T) (@setUIr T).
Canonical setU_addoid := AddLaw (@setIUl T) (@setIUr T).

End setOpsAlgebra.

Section CartesianProd.

Variables fT1 fT2 : finType.
Variables (A1 : {set fT1}) (A2 : {set fT2}).

Definition setX := [set u | u.1 \in A1 & u.2 \in A2].

Lemma in_setX x1 x2 : ((x1, x2) \in setX) = (x1 \in A1) && (x2 \in A2).
Proof. by rewrite inE. Qed.

Lemma setXP x1 x2 : reflect (x1 \in A1 /\ x2 \in A2) ((x1, x2) \in setX).
Proof. by rewrite inE; exact: andP. Qed.

Lemma cardsX : #|setX| = #|A1| * #|A2|.
Proof. by rewrite cardsE cardX. Qed.

End CartesianProd.

Implicit Arguments setXP [x1 x2 fT1 fT2 A1 A2].
Prenex Implicits setXP.

Notation Local imset_def :=
  (fun (aT rT : finType) f mD => [set y in @image_mem aT rT f mD]).
Notation Local imset2_def :=
  (fun (aT1 aT2 rT : finType) f (D1 : mem_pred aT1) (D2 : _ -> mem_pred aT2) =>
     [set y in @image_mem _ rT (prod_curry f)
                           (mem [pred u | D1 u.1 & D2 u.1 u.2])]).

Module Type ImsetSig.
Parameter imset : forall aT rT : finType,
 (aT -> rT) -> mem_pred aT -> {set rT}.
Parameter imset2 : forall aT1 aT2 rT : finType,
 (aT1 -> aT2 -> rT) -> mem_pred aT1 -> (aT1 -> mem_pred aT2) -> {set rT}.
Axiom imsetE : imset = imset_def.
Axiom imset2E : imset2 = imset2_def.
End ImsetSig.

Module Imset : ImsetSig.
Definition imset := imset_def.
Definition imset2 := imset2_def.
Lemma imsetE : imset = imset_def. Proof. by []. Qed.
Lemma imset2E : imset2 = imset2_def. Proof. by []. Qed.
End Imset.

Notation imset := Imset.imset.
Notation imset2 := Imset.imset2.
Canonical imset_unlock := Unlockable Imset.imsetE.
Canonical imset2_unlock := Unlockable Imset.imset2E.
Definition preimset (aT : finType) rT f (R : mem_pred rT) :=
  [set x : aT | in_mem (f x) R].

Notation "f @^-1: A" := (preimset f (mem A)) (at level 24) : set_scope.
Notation "f @: A" := (imset f (mem A)) (at level 24) : set_scope.
Notation "f @2: ( A , B )" := (imset2 f (mem A) (fun _ => mem B))
  (at level 24, format "f  @2:  ( A ,  B )") : set_scope.

(* Comprehensions *)
Notation "[ 'set' E | x 'in' A ]" := ((fun x => E) @: A)
  (at level 0, E, x at level 99,
   format "[ '[hv' 'set'  E '/ '  |  x  'in'  A ] ']'") : set_scope.
Notation "[ 'set' E | x 'in' A & P ]" := [set E | x in [set x in A | P]]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'set'  E '/ '  |  x  'in'  A '/ '  &  P ] ']'") : set_scope.
Notation "[ 'set' E | x 'in' A , y 'in' B ]" :=
  (imset2 (fun x y => E) (mem A) (fun x => (mem B)))
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  'in'  A , '/   '  y  'in'  B ] ']'"
  ) : set_scope.
Notation "[ 'set' E | x 'in' A , y 'in' B & P ]" :=
  [set E | x in A, y in [set y in B | P]]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  'in'  A , '/   '  y  'in'  B '/ '  &  P ] ']'"
  ) : set_scope.

(* Typed variants. *)
Notation "[ 'set' E | x : T 'in' A ]" := ((fun x : T => E) @: A)
  (at level 0, E, x at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x : T 'in' A & P ]" :=
  [set E | x : T in [set x : T in A | P]]
  (at level 0, E, x at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x : T 'in' A , y : U 'in' B ]" :=
  (imset2 (fun (x : T) (y : U) => E) (mem A) (fun (x : T) => (mem B)))
  (at level 0, E, x, y at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x : T 'in' A , y : U 'in' B & P ]" :=
  [set E | x : T in A, y : U in [set y : U in B | P]]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.

(* Comprehensions over a type. *)
Local Notation predOfType T := (sort_of_simpl_pred (@pred_of_argType T)).
Notation "[ 'set' E | x : T ]" := [set E | x : T in predOfType T]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'set'  E '/ '  |  x  :  T ] ']'") : set_scope.
Notation "[ 'set' E | x : T & P ]" := [set E | x : T in [set x : T | P]]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'set'  E '/ '  |  x  :  T '/ '  &  P ] ']'") : set_scope.
Notation "[ 'set' E | x : T , y : U 'in' B ]" :=
  [set E | x : T in predOfType T, y : U in B]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  :  T , '/   '  y  :  U  'in'  B ] ']'")
   : set_scope.
Notation "[ 'set' E | x : T , y : U 'in' B & P ]" :=
  [set E | x : T, y : U in [set y in B | P]]
  (at level 0, E, x, y at level 99, format
 "[ '[hv ' 'set'  E '/'  |  x  :  T , '/  '  y  :  U  'in'  B '/'  &  P ] ']'"
  ) : set_scope.
Notation "[ 'set' E | x : T 'in' A , y : U ]" :=
  [set E | x : T in A, y : U in predOfType U]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  :  T  'in'  A , '/   '  y  :  U ] ']'")
   : set_scope.
Notation "[ 'set' E | x : T 'in' A , y : U & P ]" :=
  [set E | x : T in A, y : U in [set y in P]]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  :  T  'in'  A , '/   '  y  :  U  &  P ] ']'")
   : set_scope.
Notation "[ 'set' E | x : T , y : U ]" :=
  [set E | x : T, y : U in predOfType U]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  :  T , '/   '  y  :  U ] ']'")
   : set_scope.
Notation "[ 'set' E | x : T , y : U & P ]" :=
  [set E | x : T, y : U in [set y in P]]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'set'  E '/ '  |  x  :  T , '/   '  y  :  U  &  P ] ']'")
   : set_scope.

(* Untyped variants. *)
Notation "[ 'set' E | x , y 'in' B ]" := [set E | x : _, y : _ in B]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x , y 'in' B & P ]" := [set E | x : _, y : _ in B & P]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x 'in' A , y ]" := [set E | x : _ in A, y : _]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x 'in' A , y & P ]" := [set E | x : _ in A, y : _ & P]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x , y ]" := [set E | x : _, y : _]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.
Notation "[ 'set' E | x , y & P ]" := [set E | x : _, y : _ & P ]
  (at level 0, E, x, y at level 99, only parsing) : set_scope.

(* Print-only variants to work around the Coq pretty-printer K-term kink. *)
Notation "[ 'se' 't' E | x 'in' A , y 'in' B ]" :=
  (imset2 (fun x y => E) (mem A) (fun _ => mem B))
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'se' 't'  E '/ '  |  x  'in'  A , '/   '  y  'in'  B ] ']'")
   : set_scope.
Notation "[ 'se' 't' E | x 'in' A , y 'in' B & P ]" :=
  [se t E | x in A, y in [set y in B | P]]
  (at level 0, E, x, y at level 99, format
 "[ '[hv ' 'se' 't'  E '/'  |  x  'in'  A , '/  '  y  'in'  B '/'  &  P ] ']'"
  ) : set_scope.
Notation "[ 'se' 't' E | x : T , y : U 'in' B ]" :=
  (imset2 (fun x (y : U) => E) (mem (predOfType T)) (fun _ => mem B))
  (at level 0, E, x, y at level 99, format
   "[ '[hv ' 'se' 't'  E '/'  |  x  :  T , '/  '  y  :  U  'in'  B ] ']'")
   : set_scope.
Notation "[ 'se' 't' E | x : T , y : U 'in' B & P ]" :=
  [se t E | x : T, y : U in [set y in B | P]]
  (at level 0, E, x, y at level 99, format
"[ '[hv ' 'se' 't'  E '/'  |  x  :  T , '/  '  y  :  U  'in'  B '/'  &  P ] ']'"
  ) : set_scope.
Notation "[ 'se' 't' E | x : T 'in' A , y : U ]" :=
  (imset2 (fun x y => E) (mem A) (fun _ : T => mem (predOfType U)))
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'se' 't'  E '/ '  |  x  :  T  'in'  A , '/   '  y  :  U ] ']'")
   : set_scope.
Notation "[ 'se' 't' E | x : T 'in' A , y : U & P ]" :=
  (imset2 (fun x (y : U) => E) (mem A) (fun _ : T => mem [set y \in P]))
  (at level 0, E, x, y at level 99, format
"[ '[hv ' 'se' 't'  E '/'  |  x  :  T  'in'  A , '/  '  y  :  U '/'  &  P ] ']'"
  ) : set_scope.
Notation "[ 'se' 't' E | x : T , y : U ]" :=
  [se t E | x : T, y : U in predOfType U]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'se' 't'  E '/ '  |  x  :  T , '/   '  y  :  U ] ']'")
   : set_scope.
Notation "[ 'se' 't' E | x : T , y : U & P ]" :=
  [se t E | x : T, y : U in [set y in P]]
  (at level 0, E, x, y at level 99, format
   "[ '[hv' 'se' 't'  E '/'  |  x  :  T , '/   '  y  :  U '/'  &  P ] ']'")
   : set_scope.

Section FunImage.

Variables aT aT2 : finType.

Section ImsetTheory.

Variable rT : finType.

Section ImsetProp.

Variables (f : aT -> rT) (f2 : aT -> aT2 -> rT).

Lemma imsetP D y : reflect (exists2 x, in_mem x D & y = f x) (y \in imset f D).
Proof. rewrite [@imset]unlock inE; exact: imageP. Qed.

CoInductive imset2_spec D1 D2 y : Type :=
  Imset2spec x1 x2 of in_mem x1 D1 & in_mem x2 (D2 x1) & y = f2 x1 x2.

Lemma imset2P D1 D2 y : reflect (imset2_spec D1 D2 y) (y \in imset2 f2 D1 D2).
Proof.
rewrite [@imset2]unlock inE.
apply: (iffP imageP) => [[[x1 x2] Dx12] | [x1 x2 Dx1 Dx2]] -> {y}.
  by case/andP: Dx12; exists x1 x2.
by exists (x1, x2); rewrite //= !inE Dx1.
Qed.

Lemma mem_imset (D : pred aT) x : x \in D -> f x \in f @: D.
Proof. by move=> Dx; apply/imsetP; exists x. Qed.

Lemma imset0 : f @: set0 = set0.
Proof. by apply/setP => y; rewrite inE; apply/imsetP=> [[x]]; rewrite inE. Qed.

Lemma imset_eq0 (A : {set aT}) : (f @: A == set0) = (A == set0).
Proof.
have [-> | [x Ax]] := set_0Vmem A; first by rewrite imset0 !eqxx.
by rewrite -!cards_eq0 (cardsD1 x) Ax (cardsD1 (f x)) mem_imset.
Qed.

Lemma imset_set1 x : f @: [set x] = [set f x].
Proof.
apply/setP => y.
by apply/imsetP/set1P=> [[x' /set1P-> //]| ->]; exists x; rewrite ?set11.
Qed.

Lemma mem_imset2 (D : pred aT) (D2 : aT -> pred aT2) x x2 :
    x \in D -> x2 \in D2 x ->
  f2 x x2 \in imset2 f2 (mem D) (fun x1 => mem (D2 x1)).
Proof. by move=> Dx Dx2; apply/imset2P; exists x x2. Qed.

Lemma sub_imset_pre (A : pred aT) (B : pred rT) :
  (f @: A \subset B) = (A \subset f @^-1: B).
Proof.
apply/subsetP/subsetP=> [sfAB x Ax | sAf'B fx].
  by rewrite inE sfAB ?mem_imset.
by case/imsetP=> x Ax ->; move/sAf'B: Ax; rewrite inE.
Qed.

Lemma preimsetS (A B : pred rT) :
  A \subset B -> (f @^-1: A) \subset (f @^-1: B).
Proof. move=> sAB; apply/subsetP=> y; rewrite !inE; exact: (subsetP sAB). Qed.

Lemma preimset0 : f @^-1: set0 = set0.
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma preimsetT : f @^-1: setT = setT.
Proof. by apply/setP=> x; rewrite !inE. Qed.

Lemma preimsetI (A B : {set rT}) :
  f @^-1: (A :&: B) = (f @^-1: A) :&: (f @^-1: B).
Proof. by apply/setP=> y; rewrite !inE. Qed.

Lemma preimsetU (A B : {set rT}) :
  f @^-1: (A :|: B) = (f @^-1: A) :|: (f @^-1: B).
Proof. by apply/setP=> y; rewrite !inE. Qed.

Lemma preimsetD (A B : {set rT}) :
  f @^-1: (A :\: B) = (f @^-1: A) :\: (f @^-1: B).
Proof. by apply/setP=> y; rewrite !inE. Qed.

Lemma preimsetC (A : {set rT}) : f @^-1: (~: A) = ~: f @^-1: A.
Proof. by apply/setP=> y; rewrite !inE. Qed.

Lemma imsetS (A B : pred aT) : A \subset B -> f @: A \subset f @: B.
Proof.
move=> sAB; apply/subsetP=> _ /imsetP[x Ax ->].
by apply/imsetP; exists x; rewrite ?(subsetP sAB).
Qed.

Lemma imset_proper (A B : {set aT}) :
   {in B &, injective f} -> A \proper B -> f @: A \proper f @: B.
Proof.
move=> injf /properP[sAB [x Bx nAx]]; rewrite properE imsetS //=.
apply: contra nAx => sfBA.
have: f x \in f @: A by rewrite (subsetP sfBA) ?mem_imset.
by case/imsetP=> y Ay /injf-> //; exact: subsetP sAB y Ay.
Qed.

Lemma preimset_proper (A B : {set rT}) :
  B \subset codom f -> A \proper B -> (f @^-1: A) \proper (f @^-1: B).
Proof.
move=> sBc /properP[sAB [u Bu nAu]]; rewrite properE preimsetS //=.
by apply/subsetPn; exists (iinv (subsetP sBc  _ Bu)); rewrite inE /= f_iinv.
Qed.

Lemma imsetU (A B : {set aT}) : f @: (A :|: B) = (f @: A) :|: (f @: B).
Proof.
apply/eqP; rewrite eqEsubset subUset.
rewrite 2?imsetS (andbT, subsetUl, subsetUr) // andbT.
apply/subsetP=> _ /imsetP[x ABx ->]; apply/setUP.
by case/setUP: ABx => [Ax | Bx]; [left | right]; apply/imsetP; exists x.
Qed.

Lemma imsetU1 a (A : {set aT}) : f @: (a |: A) = f a |: (f @: A).
Proof. by rewrite imsetU imset_set1. Qed.

Lemma imsetI (A B : {set aT}) :
  {in A & B, injective f} -> f @: (A :&: B) = f @: A :&: f @: B.
Proof.
move=> injf; apply/eqP; rewrite eqEsubset subsetI.
rewrite 2?imsetS (andTb, subsetIl, subsetIr) //=.
apply/subsetP=> _ /setIP[/imsetP[x Ax ->] /imsetP[z Bz /injf eqxz]].
by rewrite mem_imset // inE Ax eqxz.
Qed.

Lemma imset2Sl (A B : pred aT) (C : pred aT2) :
  A \subset B -> f2 @2: (A, C) \subset f2 @2: (B, C).
Proof.
move=> sAB; apply/subsetP=> _ /imset2P[x y Ax Cy ->].
by apply/imset2P; exists x y; rewrite ?(subsetP sAB).
Qed.

Lemma imset2Sr (A B : pred aT2) (C : pred aT) :
  A \subset B -> f2 @2: (C, A) \subset f2 @2: (C, B).
Proof.
move=> sAB; apply/subsetP=> _ /imset2P[x y Ax Cy ->].
by apply/imset2P; exists x y; rewrite ?(subsetP sAB).
Qed.

Lemma imset2S (A B : pred aT) (A2 B2 : pred aT2) :
  A \subset B ->  A2 \subset B2 -> f2 @2: (A, A2) \subset f2 @2: (B, B2).
Proof.  by move=> /(imset2Sl B2) sBA /(imset2Sr A)/subset_trans->. Qed.

End ImsetProp.

Implicit Types (f g : aT -> rT) (D : {set aT}) (R : pred rT).

Lemma eq_preimset f g R : f =1 g -> f @^-1: R = g @^-1: R.
Proof. by move=> eqfg; apply/setP => y; rewrite !inE eqfg. Qed.

Lemma eq_imset f g D : f =1 g -> f @: D = g @: D.
Proof.
move=> eqfg; apply/setP=> y.
by apply/imsetP/imsetP=> [] [x Dx ->]; exists x; rewrite ?eqfg.
Qed.

Lemma eq_in_imset f g D : {in D, f =1 g} -> f @: D = g @: D.
Proof.
move=> eqfg; apply/setP => y.
by apply/imsetP/imsetP=> [] [x Dx ->]; exists x; rewrite ?eqfg.
Qed.

Lemma eq_in_imset2 (f g : aT -> aT2 -> rT) (D : pred aT) (D2 : pred aT2) :
  {in D & D2, f =2 g} -> f @2: (D, D2) = g @2: (D, D2).
Proof.
move=> eqfg; apply/setP => y.
by apply/imset2P/imset2P=> [] [x x2 Dx Dx2 ->]; exists x x2; rewrite ?eqfg.
Qed.

End ImsetTheory.

Lemma imset2_pair (A : {set aT}) (B : {set aT2}) :
  [set (x, y) | x in A, y in B] = setX A B.
Proof.
apply/setP=> [[x y]]; rewrite !inE /=.
by apply/imset2P/andP=> [[_ _ _ _ [-> ->]//]| []]; exists x y.
Qed.

Lemma setXS (A1 B1 : {set aT}) (A2 B2 : {set aT2}) :
  A1 \subset B1 -> A2 \subset B2 -> setX A1 A2 \subset setX B1 B2.
Proof. by move=> sAB1 sAB2; rewrite -!imset2_pair imset2S. Qed.

End FunImage.

Implicit Arguments imsetP [aT rT f D y].
Implicit Arguments imset2P [aT aT2 rT f2 D1 D2 y].
Prenex Implicits imsetP imset2P.

Section BigOps.

Variables (R : Type) (idx : R).
Variables (op : Monoid.law idx) (aop : Monoid.com_law idx).
Variables I J : finType.
Implicit Type A B : {set I}.
Implicit Type h : I -> J.
Implicit Type P : pred I.
Implicit Type F : I -> R.

Lemma big_set0 F : \big[op/idx]_(i in set0) F i = idx.
Proof. by apply: big_pred0 => i; rewrite inE. Qed.

Lemma big_set1 a F : \big[op/idx]_(i in [set a]) F i = F a.
Proof. by apply: big_pred1 => i; rewrite !inE. Qed.

Lemma big_setIDdep A B P F :
  \big[aop/idx]_(i in A | P i) F i =
     aop (\big[aop/idx]_(i in A :&: B | P i) F i)
         (\big[aop/idx]_(i in A :\: B | P i) F i).
Proof.
rewrite (bigID (mem B)) setDE.
by congr (aop _ _); apply: eq_bigl => i; rewrite !inE andbAC.
Qed.

Lemma big_setID A B F :
  \big[aop/idx]_(i in A) F i =
     aop (\big[aop/idx]_(i in A :&: B) F i)
         (\big[aop/idx]_(i in A :\: B) F i).
Proof.
rewrite (bigID (mem B)) !(eq_bigl _ _ (in_set _)) //=.
by congr (aop _); apply: eq_bigl => i; rewrite andbC.
Qed.

Lemma big_setD1 a A F : a \in A ->
  \big[aop/idx]_(i in A) F i = aop (F a) (\big[aop/idx]_(i in A :\ a) F i).
Proof.
move=> Aa; rewrite (bigD1 a Aa); congr (aop _).
by apply: eq_bigl => x; rewrite !inE andbC.
Qed.

Lemma big_setU1 a A F : a \notin A ->
  \big[aop/idx]_(i in a |: A) F i = aop (F a) (\big[aop/idx]_(i in A) F i).
Proof. by move=> notAa; rewrite (@big_setD1 a) ?setU11 //= setU1K. Qed.

Lemma big_imset h (A : pred I) G :
     {in A &, injective h} ->
  \big[aop/idx]_(j in h @: A) G j = \big[aop/idx]_(i in A) G (h i).
Proof.
move=> injh; pose hA := mem (image h A).
have [x0 Ax0 | A0] := pickP A; last first.
  by rewrite !big_pred0 // => x; apply/imsetP=> [[i]]; rewrite unfold_in A0.
rewrite (eq_bigl hA) => [|j]; last by exact/imsetP/imageP.
pose h' j := if insub j : {? j | hA j} is Some u then iinv (svalP u) else x0.
rewrite (reindex_onto h h') => [|j hAj]; rewrite {}/h'; last first.
  by rewrite (insubT hA hAj) f_iinv.
apply: eq_bigl => i; case: insubP => [u -> /= def_u | nhAhi].
  set i' := iinv _; have Ai' : i' \in A := mem_iinv (svalP u).
  by apply/eqP/idP=> [<- // | Ai]; apply: injh; rewrite ?f_iinv.
symmetry; rewrite (negbTE nhAhi); apply/idP=> Ai.
by case/imageP: nhAhi; exists i.
Qed.

Lemma partition_big_imset h (A : pred I) F :
  \big[aop/idx]_(i in A) F i =
     \big[aop/idx]_(j in h @: A) \big[aop/idx]_(i in A | h i == j) F i.
Proof. by apply: partition_big => i Ai; apply/imsetP; exists i. Qed.

End BigOps.

Implicit Arguments big_setID [R idx aop I A].
Implicit Arguments big_setD1 [R idx aop I A F].
Implicit Arguments big_setU1 [R idx aop I A F].
Implicit Arguments big_imset [R idx aop h I J A].
Implicit Arguments partition_big_imset [R idx aop I J].

Section Fun2Set1.

Variables aT1 aT2 rT : finType.
Variables (f : aT1 -> aT2 -> rT).

Lemma imset2_set1l x1 (D2 : pred aT2) : f @2: ([set x1], D2) = f x1 @: D2.
Proof.
apply/setP=> y; apply/imset2P/imsetP=> [[x x2 /set1P->]| [x2 Dx2 ->]].
  by exists x2.
by exists x1 x2; rewrite ?set11.
Qed.

Lemma imset2_set1r x2 (D1 : pred aT1) : f @2: (D1, [set x2]) = f^~ x2 @: D1.
Proof.
apply/setP=> y; apply/imset2P/imsetP=> [[x1 x Dx1 /set1P->]| [x1 Dx1 ->]].
  by exists x1.
by exists x1 x2; rewrite ?set11.
Qed.

End Fun2Set1.

Section CardFunImage.

Variables aT aT2 rT : finType.
Variables (f : aT -> rT) (g : rT -> aT) (f2 : aT -> aT2 -> rT).
Variables (D : pred aT) (D2 : pred aT).

Lemma imset_card : #|f @: D| = #|image f D|.
Proof. by rewrite [@imset]unlock cardsE. Qed.

Lemma leq_imset_card : #|f @: D| <= #|D|.
Proof. by rewrite imset_card leq_image_card. Qed.

Lemma card_in_imset : {in D &, injective f} -> #|f @: D| = #|D|.
Proof. by move=> injf; rewrite imset_card card_in_image. Qed.

Lemma card_imset : injective f -> #|f @: D| = #|D|.
Proof. by move=> injf; rewrite imset_card card_image. Qed.

Lemma imset_injP : reflect {in D &, injective f} (#|f @: D| == #|D|).
Proof. by rewrite [@imset]unlock cardsE; exact: image_injP. Qed.

Lemma can2_in_imset_pre :
  {in D, cancel f g} -> {on D, cancel g & f} -> f @: D = g @^-1: D.
Proof.
move=> fK gK; apply/setP=> y; rewrite inE.
by apply/imsetP/idP=> [[x Ax ->] | Agy]; last exists (g y); rewrite ?(fK, gK).
Qed.

Lemma can2_imset_pre : cancel f g -> cancel g f -> f @: D = g @^-1: D.
Proof. by move=> fK gK; apply: can2_in_imset_pre; exact: in1W. Qed.

End CardFunImage.

Implicit Arguments imset_injP [aT rT f D].

Lemma on_card_preimset (aT rT : finType) (f : aT -> rT) (R : pred rT) :
  {on R, bijective f} -> #|f @^-1: R| = #|R|.
Proof.
case=> g fK gK; rewrite -(can2_in_imset_pre gK) // card_in_imset //.
exact: can_in_inj gK.
Qed.

Lemma can_imset_pre (T : finType) f g (A : {set T}) :
  cancel f g -> f @: A = g @^-1: A :> {set T}.
Proof.
move=> fK; apply: can2_imset_pre => // x.
suffices fx: x \in codom f by rewrite -(f_iinv fx) fK.
move: x; apply/(subset_cardP (card_codom (can_inj fK))); exact/subsetP.
Qed.

Lemma imset_id (T : finType) (A : {set T}) : [set x | x in A] = A.
Proof. by apply/setP=> x; rewrite (@can_imset_pre _ _ id) ?inE. Qed.

Lemma card_preimset (T : finType) (f : T -> T) (A : {set T}) :
  injective f -> #|f @^-1: A| = #|A|.
Proof.
move=> injf; apply: on_card_preimset; apply: onW_bij.
have ontof: _ \in codom f by exact/(subset_cardP (card_codom injf))/subsetP.
by exists (fun x => iinv (ontof x)) => x; rewrite (f_iinv, iinv_f).
Qed.

Lemma card_powerset (T : finType) (A : {set T}) : #|powerset A| = 2 ^ #|A|.
Proof.
rewrite -card_bool -(card_pffun_on false) -(card_imset _ val_inj).
apply: eq_card => f; pose sf := false.-support f; pose D := finset sf.
have sDA: (D \subset A) = (sf \subset A) by apply: eq_subset; exact: in_set.
have eq_sf x : sf x = f x by rewrite /= negb_eqb addbF.
have valD: val D = f by rewrite /D unlock; apply/ffunP=> x; rewrite ffunE eq_sf.
apply/imsetP/pffun_onP=> [[B] | [sBA _]]; last by exists D; rewrite // inE ?sDA.
by rewrite inE -sDA -valD => sBA /val_inj->.
Qed.

Section FunImageComp.

Variables T T' U : finType.

Lemma imset_comp (f : T' -> U) (g : T -> T') (H : pred T) :
  (f \o g) @: H = f @: (g @: H).
Proof.
apply/setP/subset_eqP/andP.
split; apply/subsetP=> _ /imsetP[x0 Hx0 ->]; apply/imsetP.
  by exists (g x0); first apply: mem_imset.
by move/imsetP: Hx0 => [x1 Hx1 ->]; exists x1.
Qed.

End FunImageComp.

Notation "\bigcup_ ( <- r | P ) F" :=
  (\big[@setU _/set0]_(<- r | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( i <- r | P ) F" :=
  (\big[@setU _/set0]_(i <- r | P) F%SET) : set_scope.
Notation "\bigcup_ ( i <- r ) F" :=
  (\big[@setU _/set0]_(i <- r) F%SET) : set_scope.
Notation "\bigcup_ ( m <= i < n | P ) F" :=
  (\big[@setU _/set0]_(m <= i < n | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( m <= i < n ) F" :=
  (\big[@setU _/set0]_(m <= i < n) F%SET) : set_scope.
Notation "\bigcup_ ( i | P ) F" :=
  (\big[@setU _/set0]_(i | P%B) F%SET) : set_scope.
Notation "\bigcup_ i F" :=
  (\big[@setU _/set0]_i F%SET) : set_scope.
Notation "\bigcup_ ( i : t | P ) F" :=
  (\big[@setU _/set0]_(i : t | P%B) F%SET) (only parsing): set_scope.
Notation "\bigcup_ ( i : t ) F" :=
  (\big[@setU _/set0]_(i : t) F%SET) (only parsing) : set_scope.
Notation "\bigcup_ ( i < n | P ) F" :=
  (\big[@setU _/set0]_(i < n | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( i < n ) F" :=
  (\big[@setU _/set0]_ (i < n) F%SET) : set_scope.
Notation "\bigcup_ ( i 'in' A | P ) F" :=
  (\big[@setU _/set0]_(i in A | P%B) F%SET) : set_scope.
Notation "\bigcup_ ( i 'in' A ) F" :=
  (\big[@setU _/set0]_(i in A) F%SET) : set_scope.

Notation "\bigcap_ ( <- r | P ) F" :=
  (\big[@setI _/setT]_(<- r | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i <- r | P ) F" :=
  (\big[@setI _/setT]_(i <- r | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i <- r ) F" :=
  (\big[@setI _/setT]_(i <- r) F%SET) : set_scope.
Notation "\bigcap_ ( m <= i < n | P ) F" :=
  (\big[@setI _/setT]_(m <= i < n | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( m <= i < n ) F" :=
  (\big[@setI _/setT]_(m <= i < n) F%SET) : set_scope.
Notation "\bigcap_ ( i | P ) F" :=
  (\big[@setI _/setT]_(i | P%B) F%SET) : set_scope.
Notation "\bigcap_ i F" :=
  (\big[@setI _/setT]_i F%SET) : set_scope.
Notation "\bigcap_ ( i : t | P ) F" :=
  (\big[@setI _/setT]_(i : t | P%B) F%SET) (only parsing): set_scope.
Notation "\bigcap_ ( i : t ) F" :=
  (\big[@setI _/setT]_(i : t) F%SET) (only parsing) : set_scope.
Notation "\bigcap_ ( i < n | P ) F" :=
  (\big[@setI _/setT]_(i < n | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i < n ) F" :=
  (\big[@setI _/setT]_(i < n) F%SET) : set_scope.
Notation "\bigcap_ ( i 'in' A | P ) F" :=
  (\big[@setI _/setT]_(i in A | P%B) F%SET) : set_scope.
Notation "\bigcap_ ( i 'in' A ) F" :=
  (\big[@setI _/setT]_(i in A) F%SET) : set_scope.

Section BigSetOps.

Variables T I : finType.
Implicit Types (U : pred T) (P : pred I) (A B : {set I}) (F :  I -> {set T}).

(* It is very hard to use this lemma, because the unification fails to *)
(* defer the F j pattern (even though it's a Miller pattern!).         *)
Lemma bigcup_sup j P F : P j -> F j \subset \bigcup_(i | P i) F i.
Proof. by move=> Pj; rewrite (bigD1 j) //= subsetUl. Qed.

Lemma bigcup_max j U P F :
  P j -> U \subset F j -> U \subset \bigcup_(i | P i) F i.
Proof. by move=> Pj sUF; exact: subset_trans (bigcup_sup _ Pj). Qed.

Lemma bigcupP x P F :
  reflect (exists2 i, P i & x \in F i) (x \in \bigcup_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[i Pi]]; last first.
  apply: subsetP x; exact: bigcup_sup.
by elim/big_rec: _ => [|i _ Pi _ /setUP[|//]]; [rewrite inE | exists i].
Qed.

Lemma bigcupsP U P F :
  reflect (forall i, P i -> F i \subset U) (\bigcup_(i | P i) F i \subset U).
Proof.
apply: (iffP idP) => [sFU i Pi| sFU].
  by apply: subset_trans sFU; exact: bigcup_sup.
by apply/subsetP=> x /bigcupP[i Pi]; exact: (subsetP (sFU i Pi)).
Qed.

Lemma bigcup_disjoint U P F :
  (forall i, P i -> [disjoint U & F i]) -> [disjoint U & \bigcup_(i | P i) F i].
Proof.
move=> dUF; rewrite disjoint_sym disjoint_subset.
by apply/bigcupsP=> i /dUF; rewrite disjoint_sym disjoint_subset.
Qed.

Lemma bigcup_setU A B F :
  \bigcup_(i in A :|: B) F i =
     (\bigcup_(i in A) F i) :|: (\bigcup_ (i in B) F i).
Proof.
apply/setP=> x; apply/bigcupP/setUP=> [[i] | ].
  by case/setUP; [left | right]; apply/bigcupP; exists i.
by case=> /bigcupP[i Pi]; exists i; rewrite // inE Pi ?orbT.
Qed.

Lemma bigcup_seq r F : \bigcup_(i <- r) F i = \bigcup_(i in r) F i.
Proof.
elim: r => [|i r IHr]; first by rewrite big_nil big_pred0.
rewrite big_cons {}IHr; case r_i: (i \in r).
  rewrite (setUidPr _) ?bigcup_sup //.
  by apply: eq_bigl => j; rewrite !inE; case: eqP => // ->.
rewrite (bigD1 i (mem_head i r)) /=; congr (_ :|: _).
by apply: eq_bigl => j /=; rewrite andbC; case: eqP => // ->.
Qed.

(* Unlike its setU counterpart, this lemma is useable. *)
Lemma bigcap_inf j P F : P j -> \bigcap_(i | P i) F i \subset F j.
Proof. by move=> Pj; rewrite (bigD1 j) //= subsetIl. Qed.

Lemma bigcap_min j U P F :
  P j -> F j \subset U -> \bigcap_(i | P i) F i \subset U.
Proof. by move=> Pj; exact: subset_trans (bigcap_inf _ Pj). Qed.

Lemma bigcapsP U P F :
  reflect (forall i, P i -> U \subset F i) (U \subset \bigcap_(i | P i) F i).
Proof.
apply: (iffP idP) => [sUF i Pi | sUF].
  apply: subset_trans sUF _; exact: bigcap_inf.
elim/big_rec: _ => [|i V Pi sUV]; apply/subsetP=> x Ux; rewrite inE //.
by rewrite !(subsetP _ x Ux) ?sUF.
Qed.

Lemma bigcapP x P F :
  reflect (forall i, P i -> x \in F i) (x \in \bigcap_(i | P i) F i).
Proof.
rewrite -sub1set.
by apply: (iffP (bigcapsP _ _ _)) => Fx i /Fx; rewrite sub1set.
Qed.

Lemma setC_bigcup J r (P : pred J) (F : J -> {set T}) :
  ~: (\bigcup_(j <- r | P j) F j) = \bigcap_(j <- r | P j) ~: F j.
Proof. by apply: big_morph => [A B|]; rewrite ?setC0 ?setCU. Qed.

Lemma setC_bigcap J r (P : pred J) (F : J -> {set T}) :
  ~: (\bigcap_(j <- r | P j) F j) = \bigcup_(j <- r | P j) ~: F j.
Proof. by apply: big_morph => [A B|]; rewrite ?setCT ?setCI. Qed.

Lemma bigcap_setU A B F :
  (\bigcap_(i in A :|: B) F i) =
    (\bigcap_(i in A) F i) :&: (\bigcap_(i in B) F i).
Proof. by apply: setC_inj; rewrite setCI !setC_bigcap bigcup_setU. Qed.

Lemma bigcap_seq r F : \bigcap_(i <- r) F i = \bigcap_(i in r) F i.
Proof. by apply: setC_inj; rewrite !setC_bigcap bigcup_seq. Qed.

End BigSetOps.

Implicit Arguments bigcup_sup [T I P F].
Implicit Arguments bigcup_max [T I U P F].
Implicit Arguments bigcupP [T I x P F].
Implicit Arguments bigcupsP [T I U P F].
Implicit Arguments bigcap_inf [T I P F].
Implicit Arguments bigcap_min [T I U P F].
Implicit Arguments bigcapP [T I x P F].
Implicit Arguments bigcapsP [T I U P F].
Prenex Implicits bigcupP bigcupsP bigcapP bigcapsP.

Section ImsetCurry.

Variables (aT1 aT2 rT : finType) (f : aT1 -> aT2 -> rT).

Section Curry.

Variables (A1 : {set aT1}) (A2 : {set aT2}).
Variables (D1 : pred aT1) (D2 : pred aT2).

Lemma curry_imset2X : f @2: (A1, A2) = prod_curry f @: (setX A1 A2).
Proof.
rewrite [@imset]unlock unlock; apply/setP=> x; rewrite !in_set; congr (x \in _).
by apply: eq_image => u //=; rewrite !inE.
Qed.

Lemma curry_imset2l : f @2: (D1, D2) = \bigcup_(x1 in D1) f x1 @: D2.
Proof.
apply/setP=> y; apply/imset2P/bigcupP => [[x1 x2 Dx1 Dx2 ->{y}] | [x1 Dx1]].
  by exists x1; rewrite // mem_imset.
by case/imsetP=> x2 Dx2 ->{y}; exists x1 x2.
Qed.

Lemma curry_imset2r : f @2: (D1, D2) = \bigcup_(x2 in D2) f^~ x2 @: D1.
Proof.
apply/setP=> y; apply/imset2P/bigcupP => [[x1 x2 Dx1 Dx2 ->{y}] | [x2 Dx2]].
  by exists x2; rewrite // (mem_imset (f^~ x2)).
by case/imsetP=> x1 Dx1 ->{y}; exists x1 x2.
Qed.

End Curry.

Lemma imset2Ul (A B : {set aT1}) (C : {set aT2}) :
  f @2: (A :|: B, C) = f @2: (A, C) :|: f @2: (B, C).
Proof. by rewrite !curry_imset2l bigcup_setU. Qed.

Lemma imset2Ur (A : {set aT1}) (B C : {set aT2}) :
  f @2: (A, B :|: C) = f @2: (A, B) :|: f @2: (A, C).
Proof. by rewrite !curry_imset2r bigcup_setU. Qed.

End ImsetCurry.

Section Partitions.

Variables T I : finType.
Implicit Types (x y z : T) (A B D X : {set T}) (P Q : {set {set T}}).
Implicit Types (J : pred I) (F : I -> {set T}).

Definition cover P := \bigcup_(B in P) B.
Definition pblock P x := odflt set0 (pick [pred B in P | x \in B]).
Definition trivIset P := \sum_(B in P) #|B| == #|cover P|.
Definition partition P D := [&& cover P == D, trivIset P & set0 \notin P].

Definition is_transversal X P D :=
  [&& partition P D, X \subset D & [forall B in P, #|X :&: B| == 1]].
Definition transversal P D := [set odflt x [pick y in pblock P x] | x in D].
Definition transversal_repr x0 X B := odflt x0 [pick x in X :&: B].

Lemma leq_card_setU A B : #|A :|: B| <= #|A| + #|B| ?= iff [disjoint A & B].
Proof.
rewrite -(addn0 #|_|) -setI_eq0 -cards_eq0 -cardsUI eq_sym.
by rewrite (mono_leqif (leq_add2l _)).
Qed.

Lemma leq_card_cover P : #|cover P| <= \sum_(A in P) #|A| ?= iff trivIset P.
Proof.
split; last exact: eq_sym.
rewrite /cover; elim/big_rec2: _ => [|A n U _ leUn]; first by rewrite cards0.
by rewrite (leq_trans (leq_card_setU A U).1) ?leq_add2l.
Qed.

Lemma trivIsetP P :
  reflect {in P &, forall A B, A != B -> [disjoint A & B]} (trivIset P).
Proof.
have->: P = [set x in enum (mem P)] by apply/setP=> x; rewrite inE mem_enum.
elim: {P}(enum _) (enum_uniq (mem P)) => [_ | A e IHe] /=.
  by rewrite /trivIset /cover !big_set0 cards0; left=> A; rewrite inE.
case/andP; rewrite set_cons -(in_set (fun B => B \in e)) => PA {IHe}/IHe.
move: {e}[set x in e] PA => P PA IHP.
rewrite /trivIset /cover !big_setU1 //= eq_sym.
have:= leq_card_cover P; rewrite -(mono_leqif (leq_add2l #|A|)).
move/(leqif_trans (leq_card_setU _ _))->; rewrite disjoints_subset setC_bigcup.
case: bigcapsP => [disjA | meetA]; last first.
  right=> [tI]; case: meetA => B PB; rewrite -disjoints_subset.
  by rewrite tI ?setU11 ?setU1r //; apply: contraNneq PA => ->.
apply: (iffP IHP) => [] tI B C PB PC; last by apply: tI; exact: setU1r.
by case/setU1P: PC PB => [->|PC] /setU1P[->|PB]; try by [exact: tI | case/eqP];
  first rewrite disjoint_sym; rewrite disjoints_subset disjA.
Qed.

Lemma trivIsetS P Q : P \subset Q -> trivIset Q -> trivIset P.
Proof. by move/subsetP/sub_in2=> sPQ /trivIsetP/sPQ/trivIsetP. Qed.

Lemma trivIsetI P D : trivIset P -> trivIset (P ::&: D).
Proof. by apply: trivIsetS; rewrite -setI_powerset subsetIl. Qed.

Lemma cover_setI P D : cover (P ::&: D) \subset cover P :&: D.
Proof.
by apply/bigcupsP=> A /setIdP[PA sAD]; rewrite subsetI sAD andbT (bigcup_max A).
Qed.

Lemma mem_pblock P x : (x \in pblock P x) = (x \in cover P).
Proof.
rewrite /pblock; apply/esym/bigcupP.
case: pickP => /= [A /andP[PA Ax]| noA]; first by rewrite Ax; exists A.
by rewrite inE => [[A PA Ax]]; case/andP: (noA A).
Qed.

Lemma pblock_mem P x : x \in cover P -> pblock P x \in P.
Proof.
by rewrite -mem_pblock /pblock; case: pickP => [A /andP[]| _] //=; rewrite inE.
Qed.

Lemma def_pblock P B x : trivIset P -> B \in P -> x \in B -> pblock P x = B.
Proof.
move/trivIsetP=> tiP PB Bx; have Px: x \in cover P by apply/bigcupP; exists B.
apply: (contraNeq (tiP _ _ _ PB)); first by rewrite pblock_mem.
by apply/pred0Pn; exists x; rewrite /= mem_pblock Px.
Qed.

Lemma same_pblock P x y :
  trivIset P -> x \in pblock P y -> pblock P x = pblock P y.
Proof.
rewrite {1 3}/pblock => tI; case: pickP => [A|]; last by rewrite inE.
by case/andP=> PA _{y} /= Ax; exact: def_pblock.
Qed.

Lemma eq_pblock P x y :
    trivIset P -> x \in cover P ->
  (pblock P x == pblock P y) = (y \in pblock P x).
Proof.
move=> tiP Px; apply/eqP/idP=> [eq_xy | /same_pblock-> //].
move: Px; rewrite -mem_pblock eq_xy /pblock.
by case: pickP => [B /andP[] // | _]; rewrite inE.
Qed.

Lemma trivIsetU1 A P :
    {in P, forall B, [disjoint A & B]} -> trivIset P -> set0 \notin P ->
  trivIset (A |: P) /\ A \notin P.
Proof.
move=> tiAP tiP notPset0; split; last first.
  apply: contra notPset0 => P_A.
  by have:= tiAP A P_A; rewrite -setI_eq0 setIid => /eqP <-.
apply/trivIsetP=> B1 B2 /setU1P[->|PB1] /setU1P[->|PB2];
  by [exact: (trivIsetP _ tiP) | rewrite ?eqxx // ?(tiAP, disjoint_sym)].
Qed.

Lemma cover_imset J F : cover (F @: J) = \bigcup_(i in J) F i.
Proof.
apply/setP=> x.
apply/bigcupP/bigcupP=> [[_ /imsetP[i Ji ->]] | [i]]; first by exists i.
by exists (F i); first exact: mem_imset.
Qed.

Lemma trivIimset J F (P := F @: J) :
    {in J &, forall i j, j != i -> [disjoint F i & F j]} -> set0 \notin P ->
  trivIset P /\ {in J &, injective F}.
Proof.
move=> tiF notPset0; split=> [|i j Ji Jj /= eqFij].
  apply/trivIsetP=> _ _ /imsetP[i Ji ->] /imsetP[j Jj ->] neqFij.
  by rewrite tiF // (contraNneq _ neqFij) // => ->.
apply: contraNeq notPset0 => neq_ij; apply/imsetP; exists i => //; apply/eqP.
by rewrite eq_sym -[F i]setIid setI_eq0 {1}eqFij tiF.
Qed.

Lemma cover_partition P D : partition P D -> cover P = D.
Proof. by case/and3P=> /eqP. Qed.

Lemma card_partition P D : partition P D -> #|D| = \sum_(A in P) #|A|.
Proof. by case/and3P=> /eqP <- /eqnP. Qed.

Lemma card_uniform_partition n P D :
  {in P, forall A, #|A| = n} -> partition P D -> #|D| = #|P| * n.
Proof.
by move=> uniP /card_partition->; rewrite -sum_nat_const; exact: eq_bigr.
Qed.

Section BigOps.

Variables (R : Type) (idx : R) (op : Monoid.com_law idx).
Let rhs_cond P K E := \big[op/idx]_(A in P) \big[op/idx]_(x in A | K x) E x.
Let rhs P E := \big[op/idx]_(A in P) \big[op/idx]_(x in A) E x.

Lemma big_trivIset_cond P (K : pred T) (E : T -> R) :
  trivIset P -> \big[op/idx]_(x in cover P | K x) E x = rhs_cond P K E.
Proof.
move=> tiP; rewrite (partition_big (pblock P) (mem P)) -/op => /= [|x].
  apply: eq_bigr => A PA; apply: eq_bigl => x; rewrite andbAC; congr (_ && _).
  rewrite -mem_pblock; apply/andP/idP=> [[Px /eqP <- //] | Ax].
  by rewrite (def_pblock tiP PA Ax).
by case/andP=> Px _; exact: pblock_mem.
Qed.

Lemma big_trivIset P (E : T -> R) :
  trivIset P -> \big[op/idx]_(x in cover P) E x = rhs P E.
Proof.
have biginT := eq_bigl _ _ (fun _ => andbT _) => tiP.
by rewrite -biginT big_trivIset_cond //; apply: eq_bigr => A _; exact: biginT.
Qed.

Lemma set_partition_big_cond P D (K : pred T) (E : T -> R) :
  partition P D -> \big[op/idx]_(x in D | K x) E x = rhs_cond P K E.
Proof. by case/and3P=> /eqP <- tI_P _; exact: big_trivIset_cond. Qed.

Lemma set_partition_big P D (E : T -> R) :
  partition P D -> \big[op/idx]_(x in D) E x = rhs P E.
Proof. by case/and3P=> /eqP <- tI_P _; exact: big_trivIset. Qed.

Lemma partition_disjoint_bigcup (F : I -> {set T}) E :
    (forall i j, i != j -> [disjoint F i & F j]) ->
  \big[op/idx]_(x in \bigcup_i F i) E x =
    \big[op/idx]_i \big[op/idx]_(x in F i) E x.
Proof.
move=> disjF; pose P := [set F i | i in I & F i != set0].
have trivP: trivIset P.
  apply/trivIsetP=> _ _ /imsetP[i _ ->] /imsetP[j _ ->] neqFij.
  by apply: disjF; apply: contraNneq neqFij => ->.
have ->: \bigcup_i F i = cover P.
  apply/esym; rewrite cover_imset big_mkcond; apply: eq_bigr => i _.
  by rewrite inE; case: eqP.
rewrite big_trivIset // /rhs big_imset => [|i j _ /setIdP[_ notFj0] eqFij].
  rewrite big_mkcond; apply: eq_bigr => i _; rewrite inE.
  by case: eqP => //= ->; rewrite big_set0.
by apply: contraNeq (disjF _ _) _; rewrite -setI_eq0 eqFij setIid.
Qed.

End BigOps.

Section Equivalence.

Variables (R : rel T) (D : {set T}).

Let Px x := [set y in D | R x y].
Definition equivalence_partition := [set Px x | x in D].
Local Notation P := equivalence_partition.
Hypothesis eqiR : {in D & &, equivalence_rel R}.

Let Pxx x : x \in D -> x \in Px x.
Proof. by move=> Dx; rewrite !inE Dx (eqiR Dx Dx). Qed.
Let PPx x : x \in D -> Px x \in P := fun Dx => mem_imset _ Dx.

Lemma equivalence_partitionP : partition P D.
Proof.
have defD: cover P == D.
  rewrite eqEsubset; apply/andP; split.
    by apply/bigcupsP=> _ /imsetP[x Dx ->]; rewrite /Px setIdE subsetIl.
  by apply/subsetP=> x Dx; apply/bigcupP; exists (Px x); rewrite (Pxx, PPx).
have tiP: trivIset P.
  apply/trivIsetP=> _ _ /imsetP[x Dx ->] /imsetP[y Dy ->]; apply: contraR.
  case/pred0Pn=> z /andP[]; rewrite !inE => /andP[Dz Rxz] /andP[_ Ryz].
  apply/eqP/setP=> t; rewrite !inE; apply: andb_id2l => Dt.
  by rewrite (eqiR Dx Dz Dt) // (eqiR Dy Dz Dt).
rewrite /partition tiP defD /=.
by apply/imsetP=> [[x /Pxx Px_x Px0]]; rewrite -Px0 inE in Px_x.
Qed.

Lemma pblock_equivalence_partition :
  {in D &, forall x y, (y \in pblock P x) = R x y}.
Proof.
have [_ tiP _] := and3P equivalence_partitionP. 
by move=> x y Dx Dy; rewrite /= (def_pblock tiP (PPx Dx) (Pxx Dx)) inE Dy.
Qed.

End Equivalence.

Lemma pblock_equivalence P D :
  partition P D -> {in D & &, equivalence_rel (fun x y => y \in pblock P x)}.
Proof.
case/and3P=> /eqP <- tiP _ x y z Px Py Pz.
by rewrite mem_pblock; split=> // /same_pblock->.
Qed.

Lemma equivalence_partition_pblock P D :
  partition P D -> equivalence_partition (fun x y => y \in pblock P x) D = P.
Proof.
case/and3P=> /eqP <-{D} tiP notP0; apply/setP=> B /=; set D := cover P.
have defP x: x \in D -> [set y in D | y \in pblock P x] = pblock P x.
  by move=> Dx; apply/setIidPr; rewrite (bigcup_max (pblock P x)) ?pblock_mem.
apply/imsetP/idP=> [[x Px ->{B}] | PB]; first by rewrite defP ?pblock_mem.
have /set0Pn[x Bx]: B != set0 := memPn notP0 B PB.
have Px: x \in cover P by apply/bigcupP; exists B.
by exists x; rewrite // defP // (def_pblock tiP PB Bx).
Qed.

Section Preim.

Variables (rT : eqType) (f : T -> rT).

Definition preim_partition := equivalence_partition (fun x y => f x == f y).

Lemma preim_partitionP D : partition (preim_partition D) D.
Proof. by apply/equivalence_partitionP; split=> // /eqP->. Qed.

End Preim.

Lemma preim_partition_pblock P D :
  partition P D -> preim_partition (pblock P) D = P.
Proof.
move=> partP; have [/eqP defD tiP _] := and3P partP.
rewrite -{2}(equivalence_partition_pblock partP); apply: eq_in_imset => x Dx.
by apply/setP=> y; rewrite !inE eq_pblock ?defD.
Qed.

Lemma transversalP P D : partition P D -> is_transversal (transversal P D) P D.
Proof.
case/and3P=> /eqP <- tiP notP0; apply/and3P; split; first exact/and3P.
  apply/subsetP=> _ /imsetP[x Px ->]; case: pickP => //= y Pxy.
  by apply/bigcupP; exists (pblock P x); rewrite ?pblock_mem //.
apply/forall_inP=> B PB; have /set0Pn[x Bx]: B != set0 := memPn notP0 B PB.
apply/cards1P; exists (odflt x [pick y in pblock P x]); apply/esym/eqP.
rewrite eqEsubset sub1set inE -andbA; apply/andP; split.
  by apply/mem_imset/bigcupP; exists B.
rewrite (def_pblock tiP PB Bx); case def_y: _ / pickP => [y By | /(_ x)/idP//].
rewrite By /=; apply/subsetP=> _ /setIP[/imsetP[z Pz ->]].
case: {1}_ / pickP => [t zPt Bt | /(_ z)/idP[]]; last by rewrite mem_pblock.
by rewrite -(same_pblock tiP zPt) (def_pblock tiP PB Bt) def_y set11.
Qed.

Section Transversals.

Variables (X : {set T}) (P : {set {set T}}) (D : {set T}).
Hypothesis trPX : is_transversal X P D.

Lemma transversal_sub : X \subset D. Proof. by case/and3P: trPX. Qed.

Let tiP : trivIset P. Proof. by case/andP: trPX => /and3P[]. Qed.

Let sXP : {subset X <= cover P}.
Proof. by case/and3P: trPX => /andP[/eqP-> _] /subsetP. Qed.

Let trX : {in P, forall B, #|X :&: B| == 1}.
Proof. by case/and3P: trPX => _ _ /forall_inP. Qed.

Lemma setI_transversal_pblock x0 B :
  B \in P -> X :&: B = [set transversal_repr x0 X B].
Proof.
by case/trX/cards1P=> x defXB; rewrite /transversal_repr defXB /pick enum_set1.
Qed.

Lemma repr_mem_pblock x0 B : B \in P -> transversal_repr x0 X B \in B.
Proof. by move=> PB; rewrite -sub1set -setI_transversal_pblock ?subsetIr. Qed.

Lemma repr_mem_transversal x0 B : B \in P -> transversal_repr x0 X B \in X.
Proof. by move=> PB; rewrite -sub1set -setI_transversal_pblock ?subsetIl. Qed.

Lemma transversal_reprK x0 : {in P, cancel (transversal_repr x0 X) (pblock P)}.
Proof. by move=> B PB; rewrite /= (def_pblock tiP PB) ?repr_mem_pblock. Qed.

Lemma pblockK x0 : {in X, cancel (pblock P) (transversal_repr x0 X)}.
Proof.
move=> x Xx; have /bigcupP[B PB Bx] := sXP Xx; rewrite (def_pblock tiP PB Bx).
by apply/esym/set1P; rewrite -setI_transversal_pblock // inE Xx.
Qed.

Lemma pblock_inj : {in X &, injective (pblock P)}.
Proof. by move=> x0; exact: (can_in_inj (pblockK x0)). Qed.

Lemma pblock_transversal : pblock P @: X = P.
Proof.
apply/setP=> B; apply/imsetP/idP=> [[x Xx ->] | PB].
  by rewrite pblock_mem ?sXP.
have /cards1P[x0 _] := trX PB; set x := transversal_repr x0 X B.
by exists x; rewrite ?transversal_reprK ?repr_mem_transversal.
Qed.

Lemma card_transversal : #|X| = #|P|.
Proof. rewrite -pblock_transversal card_in_imset //; exact: pblock_inj. Qed.

Lemma im_transversal_repr x0 : transversal_repr x0 X @: P = X.
Proof.
rewrite -{2}[X]imset_id -pblock_transversal -imset_comp.
by apply: eq_in_imset; exact: pblockK.
Qed.

End Transversals.

End Partitions.

Implicit Arguments trivIsetP [T P].
Implicit Arguments big_trivIset_cond [T R idx op K E].
Implicit Arguments set_partition_big_cond [T R idx op D K E].
Implicit Arguments big_trivIset [T R idx op E].
Implicit Arguments set_partition_big [T R idx op D E].

Prenex Implicits cover trivIset partition pblock trivIsetP.

Lemma partition_partition (T : finType) (D : {set T}) P Q :
    partition P D -> partition Q P ->
  partition (cover @: Q) D /\ {in Q &, injective cover}.
Proof.
move=> /and3P[/eqP defG tiP notP0] /and3P[/eqP defP tiQ notQ0].
have sQP E: E \in Q -> {subset E <= P}.
  by move=> Q_E; apply/subsetP; rewrite -defP (bigcup_max E).
rewrite /partition cover_imset -(big_trivIset _ tiQ) defP -defG eqxx /= andbC.
have{notQ0} notQ0: set0 \notin cover @: Q.
  apply: contra notP0 => /imsetP[E Q_E E0].
  have /set0Pn[/= A E_A] := memPn notQ0 E Q_E.
  congr (_ \in P): (sQP E Q_E A E_A).
  by apply/eqP; rewrite -subset0 E0 (bigcup_max A).
rewrite notQ0; apply: trivIimset => // E F Q_E Q_F.
apply: contraR => /pred0Pn[x /andP[/bigcupP[A E_A Ax] /bigcupP[B F_B Bx]]].
rewrite -(def_pblock tiQ Q_E E_A) -(def_pblock tiP _ Ax) ?(sQP E) //.
by rewrite -(def_pblock tiQ Q_F F_B) -(def_pblock tiP _ Bx) ?(sQP F).
Qed.

(**********************************************************************)
(*                                                                    *)
(*  Maximum and minimun (sub)set with respect to a given pred         *)
(*                                                                    *)
(**********************************************************************)

Section MaxSetMinSet.

Variable T : finType.
Notation sT := {set T}.
Implicit Types A B C : sT.
Implicit Type P : pred sT.

Definition minset P A := [forall (B : sT | B \subset A), (B == A) == P B].

Lemma minset_eq P1 P2 A : P1 =1 P2 -> minset P1 A = minset P2 A.
Proof. by move=> eP12; apply: eq_forallb => B; rewrite eP12. Qed.

Lemma minsetP P A :
  reflect ((P A) /\ (forall B, P B -> B \subset A -> B = A)) (minset P A).
Proof.
apply: (iffP forallP) => [minA | [PA minA] B].
  split; first by have:= minA A; rewrite subxx eqxx /= => /eqP.
  by move=> B PB sBA; have:= minA B; rewrite PB sBA /= eqb_id => /eqP.
by apply/implyP=> sBA; apply/eqP; apply/eqP/idP=> [-> // | /minA]; exact.
Qed.
Implicit Arguments minsetP [P A].

Lemma minsetp P A : minset P A -> P A.
Proof. by case/minsetP. Qed.

Lemma minsetinf P A B : minset P A -> P B -> B \subset A -> B = A.
Proof. by case/minsetP=> _; exact. Qed.

Lemma ex_minset P : (exists A, P A) -> {A | minset P A}.
Proof.
move=> exP; pose pS n := [pred B | P B & #|B| == n].
pose p n := ~~ pred0b (pS n); have{exP}: exists n, p n.
  by case: exP => A PA; exists #|A|; apply/existsP; exists A; rewrite /= PA /=.
case/ex_minnP=> n /pred0P; case: (pickP (pS n)) => // A /andP[PA] /eqP <-{n} _.
move=> minA; exists A => //; apply/minsetP; split=> // B PB sBA; apply/eqP.
by rewrite eqEcard sBA minA //; apply/pred0Pn; exists B; rewrite /= PB /=.
Qed.

Lemma minset_exists P C : P C -> {A | minset P A & A \subset C}.
Proof.
move=> PC; have{PC}: exists A, P A && (A \subset C) by exists C; rewrite PC /=.
case/ex_minset=> A /minsetP[/andP[PA sAC] minA]; exists A => //; apply/minsetP.
by split=> // B PB sBA; rewrite (minA B) // PB (subset_trans sBA).
Qed.

(* The 'locked_with' allows Coq to find the value of P by unification. *)
Fact maxset_key : unit. Proof. by []. Qed.
Definition maxset P A :=
  minset (fun B => locked_with maxset_key P (~: B)) (~: A).

Lemma maxset_eq P1 P2 A : P1 =1 P2 -> maxset P1 A = maxset P2 A.
Proof. by move=> eP12; apply: minset_eq => x /=; rewrite !unlock_with eP12. Qed.

Lemma maxminset P A : maxset P A = minset [pred B | P (~: B)] (~: A).
Proof. by rewrite /maxset unlock. Qed.

Lemma minmaxset P A : minset P A = maxset [pred B | P (~: B)] (~: A).
Proof.
by rewrite /maxset unlock setCK; apply: minset_eq => B /=; rewrite setCK.
Qed.

Lemma maxsetP P A :
  reflect ((P A) /\ (forall B, P B -> A \subset B -> B = A)) (maxset P A).
Proof.
apply: (iffP minsetP); rewrite ?setCK unlock_with => [] [PA minA].
  by split=> // B PB sAB; rewrite -[B]setCK [~: B]minA (setCK, setCS).
by split=> // B PB' sBA'; rewrite -(minA _ PB') -1?setCS setCK.
Qed.

Lemma maxsetp P A : maxset P A -> P A.
Proof. by case/maxsetP. Qed.

Lemma maxsetsup P A B : maxset P A -> P B -> A \subset B -> B = A.
Proof. by case/maxsetP=> _; exact. Qed.

Lemma ex_maxset P : (exists A, P A) -> {A | maxset P A}.
Proof.
move=> exP; have{exP}: exists A, P (~: A).
  by case: exP => A PA; exists (~: A); rewrite setCK.
by case/ex_minset=> A minA; exists (~: A); rewrite /maxset unlock setCK.
Qed.

Lemma maxset_exists P C : P C -> {A : sT | maxset P A & C \subset A}.
Proof.
move=> PC; pose P' B := P (~: B); have: P' (~: C) by rewrite /P' setCK.
case/minset_exists=> B; rewrite -[B]setCK setCS.
by exists (~: B); rewrite // /maxset unlock.
Qed.

End MaxSetMinSet.

Implicit Arguments minsetP [T P A].
Implicit Arguments maxsetP [T P A].
Prenex Implicits minset maxset minsetP maxsetP.

