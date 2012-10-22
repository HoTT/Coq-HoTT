(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.

(******************************************************************************)
(*    The Finite interface describes Types with finitely many elements,       *)
(* supplying a duplicate-free sequence of all the elements. It is a subclass  *)
(* of Countable and thus of Choice and Equality. As with Countable, the       *)
(* interface explicitly includes these somewhat redundant superclasses to     *)
(* ensure that Canonical instance inference remains consistent. Finiteness    *)
(* could be stated more simply by bounding the range of the pickle function   *)
(* supplied by the Countable interface, but this would yield a useless        *)
(* computational interpretation due to the wasteful Peano integer encodings.  *)
(* Because the Countable interface is closely tied to the Finite interface    *)
(* and is not much used on its own, the Countable mixin is included inside    *)
(* the Finite mixin; this makes it much easier to derive Finite variants of   *)
(* interfaces, in this file for subFinType, and in the finalg library.        *)
(*    We define the following interfaces and structures:                      *)
(*         finType == the packed class type of the Finite interface.          *)
(*       FinType m == the packed class for the Finite mixin m.                *)
(*  Finite.axiom e == every x : T occurs exactly once in e : seq T.           *)
(*   FinMixin ax_e == the Finite mixin for T, encapsulating                   *)
(*                    ax_e : Finite.axiom e for some e : seq T.               *)
(*  UniqFinMixin uniq_e total_e == an alternative mixin constructor that uses *)
(*                    uniq_e : uniq e and total_e : e =i xpredT.              *)
(* PcanFinMixin fK == the Finite mixin for T, given f : T -> fT and g with fT *)
(*                    a finType and fK : pcancel f g.                         *)
(*  CanFinMixin fK == the Finite mixin for T, given f : T -> fT and g with fT *)
(*                    a finType and fK : cancel f g.                          *)
(*      subFinType == the join interface type for subType and finType.        *)
(*  [finType of T for fT] == clone for T of the finType fT.                   *)
(*  [finType of T] == clone for T of the finType inferred for T.              *)
(* [subFinType of T] == a subFinType structure for T, when T already has both *)
(*                    finType and subType structures.                         *)
(* [finMixin of T by <:] == a finType structure for T, when T has a subType   *)
(*                   structure over an existing finType.                      *)
(*   We define or propagate the finType structure appropriately for all basic *)
(* basic types : unit, bool, option, prod, sum, sig and sigT. We also define  *)
(* a generic type constructor for finite subtypes based on an explicit        *)
(* enumeration:                                                               *)
(*        seq_sub s == the subType of all x \in s, where s : seq T and T has  *)
(*                     a choiceType structure; the seq_sub s type has a       *)
(*                     canonical finType structure.                           *)
(* Bounded integers are supported by the following type and operations:       *)
(*    'I_n, ordinal n == the finite subType of integers i < n, whose          *)
(*                       enumeration is {0, ..., n.-1}. 'I_n coerces to nat,  *)
(*                       so all the integer arithmetic functions can be used  *)
(*                       with 'I_n.                                           *)
(*     Ordinal lt_i_n == the element of 'I_n with (nat) value i, given        *)
(*                       lt_i_n : i < n.                                      *)
(*       nat_of_ord i == the nat value of i : 'I_n (this function is a        *)
(*                       coercion so it is not usually displayed).            *)
(*         ord_enum n == the explicit increasing sequence of the i : 'I_n.    *)
(*  cast_ord eq_n_m i == the element j : 'I_m with the same value as i : 'I_n *)
(*                       given eq_n_m : n = m (indeed, i : nat and j : nat    *)
(*                       are convertible).                                    *)
(* widen_ord le_n_m i == a j : 'I_m with the same value as i : 'I_n, given    *)
(*                       le_n_m : n <= m.                                     *)
(*          rev_ord i == the complement to n.-1 of i : 'I_n, such that        *)
(*                       i + rev_ord i = n.-1.                                *)
(*            inord k == the i : 'I_n.+1 with value k (n is inferred from the *)
(*                       context).                                            *)
(*          sub_ord k == the i : 'I_n.+1 with value n - k (n is inferred from *)
(*                       the context).                                        *)
(*               ord0 == the i : 'I_n.+1 with value 0 (n is inferred from the *)
(*                       context).                                            *)
(*            ord_max == the i : 'I_n.+1 with value n (n is inferred from the *)
(*                       context).                                            *)
(*           bump h k == k.+1 if k >= h, else k (this is a nat function).     *)
(*         unbump h k == k.-1 if k > h, else k (this is a nat function).      *)
(*           lift i j == the j' : 'I_n with value bump i j, where i : 'I_n    *)
(*                       and j : 'I_n.-1.                                     *)
(*         unlift i j == None if i = j, else Some j', where j' : 'I_n.-1 has  *)
(*                       value unbump i j, given i, j : 'I_n.                 *)
(*         lshift n j == the i : 'I_(m + n) with value j : 'I_m.              *)
(*         rshift m k == the i : 'I_(m + n) with value m + k, k : 'I_n.       *)
(*          unsplit u == either lshift n j or rshift m k, depending on        *)
(*                       whether if u : 'I_m + 'I_n is inl j or inr k.        *)
(*            split i == the u : 'I_m + 'I_n such that i = unsplit u; the     *)
(*                       type 'I_(m + n) of i determines the split.           *)
(* Finally, every type T with a finType structure supports the following      *)
(* operations:                                                                *)
(*           enum A == a duplicate-free list of all the x \in A, where A is a *)
(*                     collective predicate over T.                           *)
(*             #|A| == the cardinal of A, i.e., the number of x \in A.        *)
(*       enum_val i == the i'th item of enum A, where i : 'I_(#|A|).          *)
(*      enum_rank x == the i : 'I_(#|T|) such that enum_val i = x.            *)
(* enum_rank_in Ax0 x == some i : 'I_(#|A|) such that enum_val i = x if       *)
(*                     x \in A, given Ax0 : x0 \in A.                         *)
(*      A \subset B == all x \in A satisfy x \in B.                           *)
(*      A \proper B == all x \in A satisfy x \in B but not the converse.      *)
(* [disjoint A & B] == no x \in A satisfies x \in B.                          *)
(*        image f A == the sequence of f x for all x : T such that x \in A    *)
(*                     (where a is an applicative predicate), of length #|P|. *)
(*                     The codomain of F can be any type, but image f A can   *)
(*                     only be used as a collective predicate is it is an     *)
(*                     eqType.                                                *)
(*          codom f == a sequence spanning the codomain of f (:= image f T).  *)
(*  [seq F | x : T in A] := image (fun x : T => F) A.                         *)
(*       [seq F | x : T] := [seq F | x <- {: T}].                             *)
(*      [seq F | x in A], [seq F | x] == variants without casts.              *)
(*        iinv im_y == some x such that P x holds and f x = y, given          *)
(*                     im_y : y \in image f P.                                *)
(*     invF inj_f y == the x such that f x = y, for inj_j : injective f with  *)
(*                     f : T -> T.                                            *)
(*  dinjectiveb A f == the restriction of f : T -> R to A is injective        *)
(*                     (this is a bolean predicate, R must be an eqType).     *)
(*     injectiveb f == f : T -> R is injective (boolean predicate).           *)
(*         pred0b A == no x : T satisfies x \in A.                            *)
(*    [forall x, P] == P (in which x can appear) is true for all values of x; *)
(*                     x must range over a finType.                           *)
(*    [exists x, P] == P is true for some value of x.                         *)
(*      [forall (x | C), P] := [forall x, C ==> P].                           *)
(*       [forall x in A, P] := [forall (x | x \in A), P].                     *)
(*      [exists (x | C), P] := [exists x, C && P].                            *)
(*       [exists x in A, P] := [exists (x | x \in A), P].                     *)
(* and typed variants [forall x : T, P], [forall (x : T | C), P],             *)
(*   [exists x : T, P], [exists x : T in A, P], etc.                          *)
(* -> The outer brackets can be omitted when nesting finitary quantifiers,    *)
(*    e.g., [forall i in I, forall j in J, exists a, f i j == a].             *)
(*     [pick x | P] == Some x, for an x such that P holds, or None if there   *)
(*                     is no such x.                                          *)
(*     [pick x : T] == Some x with x : T, provided T is nonempty, else None.  *)
(*    [pick x in A] == Some x, with x \in A, or None if A is empty.           *)
(* [pick x in A | P] == Some x, with x \in A s.t. P holds, else None.         *)
(*   [pick x | P & Q] := [pick x | P & Q].                                    *)
(* [pick x in A | P & Q] := [pick x | P & Q].                                 *)
(* and (un)typed variants [pick x : T | P], [pick x : T in A], [pick x], etc. *)
(* [arg min_(i < i0 | P) M] == a value of i : T minimizing M : nat, subject   *)
(*                   to the condition P (i may appear in P and M), and        *)
(*                   provided P holds for i0.                                 *)
(* [arg max_(i > i0 | P) M] == a value of i maximizing M subject to P and     *)
(*                   provided P holds for i0.                                 *)
(* [arg min_(i < i0 in A) M] == an i \in A minimizing M if i0 \in A.          *)
(* [arg max_(i > i0 in A) M] == an i \in A maximizing M if i0 \in A.          *)
(* [arg min_(i < i0) M] == an i : T minimizing M, given i0 : T.               *)
(* [arg max_(i > i0) M] == an i : T maximizing M, given i0 : T.               *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Finite.

Section RawMixin.

Variable T : eqType.

Definition axiom e := forall x, count (@pred1 T x) e = 1.

Lemma uniq_enumP e : uniq e -> e =i T -> axiom e.
Proof. by move=> Ue sT x; rewrite count_uniq_mem ?sT. Qed.

Record mixin_of := Mixin {
  mixin_base : Countable.mixin_of T;
  mixin_enum : seq T;
  _ : axiom mixin_enum
}.

End RawMixin.

Section Mixins.

Variable T : countType.

Definition EnumMixin :=
  let: Countable.Pack _ (Countable.Class _ m) _ as cT := T
    return forall e : seq cT, axiom e -> mixin_of cT in
  @Mixin (EqType _ _) m.

Definition UniqMixin e Ue eT := @EnumMixin e (uniq_enumP Ue eT).

Variable n : nat.

Definition count_enum := pmap (@pickle_inv T) (iota 0 n).

Hypothesis ubT : forall x : T, pickle x < n.

Lemma count_enumP : axiom count_enum.
Proof.
apply: uniq_enumP (pmap_uniq (@pickle_invK T) (iota_uniq _ _)) _ => x.
by rewrite mem_pmap -pickleK_inv map_f // mem_iota ubT.
Qed.

Definition CountMixin := EnumMixin count_enumP.

End Mixins.

Section ClassDef.

Record class_of T := Class {
  base : Choice.class_of T;
  mixin : mixin_of (Equality.Pack base T)
}.
Definition base2 T c := Countable.Class (@base T c) (mixin_base (mixin c)).
Local Coercion base : class_of >-> Choice.class_of.

Structure type : Type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (EqType T b0)) :=
  fun bT b & phant_id (Choice.class bT) b =>
  fun m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition countType := @Countable.Pack cT (base2 xclass) xT.

End ClassDef.

Module Import Exports.
Coercion mixin_base : mixin_of >-> Countable.mixin_of.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion base2 : class_of >-> Countable.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion countType : type >-> Countable.type.
Canonical countType.
Notation finType := type.
Notation FinType T m := (@pack T _ m _ _ id _ id).
Notation FinMixin := EnumMixin.
Notation UniqFinMixin := UniqMixin.
Notation "[ 'finType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'finType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'finType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'finType'  'of'  T ]") : form_scope.
End Exports.

Module Type EnumSig.
Parameter enum : forall cT : type, seq cT.
Axiom enumDef : enum = fun cT => mixin_enum (class cT).
End EnumSig.

Module EnumDef : EnumSig.
Definition enum cT := mixin_enum (class cT).
Definition enumDef := erefl enum.
End EnumDef.

Notation enum := EnumDef.enum.

End Finite.
Export Finite.Exports.

Canonical finEnum_unlock := Unlockable Finite.EnumDef.enumDef.

(* Workaround for the silly syntactic uniformity restriction on coercions;    *)
(* this avoids a cross-dependency between finset.v and prime.v for the        *)
(* definition of the \pi(A) notation.                                         *)
Definition fin_pred_sort (T : finType) (pT : predType T) := pred_sort pT.
Identity Coercion pred_sort_of_fin : fin_pred_sort >-> pred_sort.

Definition enum_mem T (mA : mem_pred _) := filter mA (Finite.enum T).
Notation enum A := (enum_mem (mem A)).
Definition pick (T : finType) (P : pred T) := ohead (enum P).

Notation "[ 'pick' x | P ]" := (pick (fun x => P%B))
  (at level 0, x ident, format "[ 'pick'  x  |  P  ]") : form_scope.
Notation "[ 'pick' x : T | P ]" := (pick (fun x : T => P%B))
  (at level 0, x ident, only parsing) : form_scope.
Definition pick_true T (x : T) := true.
Notation "[ 'pick' x : T ]" := [pick x : T | pick_true x]
  (at level 0, x ident, only parsing).
Notation "[ 'pick' x ]" := [pick x : _]
  (at level 0, x ident, only parsing) : form_scope.
Notation "[ 'pic' 'k' x : T ]" := [pick x : T | pick_true _]
  (at level 0, x ident, format "[ 'pic' 'k'  x : T ]") : form_scope.
Notation "[ 'pick' x | P & Q ]" := [pick x | P && Q ]
  (at level 0, x ident,
   format "[ '[hv ' 'pick'  x  |  P '/ '   &  Q ] ']'") : form_scope.
Notation "[ 'pick' x : T | P & Q ]" := [pick x : T | P && Q ]
  (at level 0, x ident, only parsing) : form_scope.
Notation "[ 'pick' x 'in' A ]" := [pick x | x \in A]
  (at level 0, x ident, format "[ 'pick'  x  'in'  A  ]") : form_scope.
Notation "[ 'pick' x : T 'in' A ]" := [pick x : T | x \in A]
  (at level 0, x ident, only parsing) : form_scope.
Notation "[ 'pick' x 'in' A | P ]" := [pick x | x \in A & P ]
  (at level 0, x ident,
   format "[ '[hv ' 'pick'  x  'in'  A '/ '   |  P ] ']'") : form_scope.
Notation "[ 'pick' x : T 'in' A | P ]" := [pick x : T | x \in A & P ]
  (at level 0, x ident, only parsing) : form_scope.
Notation "[ 'pick' x 'in' A | P & Q ]" := [pick x in A | P && Q]
  (at level 0, x ident, format
  "[ '[hv ' 'pick'  x  'in'  A '/ '   |  P '/ '  &  Q ] ']'") : form_scope.
Notation "[ 'pick' x : T 'in' A | P & Q ]" := [pick x : T in A | P && Q]
  (at level 0, x ident, only parsing) : form_scope.

(* We lock the definitions of card and subset to mitigate divergence of the   *)
(* Coq term comparison algorithm.                                             *)

Local Notation card_type := (forall T : finType, mem_pred T -> nat).
Local Notation card_def := (fun T mA => size (enum_mem mA)).
Module Type CardDefSig.
Parameter card : card_type. Axiom cardEdef : card = card_def.
End CardDefSig.
Module CardDef : CardDefSig.
Definition card : card_type := card_def. Definition cardEdef := erefl card.
End CardDef.
(* Should be Include, but for a silly restriction: can't Include at toplevel! *)
Export CardDef.

Canonical card_unlock := Unlockable cardEdef.
(* A is at level 99 to allow the notation #|G : H| in groups. *)
Notation "#| A |" := (card (mem A))
  (at level 0, A at level 99, format "#| A |") : nat_scope.

Definition pred0b (T : finType) (P : pred T) := #|P| == 0.
Prenex Implicits pred0b.

Module FiniteQuant.

CoInductive quantified := Quantified of bool.

Delimit Scope fin_quant_scope with Q. (* Bogus, only used to declare scope. *)
Bind Scope fin_quant_scope with quantified.

Notation "F ^*" := (Quantified F) (at level 2).
Notation "F ^~" := (~~ F) (at level 2).

Section Definitions.

Variable T : finType.
Implicit Types (B : quantified) (x y : T).

Definition quant0b Bp := pred0b [pred x : T | let: F^* := Bp x x in F].
(* The first redundant argument protects the notation from  Coq's K-term      *)
(* display kludge; the second protects it from simpl and /=.                  *)
Definition ex B x y := B.
(* Binding the predicate value rather than projecting it prevents spurious    *)
(* unfolding of the boolean connectives by unification.                       *)
Definition all B x y := let: F^* := B in F^~^*.
Definition all_in C B x y := let: F^* := B in (C ==> F)^~^*.
Definition ex_in C B x y :=  let: F^* := B in (C && F)^*.

End Definitions.

Notation "[ x | B ]" := (quant0b (fun x => B x)) (at level 0, x ident).
Notation "[ x : T | B ]" := (quant0b (fun x : T => B x)) (at level 0, x ident).

Module Exports.

Notation ", F" := F^* (at level 200, format ", '/ '  F") : fin_quant_scope.

Notation "[ 'forall' x B ]" := [x | all B]
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' 'forall'  x B ] ']'") : bool_scope.

Notation "[ 'forall' x : T B ]" := [x : T | all B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "[ 'forall' ( x | C ) B ]" := [x | all_in C B]
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' '[' 'forall'  ( x '/  '  |  C ) ']' B ] ']'") : bool_scope.
Notation "[ 'forall' ( x : T | C ) B ]" := [x : T | all_in C B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "[ 'forall' x 'in' A B ]" := [x | all_in (x \in A) B]
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' '[' 'forall'  x '/  '  'in'  A ']' B ] ']'") : bool_scope.
Notation "[ 'forall' x : T 'in' A B ]" := [x : T | all_in (x \in A) B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation ", 'forall' x B" := [x | all B]^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  'forall'  x B") : fin_quant_scope.
Notation ", 'forall' x : T B" := [x : T | all B]^*
  (at level 200, x at level 99, B at level 200, only parsing) : fin_quant_scope.
Notation ", 'forall' ( x | C ) B" := [x | all_in C B]^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'forall'  ( x '/  '  |  C ) ']' B") : fin_quant_scope.
Notation ", 'forall' ( x : T | C ) B" := [x : T | all_in C B]^*
  (at level 200, x at level 99, B at level 200, only parsing) : fin_quant_scope.
Notation ", 'forall' x 'in' A B" := [x | all_in (x \in A) B]^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'forall'  x '/  '  'in'  A ']' B") : bool_scope.
Notation ", 'forall' x : T 'in' A B" := [x : T | all_in (x \in A) B]^*
  (at level 200, x at level 99, B at level 200, only parsing) : bool_scope.

Notation "[ 'exists' x B ]" := [x | ex B]^~
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' 'exists'  x B ] ']'") : bool_scope.
Notation "[ 'exists' x : T B ]" := [x : T | ex B]^~
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "[ 'exists' ( x | C ) B ]" := [x | ex_in C B]^~
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' '[' 'exists'  ( x '/  '  |  C ) ']' B ] ']'") : bool_scope.
Notation "[ 'exists' ( x : T | C ) B ]" := [x : T | ex_in C B]^~
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "[ 'exists' x 'in' A B ]" := [x | ex_in (x \in A) B]^~
  (at level 0, x at level 99, B at level 200,
   format "[ '[hv' '[' 'exists'  x '/  '  'in'  A ']' B ] ']'") : bool_scope.
Notation "[ 'exists' x : T 'in' A B ]" := [x : T | ex_in (x \in A) B]^~
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation ", 'exists' x B" := [x | ex B]^~^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  'exists'  x B") : fin_quant_scope.
Notation ", 'exists' x : T B" := [x : T | ex B]^~^*
  (at level 200, x at level 99, B at level 200, only parsing) : fin_quant_scope.
Notation ", 'exists' ( x | C ) B" := [x | ex_in C B]^~^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'exists'  ( x '/  '  |  C ) ']' B") : fin_quant_scope.
Notation ", 'exists' ( x : T | C ) B" := [x : T | ex_in C B]^~^*
  (at level 200, x at level 99, B at level 200, only parsing) : fin_quant_scope.
Notation ", 'exists' x 'in' A B" := [x | ex_in (x \in A) B]^~^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'exists'  x '/  '  'in'  A ']' B") : bool_scope.
Notation ", 'exists' x : T 'in' A B" := [x : T | ex_in (x \in A) B]^~^*
  (at level 200, x at level 99, B at level 200, only parsing) : bool_scope.

End Exports.

End FiniteQuant.
Export FiniteQuant.Exports.

Definition disjoint T (A B : mem_pred _) := @pred0b T (predI A B).
Notation "[ 'disjoint' A & B ]" := (disjoint (mem A) (mem B))
  (at level 0,
   format "'[hv' [ 'disjoint' '/  '  A '/'  &  B ] ']'") : bool_scope.

Notation Local subset_type := (forall (T : finType) (A B : mem_pred T), bool).
Notation Local subset_def := (fun T A B => pred0b (predD A B)).
Module Type SubsetDefSig.
Parameter subset : subset_type. Axiom subsetEdef : subset = subset_def.
End SubsetDefSig.
Module Export SubsetDef : SubsetDefSig.
Definition subset : subset_type := subset_def.
Definition subsetEdef := erefl subset.
End SubsetDef.
Canonical subset_unlock := Unlockable subsetEdef.
Notation "A \subset B" := (subset (mem A) (mem B))
  (at level 70, no associativity) : bool_scope.

Definition proper T A B := @subset T A B && ~~ subset B A.
Notation "A \proper B" := (proper (mem A) (mem B))
  (at level 70, no associativity) : bool_scope.

(* image, xinv, inv, and ordinal operations will be defined later. *)

Section OpsTheory.

Variable T : finType.

Implicit Types A B C P Q : pred T.
Implicit Types x y : T.
Implicit Type s : seq T.

Lemma enumP : Finite.axiom (Finite.enum T).
Proof. by rewrite unlock; case T => ? [? []]. Qed.

Section EnumPick.

Variable P : pred T.

Lemma enumT : enum T = Finite.enum T.
Proof. exact: filter_predT. Qed.

Lemma mem_enum A : enum A =i A.
Proof. by move=> x; rewrite mem_filter andbC -has_pred1 has_count enumP. Qed.

Lemma enum_uniq : uniq (enum P).
Proof.
by apply/filter_uniq/count_mem_uniq => x; rewrite enumP -enumT mem_enum.
Qed.

Lemma enum0 : enum pred0 = Nil T. Proof. exact: filter_pred0. Qed.

Lemma enum1 x : enum (pred1 x) = [:: x].
Proof.
rewrite [enum _](all_pred1P x _ _); first by rewrite -count_filter enumP.
by apply/allP=> y; rewrite mem_enum.
Qed.

CoInductive pick_spec : option T -> Type :=
  | Pick x of P x         : pick_spec (Some x)
  | Nopick of P =1 xpred0 : pick_spec None.

Lemma pickP : pick_spec (pick P).
Proof.
rewrite /pick; case: (enum _) (mem_enum P) => [|x s] Pxs /=.
  by right; exact: fsym.
by left; rewrite -[P _]Pxs mem_head.
Qed.

End EnumPick.

Lemma eq_enum P Q : P =i Q -> enum P = enum Q.
Proof. move=> eqPQ; exact: eq_filter. Qed.

Lemma eq_pick P Q : P =1 Q -> pick P = pick Q.
Proof. by move=> eqPQ; rewrite /pick (eq_enum eqPQ). Qed.

Lemma cardE A : #|A| = size (enum A).
Proof. by rewrite unlock. Qed.

Lemma eq_card A B : A =i B -> #|A| = #|B|.
Proof. by move=>eqAB; rewrite !cardE (eq_enum eqAB). Qed.

Lemma eq_card_trans A B n : #|A| = n -> B =i A -> #|B| = n.
Proof. move <-; exact: eq_card. Qed.

Lemma card0 : #|@pred0 T| = 0. Proof. by rewrite cardE enum0. Qed.

Lemma cardT : #|T| = size (enum T). Proof. by rewrite cardE. Qed.

Lemma card1 x : #|pred1 x| = 1.
Proof. by rewrite cardE enum1. Qed.

Lemma eq_card0 A : A =i pred0 -> #|A| = 0.
Proof. exact: eq_card_trans card0. Qed.

Lemma eq_cardT A : A =i predT -> #|A| = size (enum T).
Proof. exact: eq_card_trans cardT. Qed.

Lemma eq_card1 x A : A =i pred1 x -> #|A| = 1.
Proof. exact: eq_card_trans (card1 x). Qed.

Lemma cardUI A B : #|[predU A & B]| + #|[predI A & B]| = #|A| + #|B|.
Proof. by rewrite !cardE -!count_filter count_predUI. Qed.

Lemma cardID B A : #|[predI A & B]| + #|[predD A & B]| = #|A|.
Proof.
rewrite -cardUI addnC [#|predI _ _|]eq_card0 => [|x] /=.
  by apply: eq_card => x; rewrite !inE andbC -andb_orl orbN.
by rewrite !inE -!andbA andbC andbA andbN.
Qed.

Lemma cardC A : #|A| + #|[predC A]| = #|T|.
Proof. by rewrite !cardE -!count_filter count_predC. Qed.

Lemma cardU1 x A : #|[predU1 x & A]| = (x \notin A) + #|A|.
Proof.
case Ax: (x \in A).
  by apply: eq_card => y; rewrite inE /=; case: eqP => // ->.
rewrite /= -(card1 x) -cardUI addnC.
rewrite [#|predI _ _|]eq_card0 => [|y /=]; first exact: eq_card.
by rewrite !inE; case: eqP => // ->.
Qed.

Lemma card2 x y : #|pred2 x y| = (x != y).+1.
Proof. by rewrite cardU1 card1 addn1. Qed.

Lemma cardC1 x : #|predC1 x| = #|T|.-1.
Proof. by rewrite -(cardC (pred1 x)) card1. Qed.

Lemma cardD1 x A : #|A| = (x \in A) + #|[predD1 A & x]|.
Proof.
case Ax: (x \in A); last first.
  by apply: eq_card => y; rewrite !inE /=; case: eqP => // ->.
rewrite /= -(card1 x) -cardUI addnC /=.
rewrite [#|predI _ _|]eq_card0 => [|y]; last by rewrite !inE; case: eqP.
by apply: eq_card => y; rewrite !inE; case: eqP => // ->.
Qed.

Lemma max_card A : #|A| <= #|T|.
Proof. by rewrite -(cardC A) leq_addr. Qed.

Lemma card_size s : #|s| <= size s.
Proof.
elim: s => [|x s IHs] /=; first by rewrite card0.
rewrite cardU1 /=; case: (~~ _) => //; exact: leqW.
Qed.

Lemma card_uniqP s : reflect (#|s| = size s) (uniq s).
Proof.
elim: s => [|x s IHs]; first by left; exact card0.
rewrite cardU1 /= /addn; case: {+}(x \in s) => /=.
  by right=> card_Ssz; have:= card_size s; rewrite card_Ssz ltnn.
by apply: (iffP IHs) => [<-| [<-]].
Qed.

Lemma card0_eq A : #|A| = 0 -> A =i pred0.
Proof. by move=> A0 x; apply/idP => Ax; rewrite (cardD1 x) Ax in A0. Qed.

Lemma pred0P P : reflect (P =1 pred0) (pred0b P).
Proof. apply: (iffP eqP); [exact: card0_eq | exact: eq_card0]. Qed.

Lemma pred0Pn P : reflect (exists x, P x) (~~ pred0b P).
Proof.
case: (pickP P) => [x Px | P0].
  by rewrite (introN (pred0P P)) => [|P0]; [left; exists x | rewrite P0 in Px].
by rewrite -lt0n eq_card0 //; right=> [[x]]; rewrite P0.
Qed.

Lemma card_gt0P A : reflect (exists i, i \in A) (#|A| > 0).
Proof. rewrite lt0n; exact: pred0Pn. Qed.

Lemma subsetE A B : (A \subset B) = pred0b [predD A & B].
Proof. by rewrite unlock. Qed.

Lemma subsetP A B : reflect {subset A <= B} (A \subset B).
Proof.
rewrite unlock; apply: (iffP (pred0P _)) => [AB0 x | sAB x /=].
  by apply/implyP; apply/idPn; rewrite negb_imply andbC [_ && _]AB0.
by rewrite andbC -negb_imply; apply/negbF/implyP; exact: sAB.
Qed.

Lemma subsetPn A B :
  reflect (exists2 x, x \in A & x \notin B) (~~ (A \subset B)).
Proof.
rewrite unlock; apply: (iffP (pred0Pn _)) => [[x] | [x Ax nBx]].
  by case/andP; exists x.
by exists x; rewrite /= nBx.
Qed.

Lemma subset_leq_card A B : A \subset B -> #|A| <= #|B|.
Proof.
move=> sAB.
rewrite -(cardID A B) [#|predI _ _|](@eq_card _ A) ?leq_addr //= => x.
rewrite !inE andbC; case Ax: (x \in A) => //; exact: subsetP Ax.
Qed.

Lemma subxx_hint (mA : mem_pred T) : subset mA mA.
Proof.
by case: mA => A; have:= introT (subsetP A A); rewrite !unlock => ->.
Qed.
Hint Resolve subxx_hint.

(* The parametrization by predType makes it easier to apply subxx. *)
Lemma subxx (pT : predType T) (pA : pT) : pA \subset pA.
Proof. by []. Qed.

Lemma eq_subset A1 A2 : A1 =i A2 -> subset (mem A1) =1 subset (mem A2).
Proof.
move=> eqA12 [B]; rewrite !unlock; congr (_ == 0).
by apply: eq_card => x; rewrite inE /= eqA12.
Qed.

Lemma eq_subset_r B1 B2 : B1 =i B2 ->
  (@subset T)^~ (mem B1) =1 (@subset T)^~ (mem B2).
Proof.
move=> eqB12 [A]; rewrite !unlock; congr (_ == 0).
by apply: eq_card => x; rewrite !inE /= eqB12.
Qed.

Lemma eq_subxx A B : A =i B -> A \subset B.
Proof. by move/eq_subset->. Qed.

Lemma subset_predT A : A \subset T.
Proof. by apply/subsetP. Qed.

Lemma predT_subset A : T \subset A -> forall x, x \in A.
Proof. move/subsetP=> allA x; exact: allA. Qed.

Lemma subset_pred1 A x : (pred1 x \subset A) = (x \in A).
Proof. by apply/subsetP/idP=> [-> // | Ax y /eqP-> //]; exact: eqxx. Qed.

Lemma subset_eqP A B : reflect (A =i B) ((A \subset B) && (B \subset A)).
Proof.
apply: (iffP andP) => [[sAB sBA] x| eqAB]; last by rewrite !eq_subxx.
by apply/idP/idP; apply: subsetP.
Qed.

Lemma subset_cardP A B : #|A| = #|B| -> reflect (A =i B) (A \subset B).
Proof.
move=> eqcAB; case: (subsetP A B) (subset_eqP A B) => //= sAB.
case: (subsetP B A) => [//|[]] x Bx; apply/idPn => Ax.
case/idP: (ltnn #|A|); rewrite {2}eqcAB (cardD1 x B) Bx /=.
apply: subset_leq_card; apply/subsetP=> y Ay; rewrite inE /= andbC.
by rewrite sAB //; apply/eqP => eqyx; rewrite -eqyx Ay in Ax.
Qed.

Lemma subset_leqif_card A B : A \subset B -> #|A| <= #|B| ?= iff (B \subset A).
Proof.
move=> sAB; split; [exact: subset_leq_card | apply/eqP/idP].
  by move/subset_cardP=> sABP; rewrite (eq_subset_r (sABP sAB)).
by move=> sBA; apply: eq_card; apply/subset_eqP; rewrite sAB.
Qed.

Lemma subset_trans A B C : A \subset B -> B \subset C -> A \subset C.
Proof.
by move/subsetP=> sAB /subsetP=> sBC; apply/subsetP=> x /sAB; exact: sBC.
Qed.

Lemma subset_all s A : (s \subset A) = all (mem A) s.
Proof. by exact (sameP (subsetP _ _) allP). Qed.

Lemma properE A B : A \proper B = (A \subset B) && ~~(B \subset A).
Proof. by []. Qed.

Lemma properP A B :
  reflect (A \subset B /\ (exists2 x, x \in B & x \notin A)) (A \proper B).
Proof.
by rewrite properE; apply: (iffP andP) => [] [-> /subsetPn].
Qed.

Lemma proper_sub A B : A \proper B -> A \subset B.
Proof. by case/andP. Qed.

Lemma proper_subn A B : A \proper B -> ~~ (B \subset A).
Proof. by case/andP. Qed.

Lemma proper_trans A B C : A \proper B -> B \proper C -> A \proper C.
Proof.
case/properP=> sAB [x Bx nAx] /properP[sBC [y Cy nBy]].
rewrite properE (subset_trans sAB) //=; apply/subsetPn; exists y => //.
by apply: contra nBy; exact: subsetP.
Qed.

Lemma proper_sub_trans A B C : A \proper B -> B \subset C -> A \proper C.
Proof.
case/properP=> sAB [x Bx nAx] sBC; rewrite properE (subset_trans sAB) //.
by apply/subsetPn; exists x; rewrite ?(subsetP _ _ sBC).
Qed.

Lemma sub_proper_trans A B C : A \subset B -> B \proper C -> A \proper C.
Proof.
move=> sAB /properP[sBC [x Cx nBx]]; rewrite properE (subset_trans sAB) //.
by apply/subsetPn; exists x => //; apply: contra nBx; exact: subsetP.
Qed.

Lemma proper_card A B : A \proper B -> #|A| < #|B|.
Proof.
by case/andP=> sAB nsBA; rewrite ltn_neqAle !(subset_leqif_card sAB) andbT.
Qed.

Lemma proper_irrefl A : ~~ (A \proper A).
Proof. by rewrite properE subxx. Qed.

Lemma properxx A : (A \proper A) = false.
Proof. by rewrite properE subxx. Qed.

Lemma eq_proper A B : A =i B -> proper (mem A) =1 proper (mem B).
Proof.
move=> eAB [C]; congr (_ && _); first exact: (eq_subset eAB).
by rewrite (eq_subset_r eAB).
Qed.

Lemma eq_proper_r A B : A =i B ->
  (@proper T)^~ (mem A) =1 (@proper T)^~ (mem B).
Proof.
move=> eAB [C]; congr (_ && _); first exact: (eq_subset_r eAB).
by rewrite (eq_subset eAB).
Qed.

Lemma disjoint_sym A B : [disjoint A & B] = [disjoint B & A].
Proof. by congr (_ == 0); apply: eq_card => x; exact: andbC. Qed.

Lemma eq_disjoint A1 A2 : A1 =i A2 -> disjoint (mem A1) =1 disjoint (mem A2).
Proof.
by move=> eqA12 [B]; congr (_ == 0); apply: eq_card => x; rewrite !inE eqA12.
Qed.

Lemma eq_disjoint_r B1 B2 : B1 =i B2 ->
  (@disjoint T)^~ (mem B1) =1 (@disjoint T)^~ (mem B2).
Proof.
by move=> eqB12 [A]; congr (_ == 0); apply: eq_card => x; rewrite !inE eqB12.
Qed.

Lemma subset_disjoint A B : (A \subset B) = [disjoint A & [predC B]].
Proof. by rewrite disjoint_sym unlock. Qed.

Lemma disjoint_subset A B : [disjoint A & B] = (A \subset [predC B]).
Proof.
by rewrite subset_disjoint; apply: eq_disjoint_r => x; rewrite !inE /= negbK.
Qed.

Lemma disjoint_trans A B C :
   A \subset B -> [disjoint B & C] -> [disjoint A & C].
Proof. by rewrite 2!disjoint_subset; exact: subset_trans. Qed.

Lemma disjoint0 A : [disjoint pred0 & A].
Proof. exact/pred0P. Qed.

Lemma eq_disjoint0 A B : A =i pred0 -> [disjoint A & B].
Proof. by move/eq_disjoint->; exact: disjoint0. Qed.

Lemma disjoint1 x A : [disjoint pred1 x & A] = (x \notin A).
Proof.
apply/negbRL/(sameP (pred0Pn _)).
apply: introP => [Ax | notAx [_ /andP[/eqP->]]]; last exact: negP.
by exists x; rewrite !inE eqxx.
Qed.

Lemma eq_disjoint1 x A B :
  A =i pred1 x ->  [disjoint A & B] = (x \notin B).
Proof. by move/eq_disjoint->; exact: disjoint1. Qed.

Lemma disjointU A B C :
  [disjoint predU A B & C] = [disjoint A & C] && [disjoint B & C].
Proof.
case: [disjoint A & C] / (pred0P (xpredI A C)) => [A0 | nA0] /=.
  by congr (_ == 0); apply: eq_card => x; rewrite [x \in _]andb_orl A0.
apply/pred0P=> nABC; case: nA0 => x; apply/idPn=> /=; move/(_ x): nABC.
by rewrite [_ x]andb_orl; case/norP.
Qed.

Lemma disjointU1 x A B :
  [disjoint predU1 x A & B] = (x \notin B) && [disjoint A & B].
Proof. by rewrite disjointU disjoint1. Qed.

Lemma disjoint_cons x s B :
  [disjoint x :: s & B] = (x \notin B) && [disjoint s & B].
Proof. exact: disjointU1. Qed.

Lemma disjoint_has s A : [disjoint s & A] = ~~ has (mem A) s.
Proof.
rewrite -(@eq_has _ (mem (enum A))) => [|x]; last exact: mem_enum.
rewrite has_sym has_filter -filter_predI -has_filter has_count -eqn0Ngt.
by rewrite count_filter /disjoint /pred0b unlock.
Qed.

Lemma disjoint_cat s1 s2 A :
  [disjoint s1 ++ s2 & A] = [disjoint s1 & A] && [disjoint s2 & A].
Proof. by rewrite !disjoint_has has_cat negb_or. Qed.

End OpsTheory.

Hint Resolve subxx_hint.

Implicit Arguments pred0P [T P].
Implicit Arguments pred0Pn [T P].
Implicit Arguments subsetP [T A B].
Implicit Arguments subsetPn [T A B].
Implicit Arguments subset_eqP [T A B].
Implicit Arguments card_uniqP [T s].
Implicit Arguments properP [T A B].
Prenex Implicits pred0P pred0Pn subsetP subsetPn subset_eqP card_uniqP.

(**********************************************************************)
(*                                                                    *)
(*  Boolean quantifiers for finType                                   *)
(*                                                                    *)
(**********************************************************************)

Section Quantifiers.

Variables (T : finType) (rT : T -> eqType).
Implicit Type (D P : pred T) (f : forall x, rT x).

Lemma forallP P : reflect (forall x, P x) [forall x, P x].
Proof. by apply: (iffP pred0P) => /= P_ x; rewrite /= ?P_ ?(negbFE (P_ x)). Qed.

Lemma eqfunP f1 f2 : reflect (forall x, f1 x = f2 x) [forall x, f1 x == f2 x].
Proof. by apply: (iffP (forallP _)) => eq_f12 x; apply/eqP/eq_f12. Qed.

Lemma forall_inP D P : reflect (forall x, D x -> P x) [forall (x | D x), P x].
Proof. by apply: (iffP (forallP _)) => /= P_ x /=; apply/implyP; apply: P_. Qed.

Lemma eqfun_inP D f1 f2 :
  reflect {in D, forall x, f1 x = f2 x} [forall (x | x \in D), f1 x == f2 x].
Proof. by apply: (iffP (forall_inP _ _)) => eq_f12 x Dx; apply/eqP/eq_f12. Qed.

Lemma existsP P : reflect (exists x, P x) [exists x, P x].
Proof. by apply: (iffP pred0Pn) => [] [x]; exists x. Qed.

Lemma exists_eqP f1 f2 :
  reflect (exists x, f1 x = f2 x) [exists x, f1 x == f2 x].
Proof. by apply: (iffP (existsP _)) => [] [x /eqP]; exists x. Qed.

Lemma exists_inP D P : reflect (exists2 x, D x & P x) [exists (x | D x), P x].
Proof.
by apply: (iffP pred0Pn) => [[x /andP[]] | [x]]; exists x => //; apply/andP.
Qed.

Lemma exists_eq_inP D f1 f2 :
  reflect (exists2 x, D x & f1 x = f2 x) [exists (x | D x), f1 x == f2 x].
Proof. by apply: (iffP (exists_inP _ _)) => [] [x Dx /eqP]; exists x. Qed.

Lemma eq_existsb P1 P2 : P1 =1 P2 -> [exists x, P1 x] = [exists x, P2 x].
Proof. by move=> eqP12; congr (_ != 0); apply: eq_card. Qed.

Lemma eq_existsb_in D P1 P2 :
    (forall x, D x -> P1 x = P2 x) ->
  [exists (x | D x), P1 x] = [exists (x | D x), P2 x].
Proof. by move=> eqP12; apply: eq_existsb => x; apply: andb_id2l => /eqP12. Qed.

Lemma eq_forallb P1 P2 : P1 =1 P2 -> [forall x, P1 x] = [forall x, P2 x].
Proof. by move=> eqP12; apply/negb_inj/eq_existsb=> /= x; rewrite eqP12. Qed.

Lemma eq_forallb_in D P1 P2 :
    (forall x, D x -> P1 x = P2 x) ->
  [forall (x | D x), P1 x] = [forall (x | D x), P2 x].
Proof.
by move=> eqP12; apply: eq_forallb => i; case Di: (D i); rewrite // eqP12.
Qed.

Lemma negb_forall P : ~~ [forall x, P x] = [exists x, ~~ P x].
Proof. by []. Qed.

Lemma negb_forall_in D P :
  ~~ [forall (x | D x), P x] = [exists (x | D x), ~~ P x].
Proof. by apply: eq_existsb => x; rewrite negb_imply. Qed.

Lemma negb_exists P : ~~ [exists x, P x] = [forall x, ~~ P x].
Proof. by apply/negbLR/esym/eq_existsb=> x; apply: negbK. Qed.

Lemma negb_exists_in D P :
  ~~ [exists (x | D x), P x] = [forall (x | D x), ~~ P x].
Proof. by rewrite negb_exists; apply/eq_forallb => x; rewrite [~~ _]fun_if. Qed.

End Quantifiers.

Implicit Arguments forallP [T P].
Implicit Arguments eqfunP [T rT f1 f2].
Implicit Arguments forall_inP [T D P].
Implicit Arguments eqfun_inP [T rT D f1 f2].
Implicit Arguments existsP [T P].
Implicit Arguments exists_inP [T D P].

Section Extrema.

Variables (I : finType) (i0 : I) (P : pred I) (F : I -> nat).

Let arg_pred ord := [pred i | P i & [forall (j | P j), ord (F i) (F j)]].

Definition arg_min := odflt i0 (pick (arg_pred leq)).

Definition arg_max := odflt i0 (pick (arg_pred geq)).

CoInductive extremum_spec (ord : rel nat) : I -> Type :=
  ExtremumSpec i of P i & (forall j, P j -> ord (F i) (F j))
    : extremum_spec ord i.

Hypothesis Pi0 : P i0.

Let FP n := [exists (i | P i), F i == n].
Let FP_F i : P i -> FP (F i).
Proof. by move=> Pi; apply/existsP; exists i; rewrite Pi /=. Qed.
Let exFP : exists n, FP n. Proof. by exists (F i0); exact: FP_F. Qed.

Lemma arg_minP : extremum_spec leq arg_min.
Proof.
rewrite /arg_min; case: pickP => [i /andP[Pi /forallP/= min_i] | no_i].
  by split=> // j; apply/implyP.
case/ex_minnP: exFP => n ex_i min_i; case/pred0P: ex_i => i /=.
apply: contraFF (no_i i) => /andP[Pi /eqP def_n]; rewrite /= Pi.
by apply/forall_inP=> j Pj; rewrite def_n min_i ?FP_F.
Qed.

Lemma arg_maxP : extremum_spec geq arg_max.
Proof.
rewrite /arg_max; case: pickP => [i /andP[Pi /forall_inP/= max_i] | no_i].
  by split=> // j; apply/implyP.
have (n): FP n -> n <= foldr maxn 0 (map F (enum P)).
  case/existsP=> i; rewrite -[P i]mem_enum andbC /= => /andP[/eqP <-].
  elim: (enum P) => //= j e IHe; rewrite leq_max orbC !inE.
  by case/predU1P=> [-> | /IHe-> //]; rewrite leqnn orbT.
case/ex_maxnP=> // n ex_i max_i; case/pred0P: ex_i => i /=.
apply: contraFF (no_i i) => /andP[Pi def_n]; rewrite /= Pi.
by apply/forall_inP=> j Pj; rewrite (eqP def_n) max_i ?FP_F.
Qed.

End Extrema.

Notation "[ 'arg' 'min_' ( i < i0 | P ) F ]" :=
    (arg_min i0 (fun i => P%B) (fun i => F))
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'min_' ( i  <  i0  |  P )  F ]") : form_scope.
 
Notation "[ 'arg' 'min_' ( i < i0 'in' A ) F ]" :=
    [arg min_(i < i0 | i \in A) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'min_' ( i  <  i0  'in'  A )  F ]") : form_scope.

Notation "[ 'arg' 'min_' ( i < i0 ) F ]" := [arg min_(i < i0 | true) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'min_' ( i  <  i0 )  F ]") : form_scope.
 
Notation "[ 'arg' 'max_' ( i > i0 | P ) F ]" :=
     (arg_max i0 (fun i => P%B) (fun i => F))
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'max_' ( i  >  i0  |  P )  F ]") : form_scope.
 
Notation "[ 'arg' 'max_' ( i > i0 'in' A ) F ]" :=
    [arg max_(i > i0 | i \in A) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'max_' ( i  >  i0  'in'  A )  F ]") : form_scope.

Notation "[ 'arg' 'max_' ( i > i0 ) F ]" := [arg max_(i > i0 | true) F]
  (at level 0, i, i0 at level 10,
   format "[ 'arg'  'max_' ( i  >  i0 ) F ]") : form_scope.

(**********************************************************************)
(*                                                                    *)
(*  Boolean injectivity test for functions with a finType domain      *)
(*                                                                    *)
(**********************************************************************)

Section Injectiveb.

Variables (aT : finType) (rT : eqType) (f : aT -> rT).
Implicit Type D : pred aT.

Definition dinjectiveb D := uniq (map f (enum D)).

Definition injectiveb := dinjectiveb aT.

Lemma dinjectivePn D :
  reflect (exists2 x, x \in D & exists2 y, y \in [predD1 D & x] & f x = f y)
          (~~ dinjectiveb D).
Proof.
apply: (iffP idP) => [injf | [x Dx [y Dxy eqfxy]]]; last first.
  move: Dx; rewrite -(mem_enum D) => /rot_to[i E defE].
  rewrite /dinjectiveb -(rot_uniq i) -map_rot defE /=; apply/nandP; left.
  rewrite inE /= -(mem_enum D) -(mem_rot i) defE inE in Dxy.
  rewrite andb_orr andbC andbN in Dxy.
  by rewrite eqfxy map_f //; case/andP: Dxy.
pose p := [pred x in D | [exists (y | y \in [predD1 D & x]), f x == f y]].
case: (pickP p) => [x /= /andP[Dx /exists_inP[y Dxy /eqP eqfxy]] | no_p].
  by exists x; last exists y.
rewrite /dinjectiveb map_inj_in_uniq ?enum_uniq // in injf => x y Dx Dy eqfxy.
apply: contraNeq (negbT (no_p x)) => ne_xy /=; rewrite -mem_enum Dx.
by apply/existsP; exists y; rewrite /= !inE eq_sym ne_xy -mem_enum Dy eqfxy /=.
Qed.

Lemma dinjectiveP D : reflect {in D &, injective f} (dinjectiveb D).
Proof.
rewrite -[dinjectiveb D]negbK.
case: dinjectivePn=> [noinjf | injf]; constructor.
  case: noinjf => x Dx [y /andP[neqxy /= Dy] eqfxy] injf.
  by case/eqP: neqxy; exact: injf.
move=> x y Dx Dy /= eqfxy; apply/eqP; apply/idPn=> nxy; case: injf.
by exists x => //; exists y => //=; rewrite inE /= eq_sym nxy.
Qed.

Lemma injectivePn :
  reflect (exists x, exists2 y, x != y & f x = f y) (~~ injectiveb).
Proof.
apply: (iffP (dinjectivePn _)) => [[x _ [y nxy eqfxy]] | [x [y nxy eqfxy]]];
 by exists x => //; exists y => //; rewrite inE /= andbT eq_sym in nxy *.
Qed.

Lemma injectiveP : reflect (injective f) injectiveb.
Proof. apply: (iffP (dinjectiveP _)) => injf x y => [|_ _]; exact: injf. Qed.

End Injectiveb.

Definition image_mem T T' f mA : seq T' := map f (@enum_mem T mA).
Notation image f A := (image_mem f (mem A)).
Notation "[ 'seq' F | x 'in' A ]" := (image (fun x => F) A)
  (at level 0, F at level 99, x ident,
   format "'[hv' [ 'seq'  F '/ '  |  x  'in'  A ] ']'") : seq_scope.
Notation "[ 'seq' F | x : T 'in' A ]" := (image (fun x : T => F) A)
  (at level 0, F at level 99, x ident, only parsing) : seq_scope.
Notation "[ 'seq' F | x : T ]" :=
  [seq F | x : T in sort_of_simpl_pred (@pred_of_argType T)]
  (at level 0, F at level 99, x ident,
   format "'[hv' [ 'seq'  F '/ '  |  x  :  T ] ']'") : seq_scope.
Notation "[ 'seq' F , x ]" := [seq F | x : _ ]
  (at level 0, F at level 99, x ident, only parsing) : seq_scope.

Definition codom T T' f := @image_mem T T' f (mem T).

Section Image.

Variable T : finType.
Implicit Type A : pred T.

Section SizeImage.

Variables (T' : Type) (f : T -> T').

Lemma size_image A : size (image f A) = #|A|.
Proof. by rewrite size_map -cardE. Qed.

Lemma size_codom : size (codom f) = #|T|.
Proof. exact: size_image. Qed.

Lemma codomE : codom f = map f (enum T).
Proof. by []. Qed.

End SizeImage.

Variables (T' : eqType) (f : T -> T').

Lemma imageP A y : reflect (exists2 x, x \in A & y = f x) (y \in image f A).
Proof.
by apply: (iffP mapP) => [] [x Ax y_fx]; exists x; rewrite // mem_enum in Ax *.
Qed.

Lemma codomP y : reflect (exists x, y = f x) (y \in codom f).
Proof. by apply: (iffP (imageP _ y)) => [][x]; exists x. Qed.

Remark iinv_proof A y : y \in image f A -> {x | x \in A & f x = y}.
Proof.
move=> fy; pose b x := A x && (f x == y).
case: (pickP b) => [x /andP[Ax /eqP] | nfy]; first by exists x.
by case/negP: fy => /imageP[x Ax fx_y]; case/andP: (nfy x); rewrite fx_y.
Qed.

Definition iinv A y fAy := s2val (@iinv_proof A y fAy).

Lemma f_iinv A y fAy : f (@iinv A y fAy) = y.
Proof. exact: s2valP' (iinv_proof fAy). Qed.

Lemma mem_iinv A y fAy : @iinv A y fAy \in A.
Proof. exact: s2valP (iinv_proof fAy). Qed.

Lemma in_iinv_f A : {in A &, injective f} ->
  forall x fAfx, x \in A -> @iinv A (f x) fAfx = x.
Proof.
move=> injf x fAfx Ax; apply: injf => //; [exact: mem_iinv | exact: f_iinv].
Qed.

Lemma preim_iinv A B y fAy : preim f B (@iinv A y fAy) = B y.
Proof. by rewrite /= f_iinv. Qed.

Lemma image_f A x : x \in A -> f x \in image f A.
Proof. by move=> Ax; apply/imageP; exists x. Qed.

Lemma codom_f x : f x \in codom f.
Proof. by exact: image_f. Qed.

Lemma image_codom A : {subset image f A <= codom f}.
Proof. by move=> _ /imageP[x _ ->]; exact: codom_f. Qed.

Lemma image_pred0 : image f pred0 =i pred0.
Proof. by move=> x; rewrite /image_mem /= enum0. Qed.

Section Injective.

Hypothesis injf : injective f.

Lemma mem_image A x : (f x \in image f A) = (x \in A).
Proof. by rewrite mem_map ?mem_enum. Qed.

Lemma pre_image A : [preim f of image f A] =i A.
Proof. by move=> x; rewrite inE /= mem_image. Qed.

Lemma image_iinv A y (fTy : y \in codom f) :
  (y \in image f A) = (iinv fTy \in A).
Proof. by rewrite -mem_image ?f_iinv. Qed.

Lemma iinv_f x fTfx : @iinv T (f x) fTfx = x.
Proof. by apply: in_iinv_f; first exact: in2W. Qed.

Lemma image_pre (B : pred T') : image f [preim f of B] =i [predI B & codom f].
Proof. by move=> y; rewrite /image_mem -filter_map /= mem_filter -enumT. Qed.

Lemma bij_on_codom (x0 : T) : {on [pred y in codom f], bijective f}.
Proof.
pose g y := iinv (valP (insigd (codom_f x0) y)).
by exists g => [x fAfx | y fAy]; first apply: injf; rewrite f_iinv insubdK.
Qed.

Lemma bij_on_image A (x0 : T) : {on [pred y in image f A], bijective f}.
Proof. exact: subon_bij (@image_codom A) (bij_on_codom x0). Qed.

End Injective.

Fixpoint preim_seq s :=
  if s is y :: s' then
    (if pick (preim f (pred1 y)) is Some x then cons x else id) (preim_seq s')
    else [::].

Lemma map_preim (s : seq T') : {subset s <= codom f} -> map f (preim_seq s) = s.
Proof.
elim: s => //= y s IHs; case: pickP => [x /eqP fx_y | nfTy] fTs.
  by rewrite /= fx_y IHs // => z s_z; apply: fTs; exact: predU1r.
by case/imageP: (fTs y (mem_head y s)) => x _ fx_y; case/eqP: (nfTy x).
Qed.

End Image.

Prenex Implicits codom iinv.
Implicit Arguments imageP [T T' f A y].
Implicit Arguments codomP [T T' f y].

Lemma flatten_imageP (aT : finType) (rT : eqType) A (P : pred aT) (y : rT) :
  reflect (exists2 x, x \in P & y \in A x) (y \in flatten [seq A x | x in P]).
Proof.
by apply: (iffP flatten_mapP) => [][x Px]; exists x; rewrite ?mem_enum in Px *.
Qed.
Implicit Arguments flatten_imageP [aT rT A P y].

Section CardFunImage.

Variables (T T' : finType) (f : T -> T').
Implicit Type A : pred T.

Lemma leq_image_card A : #|image f A| <= #|A|.
Proof. by rewrite (cardE A) -(size_map f) card_size. Qed.

Lemma card_in_image A : {in A &, injective f} -> #|image f A| = #|A|.
Proof.
move=> injf; rewrite (cardE A) -(size_map f); apply/card_uniqP.
rewrite map_inj_in_uniq ?enum_uniq // => x y; rewrite !mem_enum; exact: injf.
Qed.

Lemma image_injP A : reflect {in A &, injective f} (#|image f A| == #|A|).
Proof.
apply: (iffP eqP) => [eqfA |]; last exact: card_in_image.
by apply/dinjectiveP; apply/card_uniqP; rewrite size_map -cardE.
Qed.

Hypothesis injf : injective f.

Lemma card_image A : #|image f A| = #|A|.
Proof. apply: card_in_image; exact: in2W. Qed.

Lemma card_codom : #|codom f| = #|T|.
Proof. exact: card_image. Qed.

Lemma card_preim (B : pred T') : #|[preim f of B]| = #|[predI codom f & B]|.
Proof.
rewrite -card_image /=; apply: eq_card => y.
by rewrite [y \in _]image_pre !inE andbC.
Qed.

Hypothesis card_range : #|T| = #|T'|.

Lemma inj_card_onto y : y \in codom f.
Proof. by move: y; apply/subset_cardP; rewrite ?card_codom ?subset_predT. Qed.

Lemma inj_card_bij :  bijective f.
Proof.
by exists (fun y => iinv (inj_card_onto y)) => y; rewrite ?iinv_f ?f_iinv.
Qed.

End CardFunImage.

Implicit Arguments image_injP [T T' f A].

Section FinCancel.

Variables (T : finType) (f g : T -> T).

Section Inv.

Hypothesis injf : injective f.

Lemma injF_onto y : y \in codom f. Proof. exact: inj_card_onto. Qed.
Definition invF y := iinv (injF_onto y).
Lemma invF_f : cancel f invF. Proof. by move=> x; exact: iinv_f. Qed.
Lemma f_invF : cancel invF f. Proof. by move=> y; exact: f_iinv. Qed.
Lemma injF_bij : bijective f. Proof. exact: inj_card_bij. Qed.

End Inv.

Hypothesis fK : cancel f g.

Lemma canF_sym : cancel g f.
Proof. exact/(bij_can_sym (injF_bij (can_inj fK))). Qed.

Lemma canF_LR x y : x = g y -> f x = y.
Proof. exact: canLR canF_sym. Qed.

Lemma canF_RL x y : g x = y -> x = f y.
Proof. exact: canRL canF_sym. Qed.

Lemma canF_eq x y : (f x == y) = (x == g y).
Proof. exact: (can2_eq fK canF_sym). Qed.

Lemma canF_invF : g =1 invF (can_inj fK).
Proof. by move=> y; apply: (canLR fK); rewrite f_invF. Qed.

End FinCancel.

Section EqImage.

Variables (T : finType) (T' : Type).

Lemma eq_image (A B : pred T) (f g : T -> T') :
  A =i B -> f =1 g -> image f A = image g B.
Proof.
by move=> eqAB eqfg; rewrite /image_mem (eq_enum eqAB) (eq_map eqfg).
Qed.

Lemma eq_codom (f g : T -> T') : f =1 g -> codom f = codom g.
Proof. exact: eq_image. Qed.

Lemma eq_invF f g injf injg : f =1 g -> @invF T f injf =1 @invF T g injg.
Proof.
by move=> eq_fg x; apply: (canLR (invF_f injf)); rewrite eq_fg f_invF.
Qed.

End EqImage.

(* Standard finTypes *)

Section SeqFinType.

Variables (T : choiceType) (s : seq T).

Record seq_sub : Type := SeqSub {ssval : T; ssvalP : in_mem ssval (@mem T _ s)}.

Canonical seq_sub_subType := Eval hnf in [subType for ssval].
Definition seq_sub_eqMixin := Eval hnf in [eqMixin of seq_sub by <:].
Canonical seq_sub_eqType := Eval hnf in EqType seq_sub seq_sub_eqMixin.
Definition seq_sub_choiceMixin := [choiceMixin of seq_sub by <:].
Canonical seq_sub_choiceType :=
  Eval hnf in ChoiceType seq_sub seq_sub_choiceMixin.

Definition seq_sub_enum : seq seq_sub := undup (pmap insub s).

Lemma mem_seq_sub_enum x : x \in seq_sub_enum.
Proof. by rewrite mem_undup mem_pmap -valK map_f ?ssvalP. Qed.

Lemma val_seq_sub_enum : uniq s -> map val seq_sub_enum = s.
Proof.
move=> Us; rewrite /seq_sub_enum undup_id ?pmap_sub_uniq //.
rewrite (pmap_filter (@insubK _ _ _)); apply/all_filterP.
by apply/allP => x; rewrite isSome_insub.
Qed.

Definition seq_sub_pickle x := index x seq_sub_enum.
Definition seq_sub_unpickle n := nth None (map some seq_sub_enum) n.
Lemma seq_sub_pickleK : pcancel seq_sub_pickle seq_sub_unpickle.
Proof.
rewrite /seq_sub_unpickle => x.
by rewrite (nth_map x) ?nth_index ?index_mem ?mem_seq_sub_enum.
Qed.

Definition seq_sub_countMixin := CountMixin seq_sub_pickleK.
Canonical seq_sub_countType := Eval hnf in CountType seq_sub seq_sub_countMixin.
Canonical seq_sub_subCountType := Eval hnf in [subCountType of seq_sub].
Definition seq_sub_finMixin :=
  Eval hnf in UniqFinMixin (undup_uniq _) mem_seq_sub_enum.
Canonical seq_sub_finType := Eval hnf in FinType seq_sub seq_sub_finMixin.

Lemma card_seq_sub : uniq s -> #|{:seq_sub}| = size s.
Proof.
by move=> Us; rewrite cardE enumT -(size_map val) unlock val_seq_sub_enum.
Qed.

End SeqFinType.

Lemma unit_enumP : Finite.axiom [::tt]. Proof. by case. Qed.
Definition unit_finMixin := Eval hnf in FinMixin unit_enumP.
Canonical unit_finType := Eval hnf in FinType unit unit_finMixin.
Lemma card_unit : #|{: unit}| = 1. Proof. by rewrite cardT enumT unlock. Qed.

Lemma bool_enumP : Finite.axiom [:: true; false]. Proof. by case. Qed.
Definition bool_finMixin := Eval hnf in FinMixin bool_enumP.
Canonical bool_finType := Eval hnf in FinType bool bool_finMixin.
Lemma card_bool : #|{: bool}| = 2. Proof. by rewrite cardT enumT unlock. Qed.

Local Notation enumF T := (Finite.enum T).

Section OptionFinType.

Variable T : finType.

Definition option_enum := None :: map some (enumF T).

Lemma option_enumP : Finite.axiom option_enum.
Proof. by case=> [x|]; rewrite /= count_map (count_pred0, enumP). Qed.

Definition option_finMixin := Eval hnf in FinMixin option_enumP.
Canonical option_finType := Eval hnf in FinType (option T) option_finMixin.

Lemma card_option : #|{: option T}| = #|T|.+1.
Proof. by rewrite !cardT !enumT {1}unlock /= !size_map. Qed.

End OptionFinType.

Section TransferFinType.

Variables (eT : countType) (fT : finType) (f : eT -> fT).

Lemma pcan_enumP g : pcancel f g -> Finite.axiom (undup (pmap g (enumF fT))).
Proof.
move=> fK x; rewrite count_uniq_mem ?undup_uniq // mem_undup.
by rewrite mem_pmap -fK map_f // -enumT mem_enum.
Qed.

Definition PcanFinMixin g fK := FinMixin (@pcan_enumP g fK).

Definition CanFinMixin g (fK : cancel f g) := PcanFinMixin (can_pcan fK).

End TransferFinType.

Section SubFinType.

Variables (T : choiceType) (P : pred T).
Import Finite.

Structure subFinType := SubFinType {
  subFin_sort :> subType P;
  _ : mixin_of (sub_eqType subFin_sort)
}.

Definition pack_subFinType U :=
  fun cT b m & phant_id (class cT) (@Class U b m) =>
  fun sT m'  & phant_id m' m => @SubFinType sT m'.

Implicit Type sT : subFinType.

Definition subFin_mixin sT :=
  let: SubFinType _ m := sT return mixin_of (sub_eqType sT) in m.

Coercion subFinType_subCountType sT := @SubCountType _ _ sT (subFin_mixin sT).
Canonical subFinType_subCountType.

Coercion subFinType_finType sT :=
  Pack (@Class sT (sub_choiceClass sT) (subFin_mixin sT)) sT.
Canonical subFinType_finType.

End SubFinType.

(* This assumes that T has both finType and subCountType structures. *)
Notation "[ 'subFinType' 'of' T ]" := (@pack_subFinType _ _ T _ _ _ id _ _ id)
  (at level 0, format "[ 'subFinType'  'of'  T ]") : form_scope.

Canonical seq_sub_subFinType T s :=
  Eval hnf in [subFinType of @seq_sub T s].

Section FinTypeForSub.

Variables (T : finType) (P : pred T) (sT : subCountType P).

Definition sub_enum : seq sT := pmap insub (enumF T).

Lemma mem_sub_enum u : u \in sub_enum.
Proof. by rewrite mem_pmap_sub -enumT mem_enum. Qed.

Lemma sub_enum_uniq : uniq sub_enum.
Proof. by rewrite pmap_sub_uniq // -enumT enum_uniq. Qed.

Lemma val_sub_enum : map val sub_enum = enum P.
Proof.
rewrite pmap_filter; last exact: insubK.
by apply: eq_filter => x; exact: isSome_insub.
Qed.

(* We can't declare a canonical structure here because we've already *)
(* stated that subType_sort and FinType.sort unify via to the        *)
(* subType_finType structure.                                        *)

Definition SubFinMixin := UniqFinMixin sub_enum_uniq mem_sub_enum.
Definition SubFinMixin_for (eT : eqType) of phant eT :=
  identity_nondep_rect _ Finite.mixin_of SubFinMixin eT.
Let sfT := FinType sT SubFinMixin.

Lemma card_sub : #|sfT| = #|[pred x | P x]|.
Proof. by rewrite !cardE enumT unlock -(size_map val) val_sub_enum. Qed.

Lemma eq_card_sub (A : pred sfT) : A =i predT -> #|A| = #|[pred x | P x]|.
Proof. exact: eq_card_trans card_sub. Qed.

End FinTypeForSub.

(* This assumes that T has a subCountType structure over a type that  *)
(* has a finType structure.                                           *)
Notation "[ 'finMixin' 'of' T 'by' <: ]" :=
    (SubFinMixin_for (Phant T) (erefl _))
  (at level 0, format "[ 'finMixin'  'of'  T  'by'  <: ]") : form_scope.

(* Regression for the subFinType stack
Record myb : Type := MyB {myv : bool; _ : ~~ myv}.
Canonical myb_sub := Eval hnf in [subType for myv].
Definition myb_eqm := Eval hnf in [eqMixin of myb by <:].
Canonical myb_eq := Eval hnf in EqType myb myb_eqm.
Definition myb_chm := [choiceMixin of myb by <:].
Canonical myb_ch := Eval hnf in ChoiceType myb myb_chm.
Definition myb_cntm := [countMixin of myb by <:].
Canonical myb_cnt := Eval hnf in CountType myb myb_cntm.
Canonical myb_scnt := Eval hnf in [subCountType of myb].
Definition myb_finm := [finMixin of myb by <:].
Canonical myb_fin := Eval hnf in FinType myb myb_finm.
Canonical myb_sfin := Eval hnf in [subFinType of myb].
Print Canonical Projections.
Print myb_finm.
Print myb_cntm.
*)

(* assia : no more sigs *)
(* Section CardSig. *)

(* Variables (T : finType) (P : pred T). *)

(* Definition sig_finMixin := [finMixin of {x | P x} by <:]. *)
(* Canonical sig_finType := Eval hnf in FinType {x | P x} sig_finMixin. *)
(* Canonical sig_subFinType := Eval hnf in [subFinType of {x | P x}]. *)

(* Lemma card_sig : #|{: {x | P x}}| = #|[pred x | P x]|. *)
(* Proof. exact: card_sub. Qed. *)

(* End CardSig. *)

(**********************************************************************)
(*                                                                    *)
(*  Ordinal finType : {0, ... , n-1}                                  *)
(*                                                                    *)
(**********************************************************************)

Section OrdinalSub.

Variable n : nat.

Inductive ordinal : predArgType := Ordinal m of m < n.

Coercion nat_of_ord i := let: Ordinal m _ := i in m.

Canonical ordinal_subType := [subType for nat_of_ord].
Definition ordinal_eqMixin := Eval hnf in [eqMixin of ordinal by <:].
Canonical ordinal_eqType := Eval hnf in EqType ordinal ordinal_eqMixin.
Definition ordinal_choiceMixin := [choiceMixin of ordinal by <:].
Canonical ordinal_choiceType :=
  Eval hnf in ChoiceType ordinal ordinal_choiceMixin.
Definition ordinal_countMixin := [countMixin of ordinal by <:].
Canonical ordinal_countType := Eval hnf in CountType ordinal ordinal_countMixin.
Canonical ordinal_subCountType := [subCountType of ordinal].

Lemma ltn_ord (i : ordinal) : i < n. Proof. exact: valP i. Qed.

Lemma ord_inj : injective nat_of_ord. Proof. exact: val_inj. Qed.

Definition ord_enum : seq ordinal := pmap insub (iota 0 n).

Lemma val_ord_enum : map val ord_enum = iota 0 n.
Proof.
rewrite pmap_filter; last exact: insubK.
by apply/all_filterP; apply/allP=> i; rewrite mem_iota isSome_insub.
Qed.

Lemma ord_enum_uniq : uniq ord_enum.
Proof. by rewrite pmap_sub_uniq ?iota_uniq. Qed.

Lemma mem_ord_enum i : i \in ord_enum.
Proof. by rewrite -(mem_map ord_inj) val_ord_enum mem_iota ltn_ord. Qed.

Definition ordinal_finMixin :=
  Eval hnf in UniqFinMixin ord_enum_uniq mem_ord_enum.
Canonical ordinal_finType := Eval hnf in FinType ordinal ordinal_finMixin.
Canonical ordinal_subFinType := Eval hnf in [subFinType of ordinal].

End OrdinalSub.

Notation "''I_' n" := (ordinal n)
  (at level 8, n at level 2, format "''I_' n").

Hint Resolve ltn_ord.

Section OrdinalEnum.

Variable n : nat.

Lemma val_enum_ord : map val (enum 'I_n) = iota 0 n.
Proof. by rewrite enumT unlock val_ord_enum. Qed.

Lemma size_enum_ord : size (enum 'I_n) = n.
Proof. by rewrite -(size_map val) val_enum_ord size_iota. Qed.

Lemma card_ord : #|'I_n| = n.
Proof. by rewrite cardE size_enum_ord. Qed.

Lemma nth_enum_ord i0 m : m < n -> nth i0 (enum 'I_n) m = m :> nat.
Proof.
by move=> ?; rewrite -(nth_map _ 0) (size_enum_ord, val_enum_ord) // nth_iota.
Qed.

Lemma nth_ord_enum (i0 i : 'I_n) : nth i0 (enum 'I_n) i = i.
Proof. apply: val_inj; exact: nth_enum_ord. Qed.

Lemma index_enum_ord (i : 'I_n) : index i (enum 'I_n) = i.
Proof.
by rewrite -{1}(nth_ord_enum i i) index_uniq ?(enum_uniq, size_enum_ord).
Qed.

End OrdinalEnum.

Lemma widen_ord_proof n m (i : 'I_n) : n <= m -> i < m.
Proof. exact: leq_trans. Qed.
Definition widen_ord n m le_n_m i := Ordinal (@widen_ord_proof n m i le_n_m).

Lemma cast_ord_proof n m (i : 'I_n) : n = m -> i < m.
Proof. by move <-. Qed.
Definition cast_ord n m eq_n_m i := Ordinal (@cast_ord_proof n m i eq_n_m).

Lemma cast_ord_id n eq_n i : cast_ord eq_n i = i :> 'I_n.
Proof. exact: val_inj. Qed.

Lemma cast_ord_comp n1 n2 n3 eq_n2 eq_n3 i :
  @cast_ord n2 n3 eq_n3 (@cast_ord n1 n2 eq_n2 i) =
    cast_ord (etrans eq_n2 eq_n3) i.
Proof. exact: val_inj. Qed.

Lemma cast_ordK n1 n2 eq_n :
  cancel (@cast_ord n1 n2 eq_n) (cast_ord (esym eq_n)).
Proof. by move=> i; exact: val_inj. Qed.

Lemma cast_ordKV n1 n2 eq_n :
  cancel (cast_ord (esym eq_n)) (@cast_ord n1 n2 eq_n).
Proof. by move=> i; exact: val_inj. Qed.

Lemma cast_ord_inj n1 n2 eq_n : injective (@cast_ord n1 n2 eq_n).
Proof. exact: can_inj (cast_ordK eq_n). Qed.

Lemma rev_ord_proof n (i : 'I_n) : n - i.+1  < n.
Proof. by case: n i => [|n] [i lt_i_n] //; rewrite ltnS subSS leq_subr. Qed.
Definition rev_ord n i := Ordinal (@rev_ord_proof n i).

Lemma rev_ordK n : involutive (@rev_ord n).
Proof.
by case: n => [|n] [i lti] //; apply: val_inj; rewrite /= !subSS subKn.
Qed.

Lemma rev_ord_inj {n} : injective (@rev_ord n).
Proof. exact: inv_inj (@rev_ordK n). Qed.

(* bijection between any finType T and the Ordinal finType of its cardinal *)
Section EnumRank.

Variable T : finType.
Implicit Type A : pred T.

Lemma enum_rank_subproof x0 A : x0 \in A -> 0 < #|A|.
Proof. by move=> Ax0; rewrite (cardD1 x0) Ax0. Qed.

Definition enum_rank_in x0 A (Ax0 : x0 \in A) x :=
  insubd (Ordinal (@enum_rank_subproof x0 [eta A] Ax0)) (index x (enum A)).

Definition enum_rank x := @enum_rank_in x T (erefl true) x.

Lemma enum_default A : 'I_(#|A|) -> T.
Proof. by rewrite cardE; case: (enum A) => [|//] []. Qed.

Definition enum_val A i := nth (@enum_default [eta A] i) (enum A) i.
Prenex Implicits enum_val.

Lemma enum_valP A i : @enum_val A i \in A.
Proof. by rewrite -mem_enum mem_nth -?cardE. Qed.

Lemma enum_val_nth A x i : @enum_val A i = nth x (enum A) i.
Proof. by apply: set_nth_default; rewrite cardE in i *; exact: ltn_ord. Qed.

Lemma nth_image T' y0 (f : T -> T') A (i : 'I_#|A|) :
  nth y0 (image f A) i = f (enum_val i).
Proof. by rewrite -(nth_map _ y0) // -cardE. Qed.

Lemma nth_codom T' y0 (f : T -> T') (i : 'I_#|T|) :
  nth y0 (codom f) i = f (enum_val i).
Proof. exact: nth_image. Qed.

Lemma nth_enum_rank_in x00 x0 A Ax0 :
  {in A, cancel (@enum_rank_in x0 A Ax0) (nth x00 (enum A))}.
Proof.
move=> x Ax; rewrite /= insubdK ?nth_index ?mem_enum //.
by rewrite cardE [_ \in _]index_mem mem_enum.
Qed.

Lemma nth_enum_rank x0 : cancel enum_rank (nth x0 (enum T)).
Proof. by move=> x; exact: nth_enum_rank_in. Qed.

Lemma enum_rankK_in x0 A Ax0 :
   {in A, cancel (@enum_rank_in x0 A Ax0) enum_val}.
Proof. by move=> x; exact: nth_enum_rank_in. Qed.

Lemma enum_rankK : cancel enum_rank enum_val.
Proof. by move=> x; exact: enum_rankK_in. Qed.

Lemma enum_valK_in x0 A Ax0 : cancel enum_val (@enum_rank_in x0 A Ax0).
Proof.
move=> x; apply: ord_inj; rewrite insubdK; last first.
  by rewrite cardE [_ \in _]index_mem mem_nth // -cardE.
by rewrite index_uniq ?enum_uniq // -cardE.
Qed.

Lemma enum_valK : cancel enum_val enum_rank.
Proof. by move=> x; exact: enum_valK_in. Qed.

Lemma enum_rank_inj : injective enum_rank.
Proof. exact: can_inj enum_rankK. Qed.

Lemma enum_val_inj A : injective (@enum_val A).
Proof. by move=> i; exact: can_inj (enum_valK_in (enum_valP i)) (i). Qed.

Lemma enum_val_bij_in x0 A : x0 \in A -> {on A, bijective (@enum_val A)}.
Proof.
move=> Ax0; exists (enum_rank_in Ax0) => [i _|]; last exact: enum_rankK_in.
exact: enum_valK_in.
Qed.

Lemma enum_rank_bij : bijective enum_rank.
Proof. by move: enum_rankK enum_valK; exists (@enum_val T). Qed.

Lemma enum_val_bij : bijective (@enum_val T).
Proof. by move: enum_rankK enum_valK; exists enum_rank. Qed.

(* Due to the limitations of the Coq unification patterns, P can only be      *)
(* inferred from the premise of this lemma, not its conclusion. As a result   *)
(* this lemma will only be usable in forward chaining style.                  *)
Lemma fin_all_exists U (P : forall x : T, U x -> Prop) :
  (forall x, exists u, P x u) -> (exists u, forall x, P x (u x)).
Proof.
move=> ex_u; pose Q m x := enum_rank x < m -> {ux | P x ux}.
suffices: forall m, m <= #|T| -> exists w : forall x, Q m x, True.
  case/(_ #|T|)=> // w _; pose u x := sval (w x (ltn_ord _)).
  by exists u => x; rewrite {}/u; case: (w x _).
elim=> [|m IHm] ltmX; first by have w x: Q 0 x by []; exists w.
have{IHm} [w _] := IHm (ltnW ltmX); pose i := Ordinal ltmX.
have [u Pu] := ex_u (enum_val i); suffices w' x: Q m.+1 x by exists w'.
rewrite /Q ltnS leq_eqVlt (val_eqE _ i); case: eqP => [def_i _ | _ /w //].
by rewrite -def_i enum_rankK in u Pu; exists u.
Qed.

End EnumRank.

Implicit Arguments enum_val_inj [[T] [A] x1 x2].
Implicit Arguments enum_rank_inj [[T] x1 x2].
Prenex Implicits enum_val enum_rank.

Lemma enum_rank_ord n i : enum_rank i = cast_ord (esym (card_ord n)) i.
Proof.
by apply: val_inj; rewrite insubdK ?index_enum_ord // card_ord [_ \in _]ltn_ord.
Qed.

Lemma enum_val_ord n i : enum_val i = cast_ord (card_ord n) i.
Proof.
by apply: canLR (@enum_rankK _) _; apply: val_inj; rewrite enum_rank_ord.
Qed.

(* The integer bump / unbump operations. *)

Definition bump h i := (h <= i) + i.
Definition unbump h i := i - (h < i).

Lemma bumpK h : cancel (bump h) (unbump h).
Proof.
rewrite /bump /unbump => i.
have [le_hi | lt_ih] := leqP h i; first by rewrite ltnS le_hi subn1.
by rewrite ltnNge ltnW ?subn0.
Qed.

Lemma neq_bump h i : h != bump h i.
Proof.
rewrite /bump eqn_leq; have [le_hi | lt_ih] := leqP h i.
  by rewrite ltnNge le_hi andbF.
by rewrite leqNgt lt_ih.
Qed.

Lemma unbumpKcond h i : bump h (unbump h i) = (i == h) + i.
Proof.
rewrite /bump /unbump leqNgt -subSKn.
case: (ltngtP i h) => /= [-> | ltih | ->] //; last by rewrite ltnn.
by rewrite subn1 /= leqNgt !(ltn_predK ltih, ltih, add1n).
Qed.

Lemma unbumpK h : {in predC1 h, cancel (unbump h) (bump h)}.
Proof. by move=> i; move/negbTE=> neq_h_i; rewrite unbumpKcond neq_h_i. Qed.

Lemma bump_addl h i k : bump (k + h) (k + i) = k + bump h i.
Proof. by rewrite /bump leq_add2l addnCA. Qed.

Lemma bumpS h i : bump h.+1 i.+1 = (bump h i).+1.
Proof. exact: addnS. Qed.

Lemma unbump_addl h i k : unbump (k + h) (k + i) = k + unbump h i.
Proof.
apply: (can_inj (bumpK (k + h))).
by rewrite bump_addl !unbumpKcond eqn_add2l addnCA.
Qed.

Lemma unbumpS h i : unbump h.+1 i.+1 = (unbump h i).+1.
Proof. exact: unbump_addl 1. Qed.

Lemma leq_bump h i j : (i <= bump h j) = (unbump h i <= j).
Proof.
rewrite /bump leq_subLR.
case: (leqP i h) (leqP h j) => [le_i_h | lt_h_i] [le_h_j | lt_j_h] //.
  by rewrite leqW (leq_trans le_i_h).
by rewrite !(leqNgt i) ltnW (leq_trans _ lt_h_i).
Qed.

Lemma leq_bump2 h i j : (bump h i <= bump h j) = (i <= j).
Proof. by rewrite leq_bump bumpK. Qed.

Lemma bumpC h1 h2 i :
  bump h1 (bump h2 i) = bump (bump h1 h2) (bump (unbump h2 h1) i).
Proof.
rewrite {1 5}/bump -leq_bump addnCA; congr (_ + (_ + _)).
rewrite 2!leq_bump /unbump /bump; case: (leqP h1 h2) => [le_h12 | lt_h21].
  by rewrite subn0 ltnS le_h12 subn1.
by rewrite subn1 (ltn_predK lt_h21) (leqNgt h1) lt_h21 subn0.
Qed.

(* The lift operations on ordinals; to avoid a messy dependent type, *)
(* unlift is a partial operation (returns an option).                *)

Lemma lift_subproof n h (i : 'I_n.-1) : bump h i < n.
Proof. by case: n i => [[]|n] //= i; rewrite -addnS (leq_add (leq_b1 _)). Qed.

Definition lift n (h : 'I_n) (i : 'I_n.-1) := Ordinal (lift_subproof h i).

Lemma unlift_subproof n (h : 'I_n) (u : {j | j != h}) : unbump h (val u) < n.-1.
Proof.
case: n h u => [|n h] [] //= j ne_jh.
rewrite -(leq_bump2 h.+1) bumpS unbumpK // /bump.
case: (ltngtP n h) => [|_|eq_nh]; rewrite ?(leqNgt _ h) ?ltn_ord //.
by rewrite ltn_neqAle [j <= _](valP j) {2}eq_nh andbT.
Qed.

Definition unlift n (h i : 'I_n) :=
  omap (fun u : {j | j != h} => Ordinal (unlift_subproof u)) (insub i).

CoInductive unlift_spec n h i : option 'I_n.-1 -> Type :=
  | UnliftSome j of i = lift h j : unlift_spec h i (Some j)
  | UnliftNone   of i = h        : unlift_spec h i None.

Lemma unliftP n (h i : 'I_n) : unlift_spec h i (unlift h i).
Proof.
rewrite /unlift; case: insubP => [u nhi | ] def_i /=; constructor.
  by apply: val_inj; rewrite /= def_i unbumpK.
by rewrite negbK in def_i; exact/eqP.
Qed.

Lemma neq_lift n (h : 'I_n) i : h != lift h i.
Proof. exact: neq_bump. Qed.

Lemma unlift_none n (h : 'I_n) : unlift h h = None.
Proof. by case: unliftP => // j Dh; case/eqP: (neq_lift h j). Qed.

Lemma unlift_some n (h i : 'I_n) :
  h != i -> {j | i = lift h j & unlift h i = Some j}.
Proof.
rewrite eq_sym => /eqP neq_ih.
by case Dui: (unlift h i) / (unliftP h i) => [j Dh|//]; exists j.
Qed.

Lemma lift_inj n (h : 'I_n) : injective (lift h).
Proof.
move=> i1 i2; move/eqP; rewrite [_ == _](can_eq (@bumpK _)) => eq_i12.
exact/eqP.
Qed.

Lemma liftK n (h : 'I_n) : pcancel (lift h) (unlift h).
Proof.
by move=> i; case: (unlift_some (neq_lift h i)) => j; move/lift_inj->.
Qed.

(* Shifting and splitting indices, for cutting and pasting arrays *)

Lemma lshift_subproof m n (i : 'I_m) : i < m + n.
Proof. by apply: leq_trans (valP i) _; exact: leq_addr. Qed.

Lemma rshift_subproof m n (i : 'I_n) : m + i < m + n.
Proof. by rewrite ltn_add2l. Qed.

Definition lshift m n (i : 'I_m) := Ordinal (lshift_subproof n i).
Definition rshift m n (i : 'I_n) := Ordinal (rshift_subproof m i).

Lemma split_subproof m n (i : 'I_(m + n)) : i >= m -> i - m < n.
Proof. by move/subSn <-; rewrite leq_subLR. Qed.

Definition split m n (i : 'I_(m + n)) : 'I_m + 'I_n :=
  match ltnP (i) m with
  | LtnNotGeq lt_i_m =>  inl _ (Ordinal lt_i_m)
  | GeqNotLtn ge_i_m =>  inr _ (Ordinal (split_subproof ge_i_m))
  end.

CoInductive split_spec m n (i : 'I_(m + n)) : 'I_m + 'I_n -> bool -> Type :=
  | SplitLo (j : 'I_m) of i = j :> nat     : split_spec i (inl _ j) true
  | SplitHi (k : 'I_n) of i = m + k :> nat : split_spec i (inr _ k) false.

Lemma splitP m n (i : 'I_(m + n)) : split_spec i (split i) (i < m).
Proof.
rewrite /split {-3}/leq.
by case: (@ltnP i m) => cmp_i_m //=; constructor; rewrite ?subnKC.
Qed.

Definition unsplit m n (jk : 'I_m + 'I_n) :=
  match jk with inl j => lshift n j | inr k => rshift m k end.

Lemma ltn_unsplit m n (jk : 'I_m + 'I_n) : (unsplit jk < m) = jk.
Proof. by case: jk => [j|k]; rewrite /= ?ltn_ord // ltnNge leq_addr. Qed.

Lemma splitK m n : cancel (@split m n) (@unsplit m n).
Proof. by move=> i; apply: val_inj; case: splitP. Qed.

Lemma unsplitK m n : cancel (@unsplit m n) (@split m n).
Proof.
move=> jk; have:= ltn_unsplit jk.
by do [case: splitP; case: jk => //= i j] => [|/addnI] => /ord_inj->.
Qed.

Section OrdinalPos.

Variable n' : nat.
Local Notation n := n'.+1.

Definition ord0 := Ordinal (ltn0Sn n').
Definition ord_max := Ordinal (ltnSn n').

Lemma leq_ord (i : 'I_n) : i <= n'. Proof. exact: valP i. Qed.

Lemma sub_ord_proof m : n' - m < n.
Proof.  by rewrite ltnS leq_subr. Qed.
Definition sub_ord m := Ordinal (sub_ord_proof m).

Lemma sub_ordK (i : 'I_n) : n' - (n' - i) = i.
Proof. by rewrite subKn ?leq_ord. Qed.

Definition inord m : 'I_n := insubd ord0 m.

Lemma inordK m : m < n -> inord m = m :> nat.
Proof. by move=> lt_m; rewrite val_insubd lt_m. Qed.

Lemma inord_val (i : 'I_n) : inord i = i.
Proof. by rewrite /inord /insubd valK. Qed.

Lemma enum_ordS : enum 'I_n = ord0 :: map (lift ord0) (enum 'I_n').
Proof.
apply: (inj_map val_inj); rewrite val_enum_ord /= -map_comp.
by rewrite (map_comp (addn 1)) val_enum_ord -iota_addl.
Qed.

Lemma lift_max (i : 'I_n') : lift ord_max i = i :> nat.
Proof. by rewrite /= /bump leqNgt ltn_ord. Qed.

Lemma lift0 (i : 'I_n') : lift ord0 i = i.+1 :> nat. Proof. by []. Qed.

End OrdinalPos.

Implicit Arguments ord0 [[n']].
Implicit Arguments ord_max [[n']].
Implicit Arguments inord [[n']].
Implicit Arguments sub_ord [[n']].

(* Product of two fintypes which is a fintype *)
Section ProdFinType.

Variable T1 T2 : finType.

Definition prod_enum := [seq (x1, x2) | x1 <- enum T1, x2 <- enum T2].

Lemma predX_prod_enum (A1 : pred T1) (A2 : pred T2) :
  count [predX A1 & A2] prod_enum = #|A1| * #|A2|.
Proof.
rewrite !cardE -!count_filter -!enumT /prod_enum.
elim: (enum T1) => //= x1 s1 IHs; rewrite count_cat {}IHs count_map /preim /=.
by case: (x1 \in A1); rewrite ?count_pred0.
Qed.

Lemma prod_enumP : Finite.axiom prod_enum.
Proof.
by case=> x1 x2; rewrite (predX_prod_enum (pred1 x1) (pred1 x2)) !card1.
Qed.

Definition prod_finMixin := Eval hnf in FinMixin prod_enumP.
Canonical prod_finType := Eval hnf in FinType (T1 * T2) prod_finMixin.

Lemma cardX (A1 : pred T1) (A2 : pred T2) : #|[predX A1 & A2]| = #|A1| * #|A2|.
Proof. by rewrite -predX_prod_enum unlock -count_filter unlock. Qed.

Lemma card_prod : #|{: T1 * T2}| = #|T1| * #|T2|.
Proof. by rewrite -cardX; apply: eq_card; case. Qed.

Lemma eq_card_prod (A : pred (T1 * T2)) : A =i predT -> #|A| = #|T1| * #|T2|.
Proof. exact: eq_card_trans card_prod. Qed.

End ProdFinType.

Section TagFinType.

Variables (I : finType) (T_ : I -> finType).

Definition tag_enum :=
  flatten [seq [seq Tagged T_ x | x <- enumF (T_ i)] | i <- enumF I].

Lemma tag_enumP : Finite.axiom tag_enum.
Proof.
case=> i x; rewrite -(enumP i) /tag_enum -enumT.
elim: (enum I) => //= j e IHe.
rewrite count_cat count_map {}IHe; congr (_ + _).
rewrite count_filter -cardE /=; case: eqP => [-> | ne_j_i].
  by apply: (@eq_card1 _ x) => y; rewrite -topredE /= tagged_asE ?eqxx.
by apply: eq_card0 => y.
Qed.

Definition tag_finMixin := Eval hnf in FinMixin tag_enumP.
Canonical tag_finType := Eval hnf in FinType {i : I & T_ i} tag_finMixin.

Lemma card_tagged :
  #|{: {i : I & T_ i}}| = sumn (map (fun i => #|T_ i|) (enum I)).
Proof.
rewrite cardE !enumT {1}unlock size_flatten /shape -map_comp.
by congr (sumn _); apply: eq_map => i; rewrite /= size_map -enumT -cardE.
Qed.

End TagFinType.

Section SumFinType.

Variables T1 T2 : finType.

Definition sum_enum :=
  [seq inl _ x | x <- enumF T1] ++ [seq inr _ y | y <- enumF T2].

Lemma sum_enum_uniq : uniq sum_enum.
Proof.
rewrite cat_uniq -!enumT !(enum_uniq, map_inj_uniq); try by move=> ? ? [].
by rewrite andbT; apply/hasP=> [[_ /mapP[x _ ->] /mapP[]]].
Qed.

Lemma mem_sum_enum u : u \in sum_enum.
Proof. by case: u => x; rewrite mem_cat -!enumT map_f ?mem_enum ?orbT. Qed.

Definition sum_finMixin := Eval hnf in UniqFinMixin sum_enum_uniq mem_sum_enum.
Canonical sum_finType := Eval hnf in FinType (T1 + T2) sum_finMixin.

Lemma card_sum : #|{: T1 + T2}| = #|T1| + #|T2|.
Proof. by rewrite !cardT !enumT {1}unlock size_cat !size_map. Qed.


End SumFinType.
