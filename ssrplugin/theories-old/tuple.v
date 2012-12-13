(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* Tuples, i.e., sequences with a fixed (known) length. We define:            *)
(*         n.-tuple T == the type of n-tuples of elements of type T.          *)
(*       [tuple of s] == the tuple whose underlying sequence (value) is s.    *)
(*                       The size of s must be known: specifically, Coq must  *)
(*                       be able to infer a Canonical tuple projecting on s.  *)
(*         in_tuple s == the (size s)-tuple with value s.                     *)
(*            [tuple] == the empty tuple, and                                 *)
(* [tuple x1; ..; xn] == the explicit n.-tuple <x1; ..; xn>.                  *)
(*  [tuple E | i < n] == the n.-tuple with general term E (i : 'I_n is bound  *)
(*                       in E).                                               *)
(*        tcast Emn t == the m-tuple t cast as an n-tuple using Emn : m = n.  *)
(* As n.-tuple T coerces to seq t, all seq operations (size, nth, ...) can be *)
(* applied to t : n.-tuple T; we provide a few specialized instances when     *)
(* avoids the need for a default value.                                       *)
(*            tsize t == the size of t (the n in n.-tuple T)                  *)
(*           tnth t i == the i'th component of t, where i : 'I_n.             *)
(*         [tnth t i] == the i'th component of t, where i : nat and i < n     *)
(*                       is convertible to true.                              *)
(*            thead t == the first element of t, when n is m.+1 for some m.   *)
(* Most seq constructors (cons, behead, cat, rcons, belast, take, drop, rot,  *)
(* map, ...) can be used to build tuples via the [tuple of s] construct.      *)
(*   Tuples are actually a subType of seq, and inherit all combinatorial      *)
(* structures, including the finType structure.                               *)
(*   Some useful lemmas and definitions:                                      *)
(*     tuple0 : [tuple] is the only 0.-tuple                                  *)
(*     tupleP : elimination view for n.+1.-tuple                              *)
(*     ord_tuple n : the n.-tuple of all i : 'I_n                             *)
(******************************************************************************)

Section Def.

Variables (n : nat) (T : Type).

Structure tuple_of : Type := Tuple {tval :> seq T; _ : size tval == n}.

Canonical tuple_subType := Eval hnf in [subType for tval].

Implicit Type t : tuple_of.

Definition tsize of tuple_of := n.

Lemma size_tuple t : size t = n.
Proof. exact: (eqP (valP t)). Qed.

Lemma tnth_default t : 'I_n -> T.
Proof. by rewrite -(size_tuple t); case: (tval t) => [|//] []. Qed.

Definition tnth t i := nth (tnth_default t i) t i.

Lemma tnth_nth x t i : tnth t i = nth x t i.
Proof. by apply: set_nth_default; rewrite size_tuple. Qed.

Lemma map_tnth_enum t : map (tnth t) (enum 'I_n) = t.
Proof.
case def_t: {-}(val t) => [|x0 t'].
  by rewrite [enum _]size0nil // -cardE card_ord -(size_tuple t) def_t.
apply: (@eq_from_nth _ x0) => [|i]; rewrite size_map.
  by rewrite -cardE size_tuple card_ord.
move=> lt_i_e; have lt_i_n: i < n by rewrite -cardE card_ord in lt_i_e.
by rewrite (nth_map (Ordinal lt_i_n)) // (tnth_nth x0) nth_enum_ord.
Qed.

Lemma eq_from_tnth t1 t2 : tnth t1 =1 tnth t2 -> t1 = t2.
Proof.
by move/eq_map=> eq_t; apply: val_inj; rewrite /= -!map_tnth_enum eq_t.
Qed.

Definition tuple t mkT : tuple_of :=
  mkT (let: Tuple _ tP := t return size t == n in tP).

Lemma tupleE t : tuple (fun sP => @Tuple t sP) = t.
Proof. by case: t. Qed.

End Def.

Notation "n .-tuple" := (tuple_of n)
  (at level 2, format "n .-tuple") : type_scope.

Notation "{ 'tuple' n 'of' T }" := (n.-tuple T : predArgType)
  (at level 0, only parsing) : form_scope.

Notation "[ 'tuple' 'of' s ]" := (tuple (fun sP => @Tuple _ _ s sP))
  (at level 0, format "[ 'tuple'  'of'  s ]") : form_scope.

Notation "[ 'tnth' t i ]" := (tnth t (@Ordinal (tsize t) i (erefl true)))
  (at level 0, t, i at level 8, format "[ 'tnth'  t  i ]") : form_scope.

Canonical nil_tuple T := Tuple (isT : @size T [::] == 0).
Canonical cons_tuple n T x (t : n.-tuple T) :=
  Tuple (valP t : size (x :: t) == n.+1).

Notation "[ 'tuple' x1 ; .. ; xn ]" := [tuple of x1 :: .. [:: xn] ..]
  (at level 0, format "[ 'tuple' '['  x1 ; '/'  .. ; '/'  xn ']' ]")
  : form_scope.

Notation "[ 'tuple' ]" := [tuple of [::]]
  (at level 0, format "[ 'tuple' ]") : form_scope.

Section CastTuple.

Variable T : Type.

Definition in_tuple (s : seq T) := Tuple (eqxx (size s)).

Definition tcast m n (eq_mn : m = n) t :=
  let: erefl in _ = n := eq_mn return n.-tuple T in t.

Lemma tcastE m n (eq_mn : m = n) t i :
  tnth (tcast eq_mn t) i = tnth t (cast_ord (esym eq_mn) i).
Proof. by case: n / eq_mn in i *; rewrite cast_ord_id. Qed.

Lemma tcast_id n (eq_nn : n = n) t : tcast eq_nn t = t.
Proof. by rewrite (eq_axiomK eq_nn). Qed.

Lemma tcastK m n (eq_mn : m = n) : cancel (tcast eq_mn) (tcast (esym eq_mn)).
Proof. by case: n / eq_mn. Qed.

Lemma tcastKV m n (eq_mn : m = n) : cancel (tcast (esym eq_mn)) (tcast eq_mn).
Proof. by case: n / eq_mn. Qed.

Lemma tcast_trans m n p (eq_mn : m = n) (eq_np : n = p) t:
  tcast (etrans eq_mn eq_np) t = tcast eq_np (tcast eq_mn t).
Proof. by case: n / eq_mn eq_np; case: p /. Qed.

Lemma tvalK n (t : n.-tuple T) : in_tuple t = tcast (esym (size_tuple t)) t.
Proof. by apply: val_inj => /=; case: _ / (esym _). Qed.

Lemma in_tupleE s : in_tuple s = s :> seq T. Proof. by []. Qed.

End CastTuple.

Section SeqTuple.

Variables (n m : nat) (T U rT : Type).
Implicit Type t : n.-tuple T.

Lemma rcons_tupleP t x : size (rcons t x) == n.+1.
Proof. by rewrite size_rcons size_tuple. Qed.
Canonical rcons_tuple t x := Tuple (rcons_tupleP t x).

Lemma nseq_tupleP x : @size T (nseq n x) == n.
Proof. by rewrite size_nseq. Qed.
Canonical nseq_tuple x := Tuple (nseq_tupleP x).

Lemma iota_tupleP : size (iota m n) == n.
Proof. by rewrite size_iota. Qed.
Canonical iota_tuple := Tuple iota_tupleP.

Lemma behead_tupleP t : size (behead t) == n.-1.
Proof. by rewrite size_behead size_tuple. Qed.
Canonical behead_tuple t := Tuple (behead_tupleP t).

Lemma belast_tupleP x t : size (belast x t) == n.
Proof. by rewrite size_belast size_tuple. Qed.
Canonical belast_tuple x t := Tuple (belast_tupleP x t).

Lemma cat_tupleP t (u : m.-tuple T) : size (t ++ u) == n + m.
Proof. by rewrite size_cat !size_tuple. Qed.
Canonical cat_tuple t u := Tuple (cat_tupleP t u).

Lemma take_tupleP t : size (take m t) == minn m n.
Proof. by rewrite size_take size_tuple eqxx. Qed.
Canonical take_tuple t := Tuple (take_tupleP t).

Lemma drop_tupleP t : size (drop m t) == n - m.
Proof. by rewrite size_drop size_tuple. Qed.
Canonical drop_tuple t := Tuple (drop_tupleP t).

Lemma rev_tupleP t : size (rev t) == n.
Proof. by rewrite size_rev size_tuple. Qed.
Canonical rev_tuple t := Tuple (rev_tupleP t).

Lemma rot_tupleP t : size (rot m t) == n.
Proof. by rewrite size_rot size_tuple. Qed.
Canonical rot_tuple t := Tuple (rot_tupleP t).

Lemma rotr_tupleP t : size (rotr m t) == n.
Proof. by rewrite size_rotr size_tuple. Qed.
Canonical rotr_tuple t := Tuple (rotr_tupleP t).

Lemma map_tupleP f t : @size rT (map f t) == n.
Proof. by rewrite size_map size_tuple. Qed.
Canonical map_tuple f t := Tuple (map_tupleP f t).

Lemma scanl_tupleP f x t : @size rT (scanl f x t) == n.
Proof. by rewrite size_scanl size_tuple. Qed.
Canonical scanl_tuple f x t := Tuple (scanl_tupleP f x t).

Lemma pairmap_tupleP f x t : @size rT (pairmap f x t) == n.
Proof. by rewrite size_pairmap size_tuple. Qed.
Canonical pairmap_tuple f x t := Tuple (pairmap_tupleP f x t).

Lemma zip_tupleP t (u : n.-tuple U) : size (zip t u) == n.
Proof. by rewrite size1_zip !size_tuple. Qed.
Canonical zip_tuple t u := Tuple (zip_tupleP t u).

Lemma allpairs_tupleP f t (u : m.-tuple U) : @size rT (allpairs f t u) == n * m.
Proof. by rewrite size_allpairs !size_tuple. Qed.
Canonical allpairs_tuple f t u := Tuple (allpairs_tupleP f t u).

Definition thead (u : n.+1.-tuple T) := tnth u ord0.

Lemma tnth0 x t : tnth [tuple of x :: t] ord0 = x.
Proof. by []. Qed.

Lemma theadE x t : thead [tuple of x :: t] = x.
Proof. by []. Qed.

Lemma tuple0 : all_equal_to ([tuple] : 0.-tuple T).
Proof. by move=> t; apply: val_inj; case: t => [[]]. Qed.

CoInductive tuple1_spec : n.+1.-tuple T -> Type :=
  Tuple1spec x t : tuple1_spec [tuple of x :: t].

Lemma tupleP u : tuple1_spec u.
Proof.
case: u => [[|x s] //= sz_s]; pose t := @Tuple n _ s sz_s.
rewrite (_ : Tuple _ = [tuple of x :: t]) //; exact: val_inj.
Qed.

Lemma tnth_map f t i : tnth [tuple of map f t] i = f (tnth t i) :> rT.
Proof. by apply: nth_map; rewrite size_tuple. Qed.

End SeqTuple.

Lemma tnth_behead n T (t : n.+1.-tuple T) i :
  tnth [tuple of behead t] i = tnth t (inord i.+1).
Proof. by case/tupleP: t => x t; rewrite !(tnth_nth x) inordK ?ltnS. Qed.

Lemma tuple_eta n T (t : n.+1.-tuple T) : t = [tuple of thead t :: behead t].
Proof. by case/tupleP: t => x t; exact: val_inj. Qed.

Section TupleQuantifiers.

Variables (n : nat) (T : Type).
Implicit Types (a : pred T) (t : n.-tuple T).

Lemma forallb_tnth a t : [forall i, a (tnth t i)] = all a t.
Proof.
apply: negb_inj; rewrite -has_predC -has_map negb_forall.
apply/existsP/(has_nthP true) => [[i a_t_i] | [i lt_i_n a_t_i]].
  by exists i; rewrite ?size_tuple // -tnth_nth tnth_map.
rewrite size_tuple in lt_i_n; exists (Ordinal lt_i_n).
by rewrite -tnth_map (tnth_nth true).
Qed.

Lemma existsb_tnth a t : [exists i, a (tnth t i)] = has a t.
Proof. by apply: negb_inj; rewrite negb_exists -all_predC -forallb_tnth. Qed.

Lemma all_tnthP a t : reflect (forall i, a (tnth t i)) (all a t).
Proof. by rewrite -forallb_tnth; apply: forallP. Qed.

Lemma has_tnthP a t : reflect (exists i, a (tnth t i)) (has a t).
Proof. by rewrite -existsb_tnth; apply: existsP. Qed.

End TupleQuantifiers.

Implicit Arguments all_tnthP [n T a t].
Implicit Arguments has_tnthP [n T a t].

Section EqTuple.

Variables (n : nat) (T : eqType).

Definition tuple_eqMixin := Eval hnf in [eqMixin of n.-tuple T by <:].
Canonical tuple_eqType := Eval hnf in EqType (n.-tuple T) tuple_eqMixin.

Canonical tuple_predType :=
  Eval hnf in mkPredType (fun t : n.-tuple T => mem_seq t).

Lemma memtE (t : n.-tuple T) : mem t = mem (tval t).
Proof. by []. Qed.

Lemma mem_tnth i (t : n.-tuple T) : tnth t i \in t.
Proof. by rewrite mem_nth ?size_tuple. Qed.

Lemma memt_nth x0 (t : n.-tuple T) i : i < n -> nth x0 t i \in t.
Proof. by move=> i_lt_n; rewrite mem_nth ?size_tuple. Qed.

Lemma tnthP (t : n.-tuple T) x : reflect (exists i, x = tnth t i) (x \in t).
Proof.
apply: (iffP idP) => [/(nthP x)[i ltin <-] | [i ->]]; last exact: mem_tnth.
by rewrite size_tuple in ltin; exists (Ordinal ltin); rewrite (tnth_nth x).
Qed.

Lemma seq_tnthP (s : seq T) x : x \in s -> {i | x = tnth (in_tuple s) i}.
Proof.
move=> s_x; pose i := index x s; have lt_i: i < size s by rewrite index_mem.
by exists (Ordinal lt_i); rewrite (tnth_nth x) nth_index.
Qed.

End EqTuple.

Definition tuple_choiceMixin n (T : choiceType) :=
  [choiceMixin of n.-tuple T by <:].

Canonical tuple_choiceType n (T : choiceType) :=
  Eval hnf in ChoiceType (n.-tuple T) (tuple_choiceMixin n T).

Definition tuple_countMixin n (T : countType) :=
  [countMixin of n.-tuple T by <:].

Canonical tuple_countType n (T : countType) :=
  Eval hnf in CountType (n.-tuple T) (tuple_countMixin n T).

Canonical tuple_subCountType n (T : countType) :=
  Eval hnf in [subCountType of n.-tuple T].

Module Type FinTupleSig.
Section FinTupleSig.
Variables (n : nat) (T : finType).
Parameter enum : seq (n.-tuple T).
Axiom enumP : Finite.axiom enum.
Axiom size_enum : size enum = #|T| ^ n.
End FinTupleSig.
End FinTupleSig.

Module FinTuple : FinTupleSig.
Section FinTuple.
Variables (n : nat) (T : finType).

Definition enum : seq (n.-tuple T) :=
  let extend e := flatten (codom (fun x => map (cons x) e)) in
  pmap insub (iter n extend [::[::]]).

Lemma enumP : Finite.axiom enum.
Proof.
case=> /= t t_n; rewrite -(count_map val (pred1 t)).
rewrite (pmap_filter (@insubK _ _ _)) count_filter -filter_predI.
rewrite -count_filter -(@eq_count _ (pred1 t)) => [|s /=]; last first.
  by rewrite isSome_insub; case: eqP=> // ->.
elim: n t t_n => [|m IHm] [|x t] //= {IHm}/IHm; move: (iter m _ _) => em IHm.
transitivity (x \in T : nat); rewrite // -mem_enum codomE.
elim: (fintype.enum T)  (enum_uniq T) => //= y e IHe /andP[/negPf ney].
rewrite count_cat count_map inE /preim /= {1}/eq_op /= eq_sym => /IHe->.
by case: eqP => [->|_]; rewrite ?(ney, count_pred0, IHm).
Qed.

Lemma size_enum : size enum = #|T| ^ n.
Proof.
rewrite /= cardE size_pmap_sub; elim: n => //= m IHm.
rewrite expnS /codom /image_mem; elim: {2 3}(fintype.enum T) => //= x e IHe.
by rewrite count_cat {}IHe count_map IHm.
Qed.

End FinTuple.
End FinTuple.

Section UseFinTuple.

Variables (n : nat) (T : finType).

Canonical tuple_finMixin := Eval hnf in FinMixin (@FinTuple.enumP n T).
Canonical tuple_finType := Eval hnf in FinType (n.-tuple T) tuple_finMixin.
Canonical tuple_subFinType := Eval hnf in [subFinType of n.-tuple T].

Lemma card_tuple : #|{:n.-tuple T}| = #|T| ^ n.
Proof. by rewrite [#|_|]cardT enumT unlock FinTuple.size_enum. Qed.

Lemma enum_tupleP (A : pred T) : size (enum A) == #|A|.
Proof. by rewrite -cardE. Qed.
Canonical enum_tuple A := Tuple (enum_tupleP A).

Definition ord_tuple : n.-tuple 'I_n := Tuple (introT eqP (size_enum_ord n)).
Lemma val_ord_tuple : val ord_tuple = enum 'I_n. Proof. by []. Qed.

Lemma tuple_map_ord U (t : n.-tuple U) : t = [tuple of map (tnth t) ord_tuple].
Proof. by apply: val_inj => /=; rewrite map_tnth_enum. Qed.

Lemma tnth_ord_tuple i : tnth ord_tuple i = i.
Proof.
apply: val_inj; rewrite (tnth_nth i) -(nth_map _ 0) ?size_tuple //.
by rewrite /= enumT unlock val_ord_enum nth_iota.
Qed.

Section ImageTuple.

Variables (T' : Type) (f : T -> T') (A : pred T).

Canonical image_tuple : #|A|.-tuple T' := [tuple of image f A].
Canonical codom_tuple : #|T|.-tuple T' := [tuple of codom f].

End ImageTuple.

Section MkTuple.

Variables (T' : Type) (f : 'I_n -> T').

Definition mktuple := map_tuple f ord_tuple.

Lemma tnth_mktuple i : tnth mktuple i = f i.
Proof. by rewrite tnth_map tnth_ord_tuple. Qed.

Lemma nth_mktuple x0 (i : 'I_n) : nth x0 mktuple i = f i.
Proof. by rewrite -tnth_nth tnth_mktuple. Qed.

End MkTuple.

End UseFinTuple.

Notation "[ 'tuple' F | i < n ]" := (mktuple (fun i : 'I_n => F))
  (at level 0, i at level 0,
   format "[ '[hv' 'tuple'  F '/'   |  i  <  n ] ']'") : form_scope.


