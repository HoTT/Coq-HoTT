(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*   choiceType == interface for types with a choice operator                 *)
(*    countType == interface for countable types                              *)
(* subCountType == interface for types that are both subType and countType.   *)
(*  xchoose exP == a standard x such that P x, given exP : exists x : T, P x  *)
(*                 when T is a choiceType. The choice depends only on the     *)
(*                 extent of P (in particular, it is independent of exP).     *)
(*   choose P x0 == if P x0, a standard x such that P x.                      *)
(*      pickle x == a nat encoding the value x : T, where T is a countType.   *)
(*    unpickle n == a partial inverse to pickle: unpickle (pickle x) = Some x *)
(*  pickle_inv n == a sharp partial inverse to pickle pickle_inv n = Some x   *)
(*                  if and only if pickle x = n.                              *)
(* [choiceType of T for cT] == clone for T of the choiceType cT.              *)
(*        [choiceType of T] == clone for T of the choiceType inferred for T.  *)
(*  [countType of T for cT] == clone for T of the countType cT.               *)
(*        [count Type of T] == clone for T of the countType inferred for T.   *)
(* [choiceMixin of T by <:] == Choice mixin for T when T has a subType p      *)
(*                        structure with p : pred cT and cT has a Choice      *)
(*                        structure; the corresponding structure is Canonical.*)
(*  [countMixin of T by <:] == Count mixin for a subType T of a countType.    *)
(*  PcanChoiceMixin fK == Choice mixin for T, given f : T -> cT where cT has  *)
(*                        a Choice structure, a left inverse partial function *)
(*                        g and fK : pcancel f g.                             *)
(*   CanChoiceMixin fK == Choice mixin for T, given f : T -> cT, g and        *)
(*                        fK : cancel f g.                                    *)
(*   PcanCountMixin fK == Count mixin for T, given f : T -> cT where cT has   *)
(*                        a Countable structure, a left inverse partial       *)
(*                        function g and fK : pcancel f g.                    *)
(*    CanCountMixin fK == Count mixin for T, given f : T -> cT, g and         *)
(*                        fK : cancel f g.                                    *)
(*      GenTree.tree T == generic n-ary tree type with nat-labeled nodes and  *)
(*                        T-labeled nodes. It is equipped with canonical      *)
(*                        eqType, choiceType, and countType instances, and so *)
(*                        can be used to similarly equip simple datatypes     *)
(*                        by using the mixins above.                          *)
(* In addition to the lemmas relevant to these definitions, this file also    *)
(* contains definitions of a Canonical choiceType and countType instances for *)
(* all basic datatypes (e.g., nat, bool, subTypes, pairs, sums, etc.).        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Technical definitions about coding and decoding of nat sequances, which    *)
(* are used below to define various Canonical instances of the choice and     *)
(* countable interfaces.                                                      *)

Module CodeSeq.

(* Goedel-style one-to-one encoding of seq nat into nat.                      *)
(* The code for [:: n1; ...; nk] has binary representation                    *)
(*          1 0 ... 0 1 ... 1 0 ... 0 1 0 ... 0                               *)
(*            <----->         <----->   <----->                               *)
(*             nk 0s           n2 0s     n1 0s                                *)

Definition code := foldr (fun n m => 2 ^ n * m.*2.+1) 0.

Fixpoint decode_rec (v q r : nat) {struct q} :=
  match q, r with
  | 0, _         => [:: v]
  | q'.+1, 0     => v :: [rec 0, q', q']
  | q'.+1, 1     => [rec v.+1, q', q']
  | q'.+1, r'.+2 => [rec v, q', r']
  end where "[ 'rec' v , q , r ]" := (decode_rec v q r).

Definition decode n := if n is 0 then [::] else [rec 0, n.-1, n.-1].

Lemma decodeK : cancel decode code.
Proof.
have m2s: forall n, n.*2 - n = n by move=> n; rewrite -addnn addnK.
case=> //= n; rewrite -[n.+1]mul1n -(expn0 2) -{3}[n]m2s.
elim: n {2 4}n {1 3}0 => [|q IHq] [|[|r]] v //=; rewrite {}IHq ?mul1n ?m2s //.
by rewrite expnSr -mulnA mul2n.
Qed.

Lemma codeK : cancel code decode.
Proof.
elim=> //= v s IHs; rewrite -[_ * _]prednK ?muln_gt0 ?expn_gt0 //=.
rewrite -{3}[v]addn0; elim: v {1 4}0 => [|v IHv {IHs}] q.
  rewrite mul1n /= -{1}addnn -{4}IHs; move: (_ s) {IHs} => n.
  by elim: {1 3}n => //=; case: n.
rewrite expnS -mulnA mul2n -{1}addnn -[_ * _]prednK ?muln_gt0 ?expn_gt0 //.
by rewrite doubleS addSn /= addSnnS; elim: {-2}_.-1 => //=.
Qed.

Lemma ltn_code s : all (fun j => j < code s) s.
Proof.
elim: s => //= i s IHs; rewrite -[_.+1]muln1 leq_mul 1?ltn_expl //=.
apply: sub_all IHs => j /leqW lejs; rewrite -[j.+1]mul1n leq_mul ?expn_gt0 //.
by rewrite ltnS -[j]mul1n -mul2n leq_mul.
Qed.

Lemma gtn_decode n : all (ltn^~ n) (decode n).
Proof. by rewrite -{1}[n]decodeK ltn_code. Qed.

End CodeSeq.

Section OtherEncodings.
(* Miscellaneous encodings: option T -c-> seq T, T1 * T2 -c-> {i : T1 & T2}   *)
(* T1 + T2 -c-> option T1 * option T2, unit -c-> bool; bool -c-> nat is       *)
(* already covered in ssrnat by the nat_of_bool coercion, the odd predicate,  *)
(* and their "cancellation" lemma oddb. We use these encodings to propagate   *)
(* canonical structures through these type constructors so that ultimately    *)
(* all Choice and Countable instanced derive from nat and the seq and sigT    *)
(* constructors.                                                              *)

Variables T T1 T2 : Type.

Definition seq_of_opt := @oapp T _ (nseq 1) [::].
Lemma seq_of_optK : cancel seq_of_opt ohead. Proof. by case. Qed.

Definition tag_of_pair (p : T1 * T2) := @Tagged T1 p.1 (fun _ => T2) p.2.
Definition pair_of_tag (u : {i : T1 & T2}) := (tag u, tagged u).
Lemma tag_of_pairK : cancel tag_of_pair pair_of_tag. Proof. by case. Qed.
Lemma pair_of_tagK : cancel pair_of_tag tag_of_pair. Proof. by case. Qed.

Definition opair_of_sum (s : T1 + T2) :=
  match s with inl x => (Some x, None) | inr y => (None, Some y) end.
Definition sum_of_opair p :=
  oapp (some \o @inr T1 T2) (omap (@inl _ T2) p.1) p.2.
Lemma opair_of_sumK : pcancel opair_of_sum sum_of_opair. Proof. by case. Qed.

Lemma bool_of_unitK : cancel (fun _ => true) (fun _ => tt).
Proof. by case. Qed.

End OtherEncodings.

(* Generic variable-arity tree type, providing an encoding target for         *)
(* miscellaneous user datatypes. The GenTree.tree type can be combined with   *)
(* a sigT type to model multi-sorted concrete datatypes.                      *)
Module GenTree.

Section Def.

Variable T : Type.

Unset Elimination Schemes.
Inductive tree := Leaf of T | Node of nat & seq tree.

Definition tree_rect K IH_leaf IH_node :=
  fix loop t : K t := match t with
  | Leaf x => IH_leaf x
  | Node n f0 =>
    let fix iter_pair f : foldr (fun t => prod (K t)) unit f :=
      if f is t :: f' then (loop t, iter_pair f') else tt in
    IH_node n f0 (iter_pair f0)
  end.
Definition tree_rec (K : tree -> Set) := @tree_rect K.
Definition tree_ind K IH_leaf IH_node :=
  fix loop t : K t : Type := match t with
  | Leaf x => IH_leaf x
  | Node n f0 =>
    let fix iter_conj f : foldr (fun t => and (K t)) True f :=
        if f is t :: f' then conj (loop t) (iter_conj f') else Logic.I
      in IH_node n f0 (iter_conj f0)
    end.

Fixpoint encode t : seq (nat + T) :=
  match t with
  | Leaf x => [:: inr _ x]
  | Node n f => inl _ n.+1 :: rcons (flatten (map encode f)) (inl _ 0)
  end.

Definition decode_step c fs := 
  match c with
  | inr x => (Leaf x :: fs.1, fs.2)
  | inl 0 => ([::], fs.1 :: fs.2)
  | inl n.+1 => (Node n fs.1 :: head [::] fs.2, behead fs.2)
  end.

Definition decode c := ohead (foldr decode_step ([::], [::]) c).1.

Lemma codeK : pcancel encode decode.
Proof.
move=> t; rewrite /decode; set fs := (_, _).
suffices ->: foldr decode_step fs (encode t) = (t :: fs.1, fs.2) by [].
elim: t => //= n f IHt in (fs) *; elim: f IHt => //= t f IHf [].
by rewrite rcons_cat foldr_cat => -> /= /IHf[-> -> ->].
Qed.

End Def.

End GenTree.
Implicit Arguments GenTree.codeK [].

Definition tree_eqMixin (T : eqType) := PcanEqMixin (GenTree.codeK T).
Canonical tree_eqType (T : eqType) := EqType (GenTree.tree T) (tree_eqMixin T).

(* Structures for Types with a choice function, and for Types with countably  *)
(* many elements. The two concepts are closely linked: we indeed make         *)
(* Countable a subclass of Choice, as countable choice is valid in CiC. This  *)
(* apparent redundancy is needed to ensure the consistency of the Canonical   *)
(* inference, as the canonical Choice for a given type may differ from the    *)
(* countable choice for its canonical Countable structure, e.g., for options. *)
(*   The Choice interface exposes two choice functions; for T : choiceType    *)
(* and P : pred T, we provide:                                                *)
(*    xchoose : (exists x, P x) -> T                                          *)
(*    choose : pred T -> T -> T                                               *)
(*   While P (xchoose exP) will always hold, P (choose P x0) will be true if  *)
(* and only if P x0 holds. Both xchoose and choose are extensional in P and   *)
(* do not depend on the witness exP or x0 (provided P x0 holds). Note that    *)
(* xchoose is slightly more powerful, but less convenient to use.             *)
(*   Howver, neither choose nor xchoose are composable: it would not be       *)
(* be possible to extend the Choice structure to arbitrary pairs using only   *)
(* these functions, for instance. Internally, the interfaces provides a       *)
(* subtly stronger operation, Choice.InternalTheory.find, which performs a    *)
(* limited search using an integer parameter only rather than a full value as *)
(* [x]choose does. This is neither a restriction in the constructive setting  *)
(* (where all types are concrete and hence countable), nor in an axiomatic    *)
(* such as the Coq reals library, where the axiom of choice and excluded      *)
(* middle suppress the need for guidance. Nevertheless this operation is just *)
(* what is needed to make the Choice interface compose.                       *)
(*   The Countable interface provides three functions; for T : countType we   *)
(* geth pickle : T -> nat, and unpickle, pickle_inv : nat -> option T.        *)
(* The functions provide an effective embedding of T in nat: unpickle is a    *)
(* left inverse to pickle, which satisfies pcancel pickle unpickle, i.e.,     *)
(* unpickle \o pickle =1 some; pickle_inv is a more precise inverse for which *)
(* we also have ocancel pickle_inv pickle. Both unpickle and pickle need to   *)
(* partial functions, to allow for possibly empty types such as {x | P x}.    *)
(*   The names of these functions underline the correspondence with the       *)
(* notion of "Serializable" types in programming languages.                   *)
(*   Finally, we need to provide a join class to let type inference unify     *)
(* subType and countType class constraints, e.g., for a countable subType of  *)
(* an uncountable choiceType (the issue does not arise earlier with eqType or *)
(* choiceType because in practice the base type of an Equality/Choice subType *)
(* is always an Equality/Choice Type).                                        *)

Module Choice.

Section ClassDef.

Record mixin_of T := Mixin {
  find : pred T -> nat -> option T;
  _ : forall P n x, find P n = Some x -> P x;
  _ : forall P : pred T, (exists x, P x) -> exists n, find P n;
  _ : forall P Q : pred T, P =1 Q -> find P =1 find Q
}.

Record class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Equality.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m) T.

(* Inheritance *)
Definition eqType := @Equality.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Equality.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Notation choiceType := type.
Notation choiceMixin := mixin_of.
Notation ChoiceType T m := (@pack T m _ _ id).
Notation "[ 'choiceType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'choiceType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'choiceType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'choiceType'  'of'  T ]") : form_scope.

End Exports.

Module InternalTheory.
Section InternalTheory.
(* Inner choice function. *)
Definition find T := find (mixin (class T)).

Variable T : choiceType.
Implicit Types P Q : pred T.

Lemma correct P n x : find P n = Some x -> P x.
Proof. by case: T => _ [_ []] //= in P n x *. Qed.

Lemma complete P : (exists x, P x) -> (exists n, find P n).
Proof. by case: T => _ [_ []] //= in P *. Qed.

Lemma extensional P Q : P =1 Q -> find P =1 find Q.
Proof. by case: T => _ [_ []] //= in P Q *. Qed.

Fact xchoose_subproof P exP : {x | find P (ex_minn (@complete P exP)) = Some x}.
Proof.
by case: (ex_minnP (complete exP)) => n; case: (find P n) => // x; exists x.
Qed.

End InternalTheory.
End InternalTheory.

End Choice.
Export Choice.Exports.

Section ChoiceTheory.

Implicit Type T : choiceType.
Import Choice.InternalTheory CodeSeq.
Local Notation dc := decode.

Section OneType.

Variable T : choiceType.
Implicit Types P Q : pred T.

Definition xchoose P exP := sval (@xchoose_subproof T P exP).

Lemma xchooseP P exP : P (@xchoose P exP).
Proof. by rewrite /xchoose; case: (xchoose_subproof exP) => x /= /correct. Qed.

Lemma eq_xchoose P Q exP exQ : P =1 Q -> @xchoose P exP = @xchoose Q exQ.
Proof.
rewrite /xchoose => eqPQ.
case: (xchoose_subproof exP) => x; case: (xchoose_subproof exQ) => y /=.
case: ex_minnP => n; case: ex_minnP => m.
rewrite -(extensional eqPQ) {1}(extensional eqPQ).
move=> Qm minPm Pn minQn; suffices /eqP->: m == n by move=> -> [].
by rewrite eqn_leq minQn ?minPm.
Qed.

Lemma sigW P : (exists x, P x) -> {x | P x}.
Proof. by move=> exP; exists (xchoose exP); exact: xchooseP. Qed.

Lemma sig2W P Q : (exists2 x, P x & Q x) -> {x | P x & Q x}.
Proof.
move=> exPQ; have [|x /andP[]] := @sigW (predI P Q); last by exists x.
by have [x Px Qx] := exPQ; exists x; exact/andP.
Qed.

Lemma sig_eqW (vT : eqType) (lhs rhs : T -> vT) :
  (exists x, lhs x = rhs x) -> {x | lhs x = rhs x}.
Proof.
move=> exP; suffices [x /eqP Ex]: {x | lhs x == rhs x} by exists x.
by apply: sigW; have [x /eqP Ex] := exP; exists x.
Qed.

Lemma sig2_eqW (vT : eqType) (P : pred T) (lhs rhs : T -> vT) :
  (exists2 x, P x & lhs x = rhs x) -> {x | P x & lhs x = rhs x}.
Proof.
move=> exP; suffices [x Px /eqP Ex]: {x | P x & lhs x == rhs x} by exists x.
by apply: sig2W; have [x Px /eqP Ex] := exP; exists x.
Qed.

Definition choose P x0 :=
  if insub x0 : {? x | P x} is Some (exist x Px) then
    xchoose (ex_intro [eta P] x Px)
  else x0.

(* assia : since we moved from Prop to Type, the hole for Px0 does not trigger the
  creation of a nuw subgoal and should be provided by hand. *)
Lemma chooseP P x0 : P x0 -> P (choose P x0).
Proof. by move=> Px0; rewrite /choose (insubT _ Px0) xchooseP. Qed.
(*Proof. by move=> Px0; rewrite /choose insubT xchooseP. Qed.*)

(* assia : same problem here *)
Lemma choose_id P x0 y0 : P x0 -> P y0 -> choose P x0 = choose P y0.
Proof.
(* move=> Px0 Py0; rewrite /choose !insubT /= exact: eq_xchoose. *)
move=> Px0 Py0; rewrite /choose (insubT _ Px0) (insubT _ Py0) /=. 
exact: eq_xchoose. 
Qed.

(* assia : same problem here *)
Lemma eq_choose P Q : P =1 Q -> choose P =1 choose Q.
Proof.
rewrite /choose => eqPQ x0.
do [case: insubP; rewrite eqPQ] => [[x Px] Qx0 _| ?]; last by rewrite insubN.
by rewrite (insubT _ Qx0); exact: eq_xchoose.
(* by rewrite insubT; exact: eq_xchoose.*)
Qed.

Section CanChoice.

Variables (sT : Type) (f : sT -> T).

Lemma PcanChoiceMixin f' : pcancel f f' -> choiceMixin sT.
Proof.
move=> fK; pose liftP sP := [pred x | oapp sP false (f' x)].
pose sf sP := [fun n => obind f' (find (liftP sP) n)].
exists sf => [sP n x | sP [y sPy] | sP sQ eqPQ n] /=.
- by case Df: (find _ n) => //= [?] Dx; have:= correct Df; rewrite /= Dx.
- have [|n Pn] := @complete T (liftP sP); first by exists (f y); rewrite /= fK.
  exists n; case Df: (find _ n) Pn => //= [x] _.
  by have:= correct Df => /=; case: (f' x).
by congr (obind _ _); apply: extensional => x /=; case: (f' x) => /=.
Qed.

Definition CanChoiceMixin f' (fK : cancel f f') :=
  PcanChoiceMixin (can_pcan fK).

End CanChoice.

Section SubChoice.

Variables (P : pred T) (sT : subType P).

Definition sub_choiceMixin := PcanChoiceMixin (@valK T P sT).
Definition sub_choiceClass := @Choice.Class sT (sub_eqMixin sT) sub_choiceMixin.
Canonical sub_choiceType := Choice.Pack sub_choiceClass sT.

End SubChoice.

Fact seq_choiceMixin : choiceMixin (seq T).
Proof.
pose r f := [fun xs => fun x : T => f (x :: xs) : option (seq T)].
pose fix f sP ns xs {struct ns} :=
  if ns is n :: ns1 then let fr := r (f sP ns1) xs in obind fr (find fr n)
  else if sP xs then Some xs else None.
exists (fun sP nn => f sP (dc nn) nil) => [sP n ys | sP [ys] | sP sQ eqPQ n].
- elim: {n}(dc n) nil => [|n ns IHs] xs /=; first by case: ifP => // sPxs [<-].
  by case: (find _ n) => //= [x]; apply: IHs.
- rewrite -(cats0 ys); elim/last_ind: ys nil => [|ys y IHs] xs /=.
    by move=> sPxs; exists 0; rewrite /= sPxs.
  rewrite cat_rcons => /IHs[n1 sPn1] {IHs}.
  have /complete[n]: exists z, f sP (dc n1) (z :: xs) by exists y.
  case Df: (find _ n)=> // [x] _; exists (code (n :: dc n1)).
  by rewrite codeK /= Df /= (correct Df).
elim: {n}(dc n) nil => [|n ns IHs] xs /=; first by rewrite eqPQ.
rewrite (@extensional _ _ (r (f sQ ns) xs)) => [|x]; last by rewrite IHs.
by case: find => /=.
Qed.
Canonical seq_choiceType := Eval hnf in ChoiceType (seq T) seq_choiceMixin.

End OneType.

Section TagChoice.

Variables (I : choiceType) (T_ : I -> choiceType).

Fact tagged_choiceMixin : choiceMixin {i : I & T_ i}.
Proof.
pose mkT i (x : T_ i) := Tagged T_ x.
pose ft tP n i := omap (mkT i) (find (tP \o mkT i) n).
pose fi tP ni nt := obind (ft tP nt) (find (ft tP nt) ni).
pose f tP n := if dc n is [:: ni; nt] then fi tP ni nt else None.
exists f => [tP n u | tP [[i x] tPxi] | sP sQ eqPQ n].
- rewrite /f /fi; case: (dc n) => [|ni [|nt []]] //=.
  case: (find _ _) => //= [i]; rewrite /ft.
  by case Df: (find _ _) => //= [x] [<-]; have:= correct Df.
- have /complete[nt tPnt]: exists y, (tP \o mkT i) y by exists x.
  have{tPnt}: exists j, ft tP nt j by exists i; rewrite /ft; case: find tPnt.
  case/complete=> ni tPn; exists (code [:: ni; nt]); rewrite /f codeK /fi.
  by case Df: find tPn => //= [j] _; have:= correct Df.
rewrite /f /fi; case: (dc n) => [|ni [|nt []]] //=.
rewrite (@extensional _ _ (ft sQ nt)) => [|i].
  by case: find => //= i; congr (omap _ _); apply: extensional => x /=.
by congr (omap _ _); apply: extensional => x /=.
Qed.
Canonical tagged_choiceType :=
  Eval hnf in ChoiceType {i : I & T_ i} tagged_choiceMixin.

End TagChoice.

Fact nat_choiceMixin : choiceMixin nat.
Proof.
pose f := [fun (P : pred nat) n => if P n then Some n else None].
exists f => [P n m | P [n Pn] | P Q eqPQ n] /=; last by rewrite eqPQ.
  by case: ifP => // Pn [<-].
by exists n; rewrite Pn.
Qed.
Canonical nat_choiceType := Eval hnf in ChoiceType nat nat_choiceMixin.

Definition bool_choiceMixin := CanChoiceMixin oddb.
Canonical bool_choiceType := Eval hnf in ChoiceType bool bool_choiceMixin.
Canonical bitseq_choiceType := Eval hnf in [choiceType of bitseq].

Definition unit_choiceMixin := CanChoiceMixin bool_of_unitK.
Canonical unit_choiceType := Eval hnf in ChoiceType unit unit_choiceMixin.

Definition option_choiceMixin T := CanChoiceMixin (@seq_of_optK T).
Canonical option_choiceType T :=
  Eval hnf in ChoiceType (option T) (option_choiceMixin T).

(* assia : no more sigs *)
(* Definition sig_choiceMixin T (P : pred T) : choiceMixin {x | P x} := *)
(*    sub_choiceMixin _. *)
(* Canonical sig_choiceType T (P : pred T) := *)
(*  Eval hnf in ChoiceType {x | P x} (sig_choiceMixin P). *)

Definition prod_choiceMixin T1 T2 := CanChoiceMixin (@tag_of_pairK T1 T2).
Canonical prod_choiceType T1 T2 :=
  Eval hnf in ChoiceType (T1 * T2) (prod_choiceMixin T1 T2).

Definition sum_choiceMixin T1 T2 := PcanChoiceMixin (@opair_of_sumK T1 T2).
Canonical sum_choiceType T1 T2 :=
  Eval hnf in ChoiceType (T1 + T2) (sum_choiceMixin T1 T2).

Definition tree_choiceMixin T := PcanChoiceMixin (GenTree.codeK T).
Canonical tree_choiceType T := ChoiceType (GenTree.tree T) (tree_choiceMixin T).

End ChoiceTheory.

Prenex Implicits xchoose choose.
Notation "[ 'choiceMixin' 'of' T 'by' <: ]" :=
  (sub_choiceMixin _ : choiceMixin T)
  (at level 0, format "[ 'choiceMixin'  'of'  T  'by'  <: ]") : form_scope.

Module Countable.

Record mixin_of (T : Type) : Type := Mixin {
  pickle : T -> nat;
  unpickle : nat -> option T;
  pickleK : pcancel pickle unpickle
}.

Definition EqMixin T m := PcanEqMixin (@pickleK T m).
Definition ChoiceMixin T m := PcanChoiceMixin (@pickleK T m).

Section ClassDef.

Record class_of T := Class { base : Choice.class_of T; mixin : mixin_of T }.
Local Coercion base : class_of >-> Choice.class_of.

Structure type : Type := Pack {sort : Type; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation countType := type.
Notation CountType T m := (@pack T m _ _ id).
Notation CountMixin := Mixin.
Notation CountChoiceMixin := ChoiceMixin.
Notation "[ 'countType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
 (at level 0, format "[ 'countType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'countType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'countType'  'of'  T ]") : form_scope.

End Exports.

End Countable.
Export Countable.Exports.

Definition unpickle T := Countable.unpickle (Countable.class T).
Definition pickle T := Countable.pickle (Countable.class T).
Implicit Arguments unpickle [T].
Prenex Implicits pickle unpickle.

Section CountableTheory.

Variable T : countType.

Lemma pickleK : @pcancel nat T pickle unpickle.
Proof. exact: Countable.pickleK. Qed.

Definition pickle_inv n :=
  obind (fun x : T => if pickle x == n then Some x else None) (unpickle n).

Lemma pickle_invK : ocancel pickle_inv pickle.
Proof.
by rewrite /pickle_inv => n; case def_x: (unpickle n) => //= [x]; case: eqP.
Qed.

Lemma pickleK_inv : pcancel pickle pickle_inv.
Proof. by rewrite /pickle_inv => x; rewrite pickleK /= eqxx. Qed.

Lemma pcan_pickleK sT f f' :
  @pcancel T sT f f' -> pcancel (pickle \o f) (pcomp f' unpickle).
Proof. by move=> fK x; rewrite /pcomp pickleK /= fK. Qed.

Definition PcanCountMixin sT f f' (fK : pcancel f f') :=
  @CountMixin sT _ _ (pcan_pickleK fK).

Definition CanCountMixin sT f f' (fK : cancel f f') :=
  @PcanCountMixin sT _ _ (can_pcan fK).

Definition sub_countMixin P sT := PcanCountMixin (@valK T P sT).

Definition pickle_seq s := CodeSeq.code (map (@pickle T) s).
Definition unpickle_seq n := Some (pmap (@unpickle T) (CodeSeq.decode n)).
Lemma pickle_seqK : pcancel pickle_seq unpickle_seq.
Proof. by move=> s; rewrite /unpickle_seq CodeSeq.codeK (map_pK pickleK). Qed.

Definition seq_countMixin := CountMixin pickle_seqK.
Canonical seq_countType := Eval hnf in CountType (seq T) seq_countMixin.

End CountableTheory.

Notation "[ 'countMixin' 'of' T 'by' <: ]" :=
    (sub_countMixin _ : Countable.mixin_of T)
  (at level 0, format "[ 'countMixin'  'of'  T  'by'  <: ]") : form_scope.

Section SubCountType.

Variables (T : choiceType) (P : pred T).
Import Countable.

Structure subCountType : Type :=
  SubCountType {subCount_sort :> subType P; _ : mixin_of subCount_sort}.

Coercion sub_countType (sT : subCountType) :=
  Eval hnf in pack (let: SubCountType _ m := sT return mixin_of sT in m) id.
Canonical sub_countType.

Definition pack_subCountType U :=
  fun sT cT & sub_sort sT * sort cT -> U * U =>
  fun b m   & phant_id (Class b m) (class cT) => @SubCountType sT m.

End SubCountType.

(* This assumes that T has both countType and subType structures. *)
Notation "[ 'subCountType' 'of' T ]" :=
    (@pack_subCountType _ _ T _ _ id _ _ id)
  (at level 0, format "[ 'subCountType'  'of'  T ]") : form_scope.

Section TagCountType.

Variables (I : countType) (T_ : I -> countType).

Definition pickle_tagged (u : {i : I & T_ i}) :=
  CodeSeq.code [:: pickle (tag u); pickle (tagged u)].
Definition unpickle_tagged s :=
  if CodeSeq.decode s is [:: ni; nx] then
    obind (fun i => omap (@Tagged I i T_) (unpickle nx)) (unpickle ni)
  else None.
Lemma pickle_taggedK : pcancel pickle_tagged unpickle_tagged.
Proof.
by case=> i x; rewrite /unpickle_tagged CodeSeq.codeK /= pickleK /= pickleK.
Qed.

Definition tag_countMixin := CountMixin pickle_taggedK.
Canonical tag_countType := Eval hnf in CountType {i : I & T_ i} tag_countMixin.

End TagCountType.

(* The remaining Canonicals for standard datatypes. *)
Section CountableDataTypes.

Implicit Type T : countType.

Lemma nat_pickleK : pcancel id (@Some nat). Proof. by []. Qed.
Definition nat_countMixin := CountMixin nat_pickleK.
Canonical nat_countType := Eval hnf in CountType nat nat_countMixin.

Definition bool_countMixin := CanCountMixin oddb.
Canonical bool_countType := Eval hnf in CountType bool bool_countMixin.
Canonical bitseq_countType :=  Eval hnf in [countType of bitseq].

Definition unit_countMixin := CanCountMixin bool_of_unitK.
Canonical unit_countType := Eval hnf in CountType unit unit_countMixin.

Definition option_countMixin T := CanCountMixin (@seq_of_optK T).
Canonical option_countType T :=
  Eval hnf in CountType (option T) (option_countMixin T).

(* assia : no more sigs *)
(* Definition sig_countMixin T (P : pred T) := [countMixin of {x | P x} by <:]. *)
(* Canonical sig_countType T (P : pred T) := *)
(*   Eval hnf in CountType {x | P x} (sig_countMixin P). *)
(* Canonical sig_subCountType T (P : pred T) := *)
(*   Eval hnf in [subCountType of {x | P x}]. *)

Definition prod_countMixin T1 T2 := CanCountMixin (@tag_of_pairK T1 T2).
Canonical prod_countType T1 T2 :=
  Eval hnf in CountType (T1 * T2) (prod_countMixin T1 T2).

Definition sum_countMixin T1 T2 := PcanCountMixin (@opair_of_sumK T1 T2).
Canonical sum_countType T1 T2 :=
  Eval hnf in CountType (T1 + T2) (sum_countMixin T1 T2).

Definition tree_countMixin T := PcanCountMixin (GenTree.codeK T).
Canonical tree_countType T := CountType (GenTree.tree T) (tree_countMixin T).

End CountableDataTypes.
