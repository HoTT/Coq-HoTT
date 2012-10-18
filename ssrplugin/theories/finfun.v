(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.

(******************************************************************************)
(* This file implements a type for functions with a finite domain:            *)
(*    {ffun aT -> rT} where aT should have a finType structure.               *)
(* Any eqType, choiceType, countType and finType structures on rT extend to   *)
(* {ffun aT -> rT} as Leibnitz equality and extensional equalities coincide.  *)
(*     (T ^ n)%type is notation for {ffun 'I_n -> T}, which is isomorphic     *)
(*                     ot n.-tuple T.                                         *)
(*  For f : {ffun aT -> rT}, we define                                        *)
(*              f x == the image of x under f (f coerces to a CiC function)   *)
(*         fgraph f == the graph of f, i.e., the #|aT|.-tuple rT of the       *)
(*                     values of f over enum aT.                              *)
(*       finfun lam == the f such that f =1 lam; this is the RECOMMENDED      *)
(*                     interface to build an element of {ffun aT -> rT}.      *)
(* [ffun x => expr] == finfun (fun x => expr)                                 *)
(*   [ffun => expr] == finfun (fun _ => expr)                                 *)
(*  f \in ffun_on R == the range of f is a subset of R                        *)
(*   f \in family F == f belongs to the family F (f x \in F x for all x)      *)
(*     y.-support f == the y-support of f, i.e., [pred x | f x != y].         *)
(*                     Thus, y.-support f \subset D means f has y-support D.  *)
(*                     We will put Notation support := 0.-support in ssralg.  *)
(* f \in pffun_on y D R == f is a y-partial function from D to R:             *)
(*                     f has y-support D and f x \in R for all x \in D.       *)
(*  f \in pfamily y D F == f belongs to the y-partial family from D to F:     *)
(*                     f has y-support D and f x \in F x for all x \in D.     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Def.

Variables (aT : finType) (rT : Type).

Inductive finfun_type : predArgType := Finfun of #|aT|.-tuple rT.

Definition finfun_of of phant (aT -> rT) := finfun_type.

Identity Coercion type_of_finfun : finfun_of >-> finfun_type.

Definition fgraph f := let: Finfun t := f in t.

Canonical finfun_subType := Eval hnf in [newType for fgraph].

End Def.

Notation "{ 'ffun' fT }" := (finfun_of (Phant fT))
  (at level 0, format "{ 'ffun'  '[hv' fT ']' }") : type_scope.
Definition finexp_domFinType n := ordinal_finType n.
Notation "T ^ n" := (@finfun_of (finexp_domFinType n) T (Phant _)) : type_scope.

Notation Local fun_of_fin_def :=
  (fun aT rT f x => tnth (@fgraph aT rT f) (enum_rank x)).

Notation Local finfun_def := (fun aT rT f => @Finfun aT rT (codom_tuple f)).

Module Type FunFinfunSig.
Parameter fun_of_fin : forall aT rT, finfun_type aT rT -> aT -> rT.
Parameter finfun : forall (aT : finType) rT, (aT -> rT) -> {ffun aT -> rT}.
Axiom fun_of_finE : fun_of_fin = fun_of_fin_def.
Axiom finfunE : finfun = finfun_def.
End FunFinfunSig.

Module FunFinfun : FunFinfunSig.
Definition fun_of_fin := fun_of_fin_def.
Definition finfun := finfun_def.
Lemma fun_of_finE : fun_of_fin = fun_of_fin_def. Proof. by []. Qed.
Lemma finfunE : finfun = finfun_def. Proof. by []. Qed.
End FunFinfun.

Notation fun_of_fin := FunFinfun.fun_of_fin.
Notation finfun := FunFinfun.finfun.
Coercion fun_of_fin : finfun_type >-> Funclass.
Canonical fun_of_fin_unlock := Unlockable FunFinfun.fun_of_finE.
Canonical finfun_unlock := Unlockable FunFinfun.finfunE.

Notation "[ 'ffun' x : aT => F ]" := (finfun (fun x : aT => F))
  (at level 0, x ident, only parsing) : fun_scope.

Notation "[ 'ffun' : aT => F ]" := (finfun (fun _ : aT => F))
  (at level 0, only parsing) : fun_scope.

Notation "[ 'ffun' x => F ]" := [ffun x : _ => F]
  (at level 0, x ident, format "[ 'ffun'  x  =>  F ]") : fun_scope.

Notation "[ 'ffun' => F ]" := [ffun : _ => F]
  (at level 0, format "[ 'ffun' =>  F ]") : fun_scope.

(* Helper for defining notation for function families. *)
Definition fmem aT rT (pT : predType rT) (f : aT -> pT) := [fun x => mem (f x)].

(* Lemmas on the correspondance between finfun_type and CiC functions. *)
Section PlainTheory.

Variables (aT : finType) (rT : Type).
Notation fT := {ffun aT -> rT}.
Implicit Types (f : fT) (R : pred rT).

Canonical finfun_of_subType := Eval hnf in [subType of fT].

Lemma tnth_fgraph f i : tnth (fgraph f) i = f (enum_val i).
Proof. by rewrite [@fun_of_fin]unlock enum_valK. Qed.

Lemma ffunE (g : aT -> rT) : finfun g =1 g.
Proof.
move=> x; rewrite [@finfun]unlock unlock tnth_map.
by rewrite -[tnth _ _]enum_val_nth enum_rankK.
Qed.

Lemma fgraph_codom f : fgraph f = codom_tuple f.
Proof.
apply: eq_from_tnth => i; rewrite [@fun_of_fin]unlock tnth_map.
by congr tnth; rewrite -[tnth _ _]enum_val_nth enum_valK.
Qed.

Lemma codom_ffun f : codom f = val f.
Proof. by rewrite /= fgraph_codom. Qed.

Lemma ffunP f1 f2 : f1 =1 f2 <-> f1 = f2.
Proof.
split=> [eq_f12 | -> //]; do 2!apply: val_inj => /=.
by rewrite !fgraph_codom /= (eq_codom eq_f12).
Qed.

Lemma ffunK : cancel (@fun_of_fin aT rT) (@finfun aT rT).
Proof. move=> f; apply/ffunP; exact: ffunE. Qed.

Definition family_mem mF := [pred f : fT | [forall x, in_mem (f x) (mF x)]].

Lemma familyP (pT : predType rT) (F : aT -> pT) f :
  reflect (forall x, f x \in F x) (f \in family_mem (fmem F)).
Proof. exact: forallP. Qed.

Definition ffun_on_mem mR := family_mem (fun _ => mR).

Lemma ffun_onP R f : reflect (forall x, f x \in R) (f \in ffun_on_mem (mem R)).
Proof. exact: forallP. Qed.

End PlainTheory.

Notation family F := (family_mem (fun_of_simpl (fmem F))).
Notation ffun_on R := (ffun_on_mem _ (mem R)).

Implicit Arguments familyP [aT rT pT F f].
Implicit Arguments ffun_onP [aT rT R f].

(*****************************************************************************)

Lemma nth_fgraph_ord T n (x0 : T) (i : 'I_n) f : nth x0 (fgraph f) i = f i.
Proof.
by rewrite -{2}(enum_rankK i) -tnth_fgraph (tnth_nth x0) enum_rank_ord.
Qed.

Section Support.

Variables (aT : Type) (rT : eqType).

Definition support_for y (f : aT -> rT) := [pred x | f x != y].

Lemma supportE x y f : (x \in support_for y f) = (f x != y). Proof. by []. Qed.

End Support.

Notation "y .-support" := (support_for y)
  (at level 2, format "y .-support") : fun_scope.

Section EqTheory.

Variables (aT : finType) (rT : eqType).
Notation fT := {ffun aT -> rT}.
Implicit Types (y : rT) (D : pred aT) (R : pred rT) (f : fT).

Lemma supportP y D g :
  reflect (forall x, x \notin D -> g x = y) (y.-support g \subset D).
Proof.
by apply: (iffP subsetP) => Dg x; [apply: contraNeq | apply: contraR] => /Dg->.
Qed.

Definition finfun_eqMixin :=
  Eval hnf in [eqMixin of finfun_type aT rT by <:].
Canonical finfun_eqType := Eval hnf in EqType _ finfun_eqMixin.
Canonical finfun_of_eqType := Eval hnf in [eqType of fT].

Definition pfamily_mem y mD (mF : aT -> mem_pred rT) :=
  family (fun i : aT => if in_mem i mD then pred_of_simpl (mF i) else pred1 y).

Lemma pfamilyP (pT : predType rT) y D (F : aT -> pT) f :
  reflect (y.-support f \subset D /\ {in D, forall x, f x \in F x})
          (f \in pfamily_mem y (mem D) (fmem F)).
Proof.
apply: (iffP familyP) => [/= f_pfam | [/supportP f_supp f_fam] x].
  split=> [|x Ax]; last by have:= f_pfam x; rewrite Ax.
  by apply/subsetP=> x; case: ifP (f_pfam x) => //= _ fx0 /negP[].
by case: ifPn => Ax /=; rewrite inE /= (f_fam, f_supp).
Qed.

Definition pffun_on_mem y mD mR := pfamily_mem y mD (fun _ => mR).

Lemma pffun_onP y D R f :
  reflect (y.-support f \subset D /\ {subset image f D <= R})
          (f \in pffun_on_mem y (mem D) (mem R)).
Proof.
apply: (iffP (pfamilyP y D (fun _ => R) f)) => [] [-> f_fam]; split=> //.
  by move=>  _ /imageP[x Ax ->]; exact: f_fam.
by move=> x Ax; apply: f_fam; apply/imageP; exists x.
Qed.

End EqTheory.
Canonical exp_eqType (T : eqType) n := [eqType of T ^ n].

Implicit Arguments supportP [aT rT y D g].
Notation pfamily y D F := (pfamily_mem y (mem D) (fun_of_simpl (fmem F))).
Notation pffun_on y D R := (pffun_on_mem y (mem D) (mem R)).

Definition finfun_choiceMixin aT (rT : choiceType) :=
  [choiceMixin of finfun_type aT rT by <:].
Canonical finfun_choiceType aT rT :=
  Eval hnf in ChoiceType _ (finfun_choiceMixin aT rT).
Canonical finfun_of_choiceType (aT : finType) (rT : choiceType) :=
  Eval hnf in [choiceType of {ffun aT -> rT}].
Canonical exp_choiceType (T : choiceType) n := [choiceType of T ^ n].

Definition finfun_countMixin aT (rT : countType) :=
  [countMixin of finfun_type aT rT by <:].
Canonical finfun_countType aT (rT : countType) :=
  Eval hnf in CountType _ (finfun_countMixin aT rT).
Canonical finfun_of_countType (aT : finType) (rT : countType) :=
  Eval hnf in [countType of {ffun aT -> rT}].
Canonical finfun_subCountType aT (rT : countType) :=
  Eval hnf in [subCountType of finfun_type aT rT].
Canonical finfun_of_subCountType (aT : finType) (rT : countType) :=
  Eval hnf in [subCountType of {ffun aT -> rT}].

(*****************************************************************************)

Section FinTheory.

Variables aT rT : finType.
Notation fT := {ffun aT -> rT}.
Notation ffT := (finfun_type aT rT).
Implicit Types (D : pred aT) (R : pred rT) (F : aT -> pred rT).

Definition finfun_finMixin := [finMixin of ffT by <:].
Canonical finfun_finType := Eval hnf in FinType ffT finfun_finMixin.
Canonical finfun_subFinType := Eval hnf in [subFinType of ffT].
Canonical finfun_of_finType := Eval hnf in [finType of fT for finfun_finType].
Canonical finfun_of_subFinType := Eval hnf in [subFinType of fT].

Lemma card_pfamily y0 D F :
  #|pfamily y0 D F| = foldr (fun x m => #|F x| * m) 1 (enum D).
Proof.
have:= enum_uniq D; have:= mem_enum D.
elim: {D}(enum _) {2 4}D => [|x0 s IHs] D eqDs => [_|] /=.
  rewrite -(card1 [ffun=> y0]); apply: eq_card => f.
  apply/familyP/eqP=> [f_y0 | ->{f} x]; last by rewrite ffunE -eqDs !inE.
  by apply/ffunP=> x; have:= f_y0 x; rewrite -eqDs ffunE => /eqP.
case/andP=> /negPf nsx0 /(IHs (mem s)) <- {IHs}//.
pose g1 (f : fT) := (f x0, [ffun x => if x == x0 then y0 else f x]).
pose g2 (xf : rT * fT) := [ffun x => if x == x0 then xf.1 else xf.2 x].
have g1K: cancel g1 g2.
  by move=> f; apply/ffunP=> x; rewrite !ffunE; case: eqP => // ->.
rewrite -cardX -(card_image (can_inj g1K)); apply: eq_card => [] [y f] /=.
apply/imageP/andP=> /= [[f' /familyP F_f'] [-> ->]| [Fy /familyP Ff]].
  split; first by have:= F_f' x0; rewrite -eqDs mem_head.
  apply/familyP=> x; have:= F_f' x; rewrite ffunE -eqDs inE /=.
  by case: eqP => //= -> _; rewrite nsx0 !inE.
exists (g2 (y, f)); last first.
  congr (_, _); first by rewrite ffunE eqxx.
  apply/ffunP=> x; rewrite !ffunE /=; case: (x =P x0) => // ->{x}.
  by have:= Ff x0; rewrite /= nsx0 => /eqP.
by apply/familyP=> x; have:= Ff x; rewrite -eqDs ffunE !inE; case: eqP => // ->.
Qed.

Lemma card_family F : #|family F| = foldr (fun x m => #|F x| * m) 1 (enum aT).
Proof.
case: (pickP rT) => [y0 _ | rT0].
  by rewrite -(card_pfamily y0); apply: eq_card.
case: (enum _) (mem_enum aT) => [aT0 | x0 e _]; last first.
  by rewrite /= !eq_card0 // => [f | y]; [have := rT0 (f x0) | have := rT0 y].
have no_aT P (x : aT) : P by have:= aT0 x.
rewrite /= -(card1 [ffun x => no_aT rT x]); apply: eq_card => f'.
by apply/familyP/eqP=> _; [apply/ffunP | ] => x; exact: no_aT.
Qed.

Lemma card_pffun_on y0 D R : #|pffun_on y0 D R| = #|R| ^ #|D|.
Proof.
by rewrite (cardE D) card_pfamily; elim: (enum _) => //= _ ? ->; rewrite expnS.
Qed.

Lemma card_ffun_on R : #|ffun_on R| = #|R| ^ #|aT|.
Proof.
by rewrite card_family cardT; elim: (enum _) => //= _ e ->; rewrite expnS.
Qed.

Lemma card_ffun : #|fT| = #|rT| ^ #|aT|.
Proof.
by rewrite -card_ffun_on; apply: eq_card => f; symmetry; exact/forallP.
Qed.

End FinTheory.
Canonical exp_finType (T : finType) n := [finType of T ^ n].

