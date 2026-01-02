#[warnings="-deprecated-from-Coq"]
From Coq Require Init.Tactics. (* TODO: Can remove this line and previous once Rocq 9.0 is our minimum. *)
From HoTT Require Import Basics.Overture Basics.Tactics.
From HoTT.WildCat Require Import Core NatTrans Equiv SetoidRewrite.

(** * Examples and tests of setoid rewriting *)

(** ** Examples of setoid rewriting *)

(** See theories/WildCat/HomologicalAlgebra.v for many more examples of setoid rewriting. *)

(** Rewriting works in hypotheses. *)
Proposition epic_sectionof {A} `{Is1Cat A}
  {a b : A} (f : a $-> b) :
  SectionOf f -> Epic f.
Proof.
  intros [right_inverse is_section] c g h eq_gf_hf.
  apply cat_prewhisker with (h:=right_inverse) in eq_gf_hf.
  rewrite 2 cat_assoc, is_section, 2 cat_idr in eq_gf_hf.
  exact eq_gf_hf.
Defined.

(** A different approach, working in the goal. *)
Proposition monic_retractionof {A} `{Is1Cat A}
  {b c : A} (f : b $-> c) :
  RetractionOf f -> Monic f.
Proof.
  intros [left_inverse is_retraction] a g h eq_fg_fh.
  rewrite <- (cat_idl g), <- (cat_idl h).
  rewrite <- is_retraction.
  rewrite 2 cat_assoc.
  exact (_ $@L eq_fg_fh).
Defined.

Proposition faithful_nat_equiv_faithful {A B : Type}
  {F G : A -> B} `{Is1Functor _ _ F}
  `{!Is0Functor G, !Is1Functor G}
  `{!HasEquivs B} (tau : NatEquiv F G)
  : Faithful F -> Faithful G.
Proof.
  intros faithful_F x y f g eq_Gf_Gg.
  apply faithful_F.
  apply (cate_monic_equiv (tau y)).
  rewrite 2 (isnat tau).
  by apply cat_prewhisker.
Defined.

(** ** Tests of setoid rewriting *)

Section SetoidRewriteTests.

  Goal forall (A : Type) `(H : Is0Gpd A) (a b c : A),
      a $== b -> b $== c -> a $== c.
  Proof.
    intros A ? ? ? a b c eq_ab eq_bc.
    by rewrite eq_ab, <- eq_bc.
  Defined.

  Goal forall (A : Type) `(H : Is0Gpd A) (a b c : A),
      a $== b -> b $== c -> a $== c.
  Proof.
    intros A ? ? ? a b c eq_ab eq_bc.
    symmetry.
    rewrite eq_ab, <- eq_bc.
    rewrite eq_bc.
    by rewrite <- eq_bc.
  Defined.

  Goal forall (A B : Type) (F : A -> B) `{Is1Functor _ _ F} (a b : A) (f g : a $-> b), f $== g -> fmap F f $== fmap F g.
  Proof.
    do 17 intro.
    intro eq_fg.
    by rewrite eq_fg.
  Defined.

  Goal forall (A : Type) `{Is1Cat A} (a b c : A) (f1 f2 : a $-> b) (g : b $-> c), f1 $== f2 -> g $o f1 $== g $o f2.
  Proof.
    do 11 intro.
    intro eq.
    rewrite <- eq.
    by rewrite eq.
  Defined.

  Goal forall (A : Type) `{Is1Cat A} (a b c : A) (f : a $-> b) (g1 g2 : b $-> c), g1 $== g2 -> g1 $o f $== g2 $o f.
  Proof.
  do 11 intro.
  intro eq.
  rewrite <- eq.
  rewrite eq.
  by rewrite <- eq.
  Defined.

  Goal forall (A : Type) `{Is1Cat A} (a b c : A) (f1 f2 : a $-> b) (g1 g2 : b $-> c), g1 $== g2 -> f1 $== f2 -> g1 $o f1 $== g2 $o f2.
  Proof.
    do 12 intro.
    intros eq_g eq_f.
    rewrite eq_g.
    rewrite <- eq_f.
    rewrite eq_f.
    by rewrite <- eq_g.
  Defined.

End SetoidRewriteTests.
