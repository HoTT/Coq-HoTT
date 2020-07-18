Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.

(** * Squares of morphisms in a Wild Category.  *)

(** These come up a lot as naturality squares. In this file we define basic operations on squares, to conveniently work with them. *)

(** A Square is a cubical 2-cell in a 1-category. The order of the arguments is left-right-top-bottom: [Square l r t b].  It is defined to be [r $o t $== b $o l]. *)

Definition Square {A : Type} `{Is1Cat A} {x00 x20 x02 x22 : A}
  (f01 : x00 $-> x02) (f21 : x20 $-> x22) (f10 : x00 $-> x20) (f12 : x02 $-> x22) 
  : Type
  := f21 $o f10 $== f12 $o f01.


Section Squares.
  (* We declare a context with a lot of variables: the first component is horizontal, the second vertical.
    x00 f10 x20 f30 x40
    f01     f21     f41
    x02 f12 x22 f32 x42
    f03     f23     f43
    x04 f14 x24 f34 x44 
  All morphisms are pointed to the right or down. *)
  Context {A : Type} `{HasEquivs A} {x x' x00 x20 x40 x02 x22 x42 x04 x24 x44 : A}
    {f10 f10' : x00 $-> x20} {f30 : x20 $-> x40} 
    {f12 f12' : x02 $-> x22} {f32 : x22 $-> x42} 
    {f14 : x04 $-> x24} {f34 : x24 $-> x44}
    {f01 f01' : x00 $-> x02} {f21 f21' : x20 $-> x22} {f41 f41' : x40 $-> x42}
    {f03 : x02 $-> x04} {f23 : x22 $-> x24} {f43 : x42 $-> x44}.

  (** We give a "constructor" and "destructor" for squares. *)
  Definition Build_Square (p : f21 $o f10 $== f12 $o f01) : Square f01 f21 f10 f12 := p.
  Definition gpdhom_square (s : Square f01 f21 f10 f12) : f21 $o f10 $== f12 $o f01 := s.

  (** Squares degenerate in two sides given by a single 2-morphism. *)
  Definition hdeg_square {f f' : x $-> x'} (p : f $== f') : Square f f' (Id x) (Id x')
    := cat_idr f' $@ p^$ $@ (cat_idl f)^$.
  Definition vdeg_square {f f' : x $-> x'} (p : f $== f') : Square (Id x) (Id x') f f'
    := cat_idl f $@ p $@ (cat_idr f')^$.

  (** Squares degenerate in two sides given by the identity 2-morphism at some morphism. *)
  Definition hrefl (f : x $-> x') : Square f f (Id x) (Id x') := hdeg_square (Id f).
  Definition vrefl (f : x $-> x') : Square (Id x) (Id x') f f := vdeg_square (Id f).

  (** The transpose of a square *)
  Definition transpose (s : Square f01 f21 f10 f12) : Square f10 f12 f01 f21 := s^$.

  (** Horizontal and vertical concatenation of squares *)
  Definition hconcat (s : Square f01 f21 f10 f12) (t : Square f21 f41 f30 f32)
    : Square f01 f41 (f30 $o f10) (f32 $o f12)
    := (cat_assoc _ _ _)^$ $@ (t $@R f10) $@ cat_assoc _ _ _ $@ (f32 $@L s) $@ (cat_assoc _ _ _)^$.
  Definition vconcat (s : Square f01 f21 f10 f12) (t : Square f03 f23 f12 f14)
    : Square (f03 $o f01) (f23 $o f21) f10 f14
  := cat_assoc _ _ _ $@ (f23 $@L s) $@ (cat_assoc _ _ _)^$ $@ (t $@R f01) $@ cat_assoc _ _ _.

  (** If the horiztonal morphisms in a square are equivalences then we can flip the square by inverting them. *)
  Definition hinverse (f10 : x00 $<~> x20) (f12 : x02 $<~> x22) (s : Square f01 f21 f10 f12)
    : Square f21 f01 f10^-1$ f12^-1$
    := (cat_idl _)^$ $@ ((cate_issect f12)^$ $@R _) $@ cat_assoc _ _ _
      $@ (_ $@L ((cat_assoc _ _ _)^$ $@ (s^$ $@R _) $@ cat_assoc _ _ _
      $@ (_ $@L cate_isretr f10) $@ cat_idr _)).

  (** The following four declarations modify one side of a Square using a 2-cell. The L or R indicate the side of the 2-cell. This can be thought of as rewriting the sides of a square using a homotopy. *)

  (** Rewriting the left edge. *)
  Definition hconcatL (p : f01' $== f01) (s : Square f01 f21 f10 f12)
    : Square f01' f21 f10 f12
    := s $@ (f12 $@L p^$).

  (** Rewriting the right edge. *)
  Definition hconcatR (s : Square f01 f21 f10 f12) (p : f21' $== f21)
    : Square f01 f21' f10 f12
    := (p $@R f10) $@ s.

  (** Rewriting the top edge. *)
  Definition vconcatL (p : f10' $== f10) (s : Square f01 f21 f10 f12)
    : Square f01 f21 f10' f12
    := (f21 $@L p) $@ s.

  (** Rewriting the bottom edge. *)
  Definition vconcatR (s : Square f01 f21 f10 f12) (p : f12' $== f12)
    : Square f01 f21 f10 f12'
    := s $@ (p^$ $@R f01).

End Squares.

Section Squares2.

  (** We declare the context again, now that we can reuse some declarations where the variables have been inserted. This would not need to be done if coq could generalize variables within sections. Currently this is possible in Lean and Agda. *)
  Context {A B : Type} `{HasEquivs A} `{Is1Cat B}
    {x x' x00 x20 x40 x02 x22 x42 x04 x24 x44 : A}
    {f10 f10' : x00 $-> x20} {f30 : x20 $-> x40} 
    {f12 f12' : x02 $-> x22} {f32 : x22 $-> x42} 
    {f14 : x04 $-> x24} {f34 : x24 $-> x44}
    {f01 f01' : x00 $-> x02} {f21 f21' : x20 $-> x22} {f41 f41' : x40 $-> x42}
    {f03 : x02 $-> x04} {f23 : x22 $-> x24} {f43 : x42 $-> x44}.

  (** If the vertical morphisms in a square are equivalences then we can flip the square by inverting them. *)
  Definition vinverse (f01 : x00 $<~> x02) (f21 : x20 $<~> x22) (s : Square f01 f21 f10 f12)
    : Square (f01^-1$) (f21^-1$) f12 f10
    := transpose (hinverse _ _ (transpose s)).

  (** Whisker a map in one of the corners. For the bottom-left and top-right we have two choices. *)

  Definition whiskerTL {f : x $-> x00} (s : Square f01 f21 f10 f12)
    : Square (f01 $o f) f21 (f10 $o f) f12
    := (cat_assoc _ _ _)^$ $@ (s $@R f) $@ cat_assoc _ _ _.

  Definition whiskerBR {f : x22 $-> x} (s : Square f01 f21 f10 f12)
    : Square f01 (f $o f21) f10 (f $o f12)
    := cat_assoc _ _ _ $@ (f $@L s) $@ (cat_assoc _ _ _)^$.

  Definition whiskerBL {f : x $<~> x02} (s : Square f01 f21 f10 f12)
    : Square (f^-1$ $o f01) f21 f10 (f12 $o f)
    := s $@ ((compose_hh_V _ _)^$ $@R f01) $@ cat_assoc _ _ _.

  Definition whiskerLB {f : x02 $<~> x} (s : Square f01 f21 f10 f12)
    : Square (f $o f01) f21 f10 (f12 $o f^-1$)
    := s $@ ((compose_hV_h _ _)^$ $@R f01) $@ cat_assoc _ _ _.

  Definition whiskerTR {f : x20 $<~> x} (s : Square f01 f21 f10 f12)
    : Square f01 (f21 $o f^-1$) (f $o f10) f12
    := cat_assoc _ _ _ $@ (f21 $@L compose_V_hh _ _) $@ s.

  Definition whiskerRT {f : x $<~> x20} (s : Square f01 f21 f10 f12)
    : Square f01 (f21 $o f) (f^-1$ $o f10) f12
    := cat_assoc _ _ _ $@ (f21 $@L compose_h_Vh _ _) $@ s.

  (** Moving around maps in a square. Associativity laws. *)

  Definition move_bottom_left {f01 : x00 $-> x} {f01' : x $-> x02}
    (s : Square (f01' $o f01) f21 f10 f12) 
    : Square f01 f21 f10 (f12 $o f01')
    := s $@ (cat_assoc _ _ _)^$.

  Definition move_left_bottom {f12 : x02 $-> x} {f12' : x $-> x22}
    (s : Square f01 f21 f10 (f12' $o f12)) 
    : Square (f12 $o f01) f21 f10 f12'
    := s $@ cat_assoc _ _ _.

  Definition move_right_top {f10 : x00 $-> x} {f10' : x $-> x20}
    (s : Square f01 f21 (f10' $o f10) f12) 
    : Square f01 (f21 $o f10') f10 f12
    := cat_assoc _ _ _ $@ s.

  Definition move_top_right {f21 : x20 $-> x} {f21' : x $-> x22}
    (s : Square f01 (f21' $o f21) f10 f12) 
    : Square f01 f21' (f21 $o f10) f12
    := (cat_assoc _ _ _)^$ $@ s.

  Definition fmap_square (f : A -> B) `{!Is0Functor f} `{!Is1Functor f}
    (s : Square f01 f21 f10 f12)
    : Square (fmap f f01) (fmap f f21) (fmap f f10) (fmap f f12)
    := (fmap_comp f _ _)^$ $@ fmap2 f s $@ fmap_comp f _ _.

End Squares2.

Notation "s $@h t" := (hconcat s t).
Notation "s $@v t" := (vconcat s t).
Notation "s $@hR p" := (hconcatR s p).
Notation "s $@hL p" := (hconcatL p s).
Notation "s $@vR p" := (vconcatR s p).
Notation "s $@vL p" := (vconcatL p s).
Notation "s ^h$" := (hinverse _ _ s).
Notation "s ^v$" := (vinverse _ _ s).
