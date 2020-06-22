Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.

(** * Squares of morphisms in a Wild Category.  *)

(**  These come up a lot as naturality squares. In this file we define basic operations on squares, to conveniently work with them. *)

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

  (** A Square is a cubical 2-cell in a 1-category. The order of the arguments is top-bottom-left-right: [Square t b l r].  It is defined to be [r $o t $== b $o l]. *)
  Definition Square {x00 x20 x02 x22}
    (f10 : x00 $-> x20) (f12 : x02 $-> x22) (f01 : x00 $-> x02) (f21 : x20 $-> x22)
    : Type := f21 $o f10 $== f12 $o f01.

  Definition Build_Square (p : f21 $o f10 $== f12 $o f01) : Square f10 f12 f01 f21 := p.
  Definition gpdhom_square (s : Square f10 f12 f01 f21) : f21 $o f10 $== f12 $o f01 := s.

  Definition hdeg_square {f f' : x $-> x'} (p : f $== f') : Square (Id x) (Id x') f f'
    := cat_idr f' $@ p^$ $@ (cat_idl f)^$.
  Definition vdeg_square {f f' : x $-> x'} (p : f $== f') : Square f f' (Id x) (Id x')
    := cat_idl f $@ p $@ (cat_idr f')^$.

  Definition hrefl (f : x $-> x') : Square (Id x) (Id x') f f := hdeg_square (Id f).
  Definition vrefl (f : x $-> x') : Square f f (Id x) (Id x') := vdeg_square (Id f).
  Definition hrfl {f : x $-> x'} : Square (Id x) (Id x') f f := hrefl f.
  Definition vrfl {f : x $-> x'} : Square f f (Id x) (Id x') := vrefl f.

  Definition transpose (s : Square f10 f12 f01 f21) : Square f01 f21 f10 f12 := s^$.
  Definition hconcat (s : Square f10 f12 f01 f21) (t : Square f30 f32 f21 f41)
    : Square (f30 $o f10) (f32 $o f12) f01 f41
    := (cat_assoc _ _ _)^$ $@ (t $@R f10) $@ cat_assoc _ _ _ $@ (f32 $@L s) $@ (cat_assoc _ _ _)^$.
  Definition vconcat (s : Square f10 f12 f01 f21) (t : Square f12 f14 f03 f23)
    : Square f10 f14 (f03 $o f01) (f23 $o f21)
  := cat_assoc _ _ _ $@ (f23 $@L s) $@ (cat_assoc _ _ _)^$ $@ (t $@R f01) $@ cat_assoc _ _ _.

  Definition hinverse (f10 : x00 $<~> x20) (f12 : x02 $<~> x22) (s : Square f10 f12 f01 f21)
    : Square f10^-1$ f12^-1$ f21 f01
  := (cat_idl _)^$ $@ ((cate_issect f12)^$ $@R _) $@ cat_assoc _ _ _
     $@ (_ $@L ((cat_assoc _ _ _)^$ $@ (s^$ $@R _) $@ cat_assoc _ _ _
      $@ (_ $@L cate_isretr f10) $@ cat_idr _)).

  (** The following four declarations modify one side of a Square using a 2-cell. The L or R indicate the side of the 2-cell.*)
  Definition hconcatL (p : f01' $== f01) (s : Square f10 f12 f01 f21) : Square f10 f12 f01' f21 :=
    s $@ (f12 $@L p^$).

  (* Maybe we want to reverse [p]? *)
  Definition hconcatR (s : Square f10 f12 f01 f21) (p : f21' $== f21) : Square f10 f12 f01 f21' :=
    (p $@R f10) $@ s.

  Definition vconcatL (p : f10' $== f10) (s : Square f10 f12 f01 f21) : Square f10' f12 f01 f21 :=
    (f21 $@L p) $@ s.

  Definition vconcatR (s : Square f10 f12 f01 f21) (p : f12' $== f12) : Square f10 f12' f01 f21 :=
    s $@ (p^$ $@R f01).

End Squares.

Section Squares2.
  (* We declare the context again, now that we can reuse some declarations where the variables have been inserted. *)
  Context {A B : Type} `{HasEquivs A} `{Is1Cat B} {x x' x00 x20 x40 x02 x22 x42 x04 x24 x44 : A}
    {f10 f10' : x00 $-> x20} {f30 : x20 $-> x40} 
    {f12 f12' : x02 $-> x22} {f32 : x22 $-> x42} 
    {f14 : x04 $-> x24} {f34 : x24 $-> x44}
    {f01 f01' : x00 $-> x02} {f21 f21' : x20 $-> x22} {f41 f41' : x40 $-> x42}
    {f03 : x02 $-> x04} {f23 : x22 $-> x24} {f43 : x42 $-> x44}.

  Definition vinverse (f01 : x00 $<~> x02) (f21 : x20 $<~> x22) (s : Square f10 f12 f01 f21) : Square f12 f10 (f01^-1$) (f21^-1$) :=
    transpose (hinverse _ _ (transpose s)).

  (* whisker a map in one of the corners. For the bottom-left and top-right we have two choices. *)
  Definition whiskerTL {f : x $-> x00} (s : Square f10 f12 f01 f21) : Square (f10 $o f) f12 (f01 $o f) f21 :=
    (cat_assoc _ _ _)^$ $@ (s $@R f) $@ cat_assoc _ _ _.

  Definition whiskerBR {f : x22 $-> x} (s : Square f10 f12 f01 f21) : Square f10 (f $o f12) f01 (f $o f21) :=
    cat_assoc _ _ _ $@ (f $@L s) $@ (cat_assoc _ _ _)^$.

  Definition whiskerBL {f : x $<~> x02} (s : Square f10 f12 f01 f21) : Square f10 (f12 $o f) (f^-1$ $o f01) f21 :=
    s $@ ((compose_hh_V _ _)^$ $@R f01) $@ cat_assoc _ _ _.

  Definition whiskerLB {f : x02 $<~> x} (s : Square f10 f12 f01 f21) : Square f10 (f12 $o f^-1$) (f $o f01) f21 :=
    s $@ ((compose_hV_h _ _)^$ $@R f01) $@ cat_assoc _ _ _.

  Definition whiskerTR {f : x20 $<~> x} (s : Square f10 f12 f01 f21) : Square (f $o f10) f12 f01 (f21 $o f^-1$) :=
    cat_assoc _ _ _ $@ (f21 $@L compose_V_hh _ _) $@ s.

  Definition whiskerRT {f : x $<~> x20} (s : Square f10 f12 f01 f21) : Square (f^-1$ $o f10) f12 f01 (f21 $o f) :=
    cat_assoc _ _ _ $@ (f21 $@L compose_h_Vh _ _) $@ s.

  (* moving maps around the square *)
  Definition move_bottom_left {f01 : x00 $-> x} {f01' : x $-> x02} (s : Square f10 f12 (f01' $o f01) f21) 
    : Square f10 (f12 $o f01') f01 f21 :=
    s $@ (cat_assoc _ _ _)^$.

  Definition move_left_bottom {f12 : x02 $-> x} {f12' : x $-> x22} (s : Square f10 (f12' $o f12) f01 f21) 
    : Square f10 f12' (f12 $o f01) f21 :=
    s $@ cat_assoc _ _ _.

  Definition move_right_top {f10 : x00 $-> x} {f10' : x $-> x20} (s : Square (f10' $o f10) f12 f01 f21) 
    : Square f10 f12 f01 (f21 $o f10') :=
    cat_assoc _ _ _ $@ s.

  Definition move_top_right {f21 : x20 $-> x} {f21' : x $-> x22} (s : Square f10 f12 f01 (f21' $o f21)) 
    : Square (f21 $o f10) f12 f01 f21' :=
    (cat_assoc _ _ _)^$ $@ s.

  Definition fmap_square (F : A -> B) {H0F : Is0Functor F} {H1F : Is1Functor F} (s : Square f10 f12 f01 f21) : 
    Square (fmap F f10) (fmap F f12) (fmap F f01) (fmap F f21) :=
    (fmap_comp F _ _)^$ $@ fmap2 F s $@ fmap_comp F _ _.

End Squares2.

(** TODO: Do we want these notations?
Notation "s $@h t" := (hconcat s t).
Notation "s $@v t" := (vconcat s t).
Notation "s $@hR p" := (hconcatR s p).
Notation "s $@hL p" := (hconcatL p s).
Notation "s $@vR p" := (vconcatR s p).
Notation "s $@vL p" := (vconcatL p s).
Notation "s ^h$" := (hinverse _ _ s).
Notation "s ^v$" := (vinverse _ _ s).
*)
