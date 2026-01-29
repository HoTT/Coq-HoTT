From HoTT.Basics Require Import Overture Equivalences Tactics.
From HoTT.WildCat Require Import Core SetoidRewrite AbEnriched EpiStable.
From HoTT.Spaces Require Import Nat.Core Finite.Fin.

Local Open Scope mc_add_scope.

(** * Homological algebra *)

(** Various "diagram lemmas" are proved, usually assuming the wild category satisfies [IsAbEpiStable].  The proofs use the diagram chasing method provided by WildCat.EpiStable. *)

(** We will often use the convention that a map [bc : B $-> C] is named as the juxtaposition of the domain and codomain.  When we want to highlight the importance of certain maps, they will be given different names. *)

(** ** The weak four lemmas *)

Section FourLemma.

  Context {A : Type} `{IsAbEpiStable A}.

  Context {B C D E B' C' D' E' : A}
    (bc : B $-> C) (cd : C $-> D) (de : D $-> E)
    (bc' : B' $-> C') (cd' : C' $-> D') (de' : D' $-> E')
    (g : B $-> B') (h : C $-> C') (i : D $-> D') (j : E $-> E')
    (sq2 : h $o bc $== bc' $o g) (sq3 : i $o cd $== cd' $o h)
    (sq4 : j $o de $== de' $o i)
    `{!CatIsAbExact cd de} `{!CatIsAbExact bc' cd'} `{!Epic g} `{!Monic j}.

  (** The diagram has the following shape:
<<
  B ---> C ---> D ---> E
  |      |      |      v
  |g     |h     |i     |j
  v      |      |      |
  v      v      v      v
  B' --> C' --> D' --> E'
>>
  The common assumptions are that the map [B $-> B'] is epi, the map [E $-> E'] is mono, and the sequences [C $-> D] + [D $-> E] and [B' $-> C'] + [C' $-> D'] are exact. *)

  (** If in addition the composite of [C' $-> D'] and [D' $-> C'] is zero and the map [D $-> D'] is epi, then the map [C $-> C'] is epi. *)
  Definition weak_four_epi {complex_cde' : de' $o cd' $== 0} `{!Epic i}
    : Epic h.
  Proof.
    (* To show that [h : C $-> C'] is epi, we must show that an arbitrary generalized element [c' : elt P C'] lifts along [h : C $-> C']. *)
    apply epic_elt_lift; intros P c'.

    (* Since the map [i : D $-> D'] is assumed epi, we can lift the element [cd' $o c' : elt P D'] to an element [d : elt _ D].  [ld] will be the name given to the proof that [d] is a lift. *)
    elt_lift_epic i (cd' $o c') d ld.

    (* Using exactness of the top row, we can further lift the element [d] to an element [c : elt _ C].  This step involves verifying that [d] is mapped to zero by [de : D $-> E], which requires the map [j] to be mono. *)
    (* We clear 2-cells and elements when they are no longer needed, to speed up the lifts.  The [using clear] clause is applied *after* the hypothesis is proved. *)
    elt_lift_exact cd de d c lc using clear sq4 complex_cde'.
    { apply (ismonic' j).
      rewrite_with_assoc sq4.
      rewrite ld.
      rewrite cat_assoc_opp.
      rewrite complex_cde'.
      apply precomp_zero. }

    (* The element [c] is not necessarily the correct lift of [c'].  We correct this by lifting the element [c' - h $o c] using exactness of the bottom row. This yields an element [b' : elt _ B']. *)
    elt_lift_exact bc' cd' (c' - h $o c) b' lb' using clear sq3 lc ld d.
    {
      rewrite postcomp_op_inv.
      rewrite_with_assoc sq3^$.
      rewrite lc, ld.
      apply inverse_r_0gpd. }

    (* Since we know that the map [g : B $-> B'] is epi, we can lift [b'] to an element [b : elt _ B]. *)
    elt_lift_epic g b' b lb.

    (* We obtain the correct lift by adding together the incorrect lift and its correction. *)
    provide_lift (c + bc $o b).
    (* It remains to show that this is indeed a lift of [c']. *)
    lhs' napply postcomp_op.
    rewrite_with_assoc sq2.
    rewrite lb, lb'.
    rewrite (comm_0gpd c').
    lhs_V' napply assoc_0gpd.
    rewrite inverse_r_0gpd.
    apply mon_unit_l_0gpd.
  Defined.

  (** If, in addition to the common assumptions, the composite of [B $-> C] and [C $-> D] is zero and the map [C $-> C'] is mono, then the map [D $-> D'] is mono. *)
  Definition weak_four_mono {complex_bcd : cd $o bc $== 0} `{!Monic h}
    : Monic i.
  Proof.
    (* To show that a map is mono, it suffices to show that an arbitrary generalized element [d : elt P D] that goes to [0 : elt P D'] is homotopic to [0 : elt P D]. *)
    apply monic_via_elt_isemb_ab; intros P d p.

    (* Using exactness, we lift the element [d] to [c : elt _ C]. *)
    elt_lift_exact cd de d c lc using clear sq4.
    { apply (ismonic' j).
      rewrite_with_assoc sq4.
      rewrite p.
      apply postcomp_zero. }

    (* Next we lift [h $o c] to [b' : elt _ B']. *)
    elt_lift_exact bc' cd' (h $o c) b' lb' using clear sq3 p.
    { rewrite_with_assoc sq3^$.
      rewrite lc.
      exact p. }

    (* We lift [b'] to [b : elt _ B]. *)
    elt_lift_epic g b' b lb.

    (* Since [h] is monic, it follows that [b] is a lift of [c]. *)
    assert (p' : bc $o b $== c).
    { apply (ismonic h).
      rewrite_with_assoc sq2.
      rewrite lb.
      exact lb'. }

    (* So [d] lifts all the way to [B].  Since [B -> C -> D] is a complex, [d] is zero. *)
    lhs_V' napply lc.
    rewrite <- p'.
    lhs' napply cat_assoc_opp.
    rewrite complex_bcd.
    apply precomp_zero.
  Defined.

End FourLemma.

(** ** The 3x3-lemmas as presented in Mac Lane's book "Homology" *)

Section ThreeByThree.

  Context {A : Type} `{Is1Cat A}.

  Context {X00 X01 X02 X10 X11 X12 X20 X21 X22 : A}
    (f0i : X00 $-> X01) (f0j : X01 $-> X02)
    (fi0 : X00 $-> X10) (fi1 : X01 $-> X11) (fi2 : X02 $-> X12)
    (f1i : X10 $-> X11) (f1j : X11 $-> X12)
    (fj0 : X10 $-> X20) (fj1 : X11 $-> X21) (fj2 : X12 $-> X22)
    (f2i : X20 $-> X21) (f2j : X21 $-> X22)
    (sq1 : fi1 $o f0i $== f1i $o fi0) (sq2 : fi2 $o f0j $== f1j $o fi1)
    (sq3 : fj1 $o f1i $== f2i $o fj0) (sq4 : fj2 $o f1j $== f2j $o fj1).

  (** The diagram has the following shape:
<<
  X00 ----f0i----> X01 ----f0j----> X02
   |                |                |
   |                |                |
  fi0     sq1      fi1     sq2      fi2
   |                |                |
   |                |                |
   v                v                v
  X10 ----f1i----> X11 ----f1j----> X12
   |                |                |
   |                |                |
  fj0     sq3      fj1     sq4      fj2
   |                |                |
   |                |                |
   v                v                v
  X20 ----f2i----> X21 ----f2j----> X22
>>
  *)

  (** If all three columns and the last two rows are short exact, then the top row is short exact.  We prove the three parts of the conclusion as separate results, each requiring a different subset of the hypotheses (and in fact not all of the hypotheses are needed). *)

  Definition three_by_three_monic `{!Monic f1i} `{!Monic fi0} `{!Monic fi1}
    : Monic f0i.
  Proof.
    napply (monic_cancel f0i fi1).
    exact (monic_homotopic _ _ sq1^$).
  Defined.

  (** For the remaining results, we need this assumption. *)
  Context `{!IsAbEpiStable A}.

  (** The hypotheses aren't entirely minimal here.  Instead of the two exactness hypotheses, we really only need that the lifting property holds. *)
  Definition three_by_three_ex `{!Monic f2i} `{!Monic fi1} `{!Monic fi2}
    `{!CatIsAbExact fi0 fj0} `{!CatIsAbExact f1i f1j}
    {q : fj1 $o fi1 $== 0}
    : CatIsAbExact f0i f0j.
  Proof.
    snapply Build_CatIsAbExact.
    - apply (ismonic' fi2).
      rewrite_with_assoc sq2.
      lhs' napply (_ $@L sq1).
      lhs' napply cat_assoc_opp.
      lhs' apply (isabcomplex $@R _).
      apply precomp_zero.
    - intros P x01 p.
      clear sq4.

      elt_lift_exact f1i f1j (fi1 $o x01) x10 lx10 using clear sq2 p.
      { rewrite_with_assoc sq2^$.
        lhs' napply (_ $@L p).
        apply postcomp_zero. }

      elt_lift_exact fi0 fj0 x10 x00 lx00 using clear sq3 q.
      { apply (ismonic' f2i).
        rewrite_with_assoc sq3^$.
        lhs' napply (_ $@L lx10).
        lhs' napply cat_assoc_opp.
        lhs' napply (q $@R _).
        apply precomp_zero. }

      provide_lift x00.
      apply (ismonic fi1).
      rewrite_with_assoc sq1.
      refine (_ $@ lx10).
      exact (_ $@L lx00).
  Defined.

  (** We could also do away with some hypothesis here. *)
  Definition three_by_three_epi `{!Monic fi2} `{!Epic f1j} `{!Epic fj0}
    {complex_f_2 : fj2 $o fi2 $== 0} {complex_f1_ : f1j $o f1i $== 0}
    `{!CatIsAbExact fi1 fj1} `{!CatIsAbExact f2i f2j}
    : Epic f0j.
  Proof.
    clear sq1.
    apply epic_elt_lift; intros P x02.

    elt_lift_epic f1j (fi2 $o x02) x11 lx11.

    elt_lift_exact f2i f2j (fj1 $o x11) x20 lx20 using clear sq4 complex_f_2.
    { rewrite_with_assoc sq4^$.
      lhs' napply (_ $@L lx11).
      lhs_V' napply cat_assoc.
      lhs' napply (complex_f_2 $@R _).
      apply precomp_zero. }

    elt_lift_epic fj0 x20 x10 lx10.

    elt_lift_exact fi1 fj1 (x11 - f1i $o x10) x01 lx01 using clear sq3 lx10 lx20 x20.
    { lhs' rapply postcomp_op_inv.
      rewrite_with_assoc sq3.
      rewrite lx10.
      apply (inverse_r_homotopy_0gpd lx20^$). }

    provide_lift x01.
    apply (ismonic fi2).
    rewrite_with_assoc sq2.
    rewrite lx01.
    lhs' napply postcomp_op_inv.
    rewrite <- cat_assoc.
    rewrite complex_f1_.
    rewrite precomp_zero.
    lhs' napply mon_unit_l_inv_0gpd.
    exact lx11.
  Defined.

  (** If every column is exact, the top and bottom rows are short exact, and the middle row is a complex, then the middle row is short exact.  Like above, we prove the three parts of this separately, with fewer hypotheses. *)

  Definition middle_three_by_three_mono
    `{!Monic f0i} `{!Monic f2i} `{!Monic fi1}
    `{!CatIsAbExact fi0 fj0}
    : Monic f1i.
  Proof.
    clear sq2 sq4.
    apply monic_via_elt_isemb_ab; intros P x10 p.

    elt_lift_exact fi0 fj0 x10 x00 lx00 using clear sq3.
    { apply (ismonic' f2i).
      rewrite_with_assoc sq3^$.
      lhs' napply (_ $@L p).
      apply postcomp_zero. }

    lhs_V' napply lx00.
    rhs_V' napply (postcomp_zero fi0).
    apply cat_postwhisker.
    rapply (ismonic' (fi1 $o f0i)).
    lhs' napply (sq1 $@R _).
    lhs' napply cat_assoc.
    lhs' napply (_ $@L lx00).
    exact p.
  Defined.

  Definition middle_three_by_three_ex {cpx : f1j $o f1i $== 0}
    `{!Epic fj0} `{!Monic fi2} `{!CatIsAbExact f0i f0j}
    `{!CatIsAbExact f2i f2j} `{!CatIsAbExact fi1 fj1}
    : CatIsAbExact f1i f1j.
  Proof.
    snapply (Build_CatIsAbExact _ _ _ _ _ cpx).
    intros P x11 p.

    elt_lift_exact f2i f2j (fj1 $o x11) x20 lx20 using clear sq4.
    { rewrite_with_assoc sq4^$.
      lhs' napply (_ $@L p).
      apply postcomp_zero. }

    elt_lift_epic fj0 x20 x10 lx10.

    elt_lift_exact fi1 fj1 (x11 - (f1i $o x10)) x01 lx01 using clear sq3 lx10 lx20 x20.
    { lhs' napply postcomp_op_inv.
      apply inverse_r_homotopy_0gpd.
      rewrite_with_assoc sq3.
      rhs' napply (_ $@L lx10).
      exact lx20^$. }

    elt_lift_exact f0i f0j x01 x00 lx00 using clear sq2 p cpx.
    { apply (ismonic' fi2).
      rewrite_with_assoc sq2.
      lhs' napply (_ $@L lx01).
      lhs' napply postcomp_op_inv.
      rewrite p.
      rewrite cat_assoc_opp.
      rewrite cpx.
      rewrite precomp_zero.
      apply inverse_r_0gpd. }

    provide_lift ((fi0 $o x00) + x10).
    lhs' napply postcomp_op.
    rewrite_with_assoc sq1^$.
    rewrite lx00.
    rewrite lx01.
    lhs' napply assoc_0gpd.
    rewrite inverse_l_0gpd.
    napply mon_unit_r_0gpd.
  Defined.

  Definition middle_three_by_three_epi `{!Epic f0j} `{!Epic f2j}
    `{!Epic fj1} `{!CatIsAbExact fi2 fj2}
    : Epic f1j.
  Proof.
    clear sq1 sq3.
    apply epic_elt_lift; intros P x12.

    elt_lift_epic (f2j $o fj1) (fj2 $o x12) x11 lx11.

    elt_lift_exact fi2 fj2 (x12 - (f1j $o x11)) x02 lx02 using clear sq4 lx11.
    { lhs' napply postcomp_op_inv.
      apply inverse_r_homotopy_0gpd.
      rhs_V' napply cat_assoc.
      rhs' napply (sq4 $@R _).
      exact lx11^$. }

    elt_lift_epic f0j x02 x01 lx01.

    provide_lift ((fi1 $o x01) + x11).
    lhs' napply postcomp_op.
    rewrite_with_assoc sq2^$.
    rewrite lx01.
    rewrite lx02.
    lhs' napply assoc_0gpd.
    rewrite inverse_l_0gpd.
    apply mon_unit_r_0gpd.
  Defined.

End ThreeByThree.

(** ** The spider lemma *)

Section Spider.

  Context {A : Type} `{IsAbEpiStable A}.

  (** Given a diagram
<<
    A1 -> A2
      \   ^
       v /
        X
       ^ \
      /   v
    B1 -> B2
>>
  where the diagonals are exact, if the map [B1 $-> B2] is mono/epi, so is the map [A1 $-> A2]. *)

  Context {A1 A2 X B1 B2 : A} (a : A1 $-> A2) (ax : A1 $-> X)
    (xa : X $-> A2) (b : B1 $-> B2) (bx : B1 $-> X) (xb : X $-> B2)
    {tr1 : xa $o ax $== a} {tr2 : xb $o bx $== b}
    `{!Monic ax} `{!CatIsAbExact ax xb} `{!Epic xb}
    `{!Monic bx} `{!CatIsAbExact bx xa} `{!Epic xa}.

  Definition spider_mono `{!Monic b} : Monic a.
  Proof.
    apply monic_via_elt_isemb_ab; intros P a1 p.
    apply (ismonic' ax a1).

    elt_lift_exact bx xa (ax $o a1) b1 lb1 using clear tr1 p.
    { lhs' napply cat_assoc_opp.
      lhs' napply (tr1 $@R _).
      exact p. }

    assert (b1_is_zero : b1 $== 0).
    { apply (ismonic' b).
      lhs_V' napply (tr2 $@R _).
      rewrite_with_assoc_opp lb1.
      lhs' apply (isabcomplex $@R _).
      apply precomp_zero. }

    lhs_V' napply lb1.
    lhs' napply (_ $@L b1_is_zero).
    apply postcomp_zero.
  Defined.

  Definition spider_epi `{!Epic b} : Epic a.
  Proof.
    apply epic_elt_lift; intros P a2.

    elt_lift_epic xa a2 x lx.

    elt_lift_epic b (xb $o x) b1 lb1.

    elt_lift_exact ax xb (x - (bx $o b1)) a1 la1 using clear tr2 lb1.
    { rewrite postcomp_op_inv.
      rewrite <- cat_assoc, tr2.
      rewrite <- lb1.
      apply inverse_r_0gpd. }

    provide_lift a1.
    lhs_V' napply (tr1 $@R _).
    lhs' napply cat_assoc.
    lhs' napply (_ $@L la1).
    rewrite postcomp_op_inv.
    rewrite <- cat_assoc, isabcomplex.
    rewrite precomp_zero.
    rewrite mon_unit_l_inv_0gpd.
    exact lx.
  Defined.

End Spider.

(** ** The incomplete snail lemma *)

Section Snail.

  Context {A : Type} `{IsAbEpiStable A}.

  (** Here we will prove the incomplete snail lemma.  The complete snail lemma was developed as a more general analogue of the snake lemma that holds in certain non-abelian contexts.  The incomplete snail lemma is a lemma that one can use to prove the complete snail lemma.  In fact, if the incomplete snail lemma is true and if every kernel map in the category has a cokernel, then the complete snail lemma is true.  See Janelidze, Vitale; The snail lemma in a pointed regular category. *)

  Context {W1 W2 X Y1 Y2 Z : A} (w : W1 $-> W2) (wx : W1 $-> X)
    (wz : W2 $-> Z) (xw : X $-> W2) (xy : X $-> Y2)
    (y : Y1 $-> Y2) (yx : Y1 $-> X) (yz : Y2 $-> Z)
    (tr1 :  w $== xw $o wx) (tr2 : y $== xy $o yx)
    (sq1 : wz $o xw $== yz $o xy).

  (** We assume that we have a diagram of shape:
<<
        W1 = = W1
        |      |
        |      |
        v      v
  Y1 -> X ---> W2 ---> 0
  ||    |      |
  ||    |      |
  ||    v      v
  Y1 -> Y2 --> Z
>>
  Each row and the first column is assumed to be exact.  We will show that the last column is exact as well. *)

  Definition incomplete_snail `{!Epic xw} `{!CatIsAbExact wx xy}
    `{!CatIsAbExact yx xw} `{!CatIsAbExact y yz}
    : CatIsAbExact w wz.
  Proof.
    snapply Build_CatIsAbExact.
    - lhs' napply (_ $@L tr1).
      rewrite_with_assoc sq1.
      lhs' apply (_ $@L isabcomplex).
      apply postcomp_zero.
    - intros P w2 p.
      elt_lift_epic xw w2 x lx.

      elt_lift_exact y yz (xy $o x) y1 ly1 using clear sq1 p.
      { rewrite_with_assoc sq1^$.
        lhs' napply (_ $@L lx).
        exact p. }

      elt_lift_exact wx xy (x - yx $o y1) w1 lw1 using clear tr2 ly1.
      { lhs' rapply postcomp_op_inv.
        rewrite <- cat_assoc, <- tr2.
        rewrite ly1.
        apply inverse_r_0gpd. }

      provide_lift w1.
      lhs' napply (tr1 $@R _).
      lhs' napply cat_assoc.
      lhs' napply (_ $@L lw1).
      lhs' rapply postcomp_op_inv.
      rewrite <- cat_assoc, isabcomplex.
      rewrite precomp_zero.
      lhs' napply mon_unit_l_inv_0gpd.
      exact lx.
  Defined.

End Snail.

(** ** Two-by-three lemmas *)

Section TwoByThree.

  Context {A : Type} `{IsAbEpiStable A}.

  (** Here we will show how to transport the structure of an exact sequence across a morphism of composable pairs satisfying some properties. *)

  Context {A1 A2 B1 B2 C1 C2 : A}
    (f1 : A1 $-> B1) (g1 : B1 $-> C1)
    (f2 : A2 $-> B2) (g2 : B2 $-> C2)
    (a : A1 $-> A2) (b : B1 $-> B2) (c : C1 $-> C2)
    (sq1 : b $o f1 $== f2 $o a) (sq2 : c $o g1 $== g2 $o b)
    `{!Epic a} `{!Monic c}.

  (** In general, the diagrams will be of the shape:
<<
  A1 ---> B1 ---> C1
  |        |       v
  |        |       |
  v        |       |
  v        v       v
  A2 ---> B2 ---> C2
>>
  In particular the map [A1 $-> A2] is epi and the map [C1 $-> C2] is mono. *)

  (** If the middle map [B1 $-> B2] is also epi and the upper morphisms [A1 $-> B1] and [B1 $-> C1] form an exact sequence, then the lower morphisms [A2 $-> B2] and [B2 $-> C2] form an exact sequence. *)
  Definition two_by_three_epi `{!Epic b} `{!CatIsAbExact f1 g1}
    : CatIsAbExact f2 g2.
  Proof.
    napply Build_CatIsAbExact.
    - apply (isepic a).
      rhs' napply precomp_zero.
      rewrite_with_assoc_opp sq1^$.
      lhs_V' napply (sq2 $@R _).
      lhs' napply cat_assoc.
      lhs' apply (_ $@L isabcomplex).
      apply postcomp_zero.
    - intros P b2 p.

      elt_lift_epic b b2 b1 lb1.

      elt_lift_exact f1 g1 b1 a1 la1 using clear sq2.
      { apply (ismonic' c).
        rewrite_with_assoc sq2.
        by lhs' napply (_ $@L lb1). }

      provide_lift (a $o a1).
      rewrite_with_assoc sq1^$.
      by lhs' napply (_ $@L la1).
  Defined.

  (** If the middle map [B1 $-> B2] is now mono and the lower morphisms [A2 $-> B2] and [B2 $-> C2] form an exact sequence, then the upper morphisms [A1 $-> B1] and [B1 $-> C1] form an exact sequence. *)
  Definition two_by_three_mono `{!Monic b} `{!CatIsAbExact f2 g2}
    : CatIsAbExact f1 g1.
  Proof.
    napply Build_CatIsAbExact.
    - apply (ismonic' c).
      rewrite_with_assoc sq2.
      lhs' napply (_ $@L sq1).
      lhs_V' napply cat_assoc.
      lhs' apply (isabcomplex $@R _).
      apply precomp_zero.
    - intros P b1 p.

      elt_lift_exact f2 g2 (b $o b1) a2 la2 using clear sq2 p.
      { rewrite_with_assoc sq2^$.
        lhs' napply (_ $@L p).
        apply postcomp_zero. }

      elt_lift_epic a a2 a1 la1.

      provide_lift a1.
      apply (ismonic b).
      rewrite_with_assoc sq1.
      lhs' napply (_ $@L la1).
      exact la2.
  Defined.

End TwoByThree.

(** ** The diamond lemma *)

Section Diamond.

  Context {Ae : Type} `{H0 : Is1Cat Ae} `{!IsAbEpiStable Ae}.

  Context {A B C D E F G H : Ae}
    (ab : A $-> B) (bc : B $-> C) (cd : C $-> D) (de : D $-> E)
    (ah : A $-> H) (hg : H $-> G) (gf : G $-> F) (fe : F $-> E)
    (hb : H $-> B) (bd : B $-> D) (hf : H $-> F) (fd : F $-> D)
    (tru : ab $== hb $o ah) (trr : bd $== cd $o bc)
    (trd : fe $== de $o fd) (trl : hf $== gf $o hg)
    (sq : bd $o hb $== fd $o hf)
    `{!CatIsAbExact ab bc} `{!CatIsAbExact cd de}
    `{!CatIsAbExact ah hg} `{!CatIsAbExact gf fe}
    `{!Epic hg} `{!Monic cd}.

  (** The diagram has the shape:
<<
          A
         / \
        /   \
       v     v
      H ----> B
     /|       |\
    / |       | \
   v  |       |  v
  G   |       |   C
   \  |       |  /
    \ |       | /
     vv       vv
      F ----> D
       \     /
        \   /
         v v
          E
>>
  where each diagonal is assumed to be exact. *)

  (** If the map [H $-> B] is mono, then so is [G $-> F]. *)
  Definition diamond_lemma_mono `{!Monic hb} : Monic gf.
  Proof.
    clear trd.
    apply monic_via_elt_isemb_ab.
    intros P g p.

    elt_lift_epic hg g h lh.

    elt_lift_exact ab bc (hb $o h) a la using clear trr trl p sq.
    { apply (ismonic' cd).
      lhs_V' napply cat_assoc.
      lhs_V' napply (trr $@R _).
      rewrite_with_assoc sq.
      rewrite trl.
      rewrite cat_assoc, lh, p.
      apply postcomp_zero. }

    assert (la' : ah $o a $== h).
    { apply (ismonic hb).
      lhs_V' napply cat_assoc.
      rewrite <- tru.
      exact la. }

    lhs_V' napply lh.
    lhs_V' napply (_ $@L la').
    lhs' napply cat_assoc_opp.
    lhs' rapply (isabcomplex $@R _).
    apply precomp_zero.
  Defined.

  (** If the map [F $-> D] is epi, then so is the map [B $-> C]. *)
  Definition diamond_lemma_epi `{!Epic fd} : Epic bc.
  Proof.
    clear tru.
    apply epic_elt_lift; intros P c.

    elt_lift_epic fd (cd $o c) f lf.

    elt_lift_exact gf fe f g lg using clear trd.
    { lhs' napply (trd $@R f).
      lhs' napply cat_assoc.
      lhs' napply (de $@L lf).
      lhs_V' napply cat_assoc.
      lhs' rapply (isabcomplex $@R c).
      napply precomp_zero. }

    elt_lift_epic hg g h lh.

    provide_lift (hb $o h).
    apply (ismonic cd).
    lhs' napply cat_assoc_opp.
    lhs_V' napply (trr $@R _).
    lhs' napply cat_assoc_opp.
    lhs' napply (sq $@R _).
    lhs' napply cat_assoc.
    rewrite trl.
    by rewrite cat_assoc, lh, lg, lf.
  Defined.

End Diamond.

(** ** The baby dragon lemmas *)

Section Baby_Dragon.

  (** The dragon lemmas involve diagrams which in general have the same shape, but can be elongated or shortened.  For example, the case [n = 2] below has shape:
<<
          top 0     top 1    top 2
          /   \     /  \     /  \
         /     \   /    \   /    \
        v       v v      v v      v
       mid 0   mid 1    mid 2    mid 3
         \     /   \     /  \     /
          \   /     \   /    \   /
           v v       v v      v v
          bot 0     bot 1    bot 2
>>
  where all the diagonal sequences are exact, the maps [top 0 $-> middle 0], [middle 1 $-> bot 1], and [middle 2 $-> bot 2] are epic, and the maps [top 0 $-> middle 1], [top 1 $-> middle 2], and [middle 3 $-> bot 2] are mono.

  For general [n], the diagram will have a similar shape, with [n + 1] objects in the top and bottom rows. *)

  (** The baby dragon lemma has an epi statement and a mono statement.  We shall first prove the epi part, then the mono part.  To do the epi part, we will show that if the map [middle 0 $-> bot 0] is epi, then so is [top 2 $-> middle 3].  Due to the lack of symmetry at the edges of the diagram, we need to prove a more general statement first to make the induction go through. *)

  Context {A : Type} `{IsAbEpiStable A}.

  (** We make a datatype for the above diagram with [n+1] squares. *)
  Record BabyDragon {n : nat} := {
    top : Fin n.+1 -> A;
    mid : Fin n.+2 -> A;
    bot : Fin n.+1 -> A;
    top_l (k : Fin n.+1) : top k $-> mid (fin_incl k);
    top_r (k : Fin n.+1) : top k $-> mid (fsucc k);
    bot_l (k : Fin n.+1) : mid (fin_incl k) $-> bot k;
    bot_r (k : Fin n.+1) : mid (fsucc k) $-> bot k;
    sq (k : Fin n.+1) : (bot_l k) $o (top_l k) $== (bot_r k) $o (top_r k);
    exact_r (k : Fin n) :: CatIsAbExact (top_r (fin_incl k)) (bot_l (fsucc k));
    exact_l (k : Fin n) :: CatIsAbExact (top_l (fsucc k)) (bot_r (fin_incl k))
  }.
  (** Note that [bot_l k] refers to the bottom-left map in the [k]th square, which points down and to the *right*. *)

  Arguments BabyDragon : clear implicits.

  (** In order to make an inductive argument, we need two ways of truncating a diagram.  This one drops the right-hand square, keeping the left [n+1] squares. *)
  Definition baby_dragon_trunc_left (n : nat) (D : BabyDragon n.+1)
    : BabyDragon n.
  Proof.
    snapply Build_BabyDragon; intro k; cbn.
    - exact (top D (fin_incl k)).
    - exact (mid D (fin_incl k)).
    - exact (bot D (fin_incl k)).
    - exact (top_l _ (fin_incl k)).
    - exact (top_r _ (fin_incl k)).
    - exact (bot_l _ (fin_incl k)).
    - exact (bot_r _ (fin_incl k)).
    - exact (sq _ (fin_incl k)).
    - exact (exact_r _ (fin_incl k)).
    - exact (exact_l _ (fin_incl k)).
  Defined.

  (** This one drops the left-hand square, keeping the right [n+1] squares. *)
  Definition baby_dragon_trunc_right (n : nat) (D : BabyDragon n.+1)
    : BabyDragon n.
  Proof.
    snapply Build_BabyDragon; intro k; cbn.
    - exact (top D (fsucc k)).
    - exact (mid D (fsucc k)).
    - exact (bot D (fsucc k)).
    - exact (top_l _ (fsucc k)).
    - exact (top_r _ (fsucc k)).
    - exact (bot_l _ (fsucc k)).
    - exact (bot_r _ (fsucc k)).
    - exact (sq _ (fsucc k)).
    - exact (exact_r _ (fsucc k)).
    - exact (exact_l _ (fsucc k)).
  Defined.

  (** This is a helper lemma that can be proved by induction.  The epi part of the dragon lemma follows immediately. *)
  Local Instance baby_dragon_aux_left (n : nat) (D : BabyDragon n)
    `{!forall k : Fin (n.+1), Epic (bot_l D k)} `{!Epic (top_l D fin_zero)}
    : Epic (bot_r D fin_last $o top_r D fin_last).
  Proof.
    induction n.
    - rapply (epic_homotopic _ _ (sq _ fin_zero)).
    - apply epic_elt_lift; intros P b_last.

      elt_lift_epic (bot_l D fin_last) b_last m_last lm_last.

      pose (D' := baby_dragon_trunc_left n D).
      elt_lift_epic (bot_r D' fin_last $o top_r D' fin_last)
                    (bot_r D' fin_last $o m_last) t_penult lt_penult.
      unfold D' in t_penult, lt_penult; clear D'.

      elt_lift_exact (top_l D (fsucc fin_last)) (bot_r D (fin_incl fin_last))
        (m_last - top_r D (fin_incl fin_last) $o t_penult) t_last lt_last
        using clear IHn lt_penult.
      { lhs' napply postcomp_op_inv.
        rewrite <- cat_assoc.
        rewrite <- lt_penult.
        apply inverse_r_0gpd. }

      provide_lift t_last.
      lhs_V' napply (sq D fin_last $@R _).
      lhs' napply cat_assoc.
      lhs' napply (_ $@L lt_last).
      rewrite postcomp_op_inv.
      rewrite <- cat_assoc.
      rewrite isabcomplex.
      rewrite precomp_zero.
      rewrite mon_unit_l_inv_0gpd.
      exact lm_last.
  Defined.

  (** The epi form of the baby dragon lemma states that the map [top fin_last $-> middle fin_last] is epic. *)
  Definition baby_dragon_epi (n : nat) (D : BabyDragon n)
    `{!forall k : Fin (n.+1), Epic (bot_l D k)}
    `{!Epic (top_l D fin_zero)} `{!Monic (bot_r D fin_last)}
    : Epic (top_r D fin_last)
    := epic_cancel_monic _ _.

  (** This is a helper lemma that can be proved by induction.  The mono part of the dragon lemma follows immediately. *)
  Local Instance baby_dragon_aux_right (n : nat) (D : BabyDragon n)
    `{!forall k : Fin (n.+1), Monic (top_r D k)}
    `{!Monic (bot_r D fin_last)}
    : Monic (bot_l D fin_zero $o top_l D fin_zero).
  Proof.
    induction n.
    - rapply (monic_homotopic _ _ (sq _ _)^$).
    - apply monic_via_elt_isemb_ab; intros P t zero_t.

      elt_lift_exact (top_l D (fsucc fin_zero)) (bot_r D fin_zero)
        (top_r D fin_zero $o t) t' lift_t'
        using clear zero_t.
      { lhs' napply cat_assoc_opp.
        lhs_V' napply (sq D fin_zero $@R _).
        exact zero_t. }

      rapply (ismonic' (top_r D fin_zero)).
      lhs_V' napply lift_t'.
      rhs_V' napply (postcomp_zero (top_l D (fsucc fin_zero))).
      apply cat_postwhisker.
      set (D' := baby_dragon_trunc_right n D).
      rapply (ismonic' (bot_r D' fin_zero $o top_r D' fin_zero)).
      { rapply (monic_homotopic _ _ (sq _ _)). }
      lhs_V' napply (sq D' fin_zero $@R _).
      unfold D'; clear D'.
      rewrite_with_assoc_opp lift_t'.
      lhs' apply (isabcomplex $@R _).
      apply precomp_zero.
  Defined.

  (** The mono form of the baby dragon lemma states that the map [middle fin_zero $-> bot fin_zero] is monic. *)
  Definition baby_dragon_mono (n : nat) (D : BabyDragon n)
    `{!forall k : Fin (n.+1), Monic (top_r D k)}
    `{!Monic (bot_r D fin_last)} `{!Epic (top_l D fin_zero)}
    : Monic (bot_l D fin_zero)
    := monic_cancel_epic _ _.

End Baby_Dragon.
