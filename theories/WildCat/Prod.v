(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.
Require Import Types.Prod.

(** * Product categories *)

(** Products preserve (0,1)-categories. *)
Global Instance isgraph_prod A B `{IsGraph A} `{IsGraph B}
  : IsGraph (A * B)
  := Build_IsGraph (A * B) (fun x y => (fst x $-> fst y) * (snd x $-> snd y)).

Global Instance is01cat_prod A B `{Is01Cat A} `{Is01Cat B}
  : Is01Cat (A * B).
Proof.
  econstructor.
  - intros [a b]; exact (Id a, Id b).
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2]; cbn in *.
    exact (f1 $o f2 , g1 $o g2).
Defined.

Global Instance is0gpd_prod A B `{Is0Gpd A} `{Is0Gpd B}
 : Is0Gpd (A * B).
Proof.
  srapply Build_Is0Gpd.
  intros [x1 x2] [y1 y2] [f1 f2].
  cbn in *.
  exact ( (f1^$, f2^$) ).
Defined.

Global Instance is2graph_prod A B `{Is2Graph A, Is2Graph B}
  : Is2Graph (A * B).
Proof.
  intros [x1 x2] [y1 y2].
  rapply isgraph_prod.
Defined.

Global Instance is1cat_prod A B `{Is1Cat A} `{Is1Cat B}
  : Is1Cat (A * B).
Proof.
  srapply (Build_Is1Cat).
  - intros [x1 x2] [y1 y2] [z1 z2] [h1 h2].
    srapply Build_Is0Functor.
    intros [f1 f2] [g1 g2] [p1 p2]; cbn in *.
    exact ( h1 $@L p1 , h2 $@L p2 ).
  - intros [x1 x2] [y1 y2] [z1 z2] [h1 h2].
    srapply Build_Is0Functor.
    intros [f1 f2] [g1 g2] [p1 p2]; cbn in *.
    exact ( p1 $@R h1 , p2 $@R h2 ).
  - intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] [f1 f2] [g1 g2] [h1 h2].
    cbn in *.
    exact(cat_assoc f1 g1 h1, cat_assoc f2 g2 h2).
  - intros [a1 a2] [b1 b2] [f1 f2].
    cbn in *.
    exact (cat_idl _, cat_idl _).
  - intros [a1 a2] [b1 b2] [g1 g2].
    cbn in *.
    exact (cat_idr _, cat_idr _).
Defined.

(** Product categories inherit equivalences *)

Global Instance hasequivs_prod A B `{HasEquivs A} `{HasEquivs B}
  : HasEquivs (A * B).
Proof.
  srefine (Build_HasEquivs (A * B) _ _ _ _
             (fun a b => (fst a $<~> fst b) * (snd a $<~> snd b))
             _ _ _ _ _ _ _ _ _).
  1:intros a b f; exact (CatIsEquiv (fst f) * CatIsEquiv (snd f)).
  all:cbn; intros a b f.
  - split; [ exact (fst f) | exact (snd f) ].
  - split; exact _.
  - intros [fe1 fe2]; split.
    + by rapply (Build_CatEquiv (fst f)).
    + by rapply (Build_CatEquiv (snd f)).
  - intros [fe1 fe2]; cbn; split; apply cate_buildequiv_fun.
  - split; [ exact ((fst f)^-1$) | exact ((snd f)^-1$) ].
  - split; apply cate_issect.
  - split; apply cate_isretr.
  - intros g r s; split.
    + exact (catie_adjointify (fst f) (fst g) (fst r) (fst s)).
    + exact (catie_adjointify (snd f) (snd g) (snd r) (snd s)).
Defined.

Global Instance isequivs_prod A B `{HasEquivs A} `{HasEquivs B}
       {a1 a2 : A} {b1 b2 : B} {f : a1 $-> a2} {g : b1 $-> b2}
       {ef : CatIsEquiv f} {eg : CatIsEquiv g}
  : @CatIsEquiv (A*B) _ _ _ _ _ (a1,b1) (a2,b2) (f,g) := (ef,eg).

(** ** Product functors *)

Global Instance is0functor_prod_functor {A B C D : Type}
  (F : A -> B) (G : C -> D) `{Is0Functor _ _ F, Is0Functor _ _ G}
  : Is0Functor (functor_prod F G).
Proof.
  apply Build_Is0Functor.
  intros [a1 c1] [a2 c2] [f g].
  exact (fmap F f , fmap G g).
Defined.

Global Instance is1functor_prod_functor {A B C D : Type}
  (F : A -> B) (G : C -> D) `{Is1Functor _ _ F, Is1Functor _ _ G}
  : Is1Functor (functor_prod F G).
Proof.
  apply Build_Is1Functor.
  - intros [a1 c1] [a2 c2] [f1 g1] [f2 g2] [p q].
    exact (fmap2 F p , fmap2 G q).
  - intros [a c].
    exact (fmap_id F a, fmap_id G c).
  - intros [a1 c1] [a2 c2] [a3 c3] [f1 g1] [f2 g2].
    exact (fmap_comp F f1 f2 , fmap_comp G g1 g2).
Defined.

Global Instance is0functor_fst {A B : Type} `{!IsGraph A, !IsGraph B}
  : Is0Functor (@fst A B).
Proof.
  apply Build_Is0Functor.
  intros ? ? f; exact (fst f).
Defined.

Global Instance is0functor_snd {A B : Type} `{!IsGraph A, !IsGraph B}
  : Is0Functor (@snd A B).
Proof.
  apply Build_Is0Functor.
  intros ? ? f; exact (snd f).
Defined.

(** Swap functor *)

Global Instance is0functor_equiv_prod_symm {A B : Type} `{IsGraph A, IsGraph B}
  : Is0Functor (equiv_prod_symm A B).
Proof.
  snrapply Build_Is0Functor.
  intros a b.
  apply equiv_prod_symm.
Defined.

Global Instance is1functor_equiv_prod_symm {A B : Type} `{Is1Cat A, Is1Cat B}
  : Is1Functor (equiv_prod_symm A B).
Proof.
  snrapply Build_Is1Functor.
  - intros a b f g.
    apply equiv_prod_symm.
  - intros a.
    reflexivity.
  - reflexivity.
Defined.

(** Inclusions into a product category are functorial. *)

Global Instance is0functor_prod_include10 {A B : Type} `{IsGraph A, Is01Cat B}
  (b : B)
  : Is0Functor (fun a : A => (a, b)).
Proof.
  nrapply Build_Is0Functor.
  intros a c f.
  exact (f, Id b).
Defined.

Global Instance is1functor_prod_include10 {A B : Type} `{Is1Cat A, Is1Cat B}
  (b : B)
  : Is1Functor (fun a : A => (a, b)).
Proof.
  nrapply Build_Is1Functor.
  - intros a c f g p.
    exact (p, Id _).
  - intros a; reflexivity.
  - intros a c d f g.
    exact (Id _, (cat_idl _)^$).
Defined.

Global Instance is0functor_prod_include01 {A B : Type} `{Is01Cat A, IsGraph B}
  (a : A)
  : Is0Functor (fun b : B => (a, b)).
Proof.
  nrapply Build_Is0Functor.
  intros b c f.
  exact (Id a, f).
Defined.

Global Instance is1functor_prod_include01 {A B : Type} `{Is1Cat A, Is1Cat B}
  (a : A)
  : Is1Functor (fun b : B => (a, b)).
Proof.
  nrapply Build_Is1Functor.
  - intros b c f g p.
    exact (Id _, p).
  - intros b; reflexivity.
  - intros b c d f g.
    exact ((cat_idl _)^$, Id _).
Defined.

(** Functors from a product category are functorial in each argument *)

Global Instance is0functor_functor_uncurried01 {A B C : Type}
  `{Is01Cat A, IsGraph B, IsGraph C}
  (F : A * B -> C) `{!Is0Functor F} (a : A)
  : Is0Functor (fun b => F (a, b))
  := is0functor_compose (fun b => (a, b)) F.

Global Instance is1functor_functor_uncurried01 {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A * B -> C) `{!Is0Functor F, !Is1Functor F} (a : A)
  : Is1Functor (fun b => F (a, b))
  := is1functor_compose (fun b => (a, b)) F.

Global Instance is0functor_functor_uncurried10 {A B C : Type}
  `{IsGraph A, Is01Cat B, IsGraph C}
  (F : A * B -> C) `{!Is0Functor F} (b : B)
  : Is0Functor (fun a => F (a, b))
  := is0functor_compose (fun a => (a, b)) F.

Global Instance is1functor_functor_uncurried10 {A B C : Type}
  `{Is1Cat A, Is1Cat B, Is1Cat C}
  (F : A * B -> C) `{!Is0Functor F, !Is1Functor F} (b : B)
  : Is1Functor (fun a => F (a, b))
  := is1functor_compose (fun a => (a, b)) F.

(** Applies a two variable functor via uncurrying. Note that the precondition on [C] is slightly weaker than that of [Bifunctor.fmap11]. *)
Definition fmap11_uncurry {A B C : Type} `{IsGraph A, IsGraph B, IsGraph C}
  (F : A -> B -> C) {H2 : Is0Functor (uncurry F)}
  {a0 a1 : A} (f : a0 $-> a1) {b0 b1 : B} (g : b0 $-> b1)
  : F a0 b0 $-> F a1 b1
  := @fmap _ _ _ _ (uncurry F) H2 (a0, b0) (a1, b1) (f, g).
