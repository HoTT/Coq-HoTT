Require Import Basics Types.Forall Types.Paths WildCat.
Require Import WildCat.Bifunctor WildCat.TwoOneCat.
Require Import Spaces.List Classes.implementations.list.

(** The free monoidal category generated by a type. This is in fact a groupoid, so we axiomatize it as such. *)

Inductive FMC {X : Type} : Type :=
(** Elements of the generating set *)
| el : X -> FMC
(** Tensor unit *)
| unit : FMC
(** Tensor product *)
| tensor : FMC -> FMC -> FMC
.

Arguments FMC X : clear implicits.

Inductive HomFMC {X : Type} : FMC X -> FMC X -> Type :=
(** Identity morphism *)
| id x : HomFMC x x
(** Composition of morphisms *)
| comp {x y z} : HomFMC y z ->  HomFMC x y -> HomFMC x z
(** Inversion of morphisms *)
| rev {x y} : HomFMC x y -> HomFMC y x
(** Left unitor *)
| left_unitor x : HomFMC (tensor unit x) x
(** Right unitor *)
| right_unitor x : HomFMC (tensor x unit) x
(** Associator *)
| associator x y z : HomFMC (tensor x (tensor y z)) (tensor (tensor x y) z) 
(** Functoriality of tensor *)
| tensor2 {x x' y y'} : HomFMC x y -> HomFMC x' y' -> HomFMC (tensor x x') (tensor y y')
.

Inductive Hom2FMC {X : Type} : forall {a b : FMC X}, HomFMC a b -> HomFMC a b -> Type :=
(** Identity 2-morphism *)
| id2 {x y} (f : HomFMC x y) : Hom2FMC f f
(** Composition of 2-morphisms *)
| comp2 {x y} {f g h : HomFMC x y} : Hom2FMC g h -> Hom2FMC f g  -> Hom2FMC f h
(** Inversion of 2-morphisms *)
| rev2 {x y} {f g : HomFMC x y} : Hom2FMC f g -> Hom2FMC g f
(** Left whiskering *)
| wl {x y z} (g : HomFMC y z) {f h : HomFMC x y}
  : Hom2FMC f h -> Hom2FMC (comp g f) (comp g h)
(** Right whiskering *)
| wr {x y z}  (f : HomFMC x y) {g h : HomFMC y z}
  : Hom2FMC g h -> Hom2FMC (comp g f) (comp h f)
(** Associativity of composition of morphsisms *)
| associator2 {w x y z} {f : HomFMC w x} {g : HomFMC x y} (h : HomFMC y z)
  : Hom2FMC (comp (comp h g) f) (comp h (comp g f))
(** Left identity for composition of morphisms *)
| left_unitor2 {x y} {f : HomFMC x y} : Hom2FMC (comp (id _) f) f
(** Right identity for composition of morphisms *)
| right_unitor2 {x y} {f : HomFMC x y} : Hom2FMC (comp f (id _)) f
(** Left inversion law for composition of morphisms *)
| left_invertor2 {x y} (f : HomFMC x y) : Hom2FMC (comp (rev f) f) (id _)
(** Right inversion law for composition of morphisms *)
| right_invertor2 {x y} (f : HomFMC x y) : Hom2FMC (comp f (rev f)) (id _)
(** Triangle identity *)
| triangle {x y}
  : Hom2FMC
    (tensor2 (id x) (left_unitor y))
    (comp (tensor2 (right_unitor x) (id y)) (associator x unit y))
(** Pentagon identity *)
| pentagon {w x y z}
  : Hom2FMC
    (comp (associator (tensor w x) y z) (associator w x (tensor y z)))
    (comp
      (comp (tensor2 (associator w x y) (id z)) (associator w (tensor x y) z))
      (tensor2 (id w) (associator x y z)))
(** 2-functioriality of tensor *)
| tensor3 {x x' y y'} {f g : HomFMC x y} {f' g' : HomFMC x' y'}
  : Hom2FMC f g -> Hom2FMC f' g' -> Hom2FMC (tensor2 f f') (tensor2 g g')
(** Tensor functor preserves identity morphism *)
| tensor2_id {x y} : Hom2FMC (tensor2 (id x) (id y)) (id (tensor x y))
(** Tensor functor preserves composition of morphisms *)
| tensor2_comp {x x' y y' z z'} {f : HomFMC x y} {f' : HomFMC x' y'}
  {g : HomFMC y z} {g' : HomFMC y' z'}
  : Hom2FMC (tensor2 (comp g f) (comp g' f')) (comp (tensor2 g g') (tensor2 f f'))
(** Naturality of left unitor *)
| isnat_left_unitor x y f
  : Hom2FMC (comp (left_unitor y) (tensor2 (id unit) f)) (comp f (left_unitor x))
(** Naturality of right unitor *)
| isnat_right_unitor x y f
  : Hom2FMC (comp (right_unitor y) (tensor2 f (id unit))) (comp f (right_unitor x))
(** Naturality of associator in left variable *)
| isnat_l_associator w x y z f
  : Hom2FMC
    (comp (associator y w x) (tensor2 f (id (tensor w x))))
    (comp (tensor2 (tensor2 f (id w)) (id x)) (associator z w x))
(** Naturality of associator in middle variable *)
| isnat_m_associator w x y z f
  : Hom2FMC
    (comp (associator w y x) (tensor2 (id w) (tensor2 f (id x))))
    (comp (tensor2 (tensor2 (id w) f) (id x)) (associator w z x))
(** Naturality of associator in right variable *)
|  isnat_r_associator w x y z f
  : Hom2FMC
    (comp (associator w x y) (tensor2 (id w) (tensor2 (id x) f)))
    (comp (tensor2 (id (tensor w x)) f) (associator w x z))
.

Global Instance isgraph_FMC {X : Type} : IsGraph (FMC X)
  := {| Hom := HomFMC; |}.

Global Instance is01cat_FMC {X : Type} : Is01Cat (FMC X)
  := {| Id := @id _; cat_comp := @comp _ |}.

Global Instance is2graph_FMC {X : Type} : Is2Graph (FMC X)
  := fun x y => {| Hom := Hom2FMC |}.

Global Instance is1cat_FMC {X : Type} : Is1Cat (FMC X).
Proof.
  snrapply Build_Is1Cat.
  - intros x y; snrapply Build_Is01Cat; revert X x y.
    + exact @id2.
    + exact @comp2.
  - intros x y; snrapply Build_Is0Gpd; revert X x y.
    exact @rev2.
  - intros x y z g; snrapply Build_Is0Functor; revert X x y z g.
    exact @wl.
  - intros x y z f; snrapply Build_Is0Functor; revert X x y z f.
    exact @wr.
  - revert X.
    exact @associator2.
  - revert X.
    exact @left_unitor2.
  - revert X.
    exact @right_unitor2.
Defined.

Global Instance is0gpd_FMC {X : Type} : Is0Gpd (FMC X).
Proof.
  snrapply Build_Is0Gpd; revert X.
  exact @rev.
Defined.

Global Instance is1gpd_FMC {X : Type} : Is1Gpd (FMC X).
Proof.
  snrapply Build_Is1Gpd; revert X.
  - exact @left_invertor2.
  - exact @right_invertor2.
Defined.

Global Instance hasequivs_FMC {X : Type} : HasEquivs (FMC X) := hasequivs_1gpd _.

Global Instance is0bifunctor_tensor {X}
  : Is0Bifunctor (@tensor X).
Proof.
  rapply Build_Is0Bifunctor'.
  snrapply Build_Is0Functor.
  intros [w x] [y z] [f g].
  exact (tensor2 f g).
Defined.

Global Instance is1bifunctor_tensor {X}
  : Is1Bifunctor (@tensor X).
Proof.
  snrapply Build_Is1Bifunctor'.
  snrapply Build_Is1Functor.
  - intros [w x] [y z] [f g] [h k] [p q].
    exact (tensor3 p q).
  - intros [w x].
    exact tensor2_id.
  - intros [x x'] [y y'] [z z'] [f f'] [g g'].
    exact tensor2_comp.
Defined.

Global Instance is0functor_tensor' {X y}
  : Is0Functor (flip (@tensor X) y).
Proof.
  snrapply Build_Is0Functor.
  intros x z.
  exact (flip tensor2 (id y)).
Defined.

Definition left_unitor' {X} (x : FMC X)
  : tensor unit x $<~> x.
Proof.
  exact (left_unitor x).
Defined.

Global Instance leftunitor_FMC {X} : LeftUnitor (@tensor X) unit.
Proof.
  snrapply Build_NatEquiv; revert X.
  - exact @left_unitor'.
  - exact @isnat_left_unitor.
Defined.

Definition right_unitor' {X} (x : FMC X)
  : tensor x unit $<~> x.
Proof.
  exact (right_unitor x).
Defined.

Global Instance rightunitor_FMC {X} : RightUnitor (@tensor X) unit.
Proof.
  snrapply Build_NatEquiv; revert X.
  - exact @right_unitor'.
  - exact @isnat_right_unitor.
Defined.

Definition associator' {X} (x y z : FMC X)
  : tensor x (tensor y z) $<~> tensor (tensor x y) z.
Proof.
  exact (associator x y z).
Defined.

Global Instance associator_FMC {X} : Associator (@tensor X).
Proof.
  snrapply Build_Associator.
  1: exact associator'.
  intros [[a b] c] [[a' b'] c'] [[f g] h]; cbn -[Hom] in * |-.
  change (?w $o ?x $== ?y $o ?z) with (Square z w x y).
  snrapply hconcat.
  - exact (associator' a' b' c).
  - cbn -[Square].
    nrapply vconcatR.
    1: nrapply hconcat.
    1: apply isnat_l_associator.
    1: apply isnat_m_associator.
    nrefine (comp2 (tensor2_comp) (tensor3 (id2 _) _)).
    apply rev2.
    apply left_unitor2.
  - apply isnat_r_associator.
Defined.

Global Instance triangleidentity_FMC {X} : TriangleIdentity (@tensor X) unit
  := @triangle X.

Global Instance pentagonidentity_FMC {X} : PentagonIdentity (@tensor X) unit
  := @pentagon X.

Global Instance ismonoidalcat_FMC {X} : IsMonoidal (FMC X) tensor unit := {}.

(** Attempt at normalized free monoidal categories, might be too strict *)

Definition NFMC' (X : Type) := list X $-> list X.

Global Instance isgraph_NFMC' {X : Type} : IsGraph (NFMC' X) := _.
Global Instance is01cat_NFMC' {X : Type} : Is01Cat (NFMC' X) := _.
Global Instance is2graph_NFMC' {X : Type} : Is2Graph (NFMC' X) := _.
Global Instance is1cat_NFMC' {X : Type} : Is1Cat (NFMC' X) := _.
Global Instance is0gpd_NFMC' {X : Type} : Is0Gpd (NFMC' X) := _.
Global Instance is1gpd_NFMC' {X : Type} : Is1Gpd (NFMC' X) := _.
Global Instance hasequivs_NFMC' {X : Type} : HasEquivs (NFMC' X) := hasequivs_1gpd _.

Definition nfmc'_tensor {X : Type} (x y : NFMC' X) : NFMC' X
  := x o y.

Global Instance is0bifunctor_nfmc'_tensor {X : Type}
  : Is0Bifunctor (@nfmc'_tensor X).
Proof.
  rapply Build_Is0Bifunctor'.
  snrapply Build_Is0Functor.
  intros [x x'] [y y'] [f f'].
  exact (f' $@@ f).
Defined.

Global Instance is1bifunctor_nfmc'_tensor {X : Type}
  : Is1Bifunctor (@nfmc'_tensor X).
Proof.
  snrapply Build_Is1Bifunctor'.
  snrapply Build_Is1Functor.
  - simpl.
    intros [x x'] [y y'] [f f'] [g g'] [h h'].
    refine (_ $@@ _).
    + exact (fmap2 (fun x => x $o x') h).
    + exact (fmap2 (fun y' => y $o y') h').
  - intros [x x'].
    reflexivity.
  - intros [x x'] [y y'] [z z'] [f f'] [g g'].
    rapply cat_exchange.
Defined.

Global Instance associator_NFMC' {X : Type} : Associator (fun f g : NFMC' X => f o g).
Proof.
  snrapply Build_Associator.
  1: reflexivity.
  intros [[x y] z] [[x' y'] z'] [[f g] h] l; cbn in * |-.
  simpl.
  apply equiv_p1_1q.
  cbn.
  f_ap.
  - rhs nrapply concat_pp_p.
    apply ap.
    rhs nrapply concat_pp_p.
    apply ap.
    lhs nrapply ap_pp.
    f_ap.
  - apply whiskerL.
    rhs nrapply ap_compose.
    f_ap.
    apply concat_1p.
Defined.

Global Instance leftunitor_NFMC' {X : Type} : LeftUnitor (fun f g : NFMC' X => f o g) idmap.
Proof.
  snrapply Build_NatEquiv.
  - reflexivity.
  - intros x y f l.
    apply equiv_p1_1q.
    lhs nrapply concat_1p.
    apply ap_idmap.
Defined.

Global Instance rightunitor_NFMC' {X : Type} : RightUnitor (fun f g : NFMC' X => f o g) idmap.
Proof.
  snrapply Build_NatEquiv.
  + reflexivity.
  + intros x y f l.
    apply equiv_p1_1q.
    apply concat_p1.
Defined.

Global Instance triangleidentity_NFMC' {X : Type} : TriangleIdentity (fun f g : NFMC' X => f o g) idmap.
Proof.
  hnf; reflexivity.
Defined.

Global Instance pentagonidentity_NFMC' {X : Type} : PentagonIdentity (fun f g : NFMC' X => f o g) idmap.
Proof.
  hnf; reflexivity.
Defined.

(** TODO: This can be generalized to any hom in a (2,1)-category *) 
Global Instance ismonoidal_NFMC' {X : Type}
  : IsMonoidal (NFMC' X) (fun f g => f o g) idmap := {}.

(** *** Normalization functor *)

Import ListNotations.
Local Open Scope list_scope.

Definition interp (X : Type) : FMC X -> NFMC' X.
Proof.
  intros m.
  induction m as [| | a IHa b IHb ].
  + intros xs.
    exact (x :: xs).
  + exact idmap.
  + intros xs.
    exact (IHa (IHb xs)).
Defined.

Global Instance is0functor_interp {X : Type} : Is0Functor (interp X).
Proof.
  snrapply Build_Is0Functor.
  intros x y f.
  induction f as [
    | x y z f IHf g IHg
    | x y f IHf | | |
    | x x' y y' f IHf g IHg ].
  - reflexivity.
  - exact (IHg $@ IHf).
  - exact IHf^$.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact (IHg $@@ IHf).
Defined.

Global Instance is1functor_interp (X : Type) : Is1Functor (interp X).
Proof.
  snrapply Build_Is1Functor.
  - intros x y f g p.
    induction p.
    + reflexivity.
    + exact (IHp2 $@ IHp1).
    + exact IHp^$.
    + intros l.
      specialize (IHp l).
      simpl in IHp |- *.
      destruct IHp.
      reflexivity.
    + intros l.
      specialize (IHp l).
      simpl in IHp |- *.
      destruct IHp.
      reflexivity.
    + intros l.
      apply concat_p_pp.
    + intros l.
      apply concat_p1.
    + intros l.
      apply concat_1p.
    + intros l.
      apply concat_pV.
    + intros l.
      apply concat_Vp.
    + reflexivity.
    + reflexivity.
    + intros l.
      cbn; f_ap; f_ap.
    + reflexivity.
    + simpl.
      rapply cat_exchange.
    + intros l.
      apply equiv_p1_1q.
      lhs nrapply concat_1p.
      apply ap_idmap.
    + intros l.
      apply equiv_p1_1q.
      apply concat_p1.
    + intros l.
      apply equiv_p1_1q.
      apply whiskerR.
      symmetry.
      apply concat_p1.
    + intros l.
      apply equiv_p1_1q.
      apply equiv_1p_q1.
      cbn; lhs nrapply ap_pp.
      apply concat_p1_1p.
    + intros l.
      apply equiv_p1_1q.
      apply whiskerL.
      cbn; lhs nrapply ap_pp.
      lhs nrapply concat_1p.
      symmetry.
      apply ap_compose.
  - reflexivity.
  - reflexivity.
Defined.

Definition NFMC (X : Type) := list X.

Inductive HomNFMC {X : Type} : NFMC X -> NFMC X -> Type :=
| nil_homnfmc : HomNFMC [] []
| cons_homnfmc {x xs y ys} : x = y -> HomNFMC xs ys -> HomNFMC (x :: xs) (y :: ys)
.

Arguments HomNFMC {X} xs ys.

Global Instance isgraph_nfmc {X : Type} : IsGraph (NFMC X) := isgraph_paths _.
Global Instance is01cat_nfmc {X : Type} : Is01Cat (NFMC X) := is01cat_paths _.
Global Instance is2graph_nfmc {X : Type} : Is2Graph (NFMC X) := is2graph_paths _.
Global Instance is1cat_nfmc {X : Type} : Is1Cat (NFMC X) := is1cat_paths _.
Global Instance is0gpd_nfmc {X : Type} : Is0Gpd (NFMC X) := is0gpd_paths _.
Global Instance is1gpd_nfmc {X : Type} : Is1Gpd (NFMC X) := is1gpd_paths _.
Global Instance hasequivs_nfmc {X : Type} : HasEquivs (NFMC X) := hasequivs_1gpd _.  

Global Instance is0bifunctor_app {X : Type} : Is0Bifunctor (@app X).
Proof.
  srapply Build_Is0Bifunctor'.
  snrapply Build_Is0Functor.
  intros [l l'] [p p'] [q q'].
  cbn; exact (ap011 _ q q').
Defined.

Global Instance is1bifunctor_app {X : Type} : Is1Bifunctor (@app X).
Proof.
  snrapply Build_Is1Bifunctor'.
  snrapply Build_Is1Functor.
  - intros [l l'] [m m'] [p p'] [q q'] [r r'].
    exact (ap022 _ r r').
  - reflexivity.
  - intros [l l'] [m m'] [n n'] [p p'] [q q'].
    exact (ap011_pp _ p q p' q').
Defined.

Global Instance associator_nfmc {X : Type} : Associator (@app X).
Proof.
  snrapply Build_Associator.
  1: apply app_assoc.
  simpl. hnf.
  intros [[l m] n] [[l' m'] n'] [[f g] h]; cbn in * |-.
  destruct f, g, h.
  apply concat_1p_p1.
Defined.

Global Instance leftunitor_nfmc {X : Type} : LeftUnitor (@app X) [].
Proof.
  snrapply Build_NatEquiv.
  1: reflexivity.
  intros l m p.
  apply equiv_p1_1q.
  apply ap_idmap.
Defined.

Global Instance rightunitor_nfmc {X : Type} : RightUnitor (@app X) [].
Proof.
  snrapply Build_NatEquiv.
  - intros l.
    induction l.
    + reflexivity.
    + cbn; apply ap.
      exact IHl.
  - intros l m p.
    destruct p.
    apply concat_1p_p1.
Defined.

Global Instance triangleidentity_nfmc {X : Type} : TriangleIdentity (@app X) [].
Proof.
  intros l m.
  induction l.
  1: reflexivity.
  cbn.
  apply moveL_Mp.
  rhs_V nrapply (ap011_compose' (app (A:=X)) (cons a) idmap _ 1).
  rhs nrapply (ap011_compose (app (A:=X)) (cons a)).
  lhs nrapply concat_p1.
  lhs_V nrapply ap_V.
  f_ap.
  lhs_V nrapply concat_p1.
  apply moveR_Vp.
  exact IHl.
Defined.

Global Instance pentagonidentity_nfmc {X : Type} : PentagonIdentity (@app X) [].
Proof.
  intros l m n k.
  lhs nrapply (list_pentagon l m n k).
  apply concat_pp_p.
Defined.

Global Instance ismonoidal_nfmc {X : Type} : IsMonoidal (NFMC X) (app (A:=X)) [] := {}.

Definition nfmc'_nfmc (X : Type) n : NFMC' X -> NFMC X := fun f => f n. 

Global Instance is0functor_nfmc'_nfmc {X : Type} n : Is0Functor (nfmc'_nfmc X n).
Proof.
  snrapply Build_Is0Functor.
  intros f g p.
  exact (p n).
Defined.

Global Instance is1functor_nfmc'_nfmc {X : Type} n : Is1Functor (nfmc'_nfmc X n).
Proof.
  snrapply Build_Is1Functor.
  - intros f g p q h.
    exact (h n).
  - reflexivity.
  - reflexivity.
Defined.

Definition nfmc_fmc_incl (X : Type) : NFMC X -> FMC X.
Proof.
  intros f.
  induction f as [| x xs IHxs].
  - exact unit.
  - exact (tensor (el x) IHxs).
Defined.

Global Instance is0functor_nfmc_fmc_incl {X : Type} : Is0Functor (nfmc_fmc_incl X).
Proof.
  snrapply Build_Is0Functor.
  intros l m p.
  destruct p.
  exact (Id _).
Defined.

Global Instance is1functor_nfmc_fmc_incl {X : Type} : Is1Functor (nfmc_fmc_incl X).
Proof.
  snrapply Build_Is1Functor.
  - intros l m p q h.
    destruct h.
    reflexivity.
  - reflexivity.
  - intros l m n p q.
    destruct p, q.
    symmetry.
    apply left_unitor2.
Defined.

Definition nrm' (X : Type) n : FMC X -> FMC X := nfmc_fmc_incl X o nfmc'_nfmc X n o interp X.
Global Instance is0functor_nrm' {X : Type} n : Is0Functor (nrm' X n) := _.
Global Instance is1functor_nrm' {X : Type} n : Is1Functor (nrm' X n) := _.

Definition zeta_trans {X} n
  : Transformation
      (fun a => tensor a (nfmc_fmc_incl X n))
      (nrm' X n).
Proof.
  intros x.
  induction x as [| |a IHa b IHb] in n |- *.
  - exact (id _).
  - apply left_unitor.
  - exact (IHa _ $o fmap11 tensor (Id a) (IHb _) $o (associator' _ _ _)^$).
Defined.

Lemma natequiv_left_unitor {X}
  : NatEquiv (tensor (X:=X) unit) idmap.
Proof.
  snrapply Build_NatEquiv.
  - intros x.
    apply left_unitor.
  - intros x y f.
    apply isnat_left_unitor.
Defined.

Definition isnat_left_unitor' {X} {x y : FMC X} (f : x $-> y)
  : left_unitor' y $o fmap01 tensor unit f $== f $o left_unitor' x
  := isnat_left_unitor x y f.

Definition isnat_right_unitor' {X} {x y : FMC X} (f : x $-> y)
  : right_unitor' y $o fmap10 tensor f unit $== f $o right_unitor' x
  := isnat_right_unitor x y f.

Definition triangle' {X} (x y : FMC X)
  : fmap01 tensor x (left_unitor' y) $== fmap10 tensor (right_unitor' x) y $o associator' x unit y
  := triangle.

Definition pentagon' {X} (w x y z : FMC X)
  : associator' (tensor w x) y z $o associator' w x (tensor y z)
    $== fmap10 tensor (associator' w x y) z $o associator' w (tensor x y) z
      $o fmap01 tensor w (associator' x y z)
  := pentagon.

Definition isnat_l_associator' {X} {w x y z : FMC X} (f : z $-> y)
  : associator' y w x $o fmap10 tensor f (tensor w x)
    $== fmap10 tensor (fmap10 tensor f w) x $o associator' z w x
  := isnat_l_associator w x y z f.

Definition isnat_m_associator' {X} {w x y z : FMC X} (f : z $-> y)
  : associator' w y x $o fmap01 tensor w (fmap10 tensor f x)
    $== fmap10 tensor (fmap01 tensor w f) x $o associator' w z x 
  := isnat_m_associator w x y z f.

Definition isnat_r_associator' {X} {w x y z : FMC X} (f : z $-> y)
  : associator' w x y $o fmap01 tensor w (fmap01 tensor x f)
    $== fmap01 tensor (tensor w x) f $o associator' w x z
  := isnat_r_associator w x y z f.

(** Proven in [Kelly 64]. Proof is a little tricky even though the lemma is simple. *)
Lemma unitor_tensor_law {X} x y
  : left_unitor' (tensor (X:=X) x y)
    $== fmap10 tensor (left_unitor' x) y $o associator' unit x y.
Proof.
  refine ((gpd_moveR_hV (isnat_left_unitor' _))^$ $@ ((_ $@L _) $@R _)
    $@ gpd_moveR_hV (isnat_left_unitor' _)).
  refine (_ $@ (fmap_comp _ _ _)^$).
  refine (_ $@ (gpd_moveR_Vh (isnat_m_associator' _)^$ $@R _)). 
  refine (_ $@ (cat_assoc _ _ _)^$).
  apply gpd_moveL_Vh.
  change (fmap (tensor unit) ?f) with (fmap01 tensor unit f).
  refine (_ $@L (triangle' _ _) $@ _).
  refine ((cat_assoc _ _ _)^$ $@ _).
  refine (_ $@ (cat_assoc _ _ _)^$).
  refine (_ $@ ((fmap2 _ (triangle' _ _) $@ fmap_comp _ _ _)^$ $@R _)).
  change (fmap (flip tensor y) ?f) with (fmap10 tensor f y).
  refine (_ $@ (cat_assoc _ _ _)^$).
  refine (_ $@ (_ $@L (pentagon' _ _ _ _ $@ cat_assoc _ _ _))).
  refine ((_ $@R _) $@ cat_assoc _ _ _).
  exact (isnat_l_associator' _).
Defined.

(** Main meat of proof *)
Global Instance is1natural_zeta_trans {X} n
  : Is1Natural
      (fun a => tensor a (nfmc_fmc_incl X n))
      (nrm' X n)
      (zeta_trans n).
Proof.
  intros x y f.
  (** We rewrite the goal as a square to make applying some lemmas easier. *)
  change (?w $o ?x $== ?y $o ?z) with (Square z w x y).
  (** We proceed by induction on the morphism [f]. *)
  induction f as [
    | x y z f IHf g IHg
    | x y f IHf | | |
    | a b a' b' f IHf g IHg ] in n |- *.
  - (** Identity *)
    nrapply vconcatL.
    1: exact (fmap_id (flip tensor _) x).
    nrapply vconcatR.
    2: exact (fmap_id (nfmc_fmc_incl X o (fun f => f n) o interp X) x).
    apply hrefl.
  - (** Composition *)
    nrapply vconcatL.
    1: exact (fmap_comp (flip tensor _) g f).
    nrapply vconcatR.
    2: exact (fmap_comp (nfmc_fmc_incl X o (fun f => f n) o interp X) g f).
    exact (hconcat (IHg _) (IHf _)).
  - (** Inverse *)
    nrapply vconcatL.
    1: exact (gpd_1functor_V (flip tensor _) _).
    nrapply vconcatR.
    2: exact (gpd_1functor_V (nfmc_fmc_incl X o (fun f => f n) o interp X) _).
    exact (hinverse' (IHf _)).
  - (** Left unitor *)
    change (Square
      (zeta_trans _ unit $o fmap11 tensor (Id unit) (zeta_trans n x) $o (associator' _ _ _)^$)
      (zeta_trans n x)
      (fmap (flip tensor (nfmc_fmc_incl X n)) (left_unitor x))
      (id _)).
    snrapply vconcatL.
    { refine (_ $o (associator' _ _ _)^$).
       apply left_unitor. }
    { symmetry.
      apply gpd_moveR_hV.
      apply unitor_tensor_law. }
    unfold Square.
    refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ cat_assoc _ _ _).
    refine (_ $@ (cat_idl _)^$).
    generalize (zeta_trans n x); intros h.
    refine (_ $@ (_ $@L _)).
    2: { refine (_ $@ (_ $@L _^$)).
      2: apply tensor2_id.
      symmetry.
      rapply cat_idr. }
    symmetry.
    apply isnat_left_unitor.
  - (** Right unitor *)
    change (Square
      (zeta_trans n x $o fmap11 tensor (Id x) (zeta_trans n unit) $o (associator' _ _ _)^$)
      (zeta_trans n x)
      (fmap (flip tensor (nfmc_fmc_incl X n)) (right_unitor x))
      (id _)).
    snrapply vconcatL.
    { refine (_ $o (associator' _ _ _)^$).
      refine (fmap01 tensor x _).
      apply left_unitor. }
    { apply gpd_moveL_hV.
      symmetry.
      apply triangle'. }
    apply whiskerTL.
    snrapply hconcatR.
    { refine (_ $o _).
      1: apply right_unitor.
      refine (_ $o _^$).
      2: apply right_unitor.
      refine (fmap10 tensor _ unit).
      exact (zeta_trans n x). }
    { unfold Square.
      refine (_ $@ (cat_idl _)^$).
      unfold fmap11.
      refine (_ $@ (_ $@L _^$) $@ cat_assoc _ _ _).
      2: apply tensor2_id.
      refine (_ $@ (cat_idr _)^$).
      change (fmap (tensor x) ?f) with (fmap01 tensor x f).
      refine (((cat_assoc _ _ _)^$ $@ _) $@R _).
      apply gpd_moveR_hV.
      apply isnat_right_unitor'. }
    refine (_ $@ cat_assoc _ _ _).
    apply gpd_moveL_hV.
    symmetry.
    apply isnat_right_unitor'.
  - (** Associator *)
    change (Square
      (zeta_trans _ x $o fmap11 tensor (Id x) (zeta_trans n (tensor y z)) $o (associator' _ _ _)^$)
      (zeta_trans _ (tensor x y) $o fmap11 tensor (Id (tensor x y)) (zeta_trans n z) $o (associator' _ _ _)^$)
      (fmap (flip tensor (nfmc_fmc_incl X n)) (associator x y z))
      (id _)).
    snrapply vconcat.
    { refine (associator' _ _ _ $o _).
      refine (fmap01 tensor x _)^$.
      exact (associator' _ _ _). }
    { apply vinverse'.
      unfold Square.
      refine ((cat_assoc _ _ _)^$ $@ _).
      apply gpd_moveR_hV.
      apply pentagon. }
    snrapply vconcat.
    { refine (associator' _ _ _ $o _).
      refine (fmap01 tensor x _)^$.
      rapply zeta_trans. }
    { nrapply hconcat.
      { apply hinverse'.
        nrapply hconcatR.
        2: exact ((_ $@L fmap_id _ _) $@ cat_idr _).
        rapply (fmap_square (tensor x)).
        simpl.
        unfold Square.
        refine (cat_assoc _ _ _ $@ _).
        refine ((_ $@L _) $@ _).
        1: apply left_invertor2.
        refine (cat_idr _ $@ _).
        change (comp ?x ?y) with (x $o y).
        refine (_ $@L _).
        refine (_^$ $@ _).
        1: apply tensor2_comp.
        eapply (tensor3 left_unitor2).
        apply right_unitor2. }
      simpl.
      snrapply hconcatR.
      1: exact (tensor2 (id (tensor x y)) (zeta_trans n z)).
      2: { symmetry.
        refine (_ $@ _).
        2: apply tensor2_comp.
        apply tensor3; apply rev2, right_unitor2. }
      apply transpose.
      apply isnat_r_associator. }
    unfold Square.
    refine ((cat_assoc _ _ _)^$ $@ _ $@ (cat_idl _)^$).
    apply gpd_moveR_hV.
    simpl.
    do 4 change (comp ?x ?y) with (cat_comp (A:=FMC X) x y).
    change (Hom2FMC ?f ?g) with (f $== g).
    refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
    1: apply left_invertor2.
    refine (cat_idr _ $@ _).
    refine ((cat_assoc _ _ _)^$ $@ _).
    refine ((_ $@L _) $@ _).
    1: apply tensor2_id.
    refine (cat_idr _ $@ _).
    reflexivity.
  - (** Functoriality of tensor *)
    change (Square
      (zeta_trans _ a $o fmap11 tensor (Id a) (zeta_trans n b) $o (associator' _ _ _)^$)
      (zeta_trans _ a' $o fmap11 tensor (Id a') (zeta_trans n b') $o (associator' _ _ _)^$)
      (fmap (flip tensor (nfmc_fmc_incl X n)) (tensor2 f g))
      (fmap (nrm' X n) (tensor2 f g))).
    snrapply vconcat.
    1: exact (fmap11 tensor f (tensor2 g (id _))).
    { (** Using naturality of the associator *)
      apply vinverse'.
      nrapply vconcatR.
      1: nrapply vconcatL.
      2: exact (is1natural_associator_uncurried
        (a, b, nfmc_fmc_incl X n)
        (a', b', nfmc_fmc_incl X n)
        (f, g, Id (nfmc_fmc_incl X n))).
      - nrapply comp2.
        1: nrapply wl; apply tensor2_comp.
        nrapply comp2.
        1: apply tensor2_comp.
        simpl.
        1: nrapply comp2.
        2: apply rev2, tensor2_comp.
        apply tensor3.
        1: apply rev2, left_unitor2.
        simpl. 
        nrapply comp2.
        1: apply wl, rev2, right_unitor2.
        nrapply comp2.
        1: apply tensor2_comp.
        nrapply comp2.
        2: apply right_unitor2.
        apply tensor3; apply rev2, left_unitor2.
      - refine (_ $@ (_^$ $@R _)).
        2: apply fmap_id.
        2: exact _.
        refine (_ $@ (cat_idl _)^$).
        apply tensor3.
        2: apply id2.
        simpl.
        nrapply comp2.
        1: apply tensor2_comp.
        apply tensor3.
        1,2: apply rev2.
        1: apply left_unitor2.
        apply right_unitor2. }
    snrapply vconcat.
    { rapply (fmap11 tensor f).
      exact (fmap (nrm' X n) g). }
    { rapply fmap11_square.
      1: apply vrefl.
      apply IHg. }
    nrapply vconcatR.
    2: { refine (_ $o fmap2 _ _).
      2: { refine (_ $@ _).
        1: eapply tensor3.
        1: apply rev2, left_unitor2.
        1: apply rev2, right_unitor2.
        apply tensor2_comp. }
      rapply (fmap_comp (nrm' X n)). }
    unfold fmap11.
    snrapply hconcat.
    1: rapply zeta_trans.
    + unfold Square.
      unfold Square in IHf.
      refine (IHf _ $@ _).
      refine (_ $@R _).
      unfold nfmc'_nfmc.
      unfold is0functor_nrm'.
      refine (fmap2 (nfmc_fmc_incl X) _).
      change (a $-> a') in f.
      change (fmap (nfmc'_nfmc X (interp X b n)) (fmap (interp X) f)
        $== fmap (nfmc'_nfmc X n) (fmap (interp X) (Id b) $@@ fmap (interp X) f)).
      refine (_ $@ fmap2 (nfmc'_nfmc X n) _).
      2: { refine ((_  $@ _) $@R _).
        2: refine (fmap2 _ _).
        2: symmetry.
        2: refine (fmap_id _ _).
        symmetry.
        refine (fmap_id _ _). }
      refine (_ $@ fmap2 _ _).
      2: rapply (cat_idl _)^$.
      reflexivity.
    + unfold Square in IHg |- *.
      refine ((_ $@L (fmap2 _ _ $@ _)) $@ _).
      1: exact (gpd_moveR_hV (IHg _))^$.
      1: refine (fmap_comp _ _ _ $@ (_ $@R _)).
      1: refine (fmap_comp _ _ _).
      refine ((cat_assoc _ _ _ )^$ $@ _).
      refine (_ $@L _ $@ _).
      1: nrapply gpd_1functor_V; exact _.
      apply gpd_moveR_hV.
      refine ((cat_assoc _ _ _)^$ $@ _ $@ (cat_assoc _ _ _)^$).
      set (r := tensor2 (id a') g).
      change (HomFMC ?f ?g) with (f $== g) in r.
      change (b $-> b') in g.
      change (fmap (nrm' X n) r)
        with (fmap (nfmc_fmc_incl X o nfmc'_nfmc X n) (fmap (interp X) r)).
      change (fmap (interp X) r) with (fmap (interp X) g $@@ fmap (interp X) (Id a')).
      unfold "$@@".
      refine (_ $@ (_^$ $@R _)).
      2: rapply (fmap_comp (nfmc_fmc_incl X o nfmc'_nfmc X n)).
      (* refine (_ $@ (cat_assoc _ _ _)^$). *)
      (* refine (cat_assoc _ _ _ $@ _). *)
  
      
      Check (zeta_trans (nfmc'_nfmc X n (interp X b')) a').
        (* : tensor a' (nfmc_fmc_incl X (nfmc'_nfmc X n (interp X b')))
            $-> nrm' X (nfmc'_nfmc X n (interp X b')) a' *)
      Check (fmap (tensor a') (zeta_trans n b')).
      (* : tensor a' (tensor b' (nfmc_fmc_incl X n)) $-> tensor a' (nrm' X n b') *)
      Check (fmap (tensor a') (fmap (flip tensor (nfmc_fmc_incl X n)) g)).
      (* : tensor a' (flip tensor (nfmc_fmc_incl X n) b)
        $-> tensor a' (flip tensor (nfmc_fmc_incl X n) b') *)

      Check (fmap (nfmc_fmc_incl X o nfmc'_nfmc X n) (interp X a' $@L fmap (interp X) g)).
      (* : nfmc_fmc_incl X (nfmc'_nfmc X n (interp X a' $o interp X b))
        $-> nfmc_fmc_incl X (nfmc'_nfmc X n (interp X a' $o interp X b')) *)
      Check (fmap (nfmc_fmc_incl X o nfmc'_nfmc X n) (fmap (interp X) (Id a') $@R interp X b)).
      (* nfmc_fmc_incl X (nfmc'_nfmc X n (interp X a' $o interp X b))
        $-> nfmc_fmc_incl X (nfmc'_nfmc X n (interp X a' $o interp X b)) *)
      Check ((zeta_trans (nfmc'_nfmc X n (interp X b)) a')). 
      (* : tensor a' (nfmc_fmc_incl X (nfmc'_nfmc X n (interp X b)))
        $-> nrm' X (nfmc'_nfmc X n (interp X b)) a' *)
      Check (fmap (tensor a') (zeta_trans n b)).
      (* : tensor a' (tensor b (nfmc_fmc_incl X n)) $-> tensor a' (nrm' X n b) *)


        
      (* refine ((cat_assoc _ _ _)^$ $@ _). *)
      (* refine (_ $@ cat_assoc _ _ _). *)
      change (?w $o ?x $== ?y $o ?z) with (Square z w x y).
      Arguments Square : clear implicits.
      simpl.

Admitted.

Definition zeta {X} n
  : NatEquiv 
      (fun a => tensor a (nfmc_fmc_incl X n))
      (nrm' X n).
Proof.
  snrapply Build_NatEquiv.
  1: exact (zeta_trans n).
  exact _.
Defined.

Definition nrm X := nrm' X [].

Definition coherence {X} : NatEquiv idmap (nrm X).
Proof.
  nrefine (natequiv_compose (zeta []) _).
  apply natequiv_inverse.
  exact (Monoidal.right_unitor (F := tensor)).
Defined.
