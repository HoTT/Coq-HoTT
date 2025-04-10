Require Import Basics Basics.Tactics Types.Forall Types.Paths WildCat.
Require Import WildCat.Bifunctor WildCat.TwoOneCat.
Require Import Spaces.List.Theory.

Local Open Scope list_scope.

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

Inductive Hom2FMC {X : Type} : forall {a b : FMC X},
    HomFMC a b -> HomFMC a b -> Type :=
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
| associator2 {w x y z} {f : HomFMC w x} {g : HomFMC x y}
    (h : HomFMC y z)
  : Hom2FMC (comp (comp h g) f) (comp h (comp g f))
(** Left identity for composition of morphisms *)
| left_unitor2 {x y} {f : HomFMC x y} : Hom2FMC (comp (id _) f) f
(** Right identity for composition of morphisms *)
| right_unitor2 {x y} {f : HomFMC x y} : Hom2FMC (comp f (id _)) f
(** Left inversion law for composition of morphisms *)
| left_invertor2 {x y} (f : HomFMC x y) : Hom2FMC (comp (rev f) f) (id _)
(** Right inversion law for composition of morphisms *)
| right_invertor2 {x y} (f : HomFMC x y)
  : Hom2FMC (comp f (rev f)) (id _)
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
  : Hom2FMC (tensor2 (comp g f) (comp g' f'))
      (comp (tensor2 g g') (tensor2 f f'))
(** Naturality of left unitor *)
| isnat_left_unitor x y f
  : Hom2FMC (comp (left_unitor y) (tensor2 (id unit) f))
      (comp f (left_unitor x))
(** Naturality of right unitor *)
| isnat_right_unitor x y f
  : Hom2FMC (comp (right_unitor y) (tensor2 f (id unit)))
      (comp f (right_unitor x))
(** Naturality of associator in left variable *)
| isnat_associator x x' y y' z z' (f : HomFMC x x') (g : HomFMC y y')
    (h : HomFMC z z')
  : Hom2FMC (comp (associator x' y' z') (tensor2 f (tensor2 g h)))
            (comp (tensor2 (tensor2 f g) h) (associator x y z))
.

Instance isgraph_FMC {X : Type} : IsGraph (FMC X)
  := {| Hom := HomFMC; |}.
Canonical isgraph_FMC.

Instance is01cat_FMC {X : Type} : Is01Cat (FMC X)
  := {| Id := @id _; cat_comp := @comp _ |}.

Instance is2graph_FMC {X : Type} : Is2Graph (FMC X)
  := fun x y => {| Hom := Hom2FMC |}.
Canonical is2graph_FMC.

Instance is1cat_FMC {X : Type} : Is1Cat (FMC X).
Proof.
  snapply Build_Is1Cat'.
  - intros x y; snapply Build_Is01Cat; revert X x y.
    + exact @id2.
    + exact @comp2.
  - intros x y; snapply Build_Is0Gpd; revert X x y.
    exact @rev2.
  - intros x y z g; snapply Build_Is0Functor; revert X x y z g.
    exact @wl.
  - intros x y z f; snapply Build_Is0Functor; revert X x y z f.
    exact @wr.
  - revert X.
    exact @associator2.
  - revert X.
    exact @left_unitor2.
  - revert X.
    exact @right_unitor2.
Defined.

Instance is01cat_FMC_hom {X:Type} (a b : FMC X)
  : Is01Cat (HomFMC a b)
  := is01cat_hom a b.

Instance is01gpd_FMC_hom {X:Type} (a b : FMC X)
  : Is0Gpd (H0:=is01cat_FMC_hom a b) (HomFMC a b)
  := is0gpd_hom a b.

Instance is0gpd_FMC {X : Type} : Is0Gpd (FMC X).
Proof.
  snapply Build_Is0Gpd; revert X.
  exact @rev.
Defined.

Instance is1gpd_FMC {X : Type} : Is1Gpd (FMC X).
Proof.
  snapply Build_Is1Gpd; revert X.
  - exact @left_invertor2.
  - exact @right_invertor2.
Defined.

Instance hasequivs_FMC {X : Type} : HasEquivs (FMC X) := hasequivs_1gpd _.

Instance is0bifunctor_tensor {X}
  : Is0Bifunctor (@tensor X).
Proof.
  rapply Build_Is0Bifunctor'.
  snapply Build_Is0Functor.
  intros [w x] [y z] [f g].
  exact (tensor2 f g).
Defined.

Instance is1bifunctor_tensor {X}
  : Is1Bifunctor (@tensor X).
Proof.
  snapply Build_Is1Bifunctor'.
  snapply Build_Is1Functor.
  - intros [w x] [y z] [f g] [h k] [p q].
    exact (tensor3 p q).
  - intros [w x].
    exact tensor2_id.
  - intros [x x'] [y y'] [z z'] [f f'] [g g'].
    exact tensor2_comp.
Defined.

Instance is0functor_tensor' {X y}
  : Is0Functor (flip (@tensor X) y).
Proof.
  snapply Build_Is0Functor.
  intros x z.
  exact (flip tensor2 (id y)).
Defined.

Definition left_unitor' {X} (x : FMC X)
  : tensor unit x $<~> x.
Proof.
  exact (left_unitor x).
Defined.

Instance leftunitor_FMC {X} : LeftUnitor (@tensor X) unit.
Proof.
  snapply Build_NatEquiv.
  - revert X; exact @left_unitor'.
  - apply Build_Is1Natural.
    exact (@isnat_left_unitor X).
Defined.

Definition right_unitor' {X} (x : FMC X)
  : tensor x unit $<~> x.
Proof.
  exact (right_unitor x).
Defined.

Instance rightunitor_FMC {X} : RightUnitor (@tensor X) unit.
Proof.
  snapply Build_NatEquiv.
  - revert X. exact @right_unitor'.
  - apply Build_Is1Natural. exact (@isnat_right_unitor X).
Defined.

Definition associator' {X} (x y z : FMC X)
  : tensor x (tensor y z) $<~> tensor (tensor x y) z.
Proof.
  exact (associator x y z).
Defined.

Instance associator_FMC {X} : Associator (@tensor X).
Proof.
  snapply Build_Associator.
  1: exact associator'.
  apply Build_Is1Natural.
  intros [[a b] c] [[a' b'] c'] [[f g] h]; cbn -[Hom] in * |-.
  apply isnat_associator.
Defined.

Instance triangleidentity_FMC {X} : TriangleIdentity (@tensor X) unit
  := @triangle X.

Instance pentagonidentity_FMC {X} : PentagonIdentity (@tensor X)
  := @pentagon X.

Instance ismonoidalcat_FMC {X} : IsMonoidal (FMC X) tensor unit := {}.

(** Attempt at normalized free monoidal categories *)
Definition NFMC (X : Type) := list X.
Instance isgraph_nfmc {X : Type} : IsGraph (NFMC X) := isgraph_paths _.
Instance is01cat_nfmc {X : Type} : Is01Cat (NFMC X) := is01cat_paths _.
Instance is2graph_nfmc {X : Type} : Is2Graph (NFMC X) := is2graph_paths _.
Instance is1cat_nfmc {X : Type} : Is1Cat (NFMC X) := is1cat_paths.
Instance is0gpd_nfmc {X : Type} : Is0Gpd (NFMC X) := is0gpd_paths _.
Instance is1gpd_nfmc {X : Type} : Is1Gpd (NFMC X) := is1gpd_paths.
Instance hasequivs_nfmc {X : Type} : HasEquivs (NFMC X) := hasequivs_1gpd _.

Canonical isgraph_nfmc.

Instance is0bifunctor_app {X : Type} : Is0Bifunctor (@app X).
Proof.
  srapply Build_Is0Bifunctor'.
  snapply Build_Is0Functor.
  intros [l l'] [p p'] [q q'].
  cbn; exact (ap011 _ q q').
Defined.

Instance is1bifunctor_app {X : Type} : Is1Bifunctor (@app X).
Proof.
  snapply Build_Is1Bifunctor'.
  snapply Build_Is1Functor.
  - intros [l l'] [m m'] [p p'] [q q'] [r r'].
    exact (ap022 _ r r').
  - reflexivity.
  - intros [l l'] [m m'] [n n'] [p p'] [q q'].
    exact (ap011_pp _ p q p' q').
Defined.

Instance associator_nfmc {X : Type} : Associator (@app X).
Proof.
  snapply Build_Associator.
  1: apply app_assoc.
  apply Build_Is1Natural.
  simpl. hnf.
  intros [[l m] n] [[l' m'] n'] [[f g] h]; cbn in * |-.
  destruct f, g, h.
  apply concat_1p_p1.
Defined.

Instance leftunitor_nfmc {X : Type} : LeftUnitor (@app X) nil.
Proof.
  snapply Build_NatEquiv.
  1: reflexivity.
  apply Build_Is1Natural.
  intros l m p.
  apply equiv_p1_1q.
  apply ap_idmap.
Defined.

Instance rightunitor_nfmc {X : Type} : RightUnitor (@app X) nil.
Proof.
  snapply Build_NatEquiv.
  - exact app_nil.
  - apply Build_Is1Natural. intros l m p.
    destruct p.
    apply concat_1p_p1.
Defined.

Instance triangleidentity_nfmc {X : Type} : TriangleIdentity (@app X) nil.
Proof.
  intros l m.
  induction l.
  1: reflexivity.
  cbn.
  apply moveL_Mp.
  rhs_V napply (ap011_compose' (app (A:=X)) (cons a) idmap _ 1).
  rhs napply (ap011_compose (app (A:=X)) (cons a)).
  lhs napply concat_p1.
  lhs_V napply ap_V.
  f_ap.
  lhs_V napply concat_p1.
  apply moveR_Vp.
  exact IHl.
Defined.

Instance pentagonidentity_nfmc {X : Type} : PentagonIdentity (@app X).
Proof.
  intros l m n k.
  lhs napply (list_pentagon l m n k).
  apply concat_pp_p.
Defined.

Instance ismonoidal_nfmc {X : Type} : IsMonoidal (NFMC X) (app (A:=X)) nil := {}.

(** Now that we have defined the free monoidal category [FMC X] and the normalized free monoidal category [NFMC X] on a type, we define functors between them: the [interp_nfmc] functor, from [FMC X -> NFMC X], and the [embed_fmc] functor [NFMC X -> NFMC X]. *)
Fixpoint interp_nfmc {X: Type} (A : FMC X) : NFMC X :=
  match A with
  | el x => [x]
  | unit => nil
  | tensor a b => (interp_nfmc a) ++ (interp_nfmc b)
  end.

Fixpoint ieq {X : Type} {a b : FMC X} (f : HomFMC a b)
  : paths (interp_nfmc a) (interp_nfmc b) :=
  match f in HomFMC a b return paths (interp_nfmc a) (interp_nfmc b) with
  | id x => idpath (a:=(interp_nfmc x))
  | comp x y z g f => ieq f @ ieq g
  | rev _ _ p => inverse (ieq p)
  | left_unitor x => idpath
  | right_unitor x => app_nil (interp_nfmc x)
  | associator x y z => app_assoc (interp_nfmc x) (interp_nfmc y) (interp_nfmc z)
  | tensor2 _ _ _ _ f g => ap011 app (ieq f) (ieq g)
  end.

Instance is0functor_interp_nfmc {X : Type}
  : Is0Functor (interp_nfmc (X:=X))
  := Build_Is0Functor _ _ _ _ interp_nfmc (@ieq _ ).

Fixpoint ieq2 {X : Type}
  {a b : FMC X} {f_ g_ : a $-> b} (s : f_ $== g_)
  : fmap interp_nfmc f_ $== fmap interp_nfmc g_ :=
  match s in Hom2FMC f g return paths (fmap interp_nfmc f) (fmap interp_nfmc g)
  with
  | id2 _ _ k => idpath
  | comp2 _ _ _ _ _ beta alpha => ieq2 alpha @ ieq2 beta
  | rev2 _ _ _ _ alpha => inverse (ieq2 alpha)
  | wl _ _ _ g f h alpha => whiskerR (ieq2 alpha) (ieq g)
  | wr _ _ _ f g h alpha => whiskerL (ieq f) (ieq2 alpha)
  | associator2 w x y z f g h => (concat_p_pp (ieq f) (ieq g) (ieq h))
  | left_unitor2 _ _ f => (concat_p1 (ieq f))
  | right_unitor2 _ _ f => (concat_1p (ieq f))
  | left_invertor2 _ _ f => (concat_pV (ieq f))
  | right_invertor2 _ _ f => (concat_Vp (ieq f))
  | triangle _ _ => list_triangle _ _
  | pentagon h j k l => (list_pentagon _ _ _ _ @ (concat_pp_p _ _ _))
  | tensor3 _ _ _ _ f g f' g' alpha beta => ap022 app (ieq2 alpha) (ieq2 beta)
  | tensor2_id _ _ => idpath
  | tensor2_comp _ _ _ _ _ _ f f' g g' => ap011_pp _ _ _ _ _
  | isnat_left_unitor  _ _ f =>
      (whiskerR (ap_idmap (ieq f)) 1 @ concat_p1_1p (ieq f))
  | isnat_right_unitor _ _ f => concat_A1p (f := fun z => z ++ nil) _ _
  | isnat_associator _ _ _ _ _ _ _ _ _ => concat_Ap_assoc _ _ _ _ _ _ _ _ _ _ _
  end.

Instance is1functor_interp_nfmc {X : Type}
  : Is1Functor (interp_nfmc (X:=X)).
Proof.
  apply Build_Is1Functor.
  - exact (@ieq2 X).
  - exact (fun _ => idpath).
  - exact (fun _ _ _ _ _ => idpath).
Defined.

Fixpoint embed_fmc {X : Type} (A : NFMC X) : FMC X :=
  match A with
  | nil => unit
  | x :: y => tensor (el x) (embed_fmc y)
  end.

Instance is0functor_embed_fmc {X : Type}
  : Is0Functor (embed_fmc (X:=X))
  := Build_Is0Functor _ _ _ _ embed_fmc
       (fun a b f =>
          match f in @paths _ _ y return @HomFMC _ (embed_fmc a) (embed_fmc y) with
          | @idpath _ _ => id (embed_fmc a)
          end).

Instance is1functor_embed_fmc {X : Type}
  : Is1Functor (embed_fmc (X:=X)).
Proof.
  apply Build_Is1Functor.
  - intros a b f g s.
    destruct s. exact (id2 _).
  - exact (fun _ => id2 _).
  - intros a b c f g. simpl.
    destruct f, g. simpl. apply rev2, left_unitor2.
Defined.

(** This lemma is important for arguing about the behavior
of [fmap embed_fmc] by induction on the length of the list. *)
Lemma embed_cons {X : Type} (x y : NFMC X) (a : X) (p : x = y)
  : Hom2FMC (tensor2 (id (el a)) (fmap embed_fmc p))
      (fmap embed_fmc (ap (cons a) p)).
Proof.
  destruct p.
  exact tensor2_id.
Defined.

(** We have defined the 1-functors [embed_fmc] and [interp_nfmc]. In this section we prove that [embed_fmc] is a monoidal functor. *)
Section embed_fmc_monoidal.

  (** [embed_fmc] has a lax monoidal cell. *)
  Fixpoint unit_lemma {X : Type} (A B : NFMC X)
    : HomFMC (tensor (embed_fmc A) (embed_fmc B)) (embed_fmc (A ++ B))
    := match A return
             HomFMC (tensor (embed_fmc A) (embed_fmc B)) (embed_fmc (A ++ B)) with
       | nil => left_unitor (embed_fmc B)
       | hd :: tl =>
           comp (tensor2 (id (el hd)) (unit_lemma tl B))
             (rev (associator (el hd) (embed_fmc tl) (embed_fmc B)))
       end.

  (** The lax monoidal cell is a natural transformation. *)
  Lemma embed_lax_cell_is1natural {X:Type}:
    Is1Natural
        (uncurry (fun A B => tensor (embed_fmc A) (embed_fmc B)))
        (uncurry (fun A B => (embed_fmc (app A B))))
        (fun '(A,B) => unit_lemma (X:=X) A B).
  Proof.
    apply Build_Is1Natural.
    intros [A B] [A' B'] [f g]; simpl in *.
    destruct f, g; simpl.
    refine (_ $@ right_unitor2 $@ (left_unitor2^$)).
    apply wl, tensor2_id.
  Defined.

  Definition embed_fmc_unit {X: Type}
    : unit (X:=X) $-> embed_fmc nil
    := id _.

  (** embed_fmc is a monoidal functor. This proof is not so scary as it appears; the proofs would be shorter with good setoid rewriting tactics, and support for rewriting "up to associativity."
TODO: Simplify these proofs using setoid rewrite tactics. *)
  #[export] Instance embed_fmc_IsMonoidal {X:Type}
    : IsMonoidalFunctor (embed_fmc (X:=X)).
  Proof.
    srapply Build_IsMonoidalFunctor.
    - exact ({| trans_nattrans := _ ;
              is1natural_nattrans := embed_lax_cell_is1natural
                     |}).
    - exact embed_fmc_unit.
    - intros x y z; simpl trans_nattrans.
      induction x.
      + simpl.
        repeat change (comp ?a ?b) with (a $o b).
        refine (_ $@ (cat_assoc _ _ _)^$).
        refine (_ $@ (wl (unit_lemma y z)
                        (left_unitor_associator tensor unit _ _))).
        refine (cat_assoc _ _ _ $@ _).
        refine (left_unitor2 $@ _).
        apply isnat_left_unitor.
      + simpl (unit_lemma (a :: x) (y++z)).
        refine (cat_assoc _ _ _ $@ _).
        refine (wl _ (cat_assoc _ _ _) $@ _).
        set (j := rev _ $o _).
        srefine (let h := _ :
                    j $== tensor2 (id (el a))
                      (tensor2 (id (embed_fmc x)) (unit_lemma y z))
                      $o rev (associator (el a) (embed_fmc x)
                                (tensor (embed_fmc y) (embed_fmc z)))
                 in _).
        {
          change (rev ?a) with (a^$); apply gpd_moveL_hV.
          change (rev ?a) with (a^$) in j; unfold j.
          refine (cat_assoc _ _ _ $@ _).
          apply gpd_moveR_Vh; simpl.
          refine (wr _ (tensor3 tensor2_id^$ (id2 (unit_lemma y z)))
                    $@ _).
          symmetry; apply isnat_associator.
        } 
        refine (wl _ (wl _ h) $@ _); clear h j.
        simpl unit_lemma.
        refine (_ $@ (wr _ (wl _ (fmap10_comp tensor _ _ _)^$))).
        repeat change (comp ?a ?b) with (a $o b).
        refine (_ $@ (wr _ (cat_assoc _ _ _))).
        refine (_ $@ (wr _ (wr _ (cat_assoc _ _ _)^$))).
        set (j := (rev _) $o _).
        srefine (let h := _ :
                     fmap01 tensor (el a) (tensor2 (unit_lemma x y)
                                             (id (embed_fmc z)))
                  $o rev (associator (el a)
                            (tensor (embed_fmc x) (embed_fmc y))
                            (embed_fmc z)) $== j in _).
        {
          unfold j.
          change (rev ?a) with (a^$); apply gpd_moveR_hV.
          refine (_ $@ (cat_assoc _ _ _)^$).
          apply gpd_moveL_Vh.
          apply isnat_associator.
        }
        refine (_ $@ wr _ (wr _ (wl _ h))); unfold j; clear h j.
        refine (_ $@ (cat_assoc _ _ _)^$).
        repeat change (comp ?a ?b) with (a $o b).
        refine (_ $@ (cat_assoc _ _ _)^$).
        refine (_ $@ wl _ (cat_assoc _ _ _)^$).
        set (j := rev _ $o (_ $o _)).
        srefine (let h := _ :
                     tensor2 (id (el a)) (associator (embed_fmc x)
                                            (embed_fmc y) (embed_fmc z))
                       $o rev (associator _ _ _) $== j in _).
        {
          change (rev ?a) with (a^$) in *.
          apply gpd_moveR_hV.
          refine (_ $@ (cat_assoc _ _ _)^$).
          apply gpd_moveL_Vh.
          refine (_ $@ wr _ (wr _
                               (gpd_1functor_V (flip tensor _) _)^$)).
          refine (_ $@ (cat_assoc _ _ _)^$).
          apply gpd_moveL_Vh.
          symmetry.
          refine (_ $@ (cat_assoc _ _ _)).
          apply pentagon.
        }
        refine (_ $@ (wl _ (wl _ h))); clear j h.
        refine (_ $@ (cat_assoc _ _ _)).
        refine (_ $@ (cat_assoc _ _ _)).
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine ((cat_assoc _ _ _)^$ $@ _).
        apply cat_prewhisker.
        simpl cat_tensor_associator; unfold Monoidal.associator;
          simpl cate_fun.
        refine ((wr _ (wr _
                         (embed_cons _ _ a (app_assoc x y z))^$)) $@ _).
        refine (_ $@ wr _ tensor2_comp).
        refine (_ $@ tensor2_comp).
        refine (wr _ tensor2_comp^$ $@ _).
        refine (tensor2_comp^$ $@ _).
        apply tensor3.
        1: by apply id2.
        exact IHx.
    - simpl; intro a.
      unfold left_unitor'.
      unfold embed_fmc_unit.
      unfold fmap10; simpl.
      refine (_ $@ wl _ (tensor2_id^$)).
      refine (_ $@ right_unitor2^$).
      exact left_unitor2^$.
    - intro a.
      change _ with
        (right_unitor (embed_fmc a) $==
           fmap embed_fmc (app_nil a) $o unit_lemma a nil $o
           fmap01 tensor (embed_fmc a) embed_fmc_unit).
      unfold embed_fmc_unit.
      refine (_ $@ wl _ tensor2_id^$).
      refine (_ $@ right_unitor2^$).
      induction a as [| a y IHy].
      + exact ((left_unitor_unit_right_unitor_unit tensor unit)^$
                 $@ (left_unitor2)^$).
      + refine (gpd_moveL_hV ((right_unitor_associator tensor unit
                                 (el a) (embed_fmc y))^$) $@ _).
        simpl unit_lemma.
        refine (_ $@ cat_assoc _ _ _ ).
        apply cat_prewhisker.
        change (Hom2FMC ?a ?b) with (a $== b) in IHy.
        apply (fmap2 (tensor (el a))) in IHy; refine (IHy $@ _); clear IHy.
        refine (fmap_comp (tensor (el a)) _ _ $@ _).
        match goal with
        | [ |- _ $== ?z $o _] =>
            change z with (fmap (embed_fmc (X:=X)) (app_nil (a :: y)))
        end.
        apply cat_prewhisker.
        apply embed_cons.
  Defined.

End embed_fmc_monoidal.

Fixpoint interp_unit {X : Type} (A : FMC X) : HomFMC A (embed_fmc (interp_nfmc A))
  := match A return HomFMC A (embed_fmc (interp_nfmc A)) with
     | el x => rev (right_unitor (el x))
     | unit => id unit
     | tensor a b => comp (unit_lemma (interp_nfmc a) (interp_nfmc b))
                       (tensor2 (interp_unit a) (interp_unit b))
     end.

(** Proving that the map interp_unit is natural. This theorem depends in multiple places on the theorem that [embed_fmc] is a monoidal functor.
 TODO: Simplify these proofs using setoid rewrite tactics. *)
Theorem interp_unit_natural {X: Type}
  : Is1Natural idmap (fun A => embed_fmc (interp_nfmc A)) (interp_unit (X:=X)).
Proof.
  apply Build_Is1Natural.
  intros a b f.
  induction f as [| x y z g tau f sigma (* comp *)
                 | x y f IHf (* rev *)
                 | | | |
                   x y x' y' fx IHfx fy IHfy (* tensor2 *)
    ].
  - exact (comp2 (rev2 left_unitor2) (right_unitor2)).
  - refine (hconcat sigma tau $@ (cat_prewhisker _ _ )).
    symmetry.
    exact (fmap_comp (embed_fmc o interp_nfmc) f g).
  - refine (hinverse' IHf $@ _).
    apply cat_prewhisker.
    symmetry.
    exact (gpd_1functor_V (embed_fmc o interp_nfmc) f).
  - symmetry.
    exact (left_unitor2 $@ (isnat_left_unitor _ _ (interp_unit x))).
  - simpl (fmap idmap _); simpl interp_unit.
    refine ((isnat_right_unitor _ _ (interp_unit x))^$ $@ _).
    refine (_ $@ cat_assoc (A:= FMC X) _ _ _).
    rapply (cat_prewhisker (A:=FMC X)); simpl.
    generalize (interp_nfmc x).
    clear x; intro y.
    change _ with
      (right_unitor (embed_fmc y) $==
         (fmap embed_fmc (app_nil y)) $o unit_lemma y nil).
    refine (fmap_tensor_right_unitor (F:=embed_fmc(X:=X)) y $@ _).
    refine (wl _ tensor2_id $@ _).
    exact (right_unitor2).
  - simpl (fmap idmap). simpl interp_unit. simpl (idmap _).
    refine (_ $@ cat_assoc _ _ _).
    
    refine (_ $@ wl (fmap (embed_fmc o interp_nfmc) _ $o _)
             (tensor3 (left_unitor2 (f:= (interp_unit x)))
                (id2 _) )).
    refine (_ $@ wl (fmap (embed_fmc o interp_nfmc) _ $o _)
              (tensor2_comp)^$).
    refine (_ $@ cat_assoc _ _ _).
    refine (wr _ (wl _ (
       (tensor3 (id2 (comp (unit_lemma (interp_nfmc x) _) _))
          (left_unitor2 (f:=interp_unit z))^$) $@ tensor2_comp))$@ _).
    refine ( wr _ (cat_assoc _ _ _)^$ $@ _).
    refine (cat_assoc _ _ _ $@ _).
    refine ( wl _ (isnat_associator _ _ _ _ _ _ _ _ _)^$ $@ _).
    refine ((cat_assoc _ _ _)^$ $@ _).
    apply cat_prewhisker.
    exact ((fmap_tensor_assoc (F:=embed_fmc)
              (interp_nfmc x) (interp_nfmc y) (interp_nfmc z))^$).
  - simpl (fmap idmap _).
    simpl interp_unit.
    refine (cat_assoc _ _ _ $@ _).
    refine (wl _ (tensor2_comp^$ ) $@ _).
    refine (wl _ (tensor3 IHfx IHfy) $@ _); clear IHfx IHfy.
    refine (wl _ (tensor2_comp) $@ _).
    refine (_ $@ cat_assoc _ _ _).
    refine ((cat_assoc _ _ _)^$ $@ _).
    apply cat_prewhisker.
    exact (embed_lax_cell_is1natural
             (interp_nfmc x, interp_nfmc y)
             (interp_nfmc x', interp_nfmc y')
             (fmap interp_nfmc fx, fmap interp_nfmc fy)).
Defined.

(** The counit of the equivalence. *)
Fixpoint counit {X: Type} (x : NFMC X) : x $-> interp_nfmc (embed_fmc x) :=
  match x with
  | nil => idpath
  | hd :: tl => ap (cons hd) (counit tl)
  end.

(** The counit of the equivalence is natural. This proves that [FMC X] and [NFMC X] are equivalent as wild categories. *)
Theorem counit_isnatural (X : Type)
  : Is1Natural idmap (interp_nfmc o embed_fmc) (counit (X:=X)).
Proof.
  apply Build_Is1Natural.
  intros x y f; destruct f.
  exact (concat_1p_p1 _).
Defined.

(** An equivalence of categories is a faithful functor.
 TODO: The more general principle here is that any functor with a "retraction" up to natural isomorphism is faithful. This should be stated and proved somewhere. Furthermore, theorems similar to gpd_moveL_Vh should be proved for morphisms equipped with a Cat_IsBiInv instance. *)
Instance interp_nfmc_Faithful (X: Type) : Faithful (interp_nfmc (X:=X)).
Proof.
  intros x y f f' H.
  refine (gpd_moveL_Vh (interp_unit_natural _ _ f) $@ _);
    refine (_ $@ (gpd_moveL_Vh (interp_unit_natural _ _ f'))^$).
  apply cat_postwhisker, cat_prewhisker.
  by apply (fmap2 embed_fmc).
Defined.

(** A monoidal coherence theorem for general types. *)
Theorem monoidal_coherence {X} {x y : FMC X} (f f' : x $-> y)
  (p : fmap interp_nfmc f = fmap interp_nfmc f')
  : f $== f'.
Proof.
  exact (interp_nfmc_Faithful _ _ _ _ _ p).
Defined.
