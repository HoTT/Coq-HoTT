Require Import Basics.Overture Basics.Decidable Basics.Tactics Basics.Trunc Basics.Equivalences.
Require Import Types.Forall Types.Bool Types.Paths Types.Empty Types.Equiv Types.Sigma.
Require Import WildCat.Core WildCat.Products WildCat.Coproducts WildCat.Equiv.
Require Import WildCat.PointedCat WildCat.Bifunctor WildCat.Square.
Require Import WildCat.Opposite WildCat.Monoidal.

(** * Categories with biproducts *)

(** ** Biproducts *)

Class Biproduct (I : Type) `{DecidablePaths I} {A : Type}
  `{HasEquivs A, !IsPointedCat A} {x : I -> A}
  := Build_Biproduct' {
  biproduct_product :: Product I x;
  biproduct_coproduct :: Coproduct I x;
  catie_cat_coprod_prod_incl :: CatIsEquiv (cat_coprod_prod_incl x);
}.

Arguments Biproduct I {_ A _ _ _ _ _ _} x.

Section Biproducts.
  Context {I : Type} {A : Type} (x : I -> A) `{Biproduct I A x}.
  
  Definition cate_coprod_prod : cat_coprod I x $<~> cat_prod I x
    := Build_CatEquiv (cat_coprod_prod_incl x).

  Definition cat_biprod : A
    := cat_prod I x.

  Definition cat_biprod_pr : forall (i : I), cat_biprod $-> x i
    := cat_pr.

  Definition cat_biprod_corec {z : A}
    : (forall i, z $-> x i) -> z $-> cat_biprod
    := cat_prod_corec I.

  Definition cat_biprod_corec_beta {z : A} (f : forall i, z $-> x i)
    : forall i, cat_biprod_pr i $o cat_biprod_corec f $== f i
    := cat_prod_beta I f.

  Definition cat_biprod_corec_eta {z : A} (f : z $-> cat_biprod)
    : cat_biprod_corec (fun i => cat_biprod_pr i $o f) $== f
    := cat_prod_eta I f.
  
  Definition cat_biprod_corec_eta' {z : A} {f f' : forall i, z $-> x i}
    : (forall i, f i $== f' i) -> cat_biprod_corec f $== cat_biprod_corec f'
    := cat_prod_corec_eta I.
  
  Definition cat_biprod_pr_eta {z : A} {f f' : z $-> cat_biprod}
    : (forall i, cat_biprod_pr i $o f $== cat_biprod_pr i $o f') -> f $== f'
    := cat_prod_pr_eta I.

  Definition cat_biprod_in : forall (i : I), x i $-> cat_biprod
    := fun i => cate_coprod_prod $o cat_in i.

  Definition cat_biprod_rec {z : A}
    : (forall i, x i $-> z) -> cat_biprod $-> z
    := fun f => cat_coprod_rec I f $o cate_coprod_prod^-1$. 

  Definition cat_biprod_rec_beta {z : A} (f : forall i, x i $-> z)
    : forall i, cat_biprod_rec f $o cat_biprod_in i $== f i.
  Proof.
    intros i.
    unfold cat_biprod_rec, cat_biprod_in.
    refine (_ $@ cat_coprod_beta I f i).
    nrefine (cat_assoc _ _ _ $@ (_ $@L _)).
    apply compose_V_hh.
  Defined.

  Definition cat_biprod_rec_eta {z : A} (f : cat_biprod $-> z)
    : cat_biprod_rec (fun i => f $o cat_biprod_in i) $== f.
  Proof.
    unfold cat_biprod_rec.
    apply cate_moveR_eV.
    apply cat_coprod_in_eta.
    intros i.
    refine (cat_coprod_beta I _ i $@ _^$).
    apply cat_assoc.
  Defined.

  Definition cat_biprod_rec_eta' {z : A} {f f' : forall i, x i $-> z}
    : (forall i, f i $== f' i) -> cat_biprod_rec f $== cat_biprod_rec f'.
  Proof.
    intros p.
    unfold cat_biprod_rec.
    exact (cat_coprod_rec_eta I p $@R _).
  Defined.

  Definition cat_biprod_in_eta {z : A} {f f' : cat_biprod $-> z}
    : (forall i, f $o cat_biprod_in i $== f' $o cat_biprod_in i) -> f $== f'.
  Proof.
    intros p.
    apply (cate_epic_equiv cate_coprod_prod).
    apply cat_coprod_in_eta.
    intros i.
    exact (cat_assoc _ _ _ $@ p i $@ (cat_assoc _ _ _)^$).
  Defined.

End Biproducts.

Arguments cat_biprod I {A} x {_ _ _ _ _ _ _ _}.
Arguments cat_biprod_pr {I A x _ _ _ _ _ _ _ _} i.
Arguments cat_biprod_in {I A x _ _ _ _ _ _ _ _} i.
Arguments cate_coprod_prod {I A} x {_ _ _ _ _ _ _ _}.

(** An inclusion followed by a projection of the same index is the identity. *)
Definition cat_biprod_pr_in (I : Type) {A : Type} (x : I -> A)
  `{Biproduct I A x} (i : I)
  : cat_biprod_pr i $o cat_biprod_in i $== Id _.
Proof.
  unfold cat_biprod_pr, cat_biprod_in.
  refine ((_ $@L _) $@ _).
  { refine ((cate_buildequiv_fun _ $@R _) $@ _).
    apply cat_coprod_beta. }
  refine (cat_prod_beta _ _ _ $@ _).
  destruct (dec_paths i i); simpl.
  - (** We cannot eliminate [p : i = i] with path induction, but we do have decidable equality, hence by Hedberg's theorem we must be in a hset and we can replace this with the identity. *)
    assert (r : (idpath = p)) by apply path_ishprop.
    by destruct r.
  - contradiction n.
    reflexivity.
Defined.

(** An inclusion followed by a projection of a different index is zero. *)
Definition cat_biprod_pr_in_ne (I : Type) {A : Type} (x : I -> A)
  `{Biproduct I A x} {i j : I} (p : i <> j)
  : cat_biprod_pr j $o cat_biprod_in i $== zero_morphism.
Proof.
  unfold cat_biprod_pr, cat_biprod_in.
  refine ((_ $@L _) $@ _).
  { refine ((cate_buildequiv_fun _ $@R _) $@ _).
    apply cat_coprod_beta. }
  refine (cat_prod_beta _ _ _ $@ _).
  destruct (dec_paths i j); simpl.
  - contradiction p.
  - reflexivity.
Defined.

Definition cat_biprod_diag I {A} (x : A) `{Biproduct I A (fun _ => x)}
  : x $-> cat_biprod I (fun _ => x)
  := cat_prod_diag x.

Definition cat_biprod_codiag I {A} (x : A) `{Biproduct I A (fun _ => x)}
  : cat_biprod I (fun _ => x) $-> x
  := cat_coprod_fold x $o (cate_coprod_prod (fun _ => x))^-1$.

(** Compatability of [cat_biprod_rec] and [cat_biprod_corec]. *)
Definition cat_biprod_corec_rec I `{DecidablePaths I} {A : Type}
  `{HasEquivs A, !IsPointedCat A} {x y : I -> A}
  `{!Biproduct I x, !Biproduct I y}
  (f : forall i, x i $-> y i)
  : cat_biprod_corec y (fun i => f i $o cat_biprod_pr i)
    $== cat_biprod_rec x (fun i => cat_biprod_in i $o f i).
Proof.
  apply cat_biprod_pr_eta.
  intros i.
  refine (cat_biprod_corec_beta _ _ i $@ _).
  apply cat_biprod_in_eta.
  intros j.
  refine (_ $@ (_ $@L (cat_biprod_rec_beta _ _ _)^$) $@ (cat_assoc _ _ _)^$).
  refine (cat_assoc _ _ _ $@ _ $@ cat_assoc _ _ _).
  destruct (dec_paths j i) as [p | np].
  - destruct p.
    refine ((_ $@L _) $@ cat_idr _ $@ (cat_idl _)^$ $@ (_^$ $@R _)).
    1,2: apply cat_biprod_pr_in.
  - refine ((_ $@L _) $@ cat_zero_r _ $@ (cat_zero_l _)^$ $@ (_^$ $@R _)).
    1,2: apply cat_biprod_pr_in_ne, np.
Defined.

(** *** Existence of biproducts *)
 
Class HasBiproducts (I A : Type)
  `{DecidablePaths I, HasEquivs A, !IsPointedCat A}
  := has_biproducts :: forall (x : I -> A), Biproduct I x.

(** *** Binary biproducts *)

Class BinaryBiproduct {A : Type} `{HasEquivs A, !IsPointedCat A} (x y : A)
  := binary_biproduct :: Biproduct Bool (fun b => if b then x else y).
  
Class HasBinaryBiproducts (A : Type) `{HasEquivs A, !IsPointedCat A}
  := has_binary_biproducts :: forall (x y : A), BinaryBiproduct x y.

Global Instance hasbinarybiproducts_hasbiproductsbool {A : Type}
  `{HasEquivs A, !IsPointedCat A, !HasBiproducts Bool A}
  : HasBinaryBiproducts A
  := fun x y => has_biproducts (fun b : Bool => if b then x else y).

Global Instance hasbinaryproducts_hasbinarybiproducts {A : Type}
  `{H : HasBinaryBiproducts A}
  : HasBinaryProducts A.
Proof.
  intros x y.
  apply biproduct_product.
Defined.

Global Instance hasbinarycoproducts_hasbinarybiproducts {A : Type}
  `{H : HasBinaryBiproducts A}
  : HasBinaryCoproducts A.
Proof.
  intros x y.
  nrapply biproduct_coproduct.
  apply H.
Defined.

Section BinaryBiproducts.

  Context {A : Type} `{HasEquivs A, !IsPointedCat A} {x y : A}
    `{!BinaryBiproduct x y}.

  Definition cat_binbiprod : A
    := cat_biprod Bool (fun b => if b then x else y).
  
  Definition cat_binbiprod_pr1 : cat_binbiprod $-> x := cat_biprod_pr true.
  Definition cat_binbiprod_pr2 : cat_binbiprod $-> y := cat_biprod_pr false.
  
  Definition cat_binbiprod_corec {z : A} (f : z $-> x) (g : z $-> y)
    : z $-> cat_binbiprod.
  Proof.
    apply cat_biprod_corec.
    intros [|].
    - exact f.
    - exact g.
  Defined.

  Definition cat_binbiprod_corec_beta_pr1 {z : A} (f : z $-> x) (g : z $-> y)
    : cat_binbiprod_pr1 $o cat_binbiprod_corec f g $== f
    := cat_biprod_corec_beta _ _ true.

  Definition cat_binbiprod_corec_beta_pr2 {z : A} (f : z $-> x) (g : z $-> y)
    : cat_binbiprod_pr2 $o cat_binbiprod_corec f g $== g
    := cat_biprod_corec_beta _ _ false.

  Definition cat_binbiprod_corec_eta {z : A} (f : z $-> cat_binbiprod)
    : cat_binbiprod_corec (cat_binbiprod_pr1 $o f) (cat_binbiprod_pr2 $o f)
      $== f.
  Proof.
    apply cat_biprod_pr_eta.
    intros [|].
    - exact (cat_binbiprod_corec_beta_pr1 _ _).
    - exact (cat_binbiprod_corec_beta_pr2 _ _).
  Defined.

  Definition cat_binbiprod_corec_eta' {z : A} {f f' : z $-> x} {g g' : z $-> y}
    : f $== f' -> g $== g'
      -> cat_binbiprod_corec f g $== cat_binbiprod_corec f' g'.
  Proof.
    intros p q.
    apply cat_biprod_corec_eta'.
    intros [|].
    - exact p.
    - exact q.
  Defined.

  Definition cat_binbiprod_pr_eta {z : A} {f f' : z $-> cat_binbiprod}
     : cat_binbiprod_pr1 $o f $== cat_binbiprod_pr1 $o f'
      -> cat_binbiprod_pr2 $o f $== cat_binbiprod_pr2 $o f'
      -> f $== f'.
  Proof.
    intros p q.
    apply cat_biprod_pr_eta.
    intros [|].
    - exact p.
    - exact q.
  Defined.

  Definition cat_binbiprod_inl : x $-> cat_binbiprod := cat_biprod_in true.
  Definition cat_binbiprod_inr : y $-> cat_binbiprod := cat_biprod_in false.

  Definition cat_binbiprod_rec {z : A} (f : x $-> z) (g : y $-> z)
    : cat_binbiprod $-> z.
  Proof.
    apply cat_biprod_rec.
    intros [|].
    - exact f.
    - exact g.
  Defined.

  Definition cat_binbiprod_rec_beta_inl {z : A} (f : x $-> z) (g : y $-> z)
    : cat_binbiprod_rec f g $o cat_binbiprod_inl $== f
    := cat_biprod_rec_beta _ _ true.
  
  Definition cat_binbiprod_rec_beta_inr {z : A} (f : x $-> z) (g : y $-> z)
    : cat_binbiprod_rec f g $o cat_binbiprod_inr $== g
    := cat_biprod_rec_beta _ _ false.

  Definition cat_binbiprod_rec_eta {z : A} (f : cat_binbiprod $-> z)
    : cat_binbiprod_rec (f $o cat_binbiprod_inl) (f $o cat_binbiprod_inr) $== f.
  Proof.
    apply cat_biprod_in_eta.
    intros [|].
    - exact (cat_binbiprod_rec_beta_inl _ _).
    - exact (cat_binbiprod_rec_beta_inr _ _).
  Defined.

  Definition cat_binbiprod_rec_eta' {z : A} {f f' : x $-> z} {g g' : y $-> z}
    : f $== f' -> g $== g'
      -> cat_binbiprod_rec f g $== cat_binbiprod_rec f' g'.
  Proof.
    intros p q.
    apply cat_biprod_rec_eta'.
    intros [|].
    - exact p.
    - exact q.
  Defined.

  Definition cat_binbiprod_in_eta {z : A} {f f' : cat_binbiprod $-> z}
    : f $o cat_binbiprod_inl $== f' $o cat_binbiprod_inl
      -> f $o cat_binbiprod_inr $== f' $o cat_binbiprod_inr
      -> f $== f'.
  Proof.
    intros p q.
    apply cat_biprod_in_eta.
    intros [|].
    - exact p.
    - exact q.
  Defined.

  Definition cat_binbiprod_pr1_inl
    : cat_binbiprod_pr1 $o cat_binbiprod_inl $== Id _
    := cat_biprod_pr_in Bool _ true.

  Definition cat_binbiprod_pr2_inr
    : cat_binbiprod_pr2 $o cat_binbiprod_inr $== Id _
    := cat_biprod_pr_in Bool _ false.

  Definition cat_binbiprod_pr2_inl
    : cat_binbiprod_pr2 $o cat_binbiprod_inl $== zero_morphism.
  Proof.
    snrapply (cat_biprod_pr_in_ne Bool _ (i := true) (j := false)).
    apply (not_fixed_negb false).
  Defined.
  
  Definition cat_binbiprod_pr1_inr
    : cat_binbiprod_pr1 $o cat_binbiprod_inr $== zero_morphism.
  Proof.
    snrapply (cat_biprod_pr_in_ne Bool _ (i := false) (j := true)).
    apply (not_fixed_negb true).
  Defined.

End BinaryBiproducts.

Arguments cat_binbiprod {A _ _ _ _ _ _} x y {_}.

(** Annoyingly this doesn't follow directly from the general diagonal since [fun b => if b then x else x] is not definitionally equal to [fun _ => x]. *)
Definition cat_binbiprod_diag {A : Type}
  `{HasEquivs A, !IsPointedCat A} (x : A) `{!BinaryBiproduct x x}
  : x $-> cat_binbiprod x x.
Proof.
  snrapply cat_binbiprod_corec; exact (Id _).
Defined.

Definition cat_binbiprod_codiag {A : Type}
  `{HasEquivs A, !IsPointedCat A} (x : A) `{!BinaryBiproduct x x}
  : cat_binbiprod x x $-> x.
Proof.
  snrapply cat_binbiprod_rec; exact (Id _).
Defined.

(** Compatability of [cat_binprod_rec] and [cat_binprod_corec]. *)
Definition cat_binbiprod_corec_rec {A : Type}
  `{HasEquivs A, !IsPointedCat A} {w x y z : A}
  `{!BinaryBiproduct w x, !BinaryBiproduct y z}
  (f : w $-> y) (g : x $-> z)
  : cat_binbiprod_corec (f $o cat_binbiprod_pr1) (g $o cat_binbiprod_pr2)
    $== cat_binbiprod_rec (cat_binbiprod_inl $o f) (cat_binbiprod_inr $o g).
Proof.
  unfold cat_binbiprod_corec, cat_binbiprod_rec.
  nrefine (_ $@ _ $@ _).
  2: snrapply cat_biprod_corec_rec; by intros [|].
  1: snrapply cat_biprod_corec_eta'; by intros [|].
  snrapply cat_biprod_rec_eta'; by intros [|].
Defined.

(** *** Binary biproduct bifunctor *)

Global Instance is0bifunctor_cat_binbiprod {A : Type}
  `{HasBinaryBiproducts A}
  : Is0Bifunctor (fun x y : A => cat_binbiprod x y)
  := is0bifunctor_cat_binprod.

Global Instance is1bifunctor_cat_binbiprod {A : Type}
  `{HasBinaryBiproducts A}
  : Is1Bifunctor (fun x y : A => cat_binbiprod x y)
  := is1bifunctor_cat_binprod.

(** Binary biproducts are functorial in each argument. *)
Global Instance is0functor_cat_binbiprod_l {A : Type}
  `{HasBinaryBiproducts A} (y : A)
  : Is0Functor (fun x => cat_binbiprod x y)
  := bifunctor_is0functor10 y.

Global Instance is1functor_cat_binbiprod_l {A : Type}
  `{HasBinaryBiproducts A} (y : A)
  : Is1Functor (fun x => cat_binbiprod x y)
  := bifunctor_is1functor10 y.

Global Instance is0functor_cat_binbiprod_r {A : Type}
  `{HasBinaryBiproducts A} (x : A)
  : Is0Functor (fun y => cat_binbiprod x y)
  := bifunctor_is0functor01 x.

Global Instance is1functor_cat_binbiprod_r {A : Type}
  `{HasBinaryBiproducts A} (x : A)
  : Is1Functor (fun y => cat_binbiprod x y)
  := bifunctor_is1functor01 x.

(** *** Diagonal lemmas *)

Definition cat_binbiprod_diag_fmap11 {A : Type}
  `{HasEquivs A, !IsPointedCat A, !HasBinaryBiproducts A} {x y : A} (f : x $-> y)
  : cat_binbiprod_diag y $o f
    $== fmap11 (fun x y => cat_binbiprod x y) f f $o cat_binbiprod_diag x.
Proof.
  apply cat_binbiprod_pr_eta.
  - refine ((cat_assoc _ _ _)^$ $@ _).
    refine ((_ $@R _) $@ (_ $@ _)).
    1: apply cat_binbiprod_corec_beta_pr1.
    1: apply cat_idl.
    refine (_ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
    2: rapply cat_pr1_fmap11_binprod.
    refine ((cat_idr _)^$ $@ (_ $@L _^$) $@ (cat_assoc _ _ _)^$).
    apply cat_binbiprod_corec_beta_pr1.
  - refine ((cat_assoc _ _ _)^$ $@ _).
    refine ((_ $@R _) $@ (_ $@ _)).
    1: apply cat_binbiprod_corec_beta_pr2.
    1: apply cat_idl.
    refine (_ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
    2: rapply cat_pr2_fmap11_binprod.
    refine ((cat_idr _)^$ $@ (_ $@L _^$) $@ (cat_assoc _ _ _)^$).
    apply cat_binbiprod_corec_beta_pr2.
Defined.

Definition cat_binbiprod_codiag_fmap11 {A : Type}
  `{HasEquivs A, !IsPointedCat A, !HasBinaryBiproducts A} {x y : A} (f : x $-> y)
  : f $o cat_binbiprod_codiag x
    $== cat_binbiprod_codiag y $o fmap11 (fun x y => cat_binbiprod x y) f f.
Proof.
  apply cat_binbiprod_in_eta.
  - refine (cat_assoc _ _ _ $@ (_ $@L _) $@ cat_idr _ $@ _).
    1: apply cat_binbiprod_rec_beta_inl.
    refine (_ $@ (_ $@L _) $@ (cat_assoc _ _ _)^$).
    2: { refine ((_ $@L _) $@ (cat_assoc _ _ _)^$).
      refine (_^$ $@ (cat_binbiprod_corec_rec _ _ $@R _)^$).
      apply cat_binbiprod_rec_beta_inl. }
    refine (_ $@ (_ $@L _)).
    2: { refine ((_ $@R _) $@ cat_assoc _ _ _).
      refine ((_ $@ _)^$ $@ (cat_binbiprod_corec_rec _ _ $@R _)^$).
      1: apply cat_binbiprod_rec_beta_inl.
      apply cat_idr. }
    refine (_^$ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
    2: apply cat_binbiprod_rec_beta_inl.
    apply cat_idl.
  - refine (cat_assoc _ _ _ $@ (_ $@L _) $@ cat_idr _ $@ _).
    1: apply cat_binbiprod_rec_beta_inr.
    refine (_ $@ (_ $@L _) $@ (cat_assoc _ _ _)^$).
    2: { refine ((_ $@L _) $@ (cat_assoc _ _ _)^$).
      refine ((_ $@ _)^$ $@ (cat_binbiprod_corec_rec _ _ $@R _)^$).
      1: apply cat_binbiprod_rec_beta_inr. 
      apply cat_idr. }
    refine (_ $@ (_ $@L _)).
    2: { refine ((_ $@R _) $@ _)^$.
      1: apply cat_binbiprod_corec_rec.
      apply cat_binbiprod_rec_beta_inr. }
    refine (_^$ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
    2: apply cat_binbiprod_rec_beta_inr.
    apply cat_idl.
Defined.

(** *** Symmetry *)

Section Symmetry.
  Context {A : Type} `{HasBinaryBiproducts A}.

  Definition cat_binbiprod_swap (x y : A)
    : cat_binbiprod x y $-> cat_binbiprod y x
    := cat_binbiprod_corec cat_binbiprod_pr2 cat_binbiprod_pr1.

  Lemma cat_binbiprod_swap_swap (x y : A)
    : cat_binbiprod_swap x y $o cat_binbiprod_swap y x $== Id _.
  Proof.
    rapply cat_binprod_swap_cat_binprod_swap.
  Defined.

  Local Instance symmetricbraiding_cat_binbiprod
    : SymmetricBraiding (fun x y => cat_binbiprod x y). 
  Proof.
    rapply symmetricbraiding_binprod.
  Defined.

  Lemma cat_binbiprod_swap_inl (x y : A)
    : cat_binbiprod_swap x y $o cat_binbiprod_inl
      $== cat_binbiprod_inr.
  Proof.
    apply cat_binbiprod_pr_eta.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      1: apply cat_binbiprod_corec_beta_pr1.
      refine (_ $@ _^$).
      1: apply cat_binbiprod_pr2_inl.
      apply cat_binbiprod_pr1_inr.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      1: apply cat_binbiprod_corec_beta_pr2.
      refine (_ $@ _^$).
      1: apply cat_binbiprod_pr1_inl.
      apply cat_binbiprod_pr2_inr.
  Defined.
  
  Lemma cat_binbiprod_swap_inr (x y : A)
    : cat_binbiprod_swap x y $o cat_binbiprod_inr
      $== cat_binbiprod_inl.
  Proof.
    apply cat_binbiprod_pr_eta.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      1: apply cat_binbiprod_corec_beta_pr1.
      refine (_ $@ _^$).
      1: apply cat_binbiprod_pr2_inr.
      apply cat_binbiprod_pr1_inl.
    - refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      1: apply cat_binbiprod_corec_beta_pr2.
      refine (_ $@ _^$).
      1: apply cat_binbiprod_pr1_inr.
      apply cat_binbiprod_pr2_inl.
  Defined.
    
  (** The swap map preserves the diagonal. *)
  Lemma cat_binbiprod_swap_diag (x : A)
    : cat_binbiprod_swap x x $o cat_binbiprod_diag x $== cat_binbiprod_diag x.
  Proof.
    apply cat_binbiprod_pr_eta.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: apply cat_binbiprod_corec_beta_pr1.
      refine (cat_binbiprod_corec_beta_pr2 _ _ $@ _^$).
      apply cat_binbiprod_corec_beta_pr1.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: apply cat_binbiprod_corec_beta_pr2.
      refine (cat_binbiprod_corec_beta_pr1 _ _ $@ _^$).
      apply cat_binbiprod_corec_beta_pr2.
  Defined.
  
  (** The swap map preserves the codiagonal. *)
  Lemma cat_binbiprod_swap_codiag (x : A)
    : cat_binbiprod_codiag x $o cat_binbiprod_swap x x $== cat_binbiprod_codiag x.
  Proof.
    apply cat_binbiprod_in_eta.
    - refine (_ $@ (cat_binbiprod_rec_beta_inl _ _)^$).
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
      1: apply cat_binbiprod_swap_inl.
      apply cat_binbiprod_rec_beta_inr.
    - refine (_ $@ (cat_binbiprod_rec_beta_inr _ _)^$).
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
      1: apply cat_binbiprod_swap_inr.
      apply cat_binbiprod_rec_beta_inl.
  Defined.

End Symmetry.

(** *** Associativity of binary products *)

Section Associativity.

  Context {A : Type} `{HasBinaryBiproducts A}.

  Local Instance associator_binbiprod
    : Associator (fun x y => cat_binbiprod x y)
    := associator_binprod.

  Lemma cate_binbiprod_assoc (x y z : A)
    : cat_binbiprod x (cat_binbiprod y z)
      $<~> cat_binbiprod (cat_binbiprod x y) z.
  Proof.
    rapply associator_binbiprod.
  Defined.
  
  Definition cat_binbiprod_twist (x y z : A)
    : cat_binbiprod x (cat_binbiprod y z)
      $-> cat_binbiprod y (cat_binbiprod x z)
    := cat_binprod_twist x y z.
      
  Lemma cat_binbiprod_twist_inl (x y z : A)
    : cat_binbiprod_twist x y z $o cat_binbiprod_inl
      $== cat_binbiprod_inr $o cat_binbiprod_inl.
  Proof.
    apply cat_binbiprod_pr_eta.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: apply cat_binbiprod_corec_beta_pr1.
      refine (cat_assoc _ _ _ $@ _ $@ cat_assoc _ _ _).
      refine ((_ $@L _) $@ _ $@ (_^$ $@R _)).
      1: apply cat_binbiprod_pr2_inl.
      2: apply cat_binbiprod_pr1_inr.
      refine (_ $@ _^$).
      1: apply cat_zero_r.
      apply cat_zero_l.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: apply cat_binbiprod_corec_beta_pr2.
      refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
      refine (cat_binbiprod_rec_beta_inl _ _ $@ cat_idr _ $@ _).
      refine ((cat_idl _)^$ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
      apply cat_binbiprod_pr2_inr.
  Defined.

  Lemma cat_binbiprod_twist_inr_inl (x y z : A)
    : cat_binbiprod_twist x y z $o cat_binbiprod_inr $o cat_binbiprod_inl
      $== cat_binbiprod_inl.
  Proof.
    apply cat_binbiprod_pr_eta.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
        1: apply cat_binbiprod_corec_beta_pr1. }
      refine (cat_assoc _ _ _ $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
        1: apply cat_binbiprod_pr2_inr. 
        apply cat_idl. }
      refine (_ $@ _^$).
      1,2: apply cat_binbiprod_pr1_inl.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
        1: apply cat_binbiprod_corec_beta_pr2. }
      refine (cat_assoc _ _ _ $@ (_ $@R _) $@ _).
      1: apply cat_binbiprod_corec_rec.
      refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: apply cat_binbiprod_rec_beta_inr.
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
      1: apply cat_binbiprod_pr2_inl.
      refine (_ $@ _^$).
      1: apply cat_zero_r.
      apply cat_binbiprod_pr2_inl.
  Defined.

  Lemma cat_binbiprod_twist_inr_inr (x y z : A)
    : cat_binbiprod_twist x y z $o cat_binbiprod_inr $o cat_binbiprod_inr
      $== cat_binbiprod_inr $o cat_binbiprod_inr.
  Proof.
    apply cat_binbiprod_pr_eta.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
        1: apply cat_binbiprod_corec_beta_pr1. }
      refine (cat_assoc _ _ _ $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
        1: apply cat_binbiprod_pr2_inr. 
        apply cat_idl. }
      refine (_ $@ _^$).
      1: apply cat_binbiprod_pr1_inr.
      refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: apply cat_binbiprod_pr1_inr.
      apply cat_zero_l.
    - refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
        1: apply cat_binbiprod_corec_beta_pr2. }
      refine (cat_assoc _ _ _ $@ (_ $@R _) $@ _).
      1: apply cat_binbiprod_corec_rec.
      refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: apply cat_binbiprod_rec_beta_inr.
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
      1: apply cat_binbiprod_pr2_inr.
      refine (cat_idr _ $@ _^$).
      refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
      1: apply cat_binbiprod_pr2_inr.
      apply cat_idl.
  Defined.

  Lemma cate_binbiprod_assoc_inl (x y z : A)
    : cate_binbiprod_assoc x y z $o cat_binbiprod_inl
      $== cat_binbiprod_inl $o cat_binbiprod_inl.
  Proof.
    refine ((_ $@R _) $@ _).
    1: nrapply Monoidal.associator_twist'_unfold.
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L (cat_assoc _ _ _ $@ (_ $@L _))) $@ _).
    { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ (_ $@ _)).
      1: apply cat_binbiprod_rec_beta_inl.
      apply cat_idr. }
    simpl.
    refine ((_ $@L _) $@ _).
    1: apply cat_binbiprod_twist_inl.
    refine ((cat_assoc _ _ _)^$ $@ _).
    refine (_ $@R _).
    apply cat_binbiprod_swap_inr.
  Defined.

  Lemma cate_binbiprod_assoc_inr_inl (x y z : A)
    : cate_binbiprod_assoc x y z $o cat_binbiprod_inr $o cat_binbiprod_inl
      $== cat_binbiprod_inl $o cat_binbiprod_inr.
  Proof.
    refine (((_ $@R _) $@R _) $@ _).
    1: nrapply Monoidal.associator_twist'_unfold.
    refine (cat_assoc _ _ _ $@ _).
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L (cat_assoc _ _ _ $@ (_ $@L _))) $@ _).
    { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
      refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
      apply cat_binbiprod_rec_beta_inr. }
    refine ((_ $@L _) $@ _).
    { refine ((cat_assoc _ _ _)^$ $@ _).
      refine (((cat_assoc _ _ _)^$ $@R _) $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      1: apply cat_binbiprod_swap_inl.
      apply cat_binbiprod_twist_inr_inr. }
    refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
    apply cat_binbiprod_swap_inr.
  Defined.
  
  Lemma cate_binbiprod_assoc_inr_inr (x y z : A)
    : cate_binbiprod_assoc x y z $o cat_binbiprod_inr $o cat_binbiprod_inr
      $== cat_binbiprod_inr.
  Proof.
    refine (((_ $@R _) $@R _) $@ _).
    1: nrapply Monoidal.associator_twist'_unfold.
    refine (cat_assoc _ _ _ $@ _).
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L (cat_assoc _ _ _ $@ (_ $@L _))) $@ _).
    { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
      refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
      apply cat_binbiprod_rec_beta_inr. }
    refine ((_ $@L _) $@ _).
    { refine ((cat_assoc _ _ _)^$ $@ _).
      refine (((cat_assoc _ _ _)^$ $@R _) $@ _).
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      1: apply cat_binbiprod_swap_inr.
      apply cat_binbiprod_twist_inr_inl. }
    apply cat_binbiprod_swap_inl.
  Defined.

End Associativity.
    
(** *** Biproducts in the opposite category *)

(** Biproducts exist in the opposite category if they exist in the original category. *)
Global Instance biproduct_op `{Funext} {I A : Type} {x : I -> A} `{Biproduct I A x}
  : Biproduct (A:=A^op) I x.
Proof.
  snrapply Build_Biproduct'.
  (** Products in the opposite category are coproducts in the original category. *)
  - exact _.
  (** Coproducts in the opposite category are products in the original category. *)
  - apply coproduct_op. 
    exact _.
  - snrapply catie_homotopic.
    + simpl; exact (cat_coprod_prod_incl (A:=A) x).
    + simpl; exact _.
    + (** Showing that these two maps are homotopic is a bit tricky. It boils down to showing an equality between [dec_paths (i = j)] and [dec_paths (j = i)] which is true with [Funext] but it is not certain if it holds without. *)
      apply cat_coprod_in_eta.
      intros i.
      apply cat_prod_pr_eta.
      intros j.
      simpl.
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      1: apply cat_coprod_beta.
      refine (_ $@ _).
      1: rapply cat_prod_beta.
      symmetry.
      refine ((_ $@R _) $@ _).
      1: apply cat_prod_beta.
      refine (_ $@ _).
      1: rapply cat_coprod_beta.
      simpl.
      generalize (dec_paths i j).
      generalize (dec_paths j i).
      intros p q.
      assert (r : @decidable_equiv (i = j) (j = i) inverse _ q = p).
      { destruct p as [p|np].
        - destruct q as [q|nq].
          + apply (ap inl).
            apply path_ishprop.
          + destruct (nq p^).
        - destruct q as [|nq].
          + destruct (np p^).
          + apply (ap inr).
            (** Seems to be essential. *)
            apply path_forall.
            intros p.
            destruct (np p). }
      destruct r.
      destruct q as [[]|q]; reflexivity.
Defined.

Global Instance hasbiproducts_op `{Funext} {I A : Type} `{DecidablePaths I, HasEquivs A, !IsPointedCat A, !HasBiproducts I A}
  : HasBiproducts I (A^op).
Proof.
  intros x.
  by rapply biproduct_op.
Defined.

Global Instance binarybiproduct_op `{Funext} {A : Type}
  `{HasEquivs A, !IsPointedCat A} {x y : A} {bb : BinaryBiproduct x y}
  : BinaryBiproduct (A:=A^op) x y.
Proof.
  nrapply biproduct_op.
  exact bb.
Defined.

Global Instance hasbinarybiproducts_op `{Funext} {A : Type}
  `{HasEquivs A, !IsPointedCat A} {hbb : HasBinaryBiproducts A}
  : HasBinaryBiproducts (A^op).
Proof.
  intros x y.
  rapply biproduct_op.
  exact (hbb x y).
Defined.  
