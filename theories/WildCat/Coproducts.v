Require Import Basics.Overture Basics.Tactics Basics.Decidable.
Require Import Types.Bool.
Require Import WildCat.Core WildCat.Equiv WildCat.Forall WildCat.NatTrans
               WildCat.Opposite WildCat.Products WildCat.Universe
               WildCat.Yoneda WildCat.ZeroGroupoid WildCat.PointedCat
               WildCat.Monoidal WildCat.Bifunctor.

(** * Categories with coproducts *)

Definition cat_coprod_rec_inv {I A : Type} `{Is1Cat A}
  (coprod : A) (x : I -> A) (z : A) (inj : forall i, x i $-> coprod)
  : yon_0gpd z coprod $-> prod_0gpd I (fun i => yon_0gpd z (x i))
  := cat_prod_corec_inv (coprod : A^op) x z inj.

Class Coproduct (I : Type) {A : Type} `{Is1Cat A} (x : I -> A)
  := prod_co_coprod :: Product (A:=A^op) I x.

Definition cat_coprod (I : Type) {A : Type} (x : I -> A) `{Coproduct I _ x} : A
  := cat_prod (A:=A^op) I x.

Definition cat_in {I : Type} {A : Type} {x : I -> A} `{Coproduct I _ x}
  : forall (i : I), x i $-> cat_coprod I x
  := cat_pr (A:=A^op) (x:=x).

Global Instance cat_isequiv_cat_coprod_rec_inv {I : Type} {A : Type}
  {x : I -> A} `{Coproduct I _ x}
  : forall (z : A), CatIsEquiv (cat_coprod_rec_inv (cat_coprod I x) x z cat_in)
  := cat_isequiv_cat_prod_corec_inv (A:=A^op) (x:=x).

(** A convenience wrapper for building coproducts *)
Definition Build_Coproduct (I : Type) {A : Type} `{Is1Cat A} {x : I -> A}
  (cat_coprod : A) (cat_in : forall i : I, x i $-> cat_coprod)
  (cat_coprod_rec : forall z : A,
    (forall i : I, x i $-> z) -> (cat_coprod $-> z))
  (cat_coprod_beta_in : forall (z : A) (f : forall i, x i $-> z) (i : I),
    cat_coprod_rec z f $o cat_in i $== f i)
  (cat_prod_eta_in : forall (z : A) (f g : cat_coprod $-> z),
    (forall i : I, f $o cat_in i $== g $o cat_in i) -> f $== g)
  : Coproduct I x
  := Build_Product I
      (cat_coprod : A^op)
      cat_in
      cat_coprod_rec
      cat_coprod_beta_in
      cat_prod_eta_in.

Section Lemmata.
  Context (I : Type) {A : Type} {x : I -> A} `{Coproduct I _ x}.

  Definition cate_cat_coprod_rec_inv {z : A}
    : yon_0gpd z (cat_coprod I x) $<~> prod_0gpd I (fun i => yon_0gpd z (x i))
    := cate_cat_prod_corec_inv I (A:=A^op) (x:=x).

  Definition cate_cat_coprod_rec {z : A}
    : prod_0gpd I (fun i => yon_0gpd z (x i)) $<~> yon_0gpd z (cat_coprod I x)
    := cate_cat_prod_corec I (A:=A^op) (x:=x).

  Definition cat_coprod_rec {z : A}
    : (forall i, x i $-> z) -> cat_coprod I x $-> z
    := cat_prod_corec I (A:=A^op) (x:=x).

  Definition cat_coprod_beta {z : A} (f : forall i, x i $-> z)
    : forall i, cat_coprod_rec f $o cat_in i $== f i
    := cat_prod_beta I (A:=A^op) (x:=x) f.

  Definition cat_coprod_eta {z : A} (f : cat_coprod I x $-> z)
    : cat_coprod_rec (fun i => f $o cat_in i) $== f
    := cat_prod_eta I (A:=A^op) (x:=x) f.

  Definition natequiv_cat_coprod_rec_inv
    : NatEquiv (fun z => yon_0gpd z (cat_coprod I x))
      (fun z : A => prod_0gpd I (fun i => yon_0gpd z (x i)))
    := natequiv_cat_prod_corec_inv I (A:=A^op) (x:=x).

  Definition cat_coprod_rec_eta {z : A} {f g : forall i, x i $-> z}
    : (forall i, f i $== g i) -> cat_coprod_rec f $== cat_coprod_rec g
    := cat_prod_corec_eta I (A:=A^op) (x:=x).

  Definition cat_coprod_in_eta {z : A} {f g : cat_coprod I x $-> z}
    : (forall i, f $o cat_in i $== g $o cat_in i) -> f $== g
    := cat_prod_pr_eta I (A:=A^op) (x:=x).
End Lemmata.

(** *** Codiagonal / fold map *)

Definition cat_coprod_codiag {I : Type} {A : Type} (x : A) `{Coproduct I _ (fun _ => x)}
  : cat_coprod I (fun _ => x) $-> x
  := cat_prod_diag (A:=A^op) x.

(** *** Uniqueness of coproducts *)

(** [I]-indexed coproducts are unique no matter how they are constructed. *)
Definition cate_cat_coprod {I J : Type} (ie : I <~> J) {A : Type} `{HasEquivs A}
  (x : I -> A) `{!Coproduct I x} (y : J -> A) `{!Coproduct J y}
  (e : forall (i : I), y (ie i) $<~> x i)
  : cat_coprod J y $<~> cat_coprod I x
  := cate_cat_prod (A:=A^op) ie x y e.

(** *** Existence of coproducts *)

Class HasCoproducts (I A : Type) `{Is1Cat A}
  := has_coproducts :: forall x : I -> A, Coproduct I x.

Class HasAllCoproducts (A : Type) `{Is1Cat A}
  := has_all_coproducts :: forall I : Type, HasCoproducts I A.

(** *** Coproduct functor *)

Local Instance hasproductsop_hascoproducts {I A : Type} `{HasCoproducts I A}
  : HasProducts I A^op
  := fun x : I -> A^op => @has_coproducts I A _ _ _ _ _ x.

Global Instance is0functor_cat_coprod (I : Type) `{IsGraph I}
  (A : Type) `{HasCoproducts I A}
  : @Is0Functor (I -> A) A (isgraph_forall I (fun _ => A)) _
    (fun x : I -> A => cat_coprod I x).
Proof.
  apply is0functor_op'.
  exact (is0functor_cat_prod I A^op).
Defined.

Global Instance is1functor_cat_coprod (I : Type) `{IsGraph I}
  (A : Type) `{HasCoproducts I A}
  : @Is1Functor (I -> A) A _ _ _ (is1cat_forall I (fun _ => A)) _ _ _ _
    (fun x : I -> A => cat_coprod I x) _.
Proof.
  apply is1functor_op'.
  exact (is1functor_cat_prod I A^op).
Defined.

(** *** Categories with specific kinds of coproducts *)

Definition isinitial_coprodempty {A : Type} {z : A}
  `{Coproduct Empty A (fun _ => z)}
  : IsInitial (cat_coprod Empty (fun _ => z)).
Proof.
  intros a.
  snrefine (cat_coprod_rec _ _; fun f => cat_coprod_in_eta _ _); intros [].
Defined.

(** *** Binary coproducts *)

Class BinaryCoproduct {A : Type} `{Is1Cat A} (x y : A)
  := prod_co_bincoprod :: BinaryProduct (A:=A^op) x y.

Definition cat_bincoprod {A : Type}  `{Is1Cat A} (x y : A) `{!BinaryCoproduct x y} : A
  := cat_binprod (x : A^op) y.

Definition cat_inl {A : Type} `{Is1Cat A} {x y : A} `{!BinaryCoproduct x y}
  : x $-> cat_bincoprod x y
  := cat_pr1 (A:=A^op) (x:=x) (y:=y).

Definition cat_inr {A : Type} `{Is1Cat A} {x y : A} `{!BinaryCoproduct x y}
  : y $-> cat_bincoprod x y
  := cat_pr2 (A:=A^op) (x:=x) (y:=y).

(** A category with binary coproducts is a category with a binary coproduct for each pair of objects. *)
Class HasBinaryCoproducts (A : Type) `{Is1Cat A}
  := binary_coproducts :: forall x y, BinaryCoproduct x y.

Global Instance hasbinarycoproducts_hascoproductsbool {A : Type}
  `{HasCoproducts Bool A}
  : HasBinaryCoproducts A
  := fun x y => has_coproducts (fun b : Bool => if b then x else y).

(** A convenience wrapper for building binary coproducts *)
Definition Build_BinaryCoproduct {A : Type} `{Is1Cat A} {x y : A}
  (cat_coprod : A) (cat_inl : x $-> cat_coprod) (cat_inr : y $-> cat_coprod)
  (cat_coprod_rec : forall z : A, (x $-> z) -> (y $-> z) -> cat_coprod $-> z)
  (cat_coprod_beta_inl : forall (z : A) (f : x $-> z) (g : y $-> z),
    cat_coprod_rec z f g $o cat_inl $== f)
  (cat_coprod_beta_inr : forall (z : A) (f : x $-> z) (g : y $-> z),
    cat_coprod_rec z f g $o cat_inr $== g)
  (cat_coprod_in_eta : forall (z : A) (f g : cat_coprod $-> z),
    f $o cat_inl $== g $o cat_inl -> f $o cat_inr $== g $o cat_inr -> f $== g)
  : BinaryCoproduct x y
  := Build_BinaryProduct
      (cat_coprod : A^op)
      cat_inl
      cat_inr
      cat_coprod_rec
      cat_coprod_beta_inl
      cat_coprod_beta_inr
      cat_coprod_in_eta.

Section Lemmata.
  Context {A : Type} {x y z : A} `{BinaryCoproduct _ x y}.

  Definition cat_bincoprod_rec (f : x $-> z) (g : y $-> z)
    : cat_bincoprod x y $-> z
    := @cat_binprod_corec A^op _ _ _ _ x y _ _ f g.

  Definition cat_bincoprod_beta_inl (f : x $-> z) (g : y $-> z)
    : cat_bincoprod_rec f g $o cat_inl $== f
    := @cat_binprod_beta_pr1 A^op _ _ _ _ x y _ _ f g.

  Definition cat_bincoprod_beta_inr (f : x $-> z) (g : y $-> z)
    : cat_bincoprod_rec f g $o cat_inr $== g
    := @cat_binprod_beta_pr2 A^op _ _ _ _ x y _ _ f g.

  Definition cat_bincoprod_eta (f : cat_bincoprod x y $-> z)
    : cat_bincoprod_rec (f $o cat_inl) (f $o cat_inr) $== f
    := @cat_binprod_eta A^op _ _ _ _ x y _ _ f.

  Definition cat_bincoprod_eta_in {f g : cat_bincoprod x y $-> z}
    : f $o cat_inl $== g $o cat_inl -> f $o cat_inr $== g $o cat_inr -> f $== g
    := @cat_binprod_eta_pr A^op _ _ _ _ x y _ _ f g.

  Definition cat_bincoprod_rec_eta {f f' : x $-> z} {g g' : y $-> z}
    : f $== f' -> g $== g' -> cat_bincoprod_rec f g $== cat_bincoprod_rec f' g'
    := @cat_binprod_corec_eta A^op _ _ _ _ x y _ _ f f' g g'.
End Lemmata.

(** *** Binary coproduct functor *)

(** Hint: Use [Set Printing Implicit] to see the implicit arguments in the following proofs. *)

Global Instance is0functor_cat_bincoprod_l {A : Type}
  `{hbc : HasBinaryCoproducts A} y
  : Is0Functor (A:=A) (fun x => cat_bincoprod x y).
Proof.
  rapply is0functor_op'.
  exact (is0functor_cat_binprod_l (A:=A^op) (H0:=hbc) y).
Defined.

Global Instance is1functor_cat_bincoprod_l {A : Type}
  `{hbc : HasBinaryCoproducts A} y
  : Is1Functor (fun x => cat_bincoprod x y).
Proof.
  rapply is1functor_op'.
  exact (is1functor_cat_binprod_l (A:=A^op) (H0:=hbc) y).
Defined.

Global Instance is0functor_cat_bincoprod_r {A : Type}
  `{hbc : HasBinaryCoproducts A} x
  : Is0Functor (fun y => cat_bincoprod x y).
Proof.
  rapply is0functor_op'.
  exact (is0functor_cat_binprod_r (A:=A^op) (H0:=hbc) x).
Defined.

Global Instance is1functor_cat_bincoprod_r {A : Type}
  `{hbc : HasBinaryCoproducts A} x
  : Is1Functor (fun y => cat_bincoprod x y).
Proof.
  rapply is1functor_op'.
  exact (is1functor_cat_binprod_r (A:=A^op) (H0:=hbc) x).
Defined.

Global Instance is0bifunctor_cat_bincoprod {A : Type}
  `{hbc : HasBinaryCoproducts A}
  : Is0Bifunctor (fun x y => cat_bincoprod x y).
Proof.
  nrapply is0bifunctor_op'.
  exact (is0bifunctor_cat_binprod (A:=A^op) (H0:=hbc)).
Defined.

Global Instance is1bifunctor_cat_bincoprod {A : Type}
  `{hbc : HasBinaryCoproducts A}
  : Is1Bifunctor (fun x y => cat_bincoprod x y).
Proof.
  nrapply is1bifunctor_op'.
  exact (is1bifunctor_cat_binprod (A:=A^op) (H0:=hbc)).
Defined.

(** *** Products and coproducts in the opposite category *)

Definition hasbinarycoproducts_op_hasbinaryproducts {A : Type}
  `{hbp : HasBinaryProducts A}
  : HasBinaryCoproducts A^op
  := hbp.
Hint Immediate hasbinarycoproducts_op_hasbinaryproducts : typeclass_instances.

Definition hasbinarycoproducts_hasbinaryproducts_op {A : Type}
  `{Is1Cat A, hbp : !HasBinaryProducts A^op}
  : HasBinaryCoproducts A
  := hbp.
Hint Immediate hasbinarycoproducts_hasbinaryproducts_op : typeclass_instances.

Definition hasbinaryproducts_op_hasbinarycoproducts {A : Type}
  `{hbc : HasBinaryCoproducts A}
  : HasBinaryProducts A^op
  := hbc.
Hint Immediate hasbinarycoproducts_op_hasbinaryproducts : typeclass_instances.

Definition hasbinaryproducts_hasbinarycoproducts_op {A : Type}
  `{Is1Cat A, hbc : !HasBinaryCoproducts A^op}
  : HasBinaryProducts A
  := hbc.
Hint Immediate hasbinaryproducts_hasbinarycoproducts_op : typeclass_instances.

(** *** Symmetry of coproducts *)

Definition cat_bincoprod_swap {A : Type} `{Is1Cat A}
  {hbc : HasBinaryCoproducts A} (x y : A)
  : cat_bincoprod x y $-> cat_bincoprod y x.
Proof.
  exact (@cat_binprod_swap A^op _ _ _ _ hbc _ _).
Defined.

Definition cate_bincoprod_swap {A : Type} `{HasEquivs A}
  {hbc : HasBinaryCoproducts A} (x y : A)
  : cat_bincoprod x y $<~> cat_bincoprod y x.
Proof.
  exact (@cate_binprod_swap A^op _ _ _ _ _ hbc _ _).
Defined.

(** *** Associativity of coproducts *)

Lemma cate_coprod_assoc {A : Type} `{HasEquivs A}
  {hbc : HasBinaryCoproducts A} (x y z : A)
  : cat_bincoprod x (cat_bincoprod y z)
    $<~> cat_bincoprod (cat_bincoprod x y) z.
Proof.
  exact (@associator_cat_binprod A^op _ _ _ _ _ hbc x y z)^-1$.
Defined.

Definition associator_cat_bincoprod {A : Type} `{HasEquivs A}
  `{!HasBinaryCoproducts A}
  : Associator (fun x y => cat_bincoprod x y).
Proof.
  unfold Associator.
  snrapply associator_op'.
  1: exact _.
  nrapply associator_cat_binprod.
Defined.

(** *** Codiagonal *)

Definition cat_bincoprod_codiag {A : Type}
  `{Is1Cat A} (x : A) `{!BinaryCoproduct x x}
  : cat_bincoprod x x $-> x
  := cat_binprod_diag (A:=A^op) x.

(** *** Lemmas about [cat_bincoprod_rec] *)

Definition cat_bincoprod_fmap01_rec {A : Type}
  `{Is1Cat A, !HasBinaryCoproducts A} {w x y z : A}
  (f : z $-> w) (g : y $-> x) (h : x $-> w)
  : cat_bincoprod_rec f h $o fmap01 (fun x y => cat_bincoprod x y) z g
    $== cat_bincoprod_rec f (h $o g)
  := @cat_binprod_fmap01_corec A^op _ _ _ _
      hasbinaryproducts_op_hasbinarycoproducts _ _ _ _ f g h.

Definition cat_bincoprod_fmap10_rec {A : Type}
  `{Is1Cat A, !HasBinaryCoproducts A} {w x y z : A}
  (f : y $-> x) (g : x $-> w) (h : z $-> w) 
  : cat_bincoprod_rec g h $o fmap10 (fun x y => cat_bincoprod x y) f z
    $== cat_bincoprod_rec (g $o f) h
  := @cat_binprod_fmap10_corec A^op _ _ _ _
      hasbinaryproducts_op_hasbinarycoproducts _ _ _ _ f g h.

Definition cat_bincoprod_fmap11_rec {A : Type}
  `{Is1Cat A, !HasBinaryCoproducts A} {v w x y z : A}
  (f : y $-> w) (g : z $-> x) (h : w $-> v) (i : x $-> v)
  : cat_bincoprod_rec h i $o fmap11 (fun x y => cat_binprod x y) f g
    $== cat_bincoprod_rec (h $o f) (i $o g)
  := @cat_binprod_fmap11_corec A^op _ _ _ _
      hasbinaryproducts_op_hasbinarycoproducts _ _ _ _ _ f g h i.

Definition cat_bincoprod_rec_associator {A : Type} `{HasEquivs A}
  {hbc : HasBinaryCoproducts A}
  {w x y z : A} (f : w $-> z) (g : x $-> z) (h : y $-> z)
  : cat_bincoprod_rec (cat_bincoprod_rec f g) h $o associator_cat_bincoprod w x y
    $== cat_bincoprod_rec f (cat_bincoprod_rec g h).
Proof.
  nrapply cate_moveR_eV.
  symmetry.
  exact (cat_binprod_associator_corec
           (HasBinaryProducts0:=hasbinaryproducts_op_hasbinarycoproducts (hbc:=hbc))
           f g h).
Defined.

Definition cat_bincoprod_swap_rec {A : Type} `{Is1Cat A}
  `{!HasBinaryCoproducts A} {a b c : A} (f : a $-> c) (g : b $-> c)
  : cat_bincoprod_rec f g $o cat_bincoprod_swap b a $== cat_bincoprod_rec g f
  := @cat_binprod_swap_corec A^op _ _ _ _
      hasbinaryproducts_op_hasbinarycoproducts _ _ _ _ _.

(** *** Cocartesian Monoidal Structure *)

Global Instance ismonoidal_cat_bincoprod {A : Type} `{HasEquivs A}
  `{!HasBinaryCoproducts A} (zero : A) `{!IsInitial zero}
  : IsMonoidal A (fun x y => cat_bincoprod x y) zero | 10.
Proof.
  nrapply ismonoidal_op'.
  nrapply (ismonoidal_cat_binprod (A:=A^op) zero).
  by nrapply isterminal_op_isinitial.
Defined.

Global Instance issymmetricmonoidal_cat_bincoprod {A : Type} `{HasEquivs A}
  `{!HasBinaryCoproducts A} (zero : A) `{!IsInitial zero}
  : IsSymmetricMonoidal A (fun x y => cat_bincoprod x y) zero | 10.
Proof.
  nrapply issymmetricmonoidal_op'.
  nrapply (issymmetricmonoidal_cat_binprod (A:=A^op) zero).
  by nrapply isterminal_op_isinitial.
Defined.

(** *** Coproducts in Type *)

(** [Type] has all coproducts. *)
Global Instance hasallcoproducts_type : HasAllCoproducts Type.
Proof.
  intros I x.
  snrapply Build_Coproduct.
  - exact (sig (fun i : I => x i)).
  - exact (exist x).
  - intros A f [i xi].
    exact (f i xi).
  - intros A f i xi; reflexivity.
  - intros A f g p [i xi].
    exact (p i xi).
Defined.

(** In particular, [Type] has all binary coproducts. *)
Global Instance hasbinarycoproducts_type : HasBinaryCoproducts Type
  := {}.

(** ** Canonical coproduct-product map *)

(** There is a canonical map from a coproduct to a product when the indexing set has decidable equality and the category is pointed. *)
Definition cat_coprod_prod {I : Type} `{DecidablePaths I} {A : Type}
  `{Is1Cat A, !IsPointedCat A}
  (x : I -> A) `{!Coproduct I x, !Product I x}
  : cat_coprod I x $-> cat_prod I x. 
Proof.
  apply cat_coprod_rec.
  intros i.
  apply cat_prod_corec.
  intros a.
  destruct (dec_paths i a) as [p|].
  - destruct p.
    exact (Id _).
  - apply zero_morphism. 
Defined.

Definition cat_bincoprod_binprod {A : Type} `{Is1Cat A, !IsPointedCat A}
  (x y : A) `{!BinaryCoproduct x y, !BinaryProduct x y}
  : cat_bincoprod x y $-> cat_binprod x y.
Proof.
  nrapply cat_coprod_prod; exact _.
Defined.

(** *** Coproducts in the opposite category *)

Definition coproduct_op {I A : Type} (x : I -> A)
  `{Is1Cat A} {H' : Product I x}
  : Coproduct I (A:=A^op) x
  := H'.
  
Hint Immediate coproduct_op : typeclass_instances.
