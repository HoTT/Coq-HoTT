From HoTT Require Import Basics Types Truncations.Core.
Require Import WildCat.
Require Import HSet.
Require Import AbelianGroup.
Require Import Modalities.ReflectiveSubuniverse.

Local Open Scope mc_add_scope.

(** * Biproducts of abelian groups *)

Definition ab_biprod@{u} (A B : AbGroup@{u}) : AbGroup@{u}.
Proof.
  rapply (Build_AbGroup (grp_prod A B)).
  intros [a b] [a' b'].
  apply path_prod; simpl; apply commutativity.
Defined.

(** These inherit [IsEmbedding] instances from their [grp_prod] versions. *)
Definition ab_biprod_inl {A B : AbGroup} : A $-> ab_biprod A B := grp_prod_inl.
Definition ab_biprod_inr {A B : AbGroup} : B $-> ab_biprod A B := grp_prod_inr.

(** These inherit [IsSurjection] instances from their [grp_prod] versions. *)
Definition ab_biprod_pr1 {A B : AbGroup} : ab_biprod A B $-> A := grp_prod_pr1.
Definition ab_biprod_pr2 {A B : AbGroup} : ab_biprod A B $-> B := grp_prod_pr2.

Definition ab_biprod_ind {A B : AbGroup}
  (P : ab_biprod A B -> Type)
  (Hinl : forall a, P (ab_biprod_inl a))
  (Hinr : forall b, P (ab_biprod_inr b))
  (Hop : forall x y, P x -> P y -> P (x + y))
  : forall x, P x.
Proof.
  intros [a b].
  snapply ((grp_prod_decompose a b)^ # _).
  apply Hop.
  - exact (Hinl a).
  - exact (Hinr b).
Defined.

Definition ab_biprod_ind_homotopy {A B C : AbGroup}
  {f g : ab_biprod A B $-> C}
  (Hinl : f $o ab_biprod_inl $== g $o ab_biprod_inl)
  (Hinr : f $o ab_biprod_inr $== g $o ab_biprod_inr)
  : f $== g.
Proof.
  rapply ab_biprod_ind.
  - exact Hinl.
  - exact Hinr.
  - intros x y p q.
    lhs napply grp_homo_op.
    rhs napply grp_homo_op.
    f_ap.
Defined.

(* Maps out of biproducts are determined on the two inclusions. *)
Definition equiv_ab_biprod_ind_homotopy `{Funext} {A B X : AbGroup} (phi psi : ab_biprod A B $-> X)
  : (phi $o ab_biprod_inl == psi $o ab_biprod_inl)
    * (phi $o ab_biprod_inr == psi $o ab_biprod_inr)
  <~> phi == psi.
Proof.
  apply equiv_iff_hprop.
  - exact (uncurry ab_biprod_ind_homotopy).
  - exact (fun h => (fun a => h _, fun b => h _)).
Defined.

(** Recursion principle *)
Proposition ab_biprod_rec {A B Y : AbGroup}
            (f : A $-> Y) (g : B $-> Y)
  : (ab_biprod A B) $-> Y.
Proof.
  snapply Build_GroupHomomorphism.
  - intros [a b]; exact (f a + g b).
  - intros [a b] [a' b']; simpl.
    rewrite (grp_homo_op f).
    rewrite (grp_homo_op g).
    rewrite (associativity _ (g b) _).
    rewrite <- (associativity _ (f a') _).
    rewrite (commutativity (f a') _).
    rewrite (associativity _ (g b) _).
    exact (associativity _ (f a') _)^.
Defined.

Corollary ab_biprod_rec_uncurried {A B Y : AbGroup}
  : (A $-> Y) * (B $-> Y)
    -> (ab_biprod A B) $-> Y.
Proof.
  intros [f g]. exact (ab_biprod_rec f g).
Defined.

Proposition ab_biprod_rec_eta {A B Y : AbGroup}
            (u : ab_biprod A B $-> Y)
  : ab_biprod_rec (u $o ab_biprod_inl) (u $o ab_biprod_inr) == u.
Proof.
  intros [a b]; simpl.
  refine ((grp_homo_op u _ _)^ @ ap u _).
  apply path_prod.
  - exact (right_identity a).
  - exact (left_identity b).
Defined.

Proposition ab_biprod_rec_beta_inl {A B Y : AbGroup}
            (a : A $-> Y) (b : B $-> Y)
  : (ab_biprod_rec a b) $o ab_biprod_inl == a.
Proof.
  intro x; simpl.
  rewrite (grp_homo_unit b).
  exact (right_identity (a x)).
Defined.

Proposition ab_biprod_rec_beta_inr {A B Y : AbGroup}
            (a : A $-> Y) (b : B $-> Y)
  : (ab_biprod_rec a b) $o ab_biprod_inr == b.
Proof.
  intro y; simpl.
  rewrite (grp_homo_unit a).
  exact (left_identity (b y)).
Defined.

Theorem isequiv_ab_biprod_rec `{Funext} {A B Y : AbGroup}
  : IsEquiv (@ab_biprod_rec_uncurried A B Y).
Proof.
  srapply isequiv_adjointify.
  - intro phi.
    exact (phi $o ab_biprod_inl, phi $o ab_biprod_inr).
  - intro phi.
    apply equiv_path_grouphomomorphism.
    exact (ab_biprod_rec_eta phi).
  - intros [a b].
    apply path_prod.
    + apply equiv_path_grouphomomorphism.
      apply ab_biprod_rec_beta_inl.
    + apply equiv_path_grouphomomorphism.
      apply ab_biprod_rec_beta_inr.
Defined.

(** Corecursion principle, inherited from Groups/Group.v. *)
Definition ab_biprod_corec {A B X : AbGroup} (f : X $-> A) (g : X $-> B)
  : X $-> ab_biprod A B
  := grp_prod_corec f g.

(** *** Functoriality of [ab_biprod] *)

Definition functor_ab_biprod {A A' B B' : AbGroup} (f : A $-> A') (g: B $-> B')
  : ab_biprod A B $-> ab_biprod A' B'
  := (ab_biprod_corec (f $o ab_biprod_pr1) (g $o ab_biprod_pr2)).

Definition ab_biprod_functor_beta {Z X Y A B : AbGroup} (f0 : Z $-> X) (f1 : Z $-> Y)
           (g0 : X $-> A) (g1 : Y $-> B)
  : functor_ab_biprod g0 g1 $o ab_biprod_corec f0 f1
                      $== ab_biprod_corec (g0 $o f0) (g1 $o f1)
  := fun _ => idpath.

Instance is0bifunctor_ab_biprod : Is0Bifunctor ab_biprod.
Proof.
  srapply Build_Is0Bifunctor'.
  snapply Build_Is0Functor.
  intros [A B] [A' B'] [f g].
  exact (functor_ab_biprod f g).
Defined.

Instance is1bifunctor_ab_biprod : Is1Bifunctor ab_biprod.
Proof.
  snapply Build_Is1Bifunctor'.
  snapply Build_Is1Functor.
  - intros [A B] [A' B'] [f g] [f' g'] [p q] [a b].
    snapply equiv_path_prod.
    exact (p a, q b).
  - reflexivity.
  - cbn; reflexivity.
Defined.

Definition isequiv_functor_ab_biprod {A A' B B' : AbGroup}
           (f : A $-> A') (g : B $-> B') `{IsEquiv _ _ f} `{IsEquiv _ _ g}
  : IsEquiv (functor_ab_biprod f g).
Proof.
  srapply isequiv_adjointify.
  1: { rapply functor_ab_biprod;
       apply grp_iso_inverse.
       + exact (Build_GroupIsomorphism _ _ f _).
       + exact (Build_GroupIsomorphism _ _ g _). }
  all: intros [a b]; simpl.
  all: apply path_prod'.
  1,2: apply eisretr.
  all: apply eissect.
Defined.

Definition equiv_functor_ab_biprod {A A' B B' : AbGroup}
           (f : A $-> A') (g : B $-> B') `{IsEquiv _ _ f} `{IsEquiv _ _ g}
  : GroupIsomorphism (ab_biprod A B) (ab_biprod A' B')
  := Build_GroupIsomorphism _ _ _ (isequiv_functor_ab_biprod f g).

(** Biproducts preserve embeddings. *)
Definition functor_ab_biprod_embedding {A A' B B' : AbGroup}
           (i : A $-> B) (i' : A' $-> B')
           `{IsEmbedding i} `{IsEmbedding i'}
  : IsEmbedding (functor_ab_biprod i i').
Proof.
  intros [b b'].
  apply hprop_allpath.
  intros [[a0 a0'] p] [[a1 a1'] p']; cbn in p, p'.
  rapply path_sigma_hprop; cbn.
  pose (q := (equiv_path_prod _ _)^-1 p); cbn in q.
  pose (q' := (equiv_path_prod _ _)^-1 p'); cbn in q'.
  destruct q as [q0 q1], q' as [q0' q1'].
  apply path_prod; rapply isinj_embedding; cbn.
  - exact (q0 @ q0'^).
  - exact (q1 @ q1'^).
Defined.

(** Products preserve surjections. *)
Definition functor_ab_biprod_surjection `{Funext} {A A' B B' : AbGroup}
           (p : A $-> B) (p' : A' $-> B')
           `{S : IsSurjection p} `{S' : IsSurjection p'}
  : IsSurjection (functor_ab_biprod p p').
Proof.
  intros [b b'].
  pose proof (a := S b); pose proof (a' := S' b').
  apply center in a, a'.
  strip_truncations.
  rapply contr_inhabited_hprop.
  apply tr.
  exists (ab_biprod_inl a.1 + ab_biprod_inr a'.1); cbn.
  apply path_prod;
    refine (grp_homo_op _ _ _ @ _);
    rewrite (grp_homo_unit _);
    cbn.
  - exact (right_identity _ @ a.2).
  - exact (left_identity _ @ a'.2).
Defined.

(** *** Lemmas for working with biproducts *)

(** The swap isomorphism of the biproduct of two groups. *)
Definition direct_sum_swap {A B : AbGroup}
  : ab_biprod A B $<~> ab_biprod B A.
Proof.
  snapply Build_GroupIsomorphism'.
  - apply equiv_prod_symm.
  - intro; reflexivity.
Defined.

(** Addition [+] is a group homomorphism [A+A -> A]. *)
Definition ab_codiagonal {A : AbGroup} : ab_biprod A A $-> A
  := ab_biprod_rec grp_homo_id grp_homo_id.

Definition ab_codiagonal_natural {A B : AbGroup} (f : A $-> B)
  : f $o ab_codiagonal $== ab_codiagonal $o functor_ab_biprod f f
  := fun a => grp_homo_op f _ _.

Definition ab_diagonal {A : AbGroup} : A $-> ab_biprod A A
  := ab_biprod_corec grp_homo_id grp_homo_id.

(** Given two abelian group homomorphisms [f] and [g], their pairing [(f, g) : B -> A + A] can be written as a composite. Note that [ab_biprod_corec] is an alias for [grp_prod_corec]. *)
Lemma ab_biprod_corec_diagonal `{Funext} {A B : AbGroup} (f g : B $-> A)
  : ab_biprod_corec f g = (functor_ab_biprod f g) $o ab_diagonal.
Proof.
  apply equiv_path_grouphomomorphism; reflexivity.
Defined.

(** Precomposing the codiagonal with the swap map has no effect. *)
Lemma ab_codiagonal_swap `{Funext} {A : AbGroup}
  : (@ab_codiagonal A) $o direct_sum_swap = ab_codiagonal.
Proof.
  apply equiv_path_grouphomomorphism.
  intro a; cbn.
  exact (abgroup_commutative _ _ _).
Defined.

(** The corresponding result for the diagonal is true definitionally, so it isn't strictly necessary to state it, but we record it anyways. *)
Definition ab_diagonal_swap {A : AbGroup}
  : direct_sum_swap $o (@ab_diagonal A) = ab_diagonal
  := idpath.

(** The biproduct is associative. *)
Lemma ab_biprod_assoc {A B C : AbGroup}
  : ab_biprod A (ab_biprod B C) $<~> ab_biprod (ab_biprod A B) C.
Proof.
  snapply Build_GroupIsomorphism'.
  - apply equiv_prod_assoc.
  - unfold IsSemiGroupPreserving; reflexivity.
Defined.

(** The iterated diagonals [(ab_diagonal + id) o ab_diagonal] and [(id + ab_diagonal) o ab_diagonal] agree, after reassociating the direct sum. *)
Definition ab_commute_id_diagonal {A : AbGroup}
  : (functor_ab_biprod (@ab_diagonal A) grp_homo_id) $o ab_diagonal
    = ab_biprod_assoc $o (functor_ab_biprod grp_homo_id ab_diagonal) $o ab_diagonal
  := idpath.

(** A similar result for the codiagonal. *)
Lemma ab_commute_id_codiagonal `{Funext} {A : AbGroup}
  : (@ab_codiagonal A) $o (functor_ab_biprod ab_codiagonal grp_homo_id) $o ab_biprod_assoc
    = ab_codiagonal $o (functor_ab_biprod grp_homo_id ab_codiagonal).
Proof.
  apply equiv_path_grouphomomorphism.
  intro a; cbn.
  exact (grp_assoc _ _ _)^.
Defined.

(** The next few results are used to prove associativity of the Baer sum. *)

(** A "twist" isomorphism [(A + B) + C <~> (C + B) + A]. *)
Lemma ab_biprod_twist {A B C : AbGroup@{u}}
  : ab_biprod (ab_biprod A B) C $<~> ab_biprod (ab_biprod C B) A.
Proof.
  snapply Build_GroupIsomorphism.
  - snapply Build_GroupHomomorphism.
    + intros [[a b] c].
      exact ((c,b),a).
    + unfold IsSemiGroupPreserving. reflexivity.
  - snapply isequiv_adjointify.
    + intros [[c b] a].
      exact ((a,b),c).
    + reflexivity.
    + reflexivity.
Defined.

(** The triagonal and cotriagonal homomorphisms. *)
Definition ab_triagonal {A : AbGroup} : A $-> ab_biprod (ab_biprod A A) A
  := (functor_ab_biprod ab_diagonal grp_homo_id) $o ab_diagonal.

Definition ab_cotriagonal {A : AbGroup} : ab_biprod (ab_biprod A A) A $-> A
  := ab_codiagonal $o (functor_ab_biprod ab_codiagonal grp_homo_id).

(** For an abelian group [A], precomposing the triagonal on [A] with the twist map on [A] has no effect. *)
Definition ab_triagonal_twist {A : AbGroup}
  : ab_biprod_twist $o @ab_triagonal A = ab_triagonal
  := idpath.

(** A similar result for the cotriagonal. *)
Definition ab_cotriagonal_twist `{Funext} {A : AbGroup}
  : @ab_cotriagonal A $o ab_biprod_twist = ab_cotriagonal.
Proof.
  apply equiv_path_grouphomomorphism.
  intro x. cbn.
  refine ((grp_assoc _ _ _)^ @ _).
  refine (abgroup_commutative _ _ _ @ _).
  exact (ap (fun a =>  a + snd x) (abgroup_commutative _ _ _)).
Defined.
