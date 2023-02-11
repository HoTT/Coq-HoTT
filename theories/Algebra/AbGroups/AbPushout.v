Require Import WildCat HSet.
Require Export Algebra.Groups.Image Algebra.Groups.QuotientGroup.
Require Import AbGroups.AbelianGroup AbGroups.Biproduct.

Local Open Scope mc_scope.
Local Open Scope mc_add_scope.

(** * Pushouts of abelian groups. *)

(** The pushout of two morphisms [f : A $-> B] and [g : A $-> C] is constructed as the quotient of the biproduct [B + C] by the image of [f - g]. Since this image comes up repeatedly, we name it. *)

Definition ab_pushout_subgroup {A B C : AbGroup} (f : A $-> B) (g : A $-> C)
  : Subgroup (ab_biprod B C)
  := grp_image (ab_biprod_corec (ab_homo_negation $o f) g).

Definition ab_pushout {A B C : AbGroup}
           (f : A $-> B) (g : A $-> C) : AbGroup
  := QuotientAbGroup (ab_biprod B C) (ab_pushout_subgroup f g).

(** Recursion principle. *)
Theorem ab_pushout_rec {A B C Y : AbGroup} {f : A $-> B} {g : A $-> C}
        (b : B $-> Y) (c : C $-> Y) (p : b o f == c o g)
  : ab_pushout f g $-> Y.
Proof.
  srapply grp_quotient_rec.
  - exact (ab_biprod_rec b c).
  - intros [x y] q; strip_truncations; simpl.
    destruct q as [a q]. cbn in q.
    refine (ap (uncurry (fun x y => b x + c y)) q^ @ _).
    unfold uncurry; cbn.
    refine (ap011 sg_op (preserves_negate _) (p a)^ @ _).
    exact (left_inverse _).
Defined.

Corollary ab_pushout_rec_uncurried {A B C : AbGroup}
          (f : A $-> B) (g : A $-> C) (Y : AbGroup)
  : {b : B $-> Y & {c : C $-> Y & b o f == c o g}}
      -> (ab_pushout f g $-> Y).
Proof.
  intros [b [c p]]; exact (ab_pushout_rec b c p).
Defined.

Definition ab_pushout_inl {A B C : AbGroup} {f : A $-> B} {g : A $-> C}
  : B $-> ab_pushout f g := grp_quotient_map $o grp_prod_inl.

Definition ab_pushout_inr {A B C : AbGroup} {f : A $-> B} {g : A $-> C}
  : C $-> ab_pushout f g := grp_quotient_map $o grp_prod_inr.

Proposition ab_pushout_commsq {A B C : AbGroup} {f : A $-> B} {g : A $-> C}
  : (@ab_pushout_inl A B C f g) $o f == ab_pushout_inr $o g.
Proof.
  intro a.
  apply qglue; cbn.
  apply tr.
  exists a.
  apply path_prod; simpl.
  - exact (right_identity _)^.
  - rewrite negate_mon_unit.
    exact (left_identity _)^.
Defined.

(** A map out of the pushout induces itself after restricting along the inclusions. *)
Proposition ab_pushout_rec_beta `{Funext} {A B C Y : AbGroup}
            {f : A $-> B} {g : A $-> C}
            (phi : ab_pushout f g $-> Y)
  : ab_pushout_rec (phi $o ab_pushout_inl) (phi $o ab_pushout_inr)
                   (fun a:A => ap phi (ab_pushout_commsq a)) = phi.
Proof.
  rapply (equiv_ap' (equiv_quotient_abgroup_ump (G:=ab_biprod B C) _ Y)^-1%equiv _ _)^-1.
  srapply path_sigma_hprop.
  refine (grp_quotient_rec_beta _ Y _ _ @ _).
  apply equiv_path_grouphomomorphism; intro bc.
  exact (ab_biprod_rec_beta' (phi $o grp_quotient_map) bc).
Defined.

(** Restricting [ab_pushout_rec] along [ab_pushout_inl] recovers the left inducing map. *)
Lemma ab_pushout_rec_beta_left {A B C Y : AbGroup}
            (f : A $-> B) (g : A $-> C)
            (l : B $-> Y) (r : C $-> Y) (p : l o f == r o g)
  : ab_pushout_rec l r p $o ab_pushout_inl == l.
Proof.
  intro x; simpl.
  rewrite (grp_homo_unit r).
  apply right_identity.
Defined.

Lemma ab_pushout_rec_beta_right {A B C Y : AbGroup}
      (f : A $-> B) (g : A $-> C)
      (l : B $-> Y) (r : C $-> Y) (p : l o f == r o g)
  : ab_pushout_rec l r p $o ab_pushout_inr == r.
Proof.
  intro x; simpl.
  rewrite (grp_homo_unit l).
  apply left_identity.
Defined.

Theorem isequiv_ab_pushout_rec `{Funext} {A B C Y : AbGroup}
        {f : A $-> B} {g : A $-> C}
  : IsEquiv (ab_pushout_rec_uncurried f g Y).
Proof.
  srapply isequiv_adjointify.
  - intro phi.
    refine (phi $o ab_pushout_inl; phi $o ab_pushout_inr; _).
    intro a.
    apply (ap phi).
    exact (ab_pushout_commsq a).
  - intro phi.
    exact (ab_pushout_rec_beta phi).
  - intros [b [c p]].
    srapply path_sigma.
    + apply equiv_path_grouphomomorphism.
      intro x; simpl.
      refine (ap (fun k => b x + k) (grp_homo_unit c) @ _).
      apply right_identity.
    + refine (transport_sigma' _ _ @ _).
      apply path_sigma_hprop; simpl.
      apply equiv_path_grouphomomorphism.
      intro y; simpl.
      refine (ap (fun k => k + c y) (grp_homo_unit b) @ _).
      apply left_identity.
Defined.

Definition path_ab_pushout `{Univalence} {A B C : AbGroup} (f : A $-> B) (g : A $-> C)
           (bc0 bc1 : ab_biprod B C)
  : @in_cosetL (ab_biprod B C) (ab_pushout_subgroup f g) bc0 bc1
               <~> (grp_quotient_map bc0 = grp_quotient_map bc1 :> ab_pushout f g).
Proof.
  rapply path_quotient.
Defined.

(** The pushout of an embedding is an embedding. *)
Definition ab_pushout_embedding_inl `{Univalence} {A B C : AbGroup}
           (f : A $-> B) (g : A $-> C) `{IsEmbedding g}
  : IsEmbedding (ab_pushout_inl (f:=f) (g:=g)).
Proof.
  apply isembedding_isinj_hset.
  intros c0 c1.
  refine (_ o (path_ab_pushout f g (grp_prod_inl c0) (grp_prod_inl c1))^-1).
  rapply Trunc_ind.
  cbn; intros [a p].
  assert (z : a = mon_unit).
  - rapply (isinj_embedding g).
    refine (ap snd p @ _); cbn.
    exact (left_inverse mon_unit @ (grp_homo_unit g)^).
  - apply (grp_moveR_M1).
    refine (_ @ ap fst p); cbn; symmetry.
    refine (_ @ negate_mon_unit).
    refine (ap _ _).
    exact (ap f z @ grp_homo_unit f).
Defined.

(** Functoriality of pushouts *)
Definition functor_ab_pushout {A A' B B' C C' : AbGroup}
           (f : A $-> B) (f' : A' $-> B')
           (g : A $-> C) (g' : A' $-> C')
           (alpha : A $-> A') (beta : B $-> B') (gamma : C $-> C')
           (h : beta $o f == f' $o alpha) (k : g' $o alpha == gamma $o g)
  : ab_pushout f g $-> ab_pushout f' g'.
Proof.
  srapply ab_pushout_rec.
  - exact (ab_pushout_inl $o beta).
  - exact (ab_pushout_inr $o gamma).
  - intro a.
    refine (ap ab_pushout_inl (h a) @ _ @ ap ab_pushout_inr (k a)).
    exact (ab_pushout_commsq (alpha a)).
Defined.

(** ** Properties of pushouts of maps *)

(** The pushout of an epimorphism is an epimorphism. *)
Global Instance ab_pushout_surjection_inr `{Univalence} {A B C : AbGroup}
  (f : A $-> B) (g : A $-> C) `{S : IsSurjection f}
  : IsSurjection (ab_pushout_inr (f:=f) (g:=g)).
Proof.
  intro x.
  rapply contr_inhabited_hprop.
  (* To find a preimage of [x], we may first choose a representative [x']. *)
  assert (x' : merely (hfiber grp_quotient_map x)).
  1: apply issurj_class_of.
  strip_truncations; destruct x' as [[b c] p].
  (* Now [x] = [b + c] in the quotient. We find a preimage of [a]. *)
  assert (a : merely (hfiber f b)).
  1: apply S.
  strip_truncations; destruct a as [a q].
  refine (tr (g a + c; _)).
  refine (grp_homo_op _ _ _ @ _).
  refine (ap (fun z => sg_op z _) _^ @ _).
  { refine (_^ @ ab_pushout_commsq _).
    exact (ap _ q). }
  refine (ap grp_quotient_map _ @ p).
  apply path_prod'; cbn.
  - apply right_identity.
  - apply left_identity.
Defined.
