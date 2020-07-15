Require Import Basics Types WildCat.
Require Import Algebra.Groups Algebra.AbGroups.AbelianGroup.

Local Open Scope mc_scope.
Local Open Scope mc_add_scope.

(** * Pushouts of abelian groups. *)

Definition ab_pushout {A B C : AbGroup}
           (f : A $-> B) (g : A $-> C) : AbGroup
  := QuotientAbGroup
       (ab_biprod B C)
       (grp_image (ab_biprod_corec f (g $o ab_homo_negation))).

(** Recursion principle. *)
Theorem ab_pushout_rec {A B C Y : AbGroup} {f : A $-> B} {g : A $-> C}
        (b : B $-> Y) (c : C $-> Y) (p : b o f == c o g)
  : ab_pushout f g $-> Y.
Proof.
  srapply grp_quotient_rec.
  - exact (ab_biprod_rec b c).
  - intros [[x y] q]; strip_truncations; simpl.
    destruct q as [a q]. cbn in q.
    refine (ap (uncurry (fun x y => b x + c y)) q^ @ _).
    unfold uncurry; cbn.
    refine (ap011 sg_op (p a) (preserves_negate (f:=c $o g) _) @ _).
    exact (right_inverse _).
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
  apply qglue.
  pose (bc := grp_image_in (ab_biprod_corec f (g $o ab_homo_negation)) a).
  exists (-bc); simpl.
  apply path_prod; simpl.
  - exact (right_identity (- f a))^.
  - rewrite (preserves_negate (f:=g)).
    refine (negate_involutive _ @ _).
    symmetry.
    exact (ap (fun x => x + g a) negate_mon_unit @ left_identity _).
Defined.

Proposition ab_pushout_rec_beta `{Funext} {A B C Y : AbGroup}
            {f : A $-> B} {g : A $-> C}
            (phi : ab_pushout f g $-> Y)
  : ab_pushout_rec (phi $o ab_pushout_inl) (phi $o ab_pushout_inr)
                   (fun a:A => ap phi (ab_pushout_commsq a)) = phi.
Proof.
  pose (N := grp_image (ab_biprod_corec f (g $o ab_homo_negation))).
  apply (equiv_ap' (equiv_grp_quotient_ump (G:=ab_biprod B C) N Y)^-1%equiv _ _)^-1.
  srapply path_sigma_hprop.
  change (ab_pushout_rec
            (phi $o ab_pushout_inl) (phi $o ab_pushout_inr)
            (fun a : A => ap phi (ab_pushout_commsq a)) $o grp_quotient_map
          =  phi $o grp_quotient_map).
  refine (grp_quotient_rec_beta N Y _ _ @ _).
  apply equiv_path_grouphomomorphism; intro bc.
  exact (ab_biprod_rec_beta' (phi $o grp_quotient_map) bc).
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
