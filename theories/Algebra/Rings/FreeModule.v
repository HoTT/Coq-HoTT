From HoTT Require Import Basics Types.
From HoTT.WildCat Require Import Core.
Require Import Classes.interfaces.canonical_names.
Require Import Spaces.Nat.Core.
Require Import HSet Truncations.Core Modalities.ReflectiveSubuniverse.
Require Import Algebra.Groups.Group Algebra.Groups.Subgroup.
Require Import Algebra.AbGroups.AbelianGroup Algebra.AbGroups.AbHom.
Require Import Algebra.Rings.Ring Algebra.Rings.CRing Algebra.Rings.Module.
Require Import Algebra.Rings.Bezout.

Local Open Scope module_scope.
Local Open Scope mc_add_scope.

(** * Splitting of module homomorphisms with a section *)

(** The inclusion of a submodule as a module homomorphism. *)
Definition lm_subincl {R : Ring} {M : LeftModule R} (N : LeftSubmodule M)
  : leftmodule_leftsubmodule N $-> M.
Proof.
  snapply Build_LeftModuleHomomorphism'.
  - exact pr1.
  - intros r x y; reflexivity.
Defined.

Section Splitting.
  Context {R : Ring} {M Q : LeftModule R}
    (f : M $-> Q) (s : Q $-> M) (hs : forall q, f (s q) = q).

  (** The complementary projection [id - s ∘ f]. *)
  Definition lm_split_endo : M $-> M.
  Proof.
    snapply Build_LeftModuleHomomorphism.
    - exact (grp_homo_id - grp_homo_compose s f).
    - intros r m; cbn.
      assert (p : s (f (r *L m)) = r *L s (f m)).
      { transitivity (s (r *L f m)).
        - apply ap; napply lm_homo_lact.
        - napply lm_homo_lact. }
      lhs napply (ap (fun z => r *L m - z) p).
      symmetry.
      lhs napply (lm_dist_l r m (- s (f m))).
      refine (ap (fun z => r *L m + z) _).
      exact (lm_neg r (s (f m))).
  Defined.

  (** The projection of [M] onto the kernel of [f]. *)
  Definition lm_split_proj : M $-> lm_kernel f.
  Proof.
    snapply (lm_corestrict (lm_kernel f) lm_split_endo).
    intro m; cbn.
    lhs napply grp_homo_op.
    lhs napply (ap (fun z => f m + z) (grp_homo_inv f (s (f m)))).
    lhs napply (ap (fun z => f m + (- z)) (hs (f m))).
    apply right_inverse.
  Defined.

  (** The forward map of the splitting. *)
  Definition lm_split_fwd : M $-> lm_prod (lm_kernel f) Q
    := lm_prod_corec M lm_split_proj f.

  (** The backward map of the splitting. *)
  Definition lm_split_bwd : lm_prod (lm_kernel f) Q $-> M
    := lm_prod_rec (lm_subincl (lm_kernel f)) s.

  Definition lm_split_bwd_fwd (m : M) : lm_split_bwd (lm_split_fwd m) = m.
  Proof.
    cbn.
    refine ((grp_assoc m (- s (f m)) (s (f m)))^ @ _).
    refine (ap (fun z => m + z) (left_inverse (s (f m))) @ _).
    apply right_identity.
  Defined.

  Definition lm_split_fwd_bwd (kq : lm_prod (lm_kernel f) Q)
    : lm_split_fwd (lm_split_bwd kq) = kq.
  Proof.
    destruct kq as [[k1 k2] q].
    assert (faux : f (k1 + s q) = q).
    { lhs napply grp_homo_op.
      lhs napply (ap (fun z => z + f (s q)) k2).
      lhs napply (ap (fun z => mon_unit + z) (hs q)).
      apply left_identity. }
    snapply path_prod'.
    - apply path_sigma_hprop; cbn.
      lhs napply (ap (fun w => k1 + s q - s w) faux).
      refine ((grp_assoc k1 (s q) (- s q))^ @ _).
      refine (ap (fun z => k1 + z) (right_inverse (s q)) @ _).
      apply right_identity.
    - exact faux.
  Defined.

  (** [M] is the direct sum of the kernel of [f] and [Q]. *)
  Definition lm_split_iso
    : LeftModuleIsomorphism M (lm_prod (lm_kernel f) Q).
  Proof.
    snapply Build_LeftModuleIsomorphism'.
    - snapply Build_GroupIsomorphism.
      + exact lm_split_fwd.
      + exact (isequiv_adjointify lm_split_fwd lm_split_bwd
                 lm_split_fwd_bwd lm_split_bwd_fwd).
    - intros r m; napply lm_homo_lact.
  Defined.

End Splitting.

(** * Free modules *)

(** The trivial (zero) module. *)
Definition lm_zero (R : Ring) : LeftModule R.
Proof.
  snapply (Build_LeftModule R abgroup_trivial).
  snapply Build_IsLeftModule.
  - exact (fun _ x => x).
  - intros r m n; apply path_contr.
  - intros r s m; apply path_contr.
  - intros r s m; apply path_contr.
  - intros m; apply path_contr.
Defined.

(** The regular module: a ring as a module over itself. *)
Definition lm_regular (R : Ring) : LeftModule R
  := Build_LeftModule R R _.

(** The free module [R^n]. *)
Fixpoint lm_power (R : Ring) (n : nat) : LeftModule R :=
  match n with
  | 0%nat => lm_zero R
  | S k => lm_prod (lm_regular R) (lm_power R k)
  end.

(** A module is free if it is isomorphic to some [R^n]. *)
Definition IsFreeModule {R : Ring} (M : LeftModule R) : Type
  := merely { n : nat & LeftModuleIsomorphism M (lm_power R n) }.

(** Composition of module isomorphisms. *)
Definition lm_iso_compose {R : Ring} {M N L : LeftModule R}
  (g : LeftModuleIsomorphism N L) (f : LeftModuleIsomorphism M N)
  : LeftModuleIsomorphism M L.
Proof.
  snapply Build_LeftModuleIsomorphism.
  - exact (lm_homo_compose g f).
  - rapply isequiv_compose.
Defined.

(** Freeness transports across isomorphisms. *)
Definition isfreemodule_iso {R : Ring} {M N : LeftModule R}
  (e : LeftModuleIsomorphism M N) (H : IsFreeModule N) : IsFreeModule M.
Proof.
  strip_truncations.
  exact (tr (H.1; lm_iso_compose H.2 e)).
Defined.

(** The zero module is a left unit for the direct product. *)
Definition lm_prod_zero_l {R : Ring} {X : LeftModule R}
  : LeftModuleIsomorphism (lm_prod (lm_zero R) X) X.
Proof.
  snapply Build_LeftModuleIsomorphism.
  - exact lm_prod_snd.
  - snapply isequiv_adjointify.
    + exact lm_prod_inr.
    + intro x; reflexivity.
    + intros [z x]; snapply path_prod'; [apply path_contr | reflexivity].
Defined.

(** The zero module is a right unit for the direct product. *)
Definition lm_prod_zero_r {R : Ring} {X : LeftModule R}
  : LeftModuleIsomorphism (lm_prod X (lm_zero R)) X.
Proof.
  snapply Build_LeftModuleIsomorphism.
  - exact lm_prod_fst.
  - snapply isequiv_adjointify.
    + exact lm_prod_inl.
    + intro x; reflexivity.
    + intros [x z]; snapply path_prod'; [reflexivity | apply path_contr].
Defined.

(** Associativity of the direct product. *)
Definition lm_prod_assoc {R : Ring} {A B C : LeftModule R}
  : LeftModuleIsomorphism (lm_prod (lm_prod A B) C) (lm_prod A (lm_prod B C)).
Proof.
  snapply Build_LeftModuleIsomorphism.
  - exact (lm_prod_corec _ (lm_homo_compose lm_prod_fst lm_prod_fst)
             (lm_prod_corec _ (lm_homo_compose lm_prod_snd lm_prod_fst) lm_prod_snd)).
  - snapply isequiv_adjointify.
    + exact (lm_prod_corec _
               (lm_prod_corec _ lm_prod_fst (lm_homo_compose lm_prod_fst lm_prod_snd))
               (lm_homo_compose lm_prod_snd lm_prod_snd)).
    + intros [a [b c]]; reflexivity.
    + intros [[a b] c]; reflexivity.
Defined.

(** The direct product is functorial in its second argument. *)
Definition lm_prod_iso_r {R : Ring} {A B B' : LeftModule R}
  (eB : LeftModuleIsomorphism B B')
  : LeftModuleIsomorphism (lm_prod A B) (lm_prod A B').
Proof.
  snapply Build_LeftModuleIsomorphism.
  - exact (lm_prod_corec _ lm_prod_fst (lm_homo_compose eB lm_prod_snd)).
  - snapply isequiv_adjointify.
    + exact (lm_prod_corec _ lm_prod_fst
               (lm_homo_compose (lm_iso_inverse eB) lm_prod_snd)).
    + intros [a b']; snapply path_prod'; [ reflexivity | exact (eisretr _ b') ].
    + intros [a b]; snapply path_prod'; [ reflexivity | exact (eissect _ b) ].
Defined.

(** The direct product is functorial in both arguments. *)
Definition lm_prod_iso2 {R : Ring} {A A' B B' : LeftModule R}
  (eA : LeftModuleIsomorphism A A') (eB : LeftModuleIsomorphism B B')
  : LeftModuleIsomorphism (lm_prod A B) (lm_prod A' B').
Proof.
  snapply Build_LeftModuleIsomorphism.
  - exact (lm_prod_corec _ (lm_homo_compose eA lm_prod_fst)
             (lm_homo_compose eB lm_prod_snd)).
  - snapply isequiv_adjointify.
    + exact (lm_prod_corec _ (lm_homo_compose (lm_iso_inverse eA) lm_prod_fst)
               (lm_homo_compose (lm_iso_inverse eB) lm_prod_snd)).
    + intros [a' b']; snapply path_prod'; [ exact (eisretr _ a') | exact (eisretr _ b') ].
    + intros [a b]; snapply path_prod'; [ exact (eissect _ a) | exact (eissect _ b) ].
Defined.

(** [R^m] direct sum [R^n] is [R^(m+n)]. *)
Definition lm_power_add {R : Ring} (m n : nat)
  : LeftModuleIsomorphism (lm_prod (lm_power R m) (lm_power R n))
      (lm_power R (m + n)%nat).
Proof.
  induction m as [|k IH].
  - exact lm_prod_zero_l.
  - exact (lm_iso_compose (lm_prod_iso_r IH) lm_prod_assoc).
Defined.

(** A direct sum of free modules is free. *)
Definition isfreemodule_prod {R : Ring} {M N : LeftModule R}
  (HM : IsFreeModule M) (HN : IsFreeModule N)
  : IsFreeModule (lm_prod M N).
Proof.
  strip_truncations.
  exact (tr ((HM.1 + HN.1)%nat;
    lm_iso_compose (lm_power_add HM.1 HN.1) (lm_prod_iso2 HM.2 HN.2))).
Defined.

(** A homomorphism with a section and free kernel and codomain has a free
    domain. *)
Definition isfreemodule_split {R : Ring} {M Q : LeftModule R}
  (f : M $-> Q) (s : Q $-> M) (hs : forall q, f (s q) = q)
  (Hk : IsFreeModule (lm_kernel f)) (HQ : IsFreeModule Q)
  : IsFreeModule M
  := isfreemodule_iso (lm_split_iso f s hs) (isfreemodule_prod Hk HQ).

(** [R^n] is free. *)
Definition isfreemodule_lm_power {R : Ring} (n : nat)
  : IsFreeModule (lm_power R n).
Proof.
  apply tr; exists n.
  snapply Build_LeftModuleIsomorphism.
  - exact (lm_homo_id _).
  - exact _.
Defined.

(** The regular module is free. *)
Definition isfreemodule_lm_regular {R : Ring}
  : IsFreeModule (lm_regular R)
  := tr (1%nat; lm_iso_inverse lm_prod_zero_r).

(** A contractible module is free of rank zero. *)
Definition isfreemodule_contr {R : Ring} (M : LeftModule R) `{Contr M}
  : IsFreeModule M.
Proof.
  apply tr; exists 0%nat.
  snapply Build_LeftModuleIsomorphism.
  - snapply Build_LeftModuleHomomorphism'.
    + exact (fun _ => 0).
    + intros r x y; apply path_contr.
  - rapply isequiv_contr_contr.
Defined.

(** An injective homomorphism corestricts to an isomorphism onto its image. *)
Definition lm_iso_image {R : Ring} {M N : LeftModule R} (f : M $-> N)
  `{IsEmbedding f}
  : LeftModuleIsomorphism M (lm_image f).
Proof.
  snapply Build_LeftModuleIsomorphism.
  - exact (lm_corestrict (lm_image f) f (fun m => tr (m; idpath))).
  - snapply isequiv_surj_emb.
    + apply BuildIsSurjection.
      intro b.
      napply (Trunc_functor (-1) _ b.2).
      intros [x q].
      exists x; apply path_sigma_hprop; exact q.
    + apply isembedding_isinj_hset.
      intros a b r.
      exact (isinj_embedding f _ a b (ap pr1 r)).
Defined.

(** Submodules with the same membership are isomorphic as modules. *)
Definition lm_iso_of_submodule_iff {R : Ring} {M : LeftModule R}
  (N N' : LeftSubmodule M) (h : forall y, N y <-> N' y)
  : LeftModuleIsomorphism (leftmodule_leftsubmodule N)
      (leftmodule_leftsubmodule N').
Proof.
  snapply Build_LeftModuleIsomorphism.
  - snapply Build_LeftModuleHomomorphism'.
    + exact (fun yn => (yn.1; fst (h yn.1) yn.2)).
    + intros r x y; by apply path_sigma_hprop.
  - snapply isequiv_adjointify.
    + exact (fun yn => (yn.1; snd (h yn.1) yn.2)).
    + intros [y hy]; by apply path_sigma_hprop.
    + intros [y hy]; by apply path_sigma_hprop.
Defined.

(** A homomorphism out of the regular module is multiplication by the image
    of [1]. *)
Definition lm_homo_regular_mult {R : Ring} {M : LeftModule R}
  (h : lm_regular R $-> M) (r : R) : h r = r *L h 1.
Proof.
  lhs napply (ap h (rng_mult_one_r r)^).
  napply lm_homo_lact.
Defined.

(** Divisibility is preserved by sums. *)
Definition rng_divides_plus {R : CRing} {d a b : R}
  (pa : rng_divides d a) (pb : rng_divides d b) : rng_divides d (a + b).
Proof.
  strip_truncations; destruct pa as [c1 p1], pb as [c2 p2].
  apply tr; exists (c1 + c2).
  exact (ap011 (+) p1 p2 @ (rng_dist_r c1 c2 d)^).
Defined.

(** Right multiplication by a ring element. *)
Definition lm_right_mult {R : Ring} (d : R) : lm_regular R $-> lm_regular R.
Proof.
  snapply Build_LeftModuleHomomorphism.
  - exact (grp_homo_rng_right_mult d).
  - intros r x; symmetry; rapply rng_mult_assoc.
Defined.

(** Over a commutative ring, multiplication by a regular element is an
    embedding. *)
Definition isembedding_lm_right_mult {R : CRing} (d : R) (hd : IsRegular d)
  : IsEmbedding (lm_right_mult (R:=R) d).
Proof.
  apply isembedding_isinj_hset.
  intros x y p.
  apply hd.
  exact (rng_mult_comm d x @ p @ rng_mult_comm y d).
Defined.

(** The principal submodule generated by a regular element is free of rank
    one. *)
Definition isfreemodule_image_right_mult {R : CRing} (d : R) (hd : IsRegular d)
  : IsFreeModule (lm_image (lm_right_mult (R:=R) d))
  := isfreemodule_iso
       (lm_iso_inverse
          (@lm_iso_image _ _ _ (lm_right_mult d) (isembedding_lm_right_mult d hd)))
       isfreemodule_lm_regular.

(** * Finitely generated submodules of [R] are free *)

(** A homomorphism out of [R^(S j)] decomposes along the first coordinate. *)
Definition lm_image_decomp {R : Ring} {j : nat}
  (g : lm_power R (S j) $-> lm_regular R) (x : lm_power R (S j))
  : g x = fst x *L g (lm_prod_inl 1)
          + lm_homo_compose g lm_prod_inr (snd x).
Proof.
  transitivity (g (lm_prod_inl (fst x) + lm_prod_inr (snd x))).
  - apply ap; snapply path_prod'.
    + exact (right_identity (fst x))^.
    + exact (left_identity (snd x))^.
  - lhs napply grp_homo_op.
    f_ap.
    exact (lm_homo_regular_mult (lm_homo_compose g lm_prod_inl) (fst x)).
Defined.

(** The image of a homomorphism [R^k -> R] over a Bézout ring is principal. *)
Definition lm_image_principal {R : CRing} `{IsBezoutRing R}
  : forall (k : nat) (g : lm_power R k $-> lm_regular R),
    merely { d : R & forall y, lm_image g y <-> rng_divides d y }.
Proof.
  induction k as [|j IH]; intro g.
  - apply tr; exists 0; intro y; split.
    + intros hy; strip_truncations; destruct hy as [x p].
      apply tr; exists 0.
      refine (p^ @ ap g (path_ishprop x mon_unit) @ grp_homo_unit g @ _).
      exact (rng_mult_zero_r 0)^.
    + intros hd; strip_truncations; destruct hd as [c p].
      apply tr; exists mon_unit.
      refine (grp_homo_unit g @ _).
      exact (p @ rng_mult_zero_r c)^.
  - pose (a := g (lm_prod_inl 1)).
    pose (g' := lm_homo_compose g lm_prod_inr).
    pose proof (IH g') as IHg'; strip_truncations; destruct IHg' as [d' H'].
    pose proof (bezout_relation a d') as hb; strip_truncations.
    destruct hb as [u [v hg]].
    apply tr; exists (u * a + v * d'); intro y; split.
    + intros hy; strip_truncations; destruct hy as [x p].
      refine (transport (rng_divides (u * a + v * d')) ((lm_image_decomp g x)^ @ p) _).
      apply rng_divides_plus.
      * exact (rng_divides_mul_l (fst x) (fst (fst hg))).
      * refine (rng_divides_trans (snd (fst hg)) _).
        exact (fst (H' (g' (snd x))) (tr (snd x; idpath))).
    + intros hd; strip_truncations; destruct hd as [c p].
      assert (hd' : lm_image g' d') by exact (snd (H' d') (rng_divides_refl d')).
      strip_truncations; destruct hd' as [x'' q].
      assert (hgg : lm_image g (u * a + v * d')).
      { apply tr.
        exists (u *L lm_prod_inl 1 + v *L lm_prod_inr x'').
        lhs napply grp_homo_op.
        f_ap.
        - lhs napply lm_homo_lact; reflexivity.
        - lhs napply lm_homo_lact; exact (ap (fun z => v *L z) q). }
      refine (transport (lm_image g) p^ _).
      rapply is_left_submodule; exact hgg.
Defined.

(** The difference of two module homomorphisms. *)
Definition lm_homo_sub {R : Ring} {M N : LeftModule R} (f g : M $-> N)
  : M $-> N.
Proof.
  snapply Build_LeftModuleHomomorphism.
  - exact (@lm_homo_map _ _ _ f - @lm_homo_map _ _ _ g).
  - intros r m; cbn.
    lhs napply (ap (fun z => z - g (r *L m)) (@lm_homo_lact _ _ _ f r m)).
    lhs napply (ap (fun z => r *L f m - z) (@lm_homo_lact _ _ _ g r m)).
    symmetry.
    lhs napply (lm_dist_l r (f m) (- g m)).
    napply (ap (fun z => r *L f m + z) (lm_neg r (g m))).
Defined.

(** Scalar multiplication by a fixed element, as a homomorphism out of the
    regular module. *)
Definition lm_scalar {R : Ring} {M : LeftModule R} (x : M)
  : lm_regular R $-> M.
Proof.
  snapply Build_LeftModuleHomomorphism.
  - snapply Build_GroupHomomorphism.
    + exact (fun c => c *L x).
    + intros c c'; napply lm_dist_r.
  - intros r c; symmetry; napply lm_assoc.
Defined.

(** Division by a regular element is well-defined. *)
Definition rng_div_regular {R : CRing} {d : R} (dreg : IsRegular d) {y : R}
  (h : rng_divides d y) : { c : R & y = c * d }.
Proof.
  napply (Trunc_rec (A := { c : R & y = c * d }) _ h).
  - apply hprop_allpath; intros [c p] [c' p']; apply path_sigma_hprop; cbn.
    apply dreg.
    exact (rng_mult_comm d c @ p^ @ p' @ rng_mult_comm c' d).
  - exact idmap.
Defined.

(** Dividing a homomorphism whose values are divisible by a regular [d]. *)
Definition lm_div_d {R : CRing} {d : R} (dreg : IsRegular d) {L : LeftModule R}
  (h : L $-> lm_regular R) (hdiv : forall l, rng_divides d (h l))
  : L $-> lm_regular R.
Proof.
  snapply Build_LeftModuleHomomorphism.
  - snapply Build_GroupHomomorphism.
    + exact (fun l => (rng_div_regular dreg (hdiv l)).1).
    + intros l l'; apply dreg.
      lhs napply rng_mult_comm.
      lhs_V napply (rng_div_regular dreg (hdiv (l + l'))).2.
      lhs napply grp_homo_op.
      lhs napply (ap011 (+) (rng_div_regular dreg (hdiv l)).2
                            (rng_div_regular dreg (hdiv l')).2).
      lhs_V napply rng_dist_r.
      napply rng_mult_comm.
  - intros r l; apply dreg.
    lhs napply rng_mult_comm.
    lhs_V napply (rng_div_regular dreg (hdiv (r *L l))).2.
    lhs napply (@lm_homo_lact _ _ _ h r l).
    lhs napply (ap (fun z => r * z) (rng_div_regular dreg (hdiv l)).2).
    lhs napply rng_mult_assoc.
    napply rng_mult_comm.
Defined.

(** A finitely generated submodule of [R] over a Bézout domain is free. *)
Definition isfreemodule_image_to_regular {R : CRing} `{IsBezoutDomain R} (k : nat)
  (g : lm_power R k $-> lm_regular R) : IsFreeModule (lm_image g).
Proof.
  pose proof (lm_image_principal k g) as hp; strip_truncations.
  destruct hp as [d Hg].
  destruct (intdom_zero_or_regular d) as [d0 | dreg].
  - napply isfreemodule_contr.
    snapply (Build_Contr _ (0; snd (Hg 0) (tr (0; (rng_mult_zero_l d)^)))).
    intros [y hy]; apply path_sigma_hprop; cbn.
    pose proof (transport (fun z => rng_divides z y) d0 (fst (Hg y) hy)) as hdy.
    strip_truncations; destruct hdy as [c q].
    exact (q @ rng_mult_zero_r c)^.
  - assert (hrm : forall y, lm_image g y <-> lm_image (lm_right_mult d) y).
    { intro y; split; intro h.
      - exact (Trunc_functor (-1) (fun cp => (cp.1; cp.2^)) (fst (Hg y) h)).
      - exact (snd (Hg y) (Trunc_functor (-1) (fun cp => (cp.1; cp.2^)) h)). }
    exact (isfreemodule_iso (lm_iso_of_submodule_iff _ _ hrm)
             (isfreemodule_image_right_mult d dreg)).
Defined.

(** A homomorphism landing in [{0} × R^m] has image isomorphic to that of its
    second component. *)
Definition lm_iso_image_snd {R : Ring} {L : LeftModule R} {m : nat}
  (h : L $-> lm_power R (S m)) (hfst : forall l, fst (h l) = 0)
  : LeftModuleIsomorphism (lm_image h)
      (lm_image (lm_homo_compose lm_prod_snd h)).
Proof.
  snapply Build_LeftModuleIsomorphism.
  - snapply (lm_corestrict (lm_image (lm_homo_compose lm_prod_snd h))
              (lm_homo_compose lm_prod_snd (lm_subincl (lm_image h)))).
    intros [y py].
    exact (Trunc_functor (-1) (fun lq => (lq.1; ap snd lq.2)) py).
  - snapply isequiv_adjointify.
    + snapply (lm_corestrict (lm_image h)
                (lm_homo_compose lm_prod_inr
                  (lm_subincl (lm_image (lm_homo_compose lm_prod_snd h))))).
      intros [z pz].
      exact (Trunc_functor (-1)
               (fun lq => (lq.1; path_prod' (hfst lq.1) lq.2)) pz).
    + intros [z pz]; by apply path_sigma_hprop.
    + intros [y py]; apply path_sigma_hprop; cbn.
      strip_truncations; destruct py as [l q].
      exact (path_prod' (hfst l)^ (ap snd q)^ @ q).
Defined.

(** * Submodules generated by a family *)

(** The closure of [X] under zero and [n + r *L m]. *)
Inductive sm_gen_type {R : Ring} {M : LeftModule R} (X : M -> Type) : M -> Type :=
| smgt_in (x : M) : X x -> sm_gen_type X x
| smgt_zero : sm_gen_type X 0
| smgt_comb (r : R) (n m : M)
    : sm_gen_type X n -> sm_gen_type X m -> sm_gen_type X (n + r *L m).

(** The submodule generated by a predicate. *)
Definition submodule_generated {R : Ring} {M : LeftModule R} (X : M -> Type)
  : LeftSubmodule M.
Proof.
  snapply (Build_LeftSubmodule' (fun m => merely (sm_gen_type X m))).
  - exact _.
  - exact (tr (smgt_zero X)).
  - intros r n m hn hm; strip_truncations.
    exact (tr (smgt_comb X r n m hn hm)).
Defined.

(** The generators lie in the generated submodule. *)
Definition submodule_generated_in {R : Ring} {M : LeftModule R} (X : M -> Type)
  (x : M) (hx : X x) : submodule_generated X x
  := tr (smgt_in X x hx).

(** The generated submodule is the smallest one containing the generators. *)
Definition submodule_generated_rec {R : Ring} {M : LeftModule R} (X : M -> Type)
  (N : LeftSubmodule M) (HX : forall x, X x -> N x)
  : forall m, submodule_generated X m -> N m.
Proof.
  intros m; rapply Trunc_rec; intro hm.
  induction hm as [x hx | | r n m' hn IHn hm' IHm].
  - exact (HX x hx).
  - exact issubgroup_in_unit.
  - rapply issubgroup_in_op.
    + exact IHn.
    + rapply is_left_submodule; exact IHm.
Defined.

(** The image of a homomorphism into a contractible module is free. *)
Definition isfreemodule_image_into_contr {R : Ring} {M N : LeftModule R}
  `{Contr N} (f : M $-> N) : IsFreeModule (lm_image f).
Proof.
  napply isfreemodule_contr.
  snapply Build_Contr.
  - exact (0; tr (0; grp_homo_unit f)).
  - intros [y hy]; apply path_sigma_hprop; apply path_contr.
Defined.

(** The image of a homomorphism from a contractible module is free. *)
Definition isfreemodule_image_from_contr {R : Ring} {M N : LeftModule R}
  `{Contr M} (f : M $-> N) : IsFreeModule (lm_image f).
Proof.
  napply isfreemodule_contr.
  snapply Build_Contr.
  - exact (f (center M); tr (center M; idpath)).
  - intros [y hy]; apply path_sigma_hprop; cbn.
    strip_truncations; destruct hy as [x p].
    exact (ap f (path_contr (center M) x) @ p).
Defined.

(** * Finitely generated submodules of [R^n] are free *)

(** A finitely generated submodule of [R^n] over a Bézout domain is free; the
    image of any homomorphism [R^k -> R^n] is free. *)
Definition isfreemodule_image_power {R : CRing} `{IsBezoutDomain R}
  : forall (n k : nat) (phi : lm_power R k $-> lm_power R n),
    IsFreeModule (lm_image phi).
Proof.
  induction n as [|m IHn]; intros k phi.
  - exact (isfreemodule_image_into_contr phi).
  - pose (g := lm_homo_compose lm_prod_fst phi).
    pose proof (lm_image_principal k g) as hp; strip_truncations.
    destruct hp as [d Hg].
    assert (hdivg : forall x, rng_divides d (g x))
      by exact (fun x => fst (Hg (g x)) (grp_image_in g x)).
    destruct (intdom_zero_or_regular d) as [d0 | dreg].
    + (* The principal generator vanishes, so [phi] lands in the second factor. *)
      assert (hfst : forall x, fst (phi x) = 0).
      { intro x.
        pose proof (transport (fun z => rng_divides z (g x)) d0 (hdivg x)) as hx.
        strip_truncations; destruct hx as [c q].
        exact (q @ rng_mult_zero_r c). }
      napply (isfreemodule_iso (lm_iso_image_snd phi hfst)).
      exact (IHn k (lm_homo_compose lm_prod_snd phi)).
    + (* The principal generator is regular; split off a free rank-one summand. *)
      pose proof (snd (Hg d) (rng_divides_refl d)) as hd0; strip_truncations.
      destruct hd0 as [x0 qx0].
      pose (q := lm_div_d dreg g hdivg).
      pose (kappa := lm_homo_sub phi (lm_homo_compose (lm_scalar (phi x0)) q)).
      assert (hfstk : forall x, fst (kappa x) = 0).
      { intro x.
        lhs napply (ap (fun z => g x - q x * z) qx0).
        lhs_V napply (ap (fun z => g x - z) (rng_div_regular dreg (hdivg x)).2).
        exact (right_inverse (g x)). }
      assert (hqzero : forall x, g x = 0 -> q x = 0).
      { intros x hgx; apply dreg.
        lhs napply rng_mult_comm.
        lhs_V napply (rng_div_regular dreg (hdivg x)).2.
        lhs napply hgx.
        exact (rng_mult_zero_r d)^. }
      assert (hkphi : forall x, phi (x - q x *L x0) = kappa x).
      { intro x.
        lhs napply grp_homo_op.
        napply (ap (fun z => phi x + z)).
        lhs napply grp_homo_inv.
        napply (ap (fun z => - z)).
        napply (@lm_homo_lact _ _ _ phi (q x) x0). }
      pose (f := lm_corestrict (lm_image g)
                   (lm_homo_compose lm_prod_fst (lm_subincl (lm_image phi)))
                   (fun mm => Trunc_functor (-1)
                      (fun xp => (xp.1; ap fst xp.2)) mm.2)).
      pose (m0 := (phi x0; tr (x0; idpath)) : lm_image phi).
      pose (cQ := lm_div_d dreg (lm_subincl (lm_image g))
                    (fun qq => fst (Hg qq.1) qq.2)).
      pose (s := lm_homo_compose
                   (lm_scalar (M := leftmodule_leftsubmodule (lm_image phi)) m0) cQ).
      assert (hs : forall qq, f (s qq) = qq).
      { intro qq; apply path_sigma_hprop.
        lhs napply (ap (fun z => cQ qq * z) qx0).
        exact (rng_div_regular dreg (fst (Hg qq.1) qq.2)).2^. }
      assert (Hk : IsFreeModule (lm_kernel f)).
      { snapply (isfreemodule_iso (N := lm_image kappa)).
        - snapply Build_LeftModuleIsomorphism.
          + snapply Build_LeftModuleHomomorphism'.
            * intro mp.
              exists mp.1.1.
              refine (Trunc_functor (-1) _ mp.1.2).
              intro xp.
              exists xp.1.
              pose (hg0 := ap fst xp.2 @ ap pr1 mp.2).
              refine (_ @ xp.2).
              lhs napply (ap (fun z => phi xp.1 - z *L phi x0)
                            (hqzero xp.1 hg0)).
              lhs napply (ap (fun z => phi xp.1 - z) (lm_zero_l (phi x0))).
              exact (ap (fun z => phi xp.1 + z) grp_inv_unit
                     @ grp_unit_r (phi xp.1)).
            * intros r x y; apply path_sigma_hprop; reflexivity.
          + snapply isequiv_adjointify.
            * intro zp.
              snrefine ((zp.1; _); _).
              -- exact (Trunc_functor (-1)
                   (fun xp => (xp.1 - q xp.1 *L x0; hkphi xp.1 @ xp.2)) zp.2).
              -- apply path_sigma_hprop.
                 pose proof zp.2 as pz; strip_truncations; destruct pz as [x px].
                 exact ((ap fst px)^ @ hfstk x).
            * intros [z pz]; apply path_sigma_hprop; reflexivity.
            * intros [[w pw] pf]; apply path_sigma_hprop;
                apply path_sigma_hprop; reflexivity.
        - exact (isfreemodule_iso (lm_iso_image_snd kappa hfstk)
                   (IHn k (lm_homo_compose lm_prod_snd kappa))). }
      exact (isfreemodule_split f s hs Hk (isfreemodule_image_to_regular k g)).
Defined.
