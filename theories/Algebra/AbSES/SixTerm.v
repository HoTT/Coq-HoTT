From HoTT Require Import Basics Types WildCat HSet Pointed.Core Pointed.pTrunc Pointed.pEquiv
  Modalities.ReflectiveSubuniverse Truncations.Core Truncations.SeparatedTrunc
  AbGroups Homotopy.ExactSequence Spaces.Int Spaces.FreeInt
  AbSES.Core AbSES.Pullback AbSES.Pushout BaerSum Ext PullbackFiberSequence.

(** * The contravariant six-term sequence of Ext *)

(** We construct the contravariant six-term exact sequence of Ext groups associated to any short exact sequence [A -> E -> B] and coefficient group [G]. The existence of this exact sequence follows from the final result in [PullbackFiberSequence]. However, with that definition it becomes a bit tricky to show that the connecting map is given by pushing out [E]. Instead, we give a direct proof.

  As an application, we use the six-term exact sequence to show that [Ext Z/n A] is isomorphic to [A/n], for nonzero natural numbers [n]. (See [ext_cyclic_ab].) *)

(** Exactness of [0 -> ab_hom B G -> ab_hom E G] follows from the rightmost map being an embedding. *)
Definition isexact_abses_sixterm_i `{Funext}
  {B A G : AbGroup} (E : AbSES B A)
  : IsExact (Tr (-1))
      (pconst : pUnit ->* ab_hom B G)
      (fmap10 (A:=Group^op) ab_hom (projection E) G).
Proof.
  apply isexact_purely_O.
  rapply isexact_homotopic_i.
  2: apply iff_grp_isexact_isembedding.
  1: by apply phomotopy_homotopy_hset.
  exact _. (* [isembedding_precompose_surjection_ab] *)
Defined.

(** Exactness of [ab_hom B G -> ab_hom E G -> ab_hom A G]. One can also deduce this from [isexact_abses_pullback]. *)
Definition isexact_ext_contra_sixterm_ii `{Funext}
  {B A G : AbGroup} (E : AbSES B A)
  : IsExact (Tr (-1))
      (fmap10 (A:=Group^op) ab_hom (projection E) G)
      (fmap10 (A:=Group^op) ab_hom (inclusion E) G).
Proof.
  snapply Build_IsExact.
  { apply phomotopy_homotopy_hset; intro f.
    apply equiv_path_grouphomomorphism; intro b; cbn.
    refine (ap f _ @ grp_homo_unit f).
    apply isexact_inclusion_projection. }
  hnf. intros [f q]; rapply contr_inhabited_hprop.
  srefine (tr (_; _)).
  { refine (grp_homo_compose _ (abses_cokernel_iso (inclusion E) (projection E))^-1$).
    apply (quotient_abgroup_rec _ _ f).
    intros e; rapply Trunc_ind.
    intros [b r].
    refine (ap f r^ @ _).
    exact (equiv_path_grouphomomorphism^-1 q _). }
  lazy beta.
  apply path_sigma_hprop.
  apply equiv_path_grouphomomorphism; unfold pr1.
  intro x.
  exact (ap (quotient_abgroup_rec _ _ f _)
            (abses_cokernel_iso_inv_beta _ _ _)).
Defined.

(** *** Exactness of [ab_hom E G -> ab_hom A G -> Ext B G] *)

(** If a pushout [abses_pushout alpha E] is trivial, then [alpha] factors through [inclusion E]. *)
Lemma abses_pushout_trivial_factors_inclusion `{Univalence}
  {B A A' : AbGroup} (alpha : A $-> A') (E : AbSES B A)
  : abses_pushout alpha E = pt -> exists phi, alpha = phi $o inclusion E.
Proof.
  equiv_intros (equiv_path_abses (E:=abses_pushout alpha E) (F:=pt)) p.
  destruct p as [phi [p q]].
  exists (ab_biprod_pr1 $o phi $o ab_pushout_inr).
  apply equiv_path_grouphomomorphism; intro a.
  (* We embed into the biproduct and prove equality there. *)
  apply (isinj_embedding (@ab_biprod_inl A' B) _).
  refine ((p (alpha a))^ @ _).
  refine (ap phi _ @ _).
  1: exact (left_square (abses_pushout_morphism E alpha) a).
  apply (path_prod' idpath).
  refine ((q _)^ @ _).
  refine (right_square (abses_pushout_morphism E alpha) _ @ _); cbn.
  apply isexact_inclusion_projection.
Defined.

Instance isexact_ext_contra_sixterm_iii@{u v +} `{Univalence}
  {B A G : AbGroup@{u}} (E : AbSES@{u v} B A)
  : IsExact (Tr (-1))
      (fmap10 (A:=Group^op) ab_hom (inclusion E) G)
      (abses_pushout_ext E).
Proof.
  snapply Build_IsExact.
  - apply phomotopy_homotopy_hset; intro g; cbn.
    (* this equation holds purely *)
    apply (ap tr@{v}).
    refine (abses_pushout_compose _ _ _ @ ap _ _ @ _).
    1: apply abses_pushout_inclusion.
    apply abses_pushout_point.
  - intros [F p].
    (* since we are proving a proposition, we may convert [p] to an actual path *)
    pose proof (p' := (equiv_path_Tr _ _)^-1 p).
    (* slightly faster than [strip_truncations]: *)
    revert p'; apply Trunc_rec; intro p'.
    rapply contr_inhabited_hprop; apply tr.
    (* now we construct a preimage *)
    pose (g := abses_pushout_trivial_factors_inclusion _ E p');
      destruct g as [g k].
    exists g.
    apply path_sigma_hprop; cbn.
    exact k^.
Defined.

(** *** Exactness of [ab_hom A G -> Ext1 B G -> Ext1 E G]. *)

(** We construct a morphism which witnesses exactness. *)
Definition isexact_ext_contra_sixterm_iv_mor `{Univalence}
  {B A G : AbGroup} (E : AbSES B A)
  (F : AbSES B G) (p : abses_pullback (projection E) F = pt)
  : AbSESMorphism E F.
Proof.
  pose (p' := equiv_path_abses^-1 p^);
    destruct p' as [p' [pl pr]].
  srefine (Build_AbSESMorphism _ _ grp_homo_id _ _).
  - refine (grp_homo_compose
              (grp_iso_inverse
                 (abses_kernel_iso (inclusion F) (projection F))) _).
    (* now it's easy to construct map into the kernel *)
    snapply grp_kernel_corec.
    1: exact (grp_pullback_pr1 _ _ $o p' $o ab_biprod_inr $o inclusion E).
    intro x.
    refine (right_square (abses_pullback_morphism F _) _ @ _).
    refine (ap (projection E) (pr _)^ @ _); cbn.
    apply isexact_inclusion_projection.
  - exact (grp_pullback_pr1 _ _ $o p' $o ab_biprod_inr).
  - intro a.
    napply abses_kernel_iso_inv_beta.
  - intro e.
    refine (right_square (abses_pullback_morphism F _) _
              @ ap (projection E) _).
    exact (pr _)^.
Defined.

Instance isexact_ext_contra_sixterm_iv `{Univalence}
  {B A G : AbGroup@{u}} (E : AbSES@{u v} B A)
  : IsExact (Tr (-1)) (abses_pushout_ext E)
      (fmap (pTr 0) (abses_pullback_pmap (A:=G) (projection E))).
Proof.
  snapply Build_IsExact.
  - apply phomotopy_homotopy_hset; intro g; cbn.
    (* this equation holds purely *)
    apply (ap tr@{v}).
    refine ((abses_pushout_pullback_reorder _ _ _)^
              @ ap _ _ @ _).
    1: exact (abses_pullback_projection _)^.
    apply abses_pushout_point.
  (* since we are proving a proposition, we may convert [p] to an actual path *)
  - intros [F p].
    revert dependent F; napply (Trunc_ind (n:=0) (A:=AbSES B G)).
    (* [exact _.] works here, but is slow. *)
    { intro x; napply istrunc_forall.
      intro y; exact (istrunc_leq (trunc_index_leq_succ _)). }
    intro F.
    equiv_intros (equiv_path_Tr (n:=-1) (abses_pullback (projection E) F) pt) p.
    strip_truncations.
    rapply contr_inhabited_hprop; apply tr.
    pose (g := isexact_ext_contra_sixterm_iv_mor E F p).
    exists (component1 g).
    apply path_sigma_hprop, (ap tr).
    by rapply (abses_pushout_component3_id g).
Defined.

(** *** Exactness of [Ext B G -> Ext E G -> Ext A G] *)

(** This is an immediate consequence of [isexact_abses_pullback]. *)
Instance isexact_ext_contra_sixterm_v `{Univalence}
  {B A G : AbGroup} (E : AbSES B A)
  : IsExact (Tr (-1))
      (fmap (pTr 0) (abses_pullback_pmap (A:=G) (projection E)))
      (fmap (pTr 0) (abses_pullback_pmap (A:=G) (inclusion E))).
Proof.
  rapply isexact_ptr.
  rapply isexact_purely_O.
Defined.

(** *** [Ext Z/n A] is isomorphic to [A/n] *)

(** An easy consequence of the contravariant six-term exact sequence is that [Ext Z/n A] is isomorphic to the cokernel of the multiplication-by-n endomorphism [A -> A], for any abelian group [A]. This falls out of the six-term exact sequence associated to [Z -> Z -> Z/n] and projectivity of [Z]. A minor point is that the library does not currently contain a proof that multiplication by a nonzero natural number is a self-injection of [Z]. Thus we work directly with the assumption that [Z1_mul_nat n] is an embedding. *)

(** We define our own cyclic groups using [ab_cokernel_embedding] under the assumption that [Z1_mul_nat n] is an embedding. *)
Definition cyclic' `{Funext} (n : nat) `{IsEmbedding (Z1_mul_nat n)}
  : AbGroup := ab_cokernel_embedding (Z1_mul_nat n).

(** We first show that [ab_hom Z A -> ab_hom Z A -> Ext (cyclic n) A] is exact. We could inline the proof below, but factoring it out is faster. *)
Local Definition isexact_ext_cyclic_ab_iii@{u v w | u < v, v < w} `{Univalence}
  (n : nat) `{IsEmbedding (Z1_mul_nat n)} {A : AbGroup@{u}}
  : IsExact (Tr (-1))
      (fmap10 (A:=Group^op) ab_hom (Z1_mul_nat n) A)
      (abses_pushout_ext (abses_from_inclusion (Z1_mul_nat n)))
  := isexact_ext_contra_sixterm_iii
       (abses_from_inclusion (Z1_mul_nat n)).

(** We show exactness of [A -> A -> Ext Z/n A] where the first map is multiplication by [n], but considered in universe [v]. *)
Local Definition ext_cyclic_exact@{u v w} `{Univalence}
  (n : nat) `{IsEmbedding (Z1_mul_nat n)} {A : AbGroup@{u}}
  : IsExact@{v v v v v} (Tr (-1))
      (ab_mul (A:=A) n)
      (abses_pushout_ext@{u w v} (abses_from_inclusion (Z1_mul_nat n))
         o* (pequiv_groupisomorphism (equiv_Z1_hom A))^-1*).
Proof.
  (* we first move [equiv_Z1_hom] across the total space *)
  apply moveL_isexact_equiv.
  (* now we change the left map so as to apply exactness at iii from above *)
  snapply (isexact_homotopic_i (Tr (-1))).
  1: exact (fmap10 (A:=Group^op) ab_hom (Z1_mul_nat n) A o*
              (pequiv_inverse
                 (pequiv_groupisomorphism (equiv_Z1_hom A)))).
  - apply phomotopy_homotopy_hset.
    rapply (equiv_ind (equiv_Z1_hom A)); intro f.
    refine (_ @ ap _ (eissect _ _)^).
    apply moveR_equiv_V; symmetry.
    refine (ap f _ @ _).
    1: apply Z1_rec_beta.
    exact (ab_mul_natural f n Z1_gen).
  - (* we get rid of [equiv_Z1_hom] *)
    apply isexact_equiv_fiber.
    apply isexact_ext_cyclic_ab_iii.
Defined.

(** The main result of this section. *)
Theorem ext_cyclic_ab@{u v w | u < v, v < w} `{Univalence}
  (n : nat) `{emb : IsEmbedding (Z1_mul_nat n)} {A : AbGroup@{u}}
  : ab_cokernel@{v w} (ab_mul (A:=A) n)
      $<~> ab_ext@{u v} (cyclic'@{u v} n) A.
  (* We take a large cokernel in order to apply [abses_cokernel_iso]. *)
Proof.
  pose (E := abses_from_inclusion (Z1_mul_nat n)).
  snrefine (abses_cokernel_iso (ab_mul n) _).
  - exact (grp_homo_compose
             (abses_pushout_ext E)
             (grp_iso_inverse (equiv_Z1_hom A))).
  - apply (conn_map_compose _ (grp_iso_inverse (equiv_Z1_hom A))).
    1: rapply conn_map_isequiv.
    (* Coq knows that [Ext Z1 A] is contractible since [Z1] is projective, so exactness at spot iv gives us this: *)
    exact (isconnmap_O_isexact_base_contr _ _
             (fmap (pTr 0)
                (abses_pullback_pmap (A:=A)
                   (projection E)))).
  - (* we change [grp_homo_compose] to [o*] *)
    srapply isexact_homotopic_f.
    1: exact (abses_pushout_ext (abses_from_inclusion (Z1_mul_nat n))
                o* (pequiv_groupisomorphism (equiv_Z1_hom A))^-1*).
    1: by apply phomotopy_homotopy_hset.
    apply ext_cyclic_exact.
Defined.
