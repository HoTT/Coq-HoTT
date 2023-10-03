Require Import Basics Types.
Require Import Cubical.
Require Import Join.Core Suspension.
Require Import WildCat.

(** Two proofs of the join with bool being equivalent to the suspension. *)

(** This is a direct proof that the join of bool with a type is equivalent to a suspension. The path algebra when showing the retractions is a bit unsavoury however. *)
Theorem equiv_join_susp {A : Type} : Join Bool A <~> Susp A.
Proof.
  srapply equiv_adjointify.
  - srapply Join_rec.
    + intros [|].
      * exact North.
      * exact South.
    + intros a.
      exact South.
    + intros [|] a.
      * exact (merid a).
      * reflexivity.
  - srapply Susp_rec.
    + exact (joinl true).
    + exact (joinl false).
    + intros a.
      exact (jglue _ a @ (jglue _ a)^).
  - srapply Susp_ind.
    1,2: reflexivity.
    intros a.
    simpl.
    rewrite transport_paths_FFlr.
    hott_simpl.
    rewrite 2 ap_V.
    rewrite Susp_rec_beta_merid.
    rewrite ap_pp.
    rewrite ap_V.
    rewrite 2 Join_rec_beta_jglue.
    hott_simpl.
  - srapply Join_ind.
    1: intros [|]; reflexivity.
    1: intros a; apply jglue.
    intros [|] a.
    + rewrite transport_paths_FFlr.
      rewrite Join_rec_beta_jglue.
      rewrite Susp_rec_beta_merid.
      rewrite inv_pp.
      hott_simpl.
    + rewrite transport_paths_FFlr.
      rewrite Join_rec_beta_jglue.
      hott_simpl.
Defined.

Lemma joinrecdata_susprecdata_0gpd {A} P
  : susprecdata_0gpd_fun A P $-> joinrecdata_0gpd_fun Bool A P.
Proof.
  snrapply Build_Morphism_0Gpd.
  - intros [srd_n srd_s srd_m].
    snrapply Build_JoinRecData.
    1: intros [|].
    + exact srd_n.
    + exact srd_s.
    + intro; exact srd_s.
    + intros [|].
      * exact srd_m.
      * reflexivity.
  - split; intros f g [srp_n srp_s srp_m]; simpl.
    snrapply Build_JoinRecPath.
    + intros [|].
      * exact srp_n.
      * exact srp_s.
    + intro; exact srp_s.
    + intros [|].
      * intros b.
        apply sq_path.
        apply srp_m.
      * intros y.
        exact ((concat_1p _) @ (concat_p1 _)^).
Defined.

Lemma susprecdata_joinrecdata_0gpd {A} P
  : joinrecdata_0gpd_fun Bool A P $-> susprecdata_0gpd_fun A P.
Proof.
  snrapply Build_Morphism_0Gpd.
  - intros [jl jr jglue]; simpl.
    snrapply Build_SuspRecData.
    + exact (jl true).
    + exact (jl false).
    + intros a.
      exact (jglue _ a @ (jglue _ a)^).
  - split; intros f g [srp_n srp_s srp_m]; simpl.
    snrapply Build_SuspRecPath; simpl.
    3: intros a; refine (_ @@v sq_flip_v _)%square; apply sq_path, srp_m.
Defined.

Lemma equiv_susprecdata_joinrecdata_0gpd {A} P
  : susprecdata_0gpd_fun A P $<~> joinrecdata_0gpd_fun Bool A P.
Proof.
  snrapply cate_adjointify.
  1: exact (joinrecdata_susprecdata_0gpd P).
  1: exact (susprecdata_joinrecdata_0gpd P).
  - intros x; snrapply Build_JoinRecPath.
    + intros [|]; reflexivity.
    + apply jg.
    + intros [|] a; simpl.
      * (* TODO use correct path algebra *)
        hott_simpl.
      * reflexivity.
  - intros x; snrapply Build_SuspRecPath; simpl. 
    1,2: reflexivity.        
    intros a.
    apply sq_G1.
    apply concat_p1.
Defined.

Global Instance is1natural_susprecdata_joinrecdata_0gpd {A}
  : Is1Natural _ _ (@equiv_susprecdata_joinrecdata_0gpd A).
Proof.
  hnf. intros X Y f [srd_n srd_s srd_m].
  simpl in *.
  snrapply Build_JoinRecPath; simpl.
  1: intros [|]; reflexivity.
  1: intro; reflexivity.
  intros [|] a; simpl.
  2: reflexivity.
  exact ((concat_p1 _) @ (concat_1p _)^).
Defined.

Lemma natequiv_susprecdata_joinrecdata_0gpd{A : Type}
  : susprecdata_0gpd_fun A $<~> joinrecdata_0gpd_fun Bool A.
Proof.
  snrapply Build_NatEquiv.
  1: apply equiv_susprecdata_joinrecdata_0gpd.
  exact _.
Defined.

Theorem equiv_join_susp' {A : Type} : Join Bool A $<~> Susp A.
Proof.
  srapply opyon_equiv_0gpd.
  refine (_ $oE _ $oE _).
  - rapply join_rec_natequiv. 
  - apply natequiv_susprecdata_joinrecdata_0gpd.
  - apply susp_rec_inv_natequiv.
Defined.
