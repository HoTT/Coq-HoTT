(**
  "Formalising Real Numbers in Homotopy Type Theory"
  Gaëtan Gilbert, submitted to CPP 2017.

  This file links the results of the paper with their formalizations
  in the HoTTClasses library. You can lookup definitions and theorems by their
  number in the paper.

  This is specifically for the arXiv version at https://arxiv.org/abs/1610.05072
  Other versions may have different sections and theorems. *)

Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.orders
  HoTTClasses.implementations.cauchy_reals
  HoTTClasses.implementations.dedekind
  HoTTClasses.implementations.cauchy_semidec.

(* END OF PREAMBLE *)
(* ================================================== def:premetric *)
(** Definition 2.1 *)

Definition Def_2_1 := @HoTTClasses.theory.premetric.PreMetric.


(* ================================================== def:approximation *)
(** Definition 2.3 *)

Definition Def_2_3 := @HoTTClasses.theory.premetric.Approximation.


(* ================================================== def:islimit *)
(** Definition 2.4 *)

Definition Def_2_4 := @HoTTClasses.theory.premetric.IsLimit.

(* ================================================== lem:limit-unique *)
(** Lemma 2.5 *)

Definition Lem_2_5 := @HoTTClasses.theory.premetric.limit_unique.

(* ================================================== def:cauchycomplete *)
(** Definition 2.6 *)

Definition Def_2_6 := @HoTTClasses.theory.premetric.CauchyComplete.

(* ================================================== thm:q-premetric *)
(** Theorem 2.7 *)

Definition Thm_2_7 := @HoTTClasses.theory.premetric.Q_premetric.

(* ================================================== lem:equiv-through-approx *)
(** Lemma 2.8 *)

Definition Lem_2_8 := @HoTTClasses.theory.premetric.equiv_through_approx.

(* ================================================== lem:equiv-lim-lim *)
(** Lemma 2.9 *)

Definition Lem_2_9 := @HoTTClasses.theory.premetric.equiv_lim_lim.

(* ================================================== lem:lim-same-distance *)
(** Lemma 2.10 *)

Definition Lem_2_10 := @HoTTClasses.theory.premetric.lim_same_distance.

(* ================================================== def:lipschitz *)
(** Definition 2.11 *)

Definition Def_2_11 := @HoTTClasses.theory.premetric.Lipschitz.

(* ================================================== def:continuous *)
(** Definition 2.12 *)

Definition Def_2_12 := @HoTTClasses.theory.premetric.Continuous.

(* ================================================== lem:lipschitz-continuous *)
(** Lemma 2.13 *)

Definition Lem_2_13 := @HoTTClasses.theory.premetric.lipschitz_continuous.

(* ================================================== def:close-arrow *)
(** Definition 2.14 *)

Definition Def_2_14 := @HoTTClasses.theory.premetric.close_arrow.

(* ================================================== lem:close-arrow-apply *)
(** Lemma 2.15 *)

Definition Lem_2_15 := @HoTTClasses.theory.premetric.close_arrow_apply.

(* ================================================== thm:arrow-cauchy-complete *)
(** Theorem 2.16 *)

Definition Thm_2_16 := @HoTTClasses.theory.premetric.arrow_cauchy_complete.

(* ================================================== lem:lipschitz-lim-lipschitz *)
(** Lemma 2.17 *)

Definition Lem_2_17 := @HoTTClasses.theory.premetric.lipschitz_lim_lipschitz.

(* ================================================== def:cauchy-completion *)
(** Definition 3.1 *)

Definition Def_3_1 := @HoTTClasses.implementations.cauchy_completion.Cauchy.C.

(* ================================================== def:c-ind0 *)
(** Definition 3.2 *)

Definition Def_3_2 := @HoTTClasses.implementations.cauchy_completion.C_ind0.

(* ================================================== def:equiv-rec0 *)
(** Definition 3.3 *)

Definition Def_3_3 := @HoTTClasses.implementations.cauchy_completion.equiv_rec0.

(* ================================================== def:c-rec *)
(** Definition 3.4 *)

Definition Def_3_4 := @HoTTClasses.implementations.cauchy_completion.C_rec.

(* ================================================== lem:equiv-refl *)
(** Lemma 3.5 *)

Definition Lem_3_5 := @HoTTClasses.implementations.cauchy_completion.equiv_refl.

(* ================================================== lem:c-isset *)
(** Lemma 3.6 *)

Definition Lem_3_6 := @HoTTClasses.implementations.cauchy_completion.C_isset.

(* ================================================== lem:equiv-symm *)
(** Lemma 3.7 *)

Definition Lem_3_7 := @HoTTClasses.implementations.cauchy_completion.equiv_symm.

(* ================================================== def:balls *)
(** Definition 3.8 *)

Definition Def_3_8 := @HoTTClasses.implementations.cauchy_completion.balls.

(* ================================================== def:upper-cut *)
(** Definition 3.9 *)

Definition Def_3_9 := @HoTTClasses.implementations.cauchy_completion.upper_cut.

(* ================================================== lem:balls-separated *)
(** Lemma 3.10 *)

Definition Lem_3_10 := @HoTTClasses.implementations.cauchy_completion.balls_separated.

(* ================================================== lem:upper-separated *)
(** Lemma 3.11 *)

Definition Lem_3_11 := @HoTTClasses.implementations.cauchy_completion.upper_cut_separated.

(* ================================================== lem:upper-cut-to-balls *)
(** Lemma 3.12 *)

Definition Lem_3_12 := @HoTTClasses.implementations.cauchy_completion.upper_cut_to_balls.

(* ================================================== def:equiv-alt-eta *)
(** Definition 3.13 *)

Definition Def_3_13 := @HoTTClasses.implementations.cauchy_completion.equiv_alt_eta.

(* ================================================== thm:equiv-alt *)
(** Theorem 3.14 *)

Definition Thm_3_14_def := @HoTTClasses.implementations.cauchy_completion.equiv_alt.
Definition Thm_3_14_eta_eta := @HoTTClasses.implementations.cauchy_completion.equiv_alt_eta_eta.
Definition Thm_3_14_eta_lim := @HoTTClasses.implementations.cauchy_completion.equiv_alt_eta_lim.
Definition Thm_3_14_lim_eta := @HoTTClasses.implementations.cauchy_completion.equiv_alt_lim_eta.
Definition Thm_3_14_lim_lim := @HoTTClasses.implementations.cauchy_completion.equiv_alt_lim_lim.

(* ================================================== thm:equiv-alt-equiv *)
(** Theorem 3.15 *)

Definition Thm_3_15 := @HoTTClasses.implementations.cauchy_completion.equiv_alt_rw.

(* ================================================== thm:c-premetric *)
(** Theorem 3.16 *)

Definition Thm_3_16 := @HoTTClasses.implementations.cauchy_completion.C_premetric.

(* ================================================== lem:eta-injective *)
(** Lemma 3.17 *)

Definition Lem_3_17 := @HoTTClasses.implementations.cauchy_completion.eta_injective.

(* ================================================== thm:equiv-lim *)
(** Theorem 3.18 *)

Definition Thm_3_18 := @HoTTClasses.implementations.cauchy_completion.equiv_lim.

(* ================================================== thm:unique-continuous-extension *)
(** Theorem 3.19 *)

Definition Thm_3_19 := @HoTTClasses.implementations.cauchy_completion.unique_continuous_extension.

(* ================================================== thm:lipschitz-extend *)
(** Theorem 3.20 *)

Definition Thm_3_20 := @HoTTClasses.implementations.cauchy_completion.lipschitz_extend.

(* ================================================== thm:c-of-complete *)
(** Theorem 3.21 *)

Definition Thm_3_21 := @HoTTClasses.implementations.cauchy_completion.C_of_complete.

(* ================================================== thm:c-idempotent-monad *)
(** Theorem 3.22 *)

(* implied by Lipschitz extension and its computation rules *)

(* ================================================== lem:lipschitz-extend-same-distance *)
(** Lemma 3.24 *)

Definition Lem_3_24 := @HoTTClasses.implementations.cauchy_completion.lipschitz_extend_same_distance.

(* ================================================== thm:lipschitz-extend-binary *)
(** Theorem 3.25 *)

Definition Thm_3_25 := @HoTTClasses.implementations.cauchy_completion.lipschitz_extend_binary.

(* ================================================== lem:r-lt-exists-pos-plus-le *)
(** Lemma 4.1 *)

Definition Lem_4_1 := @HoTTClasses.implementations.cauchy_reals.full_order.Rlt_exists_pos_plus_le.

(* ================================================== lem:r-le-close *)
(** Lemma 4.2 *)

Definition Lem_4_2 := @HoTTClasses.implementations.cauchy_reals.full_order.Rle_close.

(* ================================================== lem:r-lt-close-plus *)
(** Lemma 4.3 *)

Definition Lem_4_3 := @HoTTClasses.implementations.cauchy_reals.order.Rlt_close_plus.

(* ================================================== lem:r-lt-cotrans *)
(** Lemma 4.4 *)

Definition Lem_4_4 := @HoTTClasses.implementations.cauchy_reals.order.Rlt_cotrans.

(* ================================================== lem:r-lt-plus-pos *)
(** Lemma 4.5 *)

Definition Lem_4_5 := @HoTTClasses.implementations.cauchy_reals.full_order.Rlt_plus_pos.

(* ================================================== lem:from-below-pr *)
(** Lemma 4.6 *)

Definition Lem_4_6 := @HoTTClasses.implementations.cauchy_reals.full_order.from_below_pr.

(* ================================================== lem:lipschitz-approx-lim *)
(** Lemma 4.7 *)

Definition Lem_4_7 := @HoTTClasses.implementations.cauchy_reals.full_order.lipschitz_approx_lim.

(* ================================================== lem:r-not-lt-le-flip *)
(** Lemma 4.8 *)

Definition Lem_4_8 := @HoTTClasses.implementations.cauchy_reals.full_order.R_not_lt_le_flip.

(* ================================================== def:def-by-surjection *)
(** Definition 4.9 *)

Definition Def_4_9 := @HoTTClasses.theory.jections.surjective_factor.
Definition Def_4_9_pr := @HoTTClasses.theory.jections.surjective_factor_pr.

(* ================================================== def:interval *)
(** Definition 4.10 *)

Definition Def_4_10 := @HoTTClasses.theory.premetric.Interval.

(* ================================================== def:qrmult *)
(** Definition 4.11 *)

Definition Def_4_11 := @HoTTClasses.implementations.cauchy_reals.ring.QRmult.

(* ================================================== def:r-bounded-mult *)
(** Definition 4.12 *)

Definition Def_4_12 := @HoTTClasses.implementations.cauchy_reals.ring.Rbounded_mult.

(* ================================================== lem:r-qpos-bounded *)
(** Lemma 4.13 *)

Definition Lem_4_13 := @HoTTClasses.implementations.cauchy_reals.ring.R_Qpos_bounded.

(* ================================================== lem:interval-back *)
(** Lemma 4.14 *)

Definition Lem_4_14 := @HoTTClasses.implementations.cauchy_reals.ring.interval_back.

(* ================================================== def:r-mult *)
(** Definition 4.15 *)

Definition Def_4_15 := @HoTTClasses.implementations.cauchy_reals.ring.Rmult.

(* ================================================== lem:r-mult-interval-proj-applied *)
(** Lemma 4.16 *)

Definition Lem_4_16 := @HoTTClasses.implementations.cauchy_reals.ring.Rmult_interval_proj_applied.

(* ================================================== lem:r-mult-rat-rat *)
(** Lemma 4.17 *)

Definition Lem_4_17 := @HoTTClasses.implementations.cauchy_reals.ring.Rmult_rat_rat.

(* ================================================== lem:r-mult-lipschitz-aux-alt *)
(** Lemma 4.18 *)

Definition Lem_4_18 := @HoTTClasses.implementations.cauchy_reals.ring.Rmult_lipschitz_aux_alt.

(* ================================================== lem:r-mult-continuous-r *)
(** Lemma 4.19 *)

Definition Lem_4_19 := @HoTTClasses.implementations.cauchy_reals.ring.Rmult_continuous_r.

(* ================================================== lem:r-mult-rat-l *)
(** Lemma 4.20 *)

Definition Lem_4_20 := @HoTTClasses.implementations.cauchy_reals.ring.Rmult_rat_l.

(* ================================================== lem:r-mult-abs-l *)
(** Lemma 4.21 *)

Definition Lem_4_21 := @HoTTClasses.implementations.cauchy_reals.ring.Rmult_abs_l.

(* ================================================== lem:r-mult-le-compat-abs *)
(** Lemma 4.22 *)

Definition Lem_4_22 := @HoTTClasses.implementations.cauchy_reals.ring.Rmult_le_compat_abs.

(* ================================================== thm:r-mult-continuous *)
(** Theorem 4.23 *)

Definition Thm_4_23 := @HoTTClasses.implementations.cauchy_reals.ring.Rmult_continuous.

(* ================================================== lem:r-mult-pos *)
(** Lemma 4.24 *)

Definition Lem_4_24 := @HoTTClasses.implementations.cauchy_reals.full_ring.real_full_pseudo_srorder.

(* ================================================== lem:r-mult-pos-decompose-nonneg *)
(** Lemma 4.25 *)

Definition Lem_4_25 := @HoTTClasses.implementations.cauchy_reals.full_ring.Rmult_pos_decompose_nonneg.

(* ================================================== def:bounded-inverse *)
(** Definition 4.26 *)

Definition Def_4_26 := @HoTTClasses.implementations.cauchy_reals.recip.Qpos_upper_recip.

(* ================================================== def:r-recip *)
(** Definition 4.27 *)

Definition Def_4_27 := @HoTTClasses.implementations.cauchy_reals.recip.Rrecip.

(* ================================================== lem:r-recip-rat *)
(** Lemma 4.28 *)

Definition Lem_4_28 := @HoTTClasses.implementations.cauchy_reals.recip.Rrecip_rat.

(* ================================================== lem:r-recip-upper-recip *)
(** Lemma 4.29 *)

Definition Lem_4_29 := @HoTTClasses.implementations.cauchy_reals.recip.R_recip_upper_recip.

(* ================================================== lem:r-recip-inverse *)
(** Lemma 4.30 *)

Definition Lem_4_30 := @HoTTClasses.implementations.cauchy_reals.recip.R_recip_inverse.

(* ================================================== def:increasing-sequence *)
(** Definition 5.1 *)

Definition Def_5_1 := @HoTTClasses.implementations.partiality.IncreasingSequence.

(* ================================================== def:partial *)
(** Definition 5.2 *)

Definition Def_5_2 := @HoTTClasses.implementations.partiality.Partial.partial.

(* ================================================== def:sier-top *)
(** Definition 5.3 *)

Definition Def_5_3 := @HoTTClasses.implementations.sierpinsky.SierTop.

(* ================================================== lem:sier-le-imply *)
(** Lemma 5.4 *)

Definition Lem_5_4 := @HoTTClasses.implementations.sierpinsky.SierLe_imply.

(* ================================================== def:sier-join *)
(** Definition 5.5 *)

Definition Def_5_5 := @HoTTClasses.implementations.sierpinsky.SierJoin.

(* ================================================== lem:sier-join-semilattice *)
(** Lemma 5.6 *)

Definition Lem_5_6 := @HoTTClasses.implementations.sierpinsky.SierJoin_is_join.

(* ================================================== lem:sier-join-disj *)
(** Lemma 5.7 *)

Definition Lem_5_7 := @HoTTClasses.implementations.sierpinsky.top_le_join.

(* ================================================== def:sier-countable-join *)
(** Definition 5.8 *)

Definition Def_5_8 := @HoTTClasses.implementations.sierpinsky.CountableSup.

(* ================================================== def:disjoint *)
(** Definition 5.9 *)

Definition Def_5_9 := @HoTTClasses.implementations.sierpinsky.disjoint.

(* ================================================== def:interleave *)
(** Definition 5.10 *)

Definition Def_5_10 := @HoTTClasses.implementations.sierpinsky.interleave.

(* ================================================== lem:interleave-top-r *)
(** Lemma 5.11 *)

Definition Lem_5_11 := @HoTTClasses.implementations.sierpinsky.interleave_top_r.

(* ================================================== lem:interleave-pr *)
(** Lemma 5.12 *)

Definition Lem_5_12 := @HoTTClasses.implementations.sierpinsky.interleave_pr.

(* ================================================== lem:semidecidable-compare-rat *)
(** Lemma 5.13 *)

Definition Lem_5_13 := @HoTTClasses.implementations.cauchy_semidec.semidecidable_compare_rat_sig.

(* ================================================== def:is-positive *)
(** Definition 5.14 *)

Definition Def_5_14 := @HoTTClasses.implementations.cauchy_semidec.compare_cauchy_rat.

(* ================================================== thm:is-positive-ok *)
(** Theorem 5.15 *)

Definition Thm_5_15 := @HoTTClasses.implementations.cauchy_semidec.compare_cauchy_rat_pr.
