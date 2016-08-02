(** The HoTT Book formalization, cauchy reals section. *)

Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.orders
  HoTTClasses.implementations.cauchy_reals.

(* END OF PREAMBLE *)
(* ================================================== lem:opp *)
(** Lemma 2.1.1 *)

Definition Book_2_1_1 := @HoTT.Basics.Overture.inverse.

(* ================================================== lem:concat *)
(** Lemma 2.1.2 *)

Definition Book_2_1_2 := @HoTT.Basics.Overture.transitive_paths.

(* ================================================== thm:omg *)
(** Lemma 2.1.4 *)

Definition Book_2_1_4_item_i := @HoTT.Basics.PathGroupoids.concat_p1.
Definition Book_2_1_4_item_i' := @HoTT.Basics.PathGroupoids.concat_1p.
Definition Book_2_1_4_item_ii := @HoTT.Basics.PathGroupoids.concat_Vp.
Definition Book_2_1_4_item_ii' := @HoTT.Basics.PathGroupoids.concat_pV.
Definition Book_2_1_4_item_iii := @HoTT.Basics.PathGroupoids.inv_V.
Definition Book_2_1_4_item_iv := @HoTT.Basics.PathGroupoids.concat_p_pp.

(* ================================================== ordered-field *)
(** Definition 11.2.7 *)

Definition Book_11_2_7 := @HoTTClasses.interfaces.abstract_algebra.Field.
Definition Book_11_2_7' := @HoTTClasses.interfaces.orders.FullPseudoSemiRingOrder.

(* ================================================== defn:cauchy-approximation *)
(** Definition 11.2.10 *)

Definition Book_11_2_10 := @HoTTClasses.theory.premetric.Approximation.

(* ================================================== defn:cauchy-reals *)
(** Definition 11.3.2 *)

Definition Book_11_3_2 := @HoTTClasses.implementations.cauchy_completion.Cauchy.C.

(* ================================================== thm:Cauchy-reals-are-a-set *)
(** Theorem 11.3.9 *)

Definition Book_11_3_9 := @HoTTClasses.implementations.cauchy_completion.C_isset.

(* ================================================== RC-lim-onto *)
(** Lemma 11.3.10 *)

Definition Book_11_3_10 := @HoTTClasses.implementations.cauchy_completion.lim_issurj.

(* ================================================== RC-lim-factor *)
(** Lemma 11.3.11 *)



(* ================================================== thm:RCsim-symmetric *)
(** Lemma 11.3.12 *)

Definition Book_11_3_12 := @HoTTClasses.implementations.cauchy_completion.equiv_symm.

(* ================================================== defn:lipschitz *)
(** Definition 11.3.14 *)

Definition Book_11_3_14 := @HoTTClasses.theory.premetric.Lipschitz.

(* ================================================== RC-extend-Q-Lipschitz *)
(** Lemma 11.3.15 *)

Definition Book_11_3_15 := @HoTTClasses.implementations.cauchy_completion.lipschitz_extend.

(* ================================================== defn:RC-approx *)
(** Theorem 11.3.16 *)

Definition Book_11_3_16 := @HoTTClasses.implementations.cauchy_completion.equiv_alt.

(* ================================================== thm:RC-sim-characterization *)
(** Theorem 11.3.32 *)

Definition Book_11_3_32 := @HoTTClasses.implementations.cauchy_completion.equiv_alt_rw.

(* ================================================== thm:RC-sim-lim *)
(** Lemma 11.3.36 *)

Definition Book_11_3_36 := @HoTTClasses.implementations.cauchy_completion.C_equiv_through_approx.

(* ================================================== thm:RC-sim-lim-term *)
(** Lemma 11.3.37 *)

Definition Book_11_3_37 := @HoTTClasses.implementations.cauchy_completion.equiv_lim.

(* ================================================== RC-continuous-eq *)
(** Lemma 11.3.39 *)

Definition Book_11_3_39 := @HoTTClasses.implementations.cauchy_completion.unique_continuous_extension.

(* ================================================== RC-binary-nonexpanding-extension *)
(** Lemma 11.3.40 *)

Definition Book_11_3_40 := @HoTTClasses.implementations.cauchy_completion.lipschitz_extend_binary.

(* ================================================== RC-archimedean *)
(** Theorem 11.3.41 *)

Definition Book_11_3_41 := @HoTTClasses.implementations.cauchy_reals.R_archimedean.

(* ================================================== thm:RC-le-grow *)
(** Lemma 11.3.42 *)

Definition Book_11_3_42 := @HoTTClasses.implementations.cauchy_reals.Rle_close_rat.

(* ================================================== thm:RC-lt-open *)
(** Lemma 11.3.43 *)

Definition Book_11_3_43_item_i := @HoTTClasses.implementations.cauchy_reals.Rlt_close_rat_plus.
Definition Book_11_3_43_item_ii := @HoTTClasses.implementations.cauchy_reals.Rlt_close_exists_aux.

(* ================================================== RC-sim-eqv-le *)
(** Theorem 11.3.44 *)

Definition Book_11_3_44 := @HoTTClasses.implementations.cauchy_reals.equiv_metric_applied_rw.

(* ================================================== RC-squaring *)
(** Theorem 11.3.46 *)



(* ================================================== RC-archimedean-ordered-field *)
(** Theorem 11.3.48 *)

Definition Book_11_3_48_item_i := @HoTTClasses.implementations.cauchy_reals.R_archimedean.
Definition Book_11_3_48_item_ii := @HoTTClasses.implementations.cauchy_reals.real_full_pseudo_srorder.
Definition Book_11_3_48_item_iii := @HoTTClasses.implementations.cauchy_reals.real_field.

(* ================================================== RC-initial-Cauchy-complete *)
(** Theorem 11.3.50 *)

Definition Book_11_3_50 := @HoTTClasses.implementations.cauchy_reals.real_embed.

(* ================================================== lem:untruncated-linearity-reals-coincide *)
(** Lemma 11.4.1 *)



(* ================================================== when-reals-coincide *)
(** Corollary 11.4.3 *)



(* ================================================== defn:metric-space *)
(** Definition 11.5.1 *)



(* ================================================== defn:complete-metric-space *)
(** Definition 11.5.2 *)



(* ================================================== defn:total-bounded-metric-space *)
(** Definition 11.5.3 *)



(* ================================================== defn:uniformly-continuous *)
(** Definition 11.5.5 *)



(* ================================================== analysis-interval-ctb *)
(** Theorem 11.5.6 *)



(* ================================================== ctb-uniformly-continuous-sup *)
(** Theorem 11.5.7 *)



(* ================================================== analysis-bw-lpo *)
(** Theorem 11.5.9 *)



(* ================================================== classical-Heine-Borel *)
(** Theorem 11.5.11 *)



(* ================================================== defn:inductive-cover *)
(** Definition 11.5.13 *)



(* ================================================== reals-formal-topology-locally-compact *)
(** Lemma 11.5.14 *)



(* ================================================== interval-Heine-Borel *)
(** Corollary 11.5.15 *)



(* ================================================== inductive-cover-classical *)
(** Theorem 11.5.16 *)


