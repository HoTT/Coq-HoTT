(** The HoTT Book formalization. *)

(** This file links the results of the HoTT Book with their formalizations
    in the HoTT library. You can lookup definitions and theorems by their
    number in the HoTT Book. *)

(*  IMPORTANT NOTE FOR THE HoTT DEVELOPERS:

    This files is processed automagically by the etc/Book.py script. The
    script parses the file according to the markers present in it (the
    comment lines with many = signs followed by a LaTeX label). It
    reorders the entries according to entry number X.Y.Z and inserts
    missing entries. You must therefore obey the following rules:

    0. Read the description below of what the correct procedure is.

    1. Do not mess with the markers and do not insert new entries by hand.
       If a LaTeX label has been renamed you may rename the corresponding
       marker, but for addition of new entries you have to use the
       etc/Book.py script, as described below.

    2. If a theorem is gone, you may delete the corresponding entry,
       but make sure first that it was not just moved elsewhere.

    3. Make entries independent of other entries, as they may get
       reordered or deleted.

    4. If you need to import anything, do it before the first entry.

    5. Each entry should define Book_X_Y_Z, but you can also
       put in auxiliary definitions and lemmas (keep it short please).
       The script renames the Book_X_Y_Z to whatever the correct number
       is, so initially you can use whatever number you like.

       If you are formalizing a Lemma with several part, use
       Book_X_Y_Z_item_i, Book_X_Y_Z_item_ii, or some such.

    6. If there is a corresponding HoTT library theorem or definition,
       please use that one, even if it is not exactly the same.


   PROCEDURE FOR UPDATING THE FILE:

   1. Compile the latest version of the HoTT Book to update the LaTeX
      labels. Do not forget to pull in changes from HoTT/HoTT.

   2. Run `etc/Book.py` as described by `etc/Book.py` if you run it without
      arguments. If it complains, fix things.

   3. Add contents to new entries.

   4. Run `etc/Book.py` again to make sure it is happy.

   5. Compile this file with `make contrib` or `make contrib/HoTTBook.vo`.

   6. Do the git thing to submit your changes.

*)

Require Import HoTT.
Require Import HoTT.HIT.IntervalImpliesFunext.
Require HoTT.Categories.
From HoTT.Classes Require
  interfaces.abstract_algebra
  interfaces.orders
  theory.premetric.


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

(* ================================================== thm:EckmannHilton *)
(** Theorem 2.1.6 *)

Definition Book_2_1_6 := @HoTT.Basics.PathGroupoids.eckmann_hilton.

(* ================================================== def:pointedtype *)
(** Definition 2.1.7 *)

Definition Book_2_1_7 := @HoTT.Basics.Overture.pType.

(* ================================================== def:loopspace *)
(** Definition 2.1.8 *)

Definition Book_2_1_8 := @HoTT.Pointed.Loops.iterated_loops.

(* ================================================== lem:map *)
(** Lemma 2.2.1 *)

Definition Book_2_2_1 := @HoTT.Basics.Overture.ap.

(* ================================================== lem:ap-functor *)
(** Lemma 2.2.2 *)

Definition Book_2_2_2_item_i   := @HoTT.Basics.PathGroupoids.ap_pp.
Definition Book_2_2_2_item_ii  := @HoTT.Basics.PathGroupoids.inverse_ap.
Definition Book_2_2_2_item_iii := @HoTT.Basics.PathGroupoids.ap_compose.
Definition Book_2_2_2_item_iv  := @HoTT.Basics.PathGroupoids.ap_idmap.

(* ================================================== lem:transport *)
(** Lemma 2.3.1 *)

Definition Book_2_3_1 := @HoTT.Basics.Overture.transport.

(* ================================================== thm:path-lifting *)
(** Lemma 2.3.2 *)

(* special case of *)
Definition Book_2_3_2 := @HoTT.Types.Sigma.equiv_path_sigma.

(* ================================================== lem:mapdep *)
(** Lemma 2.3.4 *)

Definition Book_2_3_4 := @HoTT.Basics.Overture.apD.

(* ================================================== thm:trans-trivial *)
(** Lemma 2.3.5 *)

Definition Book_2_3_5 := @HoTT.Basics.PathGroupoids.transport_const.

(* ================================================== thm:apd-const *)
(** Lemma 2.3.8 *)

Definition Book_2_3_8 := @HoTT.Basics.PathGroupoids.apD_const.

(* ================================================== thm:transport-concat *)
(** Lemma 2.3.9 *)

Definition Book_2_3_9 := @HoTT.Basics.PathGroupoids.transport_compose.

(* ================================================== thm:transport-compose *)
(** Lemma 2.3.10 *)

Definition Book_2_3_10 := @HoTT.Basics.PathGroupoids.ap_transport.

(* ================================================== thm:ap-transport *)
(** Lemma 2.3.11 *)

Definition Book_2_3_11 := @HoTT.Basics.PathGroupoids.transport_pp.

(* ================================================== defn:homotopy *)
(** Definition 2.4.1 *)

Definition Book_2_4_1 := @HoTT.Basics.Overture.pointwise_paths.

(* ================================================== lem:homotopy-props *)
(** Lemma 2.4.2 *)

Definition Book_2_4_2 := @HoTT.Basics.Overture.pointwise_paths.

(* ================================================== lem:htpy-natural *)
(** Lemma 2.4.3 *)

Definition Book_2_4_3 := @HoTT.Basics.PathGroupoids.concat_Ap.

(* ================================================== cor:hom-fg *)
(** Corollary 2.4.4 *)

Definition Book_2_4_4 := @HoTT.Basics.PathGroupoids.concat_A1p.

(* ================================================== defn:quasi-inverse *)
(** Definition 2.4.6 *)

(** Quasi-inverses do not occur explicitly in the library since
    they are `not good'. They do only occur implicitly as input to
    isequiv_adjointify : IsEquiv f. Therefore we link to the half
    adjoint equivalence extending the quasi-inverse *)

Definition Book_2_4_6 := @HoTT.Basics.Equivalences.isequiv_adjointify.

(* ================================================== eg:idequiv *)
(** Example 2.4.7 *)

Definition Book_2_4_7 := @HoTT.Basics.Equivalences.equiv_idmap.

(* ================================================== eg:concatequiv *)
(** Example 2.4.8 *)

Definition Book_2_4_8_i := @HoTT.Types.Paths.isequiv_concat_l.
Definition Book_2_4_8_ii := @HoTT.Types.Paths.isequiv_concat_r.

(* ================================================== thm:transportequiv *)
(** Example 2.4.9 *)

Definition Book_2_4_9 := @HoTT.Basics.Equivalences.isequiv_transport.

(* ================================================== thm:equiv-eqrel *)
(** Lemma 2.4.12 *)

Definition Book_2_4_12_item_i   := @HoTT.Basics.Equivalences.reflexive_equiv.
Definition Book_2_4_12_item_ii  := @HoTT.Basics.Equivalences.symmetric_equiv.
Definition Book_2_4_12_item_iii := @HoTT.Basics.Equivalences.transitive_equiv.

(* ================================================== thm:path-prod *)
(** Theorem 2.6.2 *)

Definition Book_2_6_2 := @HoTT.Types.Prod.equiv_path_prod.

(* ================================================== thm:trans-prod *)
(** Theorem 2.6.4 *)

Definition Book_2_6_4 := @HoTT.Types.Prod.transport_prod.

(* ================================================== thm:ap-prod *)
(** Theorem 2.6.5 *)

Definition Book_2_6_5 := @HoTT.Types.Prod.ap_functor_prod.

(* ================================================== thm:path-sigma *)
(** Theorem 2.7.2 *)

Definition Book_2_7_2 := @HoTT.Types.Sigma.equiv_path_sigma.

(* ================================================== thm:eta-sigma *)
(** Corollary 2.7.3 *)

Definition Book_2_7_3 := @HoTT.Types.Sigma.eta_sigma.

(* ================================================== transport-Sigma *)
(** Theorem 2.7.4 *)

Definition Book_2_7_4 := @HoTT.Types.Sigma.transportD_is_transport.

(* ================================================== thm:path-unit *)
(** Theorem 2.8.1 *)

Definition Book_2_8_1 := @HoTT.Types.Unit.equiv_path_unit.

(* ================================================== axiom:funext *)
(** Axiom 2.9.3 *)

Definition Book_2_9_3 := @HoTT.Basics.Overture.path_forall.

(* ================================================== thm:dpath-arrow *)
(** Lemma 2.9.6 *)

Definition Book_2_9_6 := @HoTT.Types.Arrow.dpath_arrow.

(* ================================================== thm:dpath-forall *)
(** Lemma 2.9.7 *)

Definition Book_2_9_7 := @HoTT.Types.Forall.dpath_forall.

(* ================================================== thm:idtoeqv *)
(** Lemma 2.10.1 *)

Definition Book_2_10_1 := @HoTT.Types.Universe.equiv_path.

(* ================================================== axiom:univalence *)
(** Axiom 2.10.3 *)

Definition Book_2_10_3 := @HoTT.Types.Universe.isequiv_equiv_path.

(* ================================================== thm:transport-is-ap *)
(** Lemma 2.10.5 *)

(** Lemma 2.10.5 is a special case of Lemma 2.3.10, but also of: *)
Definition Book_2_10_5 := @HoTT.Types.Universe.transport_path_universe'.

(* ================================================== thm:paths-respects-equiv *)
(** Theorem 2.11.1 *)

Definition Book_2_11_1 := @HoTT.Basics.Equivalences.isequiv_ap.

(* ================================================== cor:transport-path-prepost *)
(** Lemma 2.11.2 *)

Definition Book_2_11_2_item_1 := @HoTT.Types.Paths.transport_paths_l.
Definition Book_2_11_2_item_2 := @HoTT.Types.Paths.transport_paths_r.
Definition Book_2_11_2_item_3 := @HoTT.Types.Paths.transport_paths_lr.

(* ================================================== thm:transport-path *)
(** Theorem 2.11.3 *)

Definition Book_2_11_3 := @HoTT.Types.Paths.transport_paths_FlFr.

(* ================================================== thm:transport-path2 *)
(** Theorem 2.11.4 *)

Definition Book_2_11_4 := @HoTT.Types.Paths.transport_paths_FlFr_D.

(* ================================================== thm:dpath-path *)
(** Theorem 2.11.5 *)

Definition Book_2_11_5 := @HoTT.Types.Paths.dpath_path_lr.

(* ================================================== thm:path-coprod *)
(** Theorem 2.12.5 *)

Definition Book_2_12_5 := @HoTT.Types.Sum.equiv_path_sum.

(* ================================================== thm:path-nat *)
(** Theorem 2.13.1 *)

Definition Book_2_13_1 := @HoTT.Spaces.Nat.equiv_path_nat.

(* ================================================== thm:prod-ump *)
(** Theorem 2.15.2 *)

(** non-dependent as special case of dependent, Theorem 2.15.5 *)
Definition Book_2_15_2 := @HoTT.Types.Prod.isequiv_prod_coind.

(* ================================================== thm:prod-umpd *)
(** Theorem 2.15.5 *)

Definition Book_2_15_5 := @HoTT.Types.Prod.isequiv_prod_coind.

(* ================================================== thm:ttac *)
(** Theorem 2.15.7 *)

Definition Book_2_15_7 := @HoTT.Types.Sigma.isequiv_sigT_coind.

(* ================================================== defn:set *)
(** Definition 3.1.1 *)

Definition Book_3_1_1 := @HoTT.Basics.Overture.IsTrunc 0.

(* ================================================== eg:isset-unit *)
(** Example 3.1.2 *)

Definition Book_3_1_2 := @HoTT.Types.Unit.contr_unit.

(* ================================================== eg:isset-empty *)
(** Example 3.1.3 *)

Definition Book_3_1_3 := @HoTT.Types.Empty.hprop_Empty.

(* ================================================== thm:nat-set *)
(** Example 3.1.4 *)

Definition Book_3_1_4 := @HoTT.Spaces.Nat.hset_nat.

(* ================================================== thm:isset-prod *)
(** Example 3.1.5 *)

Definition Book_3_1_5 := @HoTT.Types.Prod.trunc_prod.

(* ================================================== thm:isset-forall *)
(** Example 3.1.6 *)

Definition Book_3_1_6 := @HoTT.Types.Forall.trunc_forall.

(* ================================================== defn:1type *)
(** Definition 3.1.7 *)

Definition Book_3_1_7 := @HoTT.Basics.Overture.IsTrunc 1.

(* ================================================== thm:isset-is1type *)
(** Lemma 3.1.8 *)

Definition Book_3_1_8 := @HoTT.Basics.Trunc.trunc_succ 0.

(* ================================================== thm:type-is-not-a-set *)
(** Example 3.1.9 *)

Definition Book_3_1_9 := @HoTT.Types.Universe.not_hset_Type.

(* ================================================== thm:not-dneg *)
(** Theorem 3.2.2 *)



(* ================================================== thm:not-lem *)
(** Corollary 3.2.7 *)



(* ================================================== defn:isprop *)
(** Definition 3.3.1 *)

Definition Book_3_3_1 := @HoTT.Basics.Overture.IsTrunc -1.

(* ================================================== thm:inhabprop-eqvunit *)
(** Lemma 3.3.2 *)

Definition Book_3_3_2 := @HoTT.HProp.if_hprop_then_equiv_Unit.

(* ================================================== lem:equiv-iff-hprop *)
(** Lemma 3.3.3 *)

Definition Book_3_3_3 := @HoTT.Basics.Trunc.equiv_iff_hprop.

(* ================================================== thm:prop-set *)
(** Lemma 3.3.4 *)

Definition Book_3_3_4 := @HoTT.Basics.Trunc.trunc_succ -1.

(* ================================================== thm:isprop-isset *)
(** Lemma 3.3.5 *)

Definition Book_3_3_5_i := @HoTT.HProp.hprop_trunc.

(* ================================================== thm:isprop-isprop *)
(** Lemma 3.3.5 *)

Definition Book_3_3_5_ii := @HoTT.HProp.hprop_trunc.

(* ================================================== defn:decidable-equality *)
(** Definition 3.4.3 *)

Definition Book_3_4_3_part_i   := @HoTT.Basics.Decidable.Decidable.
(** Definition Book_3_4_3_part_ii  :=  *)
Definition Book_3_4_3_part_iii := @HoTT.Basics.Decidable.DecidablePaths.

(* ================================================== defn:setof *)
(** Lemma 3.5 *)



(* ================================================== thm:path-subset *)
(** Lemma 3.5.1 *)

Definition Book_3_5_1 := @HoTT.Types.Sigma.path_sigma_hprop.

(* ================================================== thm:isprop-forall *)
(** Example 3.6.2 *)

Definition Book_3_6_2 `{Funext} (A : Type) (B : A -> Type)
  := @HoTT.Types.Forall.trunc_forall _ A B -1.

(* ================================================== defn:logical-notation *)
(** Definition 3.7.1 *)



(* ================================================== thm:ac-epis-split *)
(** Lemma 3.8.2 *)



(* ================================================== thm:no-higher-ac *)
(** Lemma 3.8.5 *)



(* ================================================== thm:prop-equiv-trunc *)
(** Lemma 3.9.1 *)

Definition Book_3_9_1 := @HoTT.Truncations.Core.TrM.RSU.isequiv_to_O_inO -1.

(* ================================================== cor:UC *)
(** Corollary 3.9.2 *)

Definition Book_3_9_2 := @HoTT.HIT.unique_choice.unique_choice.

(* ================================================== defn:contractible *)
(** Definition 3.11.1 *)

Definition Book_3_11_1 := @HoTT.Basics.Overture.IsTrunc -2.

(* ================================================== thm:contr-unit *)
(** Lemma 3.11.3 *)

Definition Book_3_11_3 := @HoTT.Types.Unit.contr_unit.

(* ================================================== thm:isprop-iscontr *)
(** Lemma 3.11.4 *)

Definition Book_3_11_4 := @HoTT.HProp.hprop_trunc.

(* ================================================== thm:contr-contr *)
(** Corollary 3.11.5 *)

Definition Book_3_11_5 := @HoTT.HProp.contr_contr.

(* ================================================== thm:contr-forall *)
(** Lemma 3.11.6 *)

Definition Book_3_11_6 := @HoTT.Types.Forall.trunc_forall.

(* ================================================== thm:retract-contr *)
(** Lemma 3.11.7 *)

Definition Book_3_11_7a := @HoTT.Idempotents.contr_retracttype.
Definition Book_3_11_7 := @HoTT.Truncations.Core.TrM.RSU.inO_to_O_retract -2.

(* ================================================== thm:contr-paths *)
(** Lemma 3.11.8 *)

Definition Book_3_11_8 := @HoTT.Basics.Contractible.contr_basedpaths.

(* ================================================== thm:omit-contr *)
(** Lemma 3.11.9 *)

Definition Book_3_11_9_part_i  := @HoTT.Types.Sigma.equiv_sigma_contr.
Definition Book_3_11_9_part_ii := @HoTT.Types.Sigma.equiv_contr_sigma.

(* ================================================== thm:prop-minusonetype *)
(** Lemma 3.11.10 *)

Definition Book_3_11_10_if     := @HoTT.Basics.Trunc.path_ishprop.
Definition Book_3_11_10_onlyif := @HoTT.Basics.Trunc.hprop_allpath.

(* ================================================== lem:qinv-autohtpy *)
(** Lemma 4.1.1 *)



(* ================================================== lem:autohtpy *)
(** Lemma 4.1.2 *)



(* ================================================== thm:qinv-notprop *)
(** Theorem 4.1.3 *)



(* ================================================== defn:ishae *)
(** Definition 4.2.1 *)

Definition Book_4_2_1 := @HoTT.Basics.Overture.IsEquiv.

(* ================================================== lem:coh-equiv *)
(** Lemma 4.2.2 *)

Definition Book_4_2_2 := @HoTT.Basics.Equivalences.other_adj.

(* ================================================== thm:equiv-iso-adj *)
(** Theorem 4.2.3 *)

Definition Book_4_2_3 := @HoTT.Basics.Equivalences.isequiv_adjointify.

(* ================================================== defn:homotopy-fiber *)
(** Definition 4.2.4 *)

Definition Book_4_2_4 := @HoTT.Basics.Overture.hfiber.

(* ================================================== lem:hfib *)
(** Lemma 4.2.5 *)

Definition Book_4_2_5 := @HoTT.Fibrations.equiv_path_hfiber.

(* ================================================== thm:contr-hae *)
(** Theorem 4.2.6 *)

Definition Book_4_2_6 := @HoTT.EquivalenceVarieties.fcontr_isequiv.

(* ================================================== defn:linv-rinv *)
(** Definition 4.2.7 *)

Definition Book_4_2_7 := @HoTT.Basics.Overture.Sect.

(* ================================================== thm:equiv-compose-equiv *)
(** Lemma 4.2.8 *)

Definition Book_4_2_8_i  := @HoTT.Basics.Equivalences.isequiv_postcompose.
Definition Book_4_2_8_ii := @HoTT.Basics.Equivalences.isequiv_precompose.

(* ================================================== lem:inv-hprop *)
(** Lemma 4.2.9 *)

Definition Book_4_2_9_i  := @HoTT.EquivalenceVarieties.contr_sect_equiv.
Definition Book_4_2_9_ii := @HoTT.EquivalenceVarieties.contr_retr_equiv.

(* ================================================== defn:lcoh-rcoh *)
(** Definition 4.2.10 *)



(* ================================================== lem:coh-hfib *)
(** Lemma 4.2.11 *)



(* ================================================== lem:coh-hprop *)
(** Lemma 4.2.12 *)



(* ================================================== thm:hae-hprop *)
(** Theorem 4.2.13 *)

Definition Book_4_2_13 := @HoTT.Types.Equiv.hprop_isequiv.

(* ================================================== defn:biinv *)
(** Definition 4.3.1 *)

Definition Book_4_3_1  := @HoTT.EquivalenceVarieties.BiInv.

(* ================================================== thm:isprop-biinv *)
(** Theorem 4.3.2 *)

Definition Book_4_3_2  := @HoTT.EquivalenceVarieties.isprop_biinv.

(* ================================================== thm:equiv-biinv-isequiv *)
(** Corollary 4.3.3 *)

Definition Book_4_3_3  := @HoTT.EquivalenceVarieties.equiv_biinv_isequiv.

(* ================================================== defn:equivalence *)
(** Definition 4.4.1 *)

Definition Book_4_4_1 := @HoTT.Basics.Trunc.IsTruncMap -2.

(* ================================================== thm:lequiv-contr-hae *)
(** Theorem 4.4.3 *)

Definition Book_4_4_3 := @HoTT.EquivalenceVarieties.isequiv_fcontr.

(* ================================================== thm:contr-hprop *)
(** Lemma 4.4.4 *)

Definition Book_4_4_4 := @HoTT.HProp.hprop_trunc.

(* ================================================== thm:equiv-contr-hae *)
(** Theorem 4.4.5 *)

Definition Book_4_4_5 := @HoTT.EquivalenceVarieties.equiv_fcontr_isequiv.

(* ================================================== thm:equiv-inhabcod *)
(** Corollary 4.4.6 *)

Definition Book_4_4_6 := @HoTT.EquivalenceVarieties.isequiv_inhab_codomain.

(* ================================================== defn:surj-emb *)
(** Definition 4.6.1 *)

Definition Book_4_6_1 := @HoTT.Basics.Trunc.IsTruncMap -1.

(* ================================================== thm:mono-surj-equiv *)
(** Theorem 4.6.3 *)

Definition Book_4_6_3 := @HoTT.Truncations.Core.TrM.RSU.isequiv_conn_ino_map.

(* ================================================== thm:two-out-of-three *)
(** Theorem 4.7.1 *)

Definition Book_4_7_1_part_i   := @HoTT.Basics.Equivalences.isequiv_compose.
Definition Book_4_7_1_part_ii  := @HoTT.Basics.Equivalences.cancelR_isequiv.
Definition Book_4_7_1_part_iii := @HoTT.Basics.Equivalences.cancelL_isequiv.

(* ================================================== defn:retract *)
(** Definition 4.7.2 *)



(* ================================================== lem:func_retract_to_fiber_retract *)
(** Lemma 4.7.3 *)



(* ================================================== thm:retract-equiv *)
(** Theorem 4.7.4 *)



(* ================================================== defn:total-map *)
(** Definition 4.7.5 *)

Definition Book_4_7_5 := @HoTT.Types.Sigma.functor_sigma.

(* ================================================== fibwise-fiber-total-fiber-equiv *)
(** Theorem 4.7.6 *)

Definition Book_4_7_6 := @HoTT.Fibrations.hfiber_functor_sigma.

(* ================================================== thm:total-fiber-equiv *)
(** Theorem 4.7.7 *)

Definition Book_4_7_7 := @HoTT.Fibrations.isequiv_from_functor_sigma.

(* ================================================== thm:fiber-of-a-fibration *)
(** Lemma 4.8.1 *)

Definition Book_4_8_1 := @HoTT.Fibrations.hfiber_fibration.

(* ================================================== thm:total-space-of-the-fibers *)
(** Lemma 4.8.2 *)

Definition Book_4_8_2 := @HoTT.Fibrations.equiv_fibration_replacement.

(* ================================================== thm:nobject-classifier-appetizer *)
(** Theorem 4.8.3 *)

Definition Book_4_8_3 := @HoTT.ObjectClassifier.FamequivPow.

(* ================================================== thm:object-classifier *)
(** Theorem 4.8.4 *)

Definition Book_4_8_4 := @HoTT.ObjectClassifier.objclasspb_is_fibrantreplacement.

(* ================================================== weakfunext *)
(** Definition 4.9.1 *)

Definition Book_4_9_1 := @HoTT.FunextVarieties.WeakFunext.

(* ================================================== UA-eqv-hom-eqv *)
(** Lemma 4.9.2 *)

Definition Book_4_9_2 := @HoTT.UnivalenceImpliesFunext.univalence_isequiv_postcompose.

(* ================================================== contrfamtotalpostcompequiv *)
(** Corollary 4.9.3 *)



(* ================================================== uatowfe *)
(** Theorem 4.9.4 *)

Definition Book_4_9_4 := @HoTT.UnivalenceImpliesFunext.Univalence_implies_WeakFunext.

(* ================================================== wfetofe *)
(** Theorem 4.9.5 *)

Definition Book_4_9_5 := @HoTT.FunextVarieties.WeakFunext_implies_Funext.

(* ================================================== thm:nat-uniq *)
(** Theorem 5.1.1 *)



(* ================================================== thm:w-uniq *)
(** Theorem 5.3.1 *)



(* ================================================== defn:nalg *)
(** Definition 5.4.1 *)



(* ================================================== defn:nhom *)
(** Definition 5.4.2 *)



(* ================================================== thm:nat-hinitial *)
(** Theorem 5.4.5 *)



(* ================================================== thm:w-hinit *)
(** Theorem 5.4.7 *)



(* ================================================== lem:homotopy-induction-times-3 *)
(** Lemma 5.5.4 *)



(* ================================================== defn:identity-systems *)
(** Definition 5.8.1 *)



(* ================================================== thm:identity-systems *)
(** Theorem 5.8.2 *)



(* ================================================== thm:ML-identity-systems *)
(** Theorem 5.8.4 *)



(* ================================================== thm:equiv-induction *)
(** Corollary 5.8.5 *)

Definition Book_5_8_5 := @HoTT.Types.Universe.equiv_induction'.
Definition Book_5_8_5_comp := @HoTT.Types.Universe.equiv_induction'_comp.

(* ================================================== thm:htpy-induction *)
(** Corollary 5.8.6 *)



(* ================================================== thm:S1rec *)
(** Lemma 6.2.5 *)

Definition Book_6_2_5 := @HoTT.HIT.Circle.S1_rec.

(* ================================================== thm:uniqueness-for-functions-on-S1 *)
(** Lemma 6.2.8 *)



(* ================================================== thm:S1ump *)
(** Lemma 6.2.9 *)



(* ================================================== thm:contr-interval *)
(** Lemma 6.3.1 *)

Definition Book_6_3_1 := @HoTT.HIT.Interval.contr_interval.

(* ================================================== thm:interval-funext *)
(** Lemma 6.3.2 *)

Definition Book_6_3_2 := @HoTT.HIT.IntervalImpliesFunext.funext_type_from_interval.

(* ================================================== thm:loop-nontrivial *)
(** Lemma 6.4.1 *)



(* ================================================== thm:S1-autohtpy *)
(** Lemma 6.4.2 *)



(* ================================================== thm:ap2 *)
(** Lemma 6.4.4 *)

Definition Book_6_4_4 := @HoTT.Basics.PathGroupoids.ap02.

(* ================================================== thm:transport2 *)
(** Lemma 6.4.5 *)

Definition Book_6_4_5 := @HoTT.Basics.PathGroupoids.transport2.

(* ================================================== thm:apd2 *)
(** Lemma 6.4.6 *)

Definition Book_6_4_6 := @HoTT.Basics.PathGroupoids.apD02.

(* ================================================== thm:suspbool *)
(** Lemma 6.5.1 *)

Definition Book_6_5_1 := @HoTT.HIT.Spheres.isequiv_Sph1_to_S1.

(* ================================================== lem:susp-loop-adj *)
(** Lemma 6.5.4 *)

Definition Book_6_5_4 := @HoTT.Pointed.pSusp.loop_susp_adjoint.

(* ================================================== defn:cocone *)
(** Definition 6.8.1 *)



(* ================================================== thm:pushout-ump *)
(** Lemma 6.8.2 *)



(* ================================================== thm:trunc0-ind *)
(** Lemma 6.9.1 *)

Definition Book_6_9_1 := @HoTT.Truncations.Core.Trunc.Trunc_ind 0.

(* ================================================== thm:trunc0-lump *)
(** Lemma 6.9.2 *)

Definition Book_6_9_2 := @HoTT.Truncations.Core.TrM.isequiv_o_to_O.

(* ================================================== thm:set-pushout *)
(** Lemma 6.9.3 *)



(* ================================================== thm:quotient-surjective *)
(** Lemma 6.10.2 *)

Definition Book_6_10_2 := @HoTT.HIT.quotient.quotient_surjective.

(* ================================================== thm:quotient-ump *)
(** Lemma 6.10.3 *)

Definition Book_6_10_3 := @HoTT.HIT.quotient.quotient_ump.

(* ================================================== def:VVquotient *)
(** Definition 6.10.5 *)



(* ================================================== lem:quotient-when-canonical-representatives *)
(** Lemma 6.10.8 *)



(* ================================================== thm:retraction-quotient *)
(** Corollary 6.10.10 *)



(* ================================================== thm:sign-induction *)
(** Lemma 6.10.12 *)



(* ================================================== thm:looptothe *)
(** Corollary 6.10.13 *)



(* ================================================== thm:homotopy-groups *)
(** Example 6.11.4 *)



(* ================================================== thm:free-monoid *)
(** Lemma 6.11.5 *)



(* ================================================== thm:transport-is-given *)
(** Lemma 6.12.1 *)

Definition Book_6_12_1 := @HoTT.Types.Universe.transport_path_universe'.

(* ================================================== thm:flattening *)
(** Lemma 6.12.2 *)

Definition Book_6_12_2 := @HoTT.HIT.Flattening.equiv_flattening.

(* ================================================== thm:flattening-cp *)
(** Lemma 6.12.3 *)



(* ================================================== thm:flattening-rect *)
(** Lemma 6.12.4 *)

Definition Book_6_12_4 := @HoTT.HIT.Flattening.sWtil_ind.

(* ================================================== thm:flattening-rectnd *)
(** Lemma 6.12.5 *)

Definition Book_6_12_5 := @HoTT.HIT.Flattening.sWtil_rec.

(* ================================================== thm:ap-sigma-rect-path-pair *)
(** Lemma 6.12.7 *)

Definition Book_6_12_7 := @HoTT.Types.Sigma.ap_sigT_rec_path_sigma.

(* ================================================== thm:flattening-rectnd-beta-ppt *)
(** Lemma 6.12.8 *)

Definition Book_6_12_8 := @HoTT.HIT.Flattening.sWtil_rec_beta_ppt.

(* ================================================== eg:unnatural-hit *)
(** Example 6.13.1 *)



(* ================================================== def:hlevel *)
(** Definition 7.1.1 *)



(* ================================================== thm:h-level-retracts *)
(** Theorem 7.1.4 *)



(* ================================================== cor:preservation-hlevels-weq *)
(** Corollary 7.1.5 *)



(* ================================================== thm:isntype-mono *)
(** Theorem 7.1.6 *)



(* ================================================== thm:hlevel-cumulative *)
(** Theorem 7.1.7 *)



(* ================================================== thm:ntypes-sigma *)
(** Theorem 7.1.8 *)



(* ================================================== thm:hlevel-prod *)
(** Theorem 7.1.9 *)

Definition Book_7_1_9 := @HoTT.Types.Forall.trunc_forall.

(* ================================================== thm:isaprop-isofhlevel *)
(** Theorem 7.1.10 *)



(* ================================================== thm:hleveln-of-hlevelSn *)
(** Theorem 7.1.11 *)

Definition Book7_1_11 := @HoTT.TruncType.istrunc_trunctype.

(* ================================================== thm:h-set-uip-K *)
(** Theorem 7.2.1 *)



(* ================================================== thm:h-set-refrel-in-paths-sets *)
(** Theorem 7.2.2 *)

Definition Book_7_2_2 := @HoTT.HSet.ishset_hrel_subpaths.

(* ================================================== notnotstable-equality-to-set *)
(** Corollary 7.2.3 *)



(* ================================================== lem:hedberg-helper *)
(** Lemma 7.2.4 *)



(* ================================================== thm:hedberg *)
(** Theorem 7.2.5 *)



(* ================================================== prop:nat-is-set *)
(** Theorem 7.2.6 *)



(* ================================================== thm:hlevel-loops *)
(** Theorem 7.2.7 *)



(* ================================================== lem:hlevel-if-inhab-hlevel *)
(** Lemma 7.2.8 *)



(* ================================================== thm:ntype-nloop *)
(** Theorem 7.2.9 *)



(* ================================================== thm:truncn-ind *)
(** Theorem 7.3.2 *)



(* ================================================== thm:trunc-reflective *)
(** Lemma 7.3.3 *)



(* ================================================== thm:trunc-htpy *)
(** Lemma 7.3.5 *)



(* ================================================== cor:trunc-prod *)
(** Theorem 7.3.8 *)



(* ================================================== thm:trunc-in-truncated-sigma *)
(** Theorem 7.3.9 *)



(* ================================================== thm:refl-over-ntype-base *)
(** Corollary 7.3.10 *)



(* ================================================== thm:path-truncation *)
(** Theorem 7.3.12 *)

Definition Book_7_3_12 := @HoTT.Truncations.Core.equiv_path_Tr.

(* ================================================== lem:truncation-le *)
(** Lemma 7.3.15 *)



(* ================================================== thm:conemap-funct *)
(** Lemma 7.4.10 *)



(* ================================================== reflectcommutespushout *)
(** Theorem 7.4.12 *)



(* ================================================== thm:minusoneconn-surjective *)
(** Lemma 7.5.2 *)



(* ================================================== lem:nconnected_postcomp *)
(** Lemma 7.5.6 *)



(* ================================================== cor:totrunc-is-connected *)
(** Corollary 7.5.8 *)

Definition Book_7_5_8 := @HoTT.Truncations.Core.TrM.conn_map_to_O.

(* ================================================== thm:nconn-to-ntype-const *)
(** Corollary 7.5.9 *)



(* ================================================== connectedtotruncated *)
(** Corollary 7.5.9 *)



(* ================================================== lem:nconnected_to_leveln_to_equiv *)
(** Lemma 7.5.10 *)



(* ================================================== thm:connected-pointed *)
(** Lemma 7.5.11 *)



(* ================================================== lem:nconnected_postcomp_variation *)
(** Lemma 7.5.12 *)



(* ================================================== prop:nconn_fiber_to_total *)
(** Lemma 7.5.13 *)



(* ================================================== lem:connected-map-equiv-truncation *)
(** Lemma 7.5.14 *)



(* ================================================== thm:modal-mono *)
(** Lemma 7.6.2 *)

Definition Book_7_6_2 := @HoTT.Fibrations.equiv_istruncmap_ap.

(* ================================================== defn:modal-image *)
(** Definition 7.6.3 *)



(* ================================================== prop:to_image_is_connected *)
(** Lemma 7.6.4 *)



(* ================================================== prop:factor_equiv_fiber *)
(** Lemma 7.6.5 *)



(* ================================================== thm:orth-fact *)
(** Theorem 7.6.6 *)



(* ================================================== lem:hfiber_wrt_pullback *)
(** Lemma 7.6.8 *)



(* ================================================== thm:stable-images *)
(** Theorem 7.6.9 *)



(* ================================================== defn:reflective-subuniverse *)
(** Definition 7.7.1 *)



(* ================================================== thm:reflsubunv-forall *)
(** Theorem 7.7.2 *)



(* ================================================== cor:trunc_prod *)
(** Corollary 7.7.3 *)



(* ================================================== thm:modal-char *)
(** Theorem 7.7.4 *)



(* ================================================== defn:modality *)
(** Definition 7.7.5 *)



(* ================================================== prop:lv_n_deptype_sec_equiv_by_precomp *)
(** Theorem 7.7.7 *)



(* ================================================== def-of-homotopy-groups *)
(** Definition 8.0.1 *)



(* ================================================== S1-universal-cover *)
(** Definition 8.1.1 *)



(* ================================================== lem:transport-s1-code *)
(** Lemma 8.1.2 *)



(* ================================================== thm:pi1s1-decode *)
(** Definition 8.1.6 *)



(* ================================================== lem:s1-decode-encode *)
(** Lemma 8.1.7 *)



(* ================================================== lem:s1-encode-decode *)
(** Lemma 8.1.8 *)



(* ================================================== cor:omega-s1 *)
(** Corollary 8.1.10 *)



(* ================================================== cor:pi1s1 *)
(** Corollary 8.1.11 *)



(* ================================================== thm:iscontr-s1cover *)
(** Lemma 8.1.12 *)



(* ================================================== thm:encode-total-equiv *)
(** Corollary 8.1.13 *)



(* ================================================== thm:suspension-increases-connectedness *)
(** Theorem 8.2.1 *)



(* ================================================== cor:sn-connected *)
(** Corollary 8.2.2 *)



(* ================================================== lem:pik-nconnected *)
(** Lemma 8.3.2 *)



(* ================================================== def:pointedmap *)
(** Definition 8.4.1 *)



(* ================================================== def:loopfunctor *)
(** Definition 8.4.2 *)



(* ================================================== thm:fiber-of-the-fiber *)
(** Lemma 8.4.4 *)



(* ================================================== thm:les *)
(** Theorem 8.4.6 *)



(* ================================================== thm:ses *)
(** Lemma 8.4.7 *)



(* ================================================== thm:conn-pik *)
(** Corollary 8.4.8 *)



(* ================================================== thm:hopf-fibration *)
(** Theorem 8.5.1 *)



(* ================================================== cor:pis2-hopf *)
(** Corollary 8.5.2 *)



(* ================================================== lem:fibration-over-pushout *)
(** Lemma 8.5.3 *)



(* ================================================== lem:hopf-construction *)
(** Lemma 8.5.7 *)



(* ================================================== lem:hspace-S1 *)
(** Lemma 8.5.8 *)



(* ================================================== thm:conn-trunc-variable-ind *)
(** Lemma 8.6.1 *)



(* ================================================== thm:wedge-connectivity *)
(** Lemma 8.6.2 *)



(* ================================================== thm:freudenthal *)
(** Theorem 8.6.4 *)



(* ================================================== thm:freudcode *)
(** Definition 8.6.5 *)



(* ================================================== thm:freudlemma *)
(** Lemma 8.6.10 *)



(* ================================================== cor:freudenthal-equiv *)
(** Corollary 8.6.14 *)



(* ================================================== cor:stability-spheres *)
(** Corollary 8.6.15 *)



(* ================================================== thm:pinsn *)
(** Theorem 8.6.17 *)



(* ================================================== thm:pi3s2 *)
(** Corollary 8.6.19 *)



(* ================================================== thm:naive-van-kampen *)
(** Theorem 8.7.4 *)



(* ================================================== eg:circle *)
(** Example 8.7.6 *)



(* ================================================== eg:suspension *)
(** Example 8.7.7 *)



(* ================================================== eg:wedge *)
(** Example 8.7.8 *)



(* ================================================== thm:kbar *)
(** Lemma 8.7.9 *)



(* ================================================== thm:van-Kampen *)
(** Theorem 8.7.12 *)



(* ================================================== eg:clvk *)
(** Example 8.7.13 *)



(* ================================================== eg:cofiber *)
(** Example 8.7.14 *)



(* ================================================== eg:torus *)
(** Example 8.7.15 *)



(* ================================================== eg:kg1 *)
(** Example 8.7.17 *)



(* ================================================== thm:whitehead0 *)
(** Theorem 8.8.1 *)



(* ================================================== thm:whitehead1 *)
(** Corollary 8.8.2 *)



(* ================================================== thm:whiteheadn *)
(** Theorem 8.8.3 *)



(* ================================================== thm:whitehead-contr *)
(** Corollary 8.8.4 *)



(* ================================================== thm:pik-conn *)
(** Corollary 8.8.5 *)



(* ================================================== Blakers-Massey *)
(** Theorem 8.10.2 *)



(* ================================================== Eilenberg-Mac-Lane-Spaces *)
(** Theorem 8.10.3 *)



(* ================================================== thm:covering-spaces *)
(** Theorem 8.10.4 *)



(* ================================================== ct:precategory *)
(** Definition 9.1.1 *)

Definition Book_9_1_1 := @HoTT.Categories.Category.Core.PreCategory.

(* ================================================== ct:isomorphism *)
(** Definition 9.1.2 *)

Definition Book_9_1_2 := @HoTT.Categories.Category.Morphisms.Isomorphic.

(* ================================================== ct:isoprop *)
(** Lemma 9.1.3 *)

Definition Book_9_1_3 := @HoTT.Categories.Category.Morphisms.trunc_isisomorphism.

(* ================================================== ct:idtoiso *)
(** Lemma 9.1.4 *)

Definition Book_9_1_4 := @HoTT.Categories.Category.Morphisms.idtoiso.

(* ================================================== ct:precatset *)
(** Example 9.1.5 *)

Definition Book_9_1_5 := @HoTT.Categories.SetCategory.Core.set_cat.

(* ================================================== ct:category *)
(** Definition 9.1.6 *)

Definition Book_9_1_6 C := (HoTT.Categories.Category.Univalent.IsCategory C).

(* ================================================== ct:eg:set *)
(** Example 9.1.7 *)

(** Once this is proven, we will have
<<
Definition Book_9_1_7 := @HoTT.Categories.SetCategory.Morphisms.iscategory_set_cat.
>>
*)

(* ================================================== ct:obj-1type *)
(** Lemma 9.1.8 *)

Definition Book_9_1_8 := @HoTT.Categories.Category.Univalent.trunc_category.

(* ================================================== ct:idtoiso-trans *)
(** Lemma 9.1.9 *)



(* ================================================== ct:orders *)
(** Example 9.1.14 *)



(* ================================================== ct:gaunt *)
(** Example 9.1.15 *)

Definition Book_9_1_15 A `{H : HoTT.Categories.Category.Univalent.IsCategory A}
: IsHSet (HoTT.Categories.Category.Core.object A)
  <-> (forall a b, IsHProp (@HoTT.Categories.Category.Morphisms.Isomorphic A a b)).
Proof.
  split.
  - intros H' a b.
    eapply trunc_equiv.
    + refine (H' a b).
    + apply H.
  - intros H' a b.
    eapply trunc_equiv.
    + apply (H' a b).
    + apply (@isequiv_inverse _ _ _ (H _ _)).
Defined.

(* ================================================== ct:discrete *)
(** Example 9.1.16 *)

Definition Book_9_1_16 := @HoTT.Categories.GroupoidCategory.Core.groupoid_category.

(* ================================================== ct:fundgpd *)
(** Example 9.1.17 *)

Definition Book_9_1_17 := @HoTT.Categories.FundamentalPreGroupoidCategory.fundamental_pregroupoid_category.

(* ================================================== ct:hoprecat *)
(** Example 9.1.18 *)

Definition Book_9_1_18 := @HoTT.Categories.HomotopyPreCategory.homotopy_precategory.

(* ================================================== ct:rel *)
(** Example 9.1.19 *)



(* ================================================== ct:functor *)
(** Definition 9.2.1 *)

Definition Book_9_2_1 := @HoTT.Categories.Functor.Core.Functor.

(* ================================================== ct:nattrans *)
(** Definition 9.2.2 *)

Definition Book_9_2_2 := @HoTT.Categories.NaturalTransformation.Core.NaturalTransformation.

(* ================================================== ct:functor-precat *)
(** Definition 9.2.3 *)

Definition Book_9_2_3 := @HoTT.Categories.FunctorCategory.Core.functor_category.

(* ================================================== ct:natiso *)
(** Lemma 9.2.4 *)

Definition Book_9_2_4 := @HoTT.Categories.FunctorCategory.Morphisms.isisomorphism_natural_transformation.

(* ================================================== ct:functor-cat *)
(** Theorem 9.2.5 *)

(** When this is done, it will be
<<
Definition Book_9_2_5 := @HoTT.Categories.FunctorCategory.Morphisms.iscategory_functor_category.
>>
*)

(* ================================================== ct:functor-composition *)
(** Definition 9.2.6 *)

Definition Book_9_2_6 := @HoTT.Categories.Functor.Composition.Core.compose.

(* ================================================== ct:whisker *)
(** Definition 9.2.7 *)

Definition Book_9_2_7_l := @HoTT.Categories.NaturalTransformation.Composition.Core.whisker_l.
Definition Book_9_2_7_r := @HoTT.Categories.NaturalTransformation.Composition.Core.whisker_r.

(* ================================================== ct:interchange *)
(** Lemma 9.2.8 *)

Definition Book_9_2_8 := @HoTT.Categories.NaturalTransformation.Composition.Laws.exchange_whisker.

(* ================================================== ct:functor-assoc *)
(** Lemma 9.2.9 *)

Definition Book_9_2_9 := @HoTT.Categories.Functor.Composition.Laws.associativity.

(* ================================================== ct:pentagon *)
(** Lemma 9.2.10 *)



(* ================================================== ct:units *)
(** Lemma 9.2.11 *)

Definition Book_9_2_11_l := @HoTT.Categories.Functor.Composition.Laws.left_identity.
Definition Book_9_2_11_r := @HoTT.Categories.Functor.Composition.Laws.right_identity.
Definition Book_9_2_11 := @HoTT.Categories.Functor.Composition.Laws.triangle.

(* ================================================== ct:adjoints *)
(** Definition 9.3.1 *)

Definition Book_9_3_1 := @HoTT.Categories.Adjoint.UnitCounit.AdjunctionUnitCounit.

(* ================================================== ct:adjprop *)
(** Lemma 9.3.2 *)



(* ================================================== ct:equiv *)
(** Definition 9.4.1 *)



(* ================================================== ct:adjointification *)
(** Lemma 9.4.2 *)

Definition Book_9_4_2a := @HoTT.Categories.Functor.Attributes.IsFaithful.
Definition Book_9_4_2b := @HoTT.Categories.Functor.Attributes.IsFull.
Definition Book_9_4_2c := @HoTT.Categories.Functor.Attributes.IsFullyFaithful.

(* ================================================== ct:full-faithful *)
(** Definition 9.4.3 *)



(* ================================================== ct:split-essentially-surjective *)
(** Definition 9.4.4 *)

Definition Book_9_4_4 := @HoTT.Categories.Functor.Attributes.IsSplitEssentiallySurjective.

(* ================================================== ct:ffeso *)
(** Lemma 9.4.5 *)



(* ================================================== ct:essentially-surjective *)
(** Definition 9.4.6 *)

Definition Book_9_4_6_ess := @HoTT.Categories.Functor.Attributes.IsEssentiallySurjective.
Definition Book_9_4_6_weq := @HoTT.Categories.Functor.Attributes.IsWeakEquivalence.

(* ================================================== ct:catweq *)
(** Lemma 9.4.7 *)



(* ================================================== ct:isocat *)
(** Definition 9.4.8 *)



(* ================================================== ct:isoprecat *)
(** Lemma 9.4.9 *)



(* ================================================== ct:chaotic *)
(** Example 9.4.13 *)

Definition Book_9_4_13 := @HoTT.Categories.IndiscreteCategory.Core.indiscrete_category.

(* ================================================== ct:eqv-levelwise *)
(** Lemma 9.4.14 *)



(* ================================================== ct:cat-eq-iso *)
(** Lemma 9.4.15 *)



(* ================================================== ct:cat-2cat *)
(** Theorem 9.4.16 *)



(* ================================================== ct:opposite-category *)
(** Definition 9.5.1 *)

Definition Book_9_5_1 := @HoTT.Categories.Category.Dual.opposite.

(* ================================================== ct:prod-cat *)
(** Definition 9.5.2 *)

Definition Book_9_5_2 := @HoTT.Categories.Category.Prod.prod.

(* ================================================== ct:functorexpadj *)
(** Lemma 9.5.3 *)

(** When we prove it, this should be mapped to the law, not the functor. *)
Definition Book_9_5_3 := @HoTT.Categories.ExponentialLaws.Law4.Functors.functor.

(* ================================================== ct:yoneda *)
(** Theorem 9.5.4 *)

Definition Book_9_5_4 := @HoTT.Categories.Yoneda.yoneda_lemma.

(* ================================================== ct:yoneda-embedding *)
(** Corollary 9.5.6 *)

Definition Book_9_5_6 := @HoTT.Categories.Yoneda.yoneda_embedding.

(* ================================================== ct:yoneda-mono *)
(** Corollary 9.5.7 *)



(* ================================================== ct:representable *)
(** Definition 9.5.8 *)



(* ================================================== ct:representable-prop *)
(** Theorem 9.5.9 *)



(* ================================================== ct:adj-repr *)
(** Lemma 9.5.10 *)



(* ================================================== ct:adjprop2 *)
(** Corollary 9.5.11 *)



(* ================================================== ct:strict-category *)
(** Definition 9.6.1 *)

Definition Book_9_6_1 C := HoTT.Categories.Category.Strict.IsStrictCategory C.

(* ================================================== ct:mono-cat *)
(** Example 9.6.2 *)



(* ================================================== ct:galois *)
(** Example 9.6.3 *)



(* ================================================== ct:dagger-precategory *)
(** Definition 9.7.1 *)



(* ================================================== ct:unitary *)
(** Definition 9.7.2 *)



(* ================================================== ct:idtounitary *)
(** Lemma 9.7.3 *)



(* ================================================== ct:dagger-category *)
(** Definition 9.7.4 *)



(* ================================================== ct:rel-dagger-cat *)
(** Example 9.7.5 *)



(* ================================================== ct:groupoid-dagger-cat *)
(** Example 9.7.6 *)



(* ================================================== ct:hilb *)
(** Example 9.7.7 *)



(* ================================================== ct:sig *)
(** Definition 9.8.1 *)

Definition Book_9_8_1 := @HoTT.Categories.Structure.Core.NotionOfStructure.

(* ================================================== thm:sip *)
(** Theorem 9.8.2 *)

Definition Book_9_8_2 := @HoTT.Categories.Structure.IdentityPrinciple.structure_identity_principle.

(* ================================================== ct:sip-functor-cat *)
(** Example 9.8.3 *)



(* ================================================== defn:fo-notion-of-structure *)
(** Definition 9.8.4 *)



(* ================================================== ct:esosurj-postcomp-faithful *)
(** Lemma 9.9.1 *)



(* ================================================== ct:esofull-precomp-ff *)
(** Lemma 9.9.2 *)



(* ================================================== ct:cat-weq-eq *)
(** Theorem 9.9.4 *)



(* ================================================== thm:rezk-completion *)
(** Theorem 9.9.5 *)



(* ================================================== ct:rezk-fundgpd-trunc1 *)
(** Example 9.9.6 *)



(* ================================================== ct:hocat *)
(** Example 9.9.7 *)



(* ================================================== ct:weq-iso-precat-cat *)
(** Theorem 9.9.8 *)



(* ================================================== thm:mono *)
(** Lemma 10.1.1 *)

(** The third notion in the book is called embedding. No complete equivalence yet, but see:*)
Definition Book_10_1_1_iii := @HSet.isinj_embedding.

(* ================================================== thm:inj-mono *)
(** Lemma 10.1.2 *)

Definition Book_10_1_2rl := @HSet.isinj_ismono.
Definition Book_10_1_2lr := @HSet.ismono_isinj.
(* This one is not in the book, but close to 10.1.2:
 HSet.isembedding_isinj_hset*)

(* ================================================== epis-surj *)
(** Lemma 10.1.4 *)

Definition Book_10_1_4_i_iii := @HIT.epi.isepi_issurj.
Definition Book_10_1_4_i_ii := @HIT.epi.isepi'_contr_cone.
Definition Book_10_1_4_iii_i := @HIT.epi.issurj_isepi.

(* ================================================== lem:images_are_coequalizers *)
(** Theorem 10.1.5 *)



(* ================================================== thm:set_regular *)
(** Theorem 10.1.5 *)



(* ================================================== lem:pb_of_coeq_is_coeq *)
(** Lemma 10.1.6 *)



(* ================================================== lem:sets_exact *)
(** Lemma 10.1.8 *)

Definition Book_10_1_8 := @HIT.quotient.sets_exact.

(* ================================================== prop:kernels_are_effective *)
(** Theorem 10.1.9 *)

(* See: HIT.unique_choice.unique_choice
theories.ObjectClassifier.PowisoPFam
Apparently closure under Pi and Sigma are still missing ? *)

(* ================================================== thm:settopos *)
(** Theorem 10.1.12 *)



(* ================================================== prop:trunc_of_prop_is_set *)
(** Lemma 10.1.13 *)



(* ================================================== thm:1surj_to_surj_to_pem *)
(** Theorem 10.1.14 *)



(* ================================================== thm:ETCS *)
(** Theorem 10.1.15 *)



(* ================================================== defn:card *)
(** Definition 10.2.1 *)



(* ================================================== card:semiring *)
(** Lemma 10.2.4 *)



(* ================================================== card:exp *)
(** Lemma 10.2.6 *)



(* ================================================== thm:injsurj *)
(** Lemma 10.2.9 *)



(* ================================================== defn:accessibility *)
(** Definition 10.3.1 *)



(* ================================================== thm:nat-wf *)
(** Example 10.3.5 *)



(* ================================================== thm:wtype-wf *)
(** Example 10.3.6 *)



(* ================================================== thm:wfrec *)
(** Lemma 10.3.7 *)



(* ================================================== thm:wfmin *)
(** Lemma 10.3.8 *)



(* ================================================== def:simulation *)
(** Definition 10.3.11 *)



(* ================================================== thm:wfcat *)
(** Corollary 10.3.15 *)



(* ================================================== thm:ordord *)
(** Theorem 10.3.20 *)



(* ================================================== thm:ordsucc *)
(** Lemma 10.3.21 *)



(* ================================================== thm:ordunion *)
(** Lemma 10.3.22 *)



(* ================================================== thm:wellorder *)
(** Theorem 10.4.3 *)



(* ================================================== thm:wop *)
(** Theorem 10.4.4 *)



(* ================================================== defn:V *)
(** Definition 10.5.1 *)

Definition Book_10_5_1 := @HoTT.HIT.V.CumulativeHierarchy.V.

(* ================================================== def:bisimulation *)
(** Definition 10.5.4 *)

Definition Book_10_5_4 := @HoTT.HIT.V.bisimulation.

(* ================================================== lem:BisimEqualsId *)
(** Lemma 10.5.5 *)

Definition Book_10_5_5 := @HoTT.HIT.V.bisimulation_equiv_id.

(* ================================================== lem:MonicSetPresent *)
(** Lemma 10.5.6 *)

Definition Book_10_5_6 := @HoTT.HIT.V.monic_set_present.

(* ================================================== def:TypeOfElements *)
(** Definition 10.5.7 *)

Definition Book_10_5_7 := @HoTT.HIT.V.type_of_members.

(* ================================================== thm:VisCST *)
(** Theorem 10.5.8 *)

Definition Book_10_5_8_item_i := @HoTT.HIT.V.extensionality.
Definition Book_10_5_8_item_ii := @HoTT.HIT.V.not_mem_Vempty.
Definition Book_10_5_8_item_iii := @HoTT.HIT.V.pairing.
Definition Book_10_5_8_item_iv := @HoTT.HIT.V.infinity.
Definition Book_10_5_8_item_v := @HoTT.HIT.V.union.
Definition Book_10_5_8_item_vi := @HoTT.HIT.V.function.
Definition Book_10_5_8_item_vii := @HoTT.HIT.V.mem_induction.
Definition Book_10_5_8_item_viii := @HoTT.HIT.V.replacement.
Definition Book_10_5_8_item_ix := @HoTT.HIT.V.separation.

(* ================================================== cor:Delta0sep *)
(** Corollary 10.5.9 *)



(* ================================================== lem:fullsep *)
(** Lemma 10.5.10 *)



(* ================================================== thm:zfc *)
(** Theorem 10.5.11 *)



(* ================================================== defn:dedekind-reals *)
(** Definition 11.2.1 *)



(* ================================================== dedekind-in-cut-as-le *)
(** Lemma 11.2.2 *)



(* ================================================== RD-inverse-apart-0 *)
(** Theorem 11.2.4 *)



(* ================================================== RD-archimedean *)
(** Theorem 11.2.6 *)



(* ================================================== ordered-field *)
(** Definition 11.2.7 *)

Definition Book_11_2_7 := @HoTT.Classes.interfaces.abstract_algebra.Field.
Definition Book_11_2_7' := @HoTT.Classes.interfaces.orders.FullPseudoSemiRingOrder.

(* ================================================== RD-archimedean-ordered-field *)
(** Theorem 11.2.8 *)



(* ================================================== defn:cauchy-approximation *)
(** Definition 11.2.10 *)

Definition Book_11_2_10 := @HoTT.Classes.theory.premetric.Approximation.

(* ================================================== RD-cauchy-complete *)
(** Theorem 11.2.12 *)



(* ================================================== RD-final-field *)
(** Theorem 11.2.14 *)



(* ================================================== lem:cuts-preserve-admissibility *)
(** Lemma 11.2.15 *)



(* ================================================== RD-dedekind-complete *)
(** Corollary 11.2.16 *)



(* ================================================== defn:cauchy-reals *)
(** Definition 11.3.2 *)



(* ================================================== lem:close-reflexive *)
(** Lemma 11.3.8 *)



(* ================================================== thm:Cauchy-reals-are-a-set *)
(** Theorem 11.3.9 *)



(* ================================================== RC-lim-onto *)
(** Lemma 11.3.10 *)



(* ================================================== RC-lim-factor *)
(** Lemma 11.3.11 *)



(* ================================================== thm:RCsim-symmetric *)
(** Lemma 11.3.12 *)



(* ================================================== defn:lipschitz *)
(** Definition 11.3.14 *)

Definition Book_11_3_14 := @HoTT.Classes.theory.premetric.Lipschitz.

(* ================================================== RC-extend-Q-Lipschitz *)
(** Lemma 11.3.15 *)



(* ================================================== defn:RC-approx *)
(** Theorem 11.3.16 *)



(* ================================================== thm:RC-sim-characterization *)
(** Theorem 11.3.32 *)



(* ================================================== thm:RC-sim-lim *)
(** Lemma 11.3.36 *)



(* ================================================== thm:RC-sim-lim-term *)
(** Lemma 11.3.37 *)



(* ================================================== RC-continuous-eq *)
(** Lemma 11.3.39 *)



(* ================================================== RC-binary-nonexpanding-extension *)
(** Lemma 11.3.40 *)



(* ================================================== RC-archimedean *)
(** Theorem 11.3.41 *)



(* ================================================== thm:RC-le-grow *)
(** Lemma 11.3.42 *)



(* ================================================== thm:RC-lt-open *)
(** Lemma 11.3.43 *)



(* ================================================== RC-sim-eqv-le *)
(** Theorem 11.3.44 *)



(* ================================================== RC-squaring *)
(** Theorem 11.3.46 *)



(* ================================================== RC-archimedean-ordered-field *)
(** Theorem 11.3.48 *)



(* ================================================== RC-initial-Cauchy-complete *)
(** Theorem 11.3.50 *)



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



(* ================================================== defn:surreals *)
(** Definition 11.6.1 *)

Definition Book_11_6_1 := @HoTT.Spaces.No.Core.No.

(* ================================================== thm:NO-simplicity *)
(** Theorem 11.6.2 *)



(* ================================================== thm:NO-refl-opt *)
(** Theorem 11.6.4 *)

Definition Book_11_6_4_i := @HoTT.Spaces.No.Core.le_reflexive.
Definition Book_11_6_4_ii_l := @HoTT.Spaces.No.Core.lt_lopt.
Definition Book_11_6_4_ii_r := @HoTT.Spaces.No.Core.lt_ropt.

(* ================================================== thm:NO-set *)
(** Corollary 11.6.5 *)

Definition Book_11_6_5 := @HoTT.Spaces.No.Core.isset_No.

(* ================================================== defn:No-codes *)
(** Theorem 11.6.7 *)

Definition Book_11_6_7 := @HoTT.Spaces.No.Core.No_codes_package.

(* ================================================== thm:NO-encode-decode *)
(** Theorem 11.6.16 *)

Definition Book_11_6_16_i := @HoTT.Spaces.No.Core.No_encode_le_lt.
Definition Book_11_6_16_ii := @HoTT.Spaces.No.Core.No_decode_le_lt.

(* ================================================== thm:NO-unstrict-transitive *)
(** Corollary 11.6.17 *)

Definition Book_11_6_17_i := @HoTT.Spaces.No.Core.lt_le.
Definition Book_11_6_17_ii := @HoTT.Spaces.No.Core.le_le_trans.
Definition Book_11_6_17_iii := @HoTT.Spaces.No.Core.le_lt_trans.
Definition Book_11_6_17_iv := @HoTT.Spaces.No.Core.lt_le_trans.

(* ================================================== eg:surreal-addition *)
(** Example 11.6.18 *)

Definition Book_11_6_18 := @HoTT.Spaces.No.Addition.plus.

