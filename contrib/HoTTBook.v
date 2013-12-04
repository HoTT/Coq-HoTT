(** The HoTT Book formalization. *)

(** This file links the results of the HoTT Book with their formalizations
    in the HoTT library. You can lookup definitions and theorems by their
    number in the HoTT Book.

    IMPORTANT NOTE FOR THE HoTT DEVELOPERS:

    This files is processed automagically by the etc/Book.py script. The
    script parses the file according to the markers present in it (the
    comment lines with many = signs followed by a LaTeX label). It
    reorders the entries according to entry number X.Y.Z and inserts
    missing entries. You must therefore obey the following rules:

    1. Do not mess with the markers. If a LaTeX label has been renamed
       you may rename the corresponding marker.

    3. If a theorem is gone, you may delete the corresponding entry,
       but make sure first that it was not just moved elsewhere.

    4. Strive to make entries as self-sufficient as possible. Entries may
       get reordered or deleted.

    5. If you need to import anything, do it before the first entry.

    6. Each entry should define Book_X_Y_Z, but you can also
       put in auxiliary definitions and lemmas (keep it short please).
       The script renames the Book_X_Y_Z to whatever the correct number
       is, so initially you can use whatever number you like.

       If you are formalizing a Lemma with several part, use
       Book_X_Y_Z_item_i, Book_X_Y_Z_item_ii, or some such.

    7. If there is a corresponding HoTT library theorem or definition,
       please use that one, even if it is not exactly the same.
*)

Require Import HoTT HoTT.types.ObjectClassifier.

(* ================================================== ex:composition *)
(* Exercise 1.1 *)

Definition Book_1_1 := @compose.

(* ================================================== ex:pr-to-rec *)
(* Exercise 1.2 *)



(* ================================================== ex:pr-to-ind *)
(* Exercise 1.3 *)



(* ================================================== ex:iterator *)
(* Exercise 1.4 *)



(* ================================================== ex:sum-via-bool *)
(* Exercise 1.5 *)



(* ================================================== ex:prod-via-bool *)
(* Exercise 1.6 *)



(* ================================================== ex:pm-to-ml *)
(* Exercise 1.7 *)



(* ================================================== ex:fin *)
(* Exercise 1.9 *)



(* ================================================== ex:ackermann *)
(* Exercise 1.10 *)

Fixpoint ack (n m : nat) : nat :=
  match n with
  | O => S m
  | S p => let fix ackn (m : nat) :=
               match m with
                 | O => ack p 1
                 | S q => ack p (ackn q)
               end
           in ackn m
  end.

Definition Book_1_10 := ack.

(* ================================================== ex:neg-ldn *)
(* Exercise 1.11 *)



(* ================================================== ex:tautologies *)
(* Exercise 1.12 *)



(* ================================================== ex:not-not-lem *)
(* Exercise 1.13 *)



(* ================================================== ex:without-K *)
(* Exercise 1.14 *)



(* ================================================== ex:subtFromPathInd *)
(* Exercise 1.15 *)



(* ================================================== lem:opp *)
(* Lemma 2.1.1 *)

Definition Book_2_1_1 := @HoTT.Overture.inverse.

(* ================================================== lem:concat *)
(* Lemma 2.1.2 *)

Definition Book_2_1_2 := @HoTT.Overture.concat.

(* ================================================== thm:omg *)
(* Lemma 2.1.4 *)

Definition Book_2_1_4_item_i := @HoTT.PathGroupoids.concat_p1.
Definition Book_2_1_4_item_i' := @HoTT.PathGroupoids.concat_1p.
Definition Book_2_1_4_item_ii := @HoTT.PathGroupoids.concat_Vp.
Definition Book_2_1_4_item_ii' := @HoTT.PathGroupoids.concat_pV.
Definition Book_2_1_4_item_iii := @HoTT.PathGroupoids.inv_V.
Definition Book_2_1_4_item_iv := @HoTT.PathGroupoids.concat_p_pp.

(* ================================================== thm:EckmannHilton *)
(* Theorem 2.1.6 *)

Definition Book_2_1_6 := @HoTT.PathGroupoids.eckmann_hilton.

(* ================================================== def:pointedtype *)
(* Definition 2.1.7 *)

Definition Book_2_1_7 := @HoTT.Overture.pointedType.

(* ================================================== def:loopspace *)
(* Definition 2.1.8 *)



(* ================================================== lem:map *)
(* Lemma 2.2.1 *)

Definition Book_2_2_1 := @HoTT.Overture.ap.

(* ================================================== lem:ap-functor *)
(* Lemma 2.2.2 *)

Definition Book_2_2_2_item_i   := @HoTT.PathGroupoids.ap_pp.
Definition Book_2_2_2_item_ii  := @HoTT.PathGroupoids.inverse_ap.
Definition Book_2_2_2_item_iii := @HoTT.PathGroupoids.ap_compose.
Definition Book_2_2_2_item_iv  := @HoTT.PathGroupoids.ap_idmap.

(* ================================================== lem:transport *)
(* Lemma 2.3.1 *)

Definition Book_2_3_1 := @HoTT.Overture.transport.

(* ================================================== thm:path-lifting *)
(* Lemma 2.3.2 *)

(* special case of *)
Definition Book_2_3_2 := @HoTT.types.Sigma.equiv_path_sigma.

(* ================================================== lem:mapdep *)
(* Lemma 2.3.4 *)

Definition Book_2_3_4 := @HoTT.Overture.apD.

(* ================================================== thm:trans-trivial *)
(* Lemma 2.3.5 *)

Definition Book_2_3_5 := @HoTT.PathGroupoids.transport_const.

(* ================================================== thm:apd-const *)
(* Lemma 2.3.8 *)

Definition Book_2_3_8 := @HoTT.PathGroupoids.apD_const.

(* ================================================== thm:transport-concat *)
(* Lemma 2.3.9 *)

Definition Book_2_3_9 := @HoTT.PathGroupoids.transport_compose.

(* ================================================== thm:transport-compose *)
(* Lemma 2.3.10 *)

Definition Book_2_3_10 := @HoTT.PathGroupoids.ap_transport.

(* ================================================== thm:ap-transport *)
(* Lemma 2.3.11 *)

Definition Book_2_3_11 := @HoTT.PathGroupoids.transport_pp.

(* ================================================== defn:homotopy *)
(* Definition 2.4.1 *)

Definition Book_2_4_1 := @HoTT.Overture.pointwise_paths.

(* ================================================== lem:homotopy-props *)
(* Lemma 2.4.2 *)

Definition Book_2_4_2 := @HoTT.Overture.pointwise_paths.

(* ================================================== lem:htpy-natural *)
(* Lemma 2.4.3 *)

Definition Book_2_4_3 := @HoTT.PathGroupoids.concat_Ap.

(* ================================================== cor:hom-fg *)
(* Corollary 2.4.4 *)

Definition Book_2_4_4 := @HoTT.PathGroupoids.concat_A1p.

(* ================================================== defn:quasi-inverse *)
(* Definition 2.4.6 *)

(** Quasi-inverses do not occur explicitly in the library since 
    they are `not good'. They do only occur implicitly as input to
    isequiv_adjointify : IsEquiv f. Therefore we link to the half
    adjoint equivalence extending the quasi-inverse *)

Definition Book_2_4_6 := @HoTT.Equivalences.isequiv_adjointify. 


(* ================================================== eg:idequiv *)
(* Example 2.4.7 *)

Definition Book_2_4_7 := @HoTT.Equivalences.equiv_idmap. 

(* ================================================== eg:concatequiv *)
(* Example 2.4.8 *)



(* ================================================== thm:transportequiv *)
(* Example 2.4.9 *)

Definition Book_2_4_9 := @HoTT.Equivalences.isequiv_transport.

(* ================================================== thm:equiv-eqrel *)
(* Lemma 2.4.12 *)

Definition Book_2_4_12_item_i   := @HoTT.Equivalences.reflexive_equiv.
(* missing? Definition Book_2_4_12_item_ii  :=  *)
Definition Book_2_4_12_item_iii := @HoTT.Equivalences.transitive_equiv.

(* ================================================== thm:path-prod *)
(* Theorem 2.6.2 *)

Definition Book_2_6_2 := @HoTT.types.Prod.equiv_path_prod.

(* ================================================== thm:trans-prod *)
(* Theorem 2.6.4 *)

Definition Book_2_6_4 := @HoTT.types.Prod.transport_prod.

(* ================================================== thm:ap-prod *)
(* Theorem 2.6.5 *)

Definition Book_2_6_5 := @HoTT.types.Prod.ap_functor_prod.

(* ================================================== thm:path-sigma *)
(* Theorem 2.7.2 *)

Definition Book_2_7_2 := @HoTT.types.Sigma.equiv_path_sigma.

(* ================================================== thm:eta-sigma *)
(* Corollary 2.7.3 *)

Definition Book_2_7_3 := @HoTT.types.Sigma.eta_sigma.

(* ================================================== transport-Sigma *)
(* Theorem 2.7.4 *)

Definition Book_2_7_4 := @HoTT.types.Sigma.transportD_is_transport.

(* ================================================== thm:path-unit *)
(* Theorem 2.8.1 *)

Definition Book_2_8_1 := @HoTT.types.Unit.equiv_path_unit.

(* ================================================== axiom:funext *)
(* Axiom 2.9.3 *)

Definition Book_2_9_3 := @HoTT.Overture.path_forall.

(* ================================================== thm:dpath-arrow *)
(* Lemma 2.9.6 *)

(** non-dependent as special case of dependent *)
Definition Book_2_9_6 := @HoTT.types.Forall.dpath_forall.

(* ================================================== thm:dpath-forall *)
(* Lemma 2.9.7 *)

Definition Book_2_9_7 := @HoTT.types.Forall.dpath_forall.

(* ================================================== axiom:univalence *)
(* Axiom 2.10.3 *)

Definition Book_2_10_1 := @HoTT.types.Universe.equiv_path.


(* ================================================== thm:transport-is-ap *)
(* Lemma 2.10.5 *)



(* ================================================== thm:paths-respects-equiv *)
(* Theorem 2.11.1 *)



(* ================================================== cor:transport-path-prepost *)
(* Lemma 2.11.2 *)



(* ================================================== thm:transport-path *)
(* Theorem 2.11.3 *)



(* ================================================== thm:transport-path2 *)
(* Theorem 2.11.4 *)



(* ================================================== thm:dpath-path *)
(* Theorem 2.11.5 *)



(* ================================================== thm:path-coprod *)
(* Theorem 2.12.5 *)



(* ================================================== thm:path-nat *)
(* Theorem 2.13.1 *)



(* ================================================== thm:prod-ump *)
(* Theorem 2.15.2 *)



(* ================================================== thm:prod-umpd *)
(* Theorem 2.15.5 *)



(* ================================================== thm:ttac *)
(* Theorem 2.15.7 *)



(* ================================================== ex:basics:concat *)
(* Exercise 2.1 *)



(* ================================================== ex:npaths *)
(* Exercise 2.4 *)



(* ================================================== ex:equiv-concat *)
(* Exercise 2.6 *)



(* ================================================== ex:ap-sigma *)
(* Exercise 2.7 *)



(* ================================================== ex:coprod-ump *)
(* Exercise 2.9 *)



(* ================================================== ex:sigma-assoc *)
(* Exercise 2.10 *)



(* ================================================== ex:pullback *)
(* Exercise 2.11 *)



(* ================================================== ex:pullback-pasting *)
(* Exercise 2.12 *)



(* ================================================== ex:eqvboolbool *)
(* Exercise 2.13 *)



(* ================================================== ex:equality-reflection *)
(* Exercise 2.14 *)



(* ================================================== ex:strong-from-weak-funext *)
(* Exercise 2.16 *)



(* ================================================== defn:set *)
(* Definition 3.1.1 *)



(* ================================================== thm:nat-set *)
(* Example 3.1.4 *)



(* ================================================== thm:isset-prod *)
(* Example 3.1.5 *)



(* ================================================== thm:isset-forall *)
(* Example 3.1.6 *)



(* ================================================== defn:1type *)
(* Definition 3.1.7 *)



(* ================================================== thm:isset-is1type *)
(* Lemma 3.1.8 *)



(* ================================================== thm:type-is-not-a-set *)
(* Example 3.1.9 *)



(* ================================================== thm:not-dneg *)
(* Theorem 3.2.2 *)



(* ================================================== thm:not-lem *)
(* Corollary 3.2.7 *)



(* ================================================== defn:isprop *)
(* Definition 3.3.1 *)



(* ================================================== thm:inhabprop-eqvunit *)
(* Lemma 3.3.2 *)



(* ================================================== lem:equiv-iff-hprop *)
(* Lemma 3.3.3 *)



(* ================================================== thm:prop-set *)
(* Lemma 3.3.4 *)



(* ================================================== thm:isprop-isset *)
(* Lemma 3.3.5 *)



(* ================================================== thm:isprop-isprop *)
(* Lemma 3.3.5 *)



(* ================================================== defn:decidable-equality *)
(* Definition 3.4.3 *)



(* ================================================== defn:setof *)
(* Lemma 3.5 *)



(* ================================================== thm:path-subset *)
(* Lemma 3.5.1 *)



(* ================================================== thm:isprop-forall *)
(* Example 3.6.2 *)



(* ================================================== defn:logical-notation *)
(* Definition 3.7.1 *)



(* ================================================== thm:ac-epis-split *)
(* Lemma 3.8.2 *)



(* ================================================== thm:no-higher-ac *)
(* Lemma 3.8.5 *)



(* ================================================== cor:UC *)
(* Corollary 3.9.2 *)



(* ================================================== defn:contractible *)
(* Definition 3.11.1 *)



(* ================================================== thm:contr-unit *)
(* Lemma 3.11.3 *)



(* ================================================== thm:isprop-iscontr *)
(* Lemma 3.11.4 *)



(* ================================================== thm:contr-contr *)
(* Corollary 3.11.5 *)



(* ================================================== thm:contr-forall *)
(* Lemma 3.11.6 *)



(* ================================================== thm:retract-contr *)
(* Lemma 3.11.7 *)



(* ================================================== thm:contr-paths *)
(* Lemma 3.11.8 *)



(* ================================================== thm:omit-contr *)
(* Lemma 3.11.9 *)



(* ================================================== thm:prop-minusonetype *)
(* Lemma 3.11.10 *)



(* ================================================== ex:isset-coprod *)
(* Exercise 3.2 *)



(* ================================================== ex:isset-sigma *)
(* Exercise 3.3 *)



(* ================================================== ex:prop-endocontr *)
(* Exercise 3.4 *)



(* ================================================== ex:prop-inhabcontr *)
(* Exercise 3.5 *)



(* ================================================== ex:lem-mereprop *)
(* Exercise 3.6 *)



(* ================================================== ex:disjoint-or *)
(* Exercise 3.7 *)



(* ================================================== ex:brck-qinv *)
(* Exercise 3.8 *)



(* ================================================== ex:lem-impred *)
(* Exercise 3.10 *)



(* ================================================== ex:lem-brck *)
(* Exercise 3.14 *)



(* ================================================== ex:impred-brck *)
(* Exercise 3.15 *)



(* ================================================== ex:prop-trunc-ind *)
(* Exercise 3.17 *)



(* ================================================== ex:lem-ldn *)
(* Exercise 3.18 *)



(* ================================================== ex:decidable-choice *)
(* Exercise 3.19 *)



(* ================================================== ex:omit-contr2 *)
(* Exercise 3.20 *)



(* ================================================== lem:qinv-autohtpy *)
(* Lemma 4.1.1 *)



(* ================================================== lem:autohtpy *)
(* Lemma 4.1.2 *)



(* ================================================== defn:ishae *)
(* Definition 4.2.1 *)



(* ================================================== lem:coh-equiv *)
(* Lemma 4.2.2 *)



(* ================================================== thm:equiv-iso-adj *)
(* Theorem 4.2.3 *)



(* ================================================== defn:homotopy-fiber *)
(* Definition 4.2.4 *)



(* ================================================== lem:hfib *)
(* Lemma 4.2.5 *)



(* ================================================== thm:contr-hae *)
(* Theorem 4.2.6 *)



(* ================================================== defn:linv-rinv *)
(* Definition 4.2.7 *)



(* ================================================== thm:equiv-compose-equiv *)
(* Lemma 4.2.8 *)



(* ================================================== lem:inv-hprop *)
(* Lemma 4.2.9 *)



(* ================================================== defn:lcoh-rcoh *)
(* Definition 4.2.10 *)



(* ================================================== lem:coh-hfib *)
(* Lemma 4.2.11 *)



(* ================================================== lem:coh-hprop *)
(* Lemma 4.2.12 *)



(* ================================================== thm:hae-hprop *)
(* Theorem 4.2.13 *)



(* ================================================== defn:biinv *)
(* Definition 4.3.1 *)



(* ================================================== thm:isprop-biinv *)
(* Theorem 4.3.2 *)



(* ================================================== thm:equiv-biinv-isequiv *)
(* Corollary 4.3.3 *)



(* ================================================== defn:equivalence *)
(* Definition 4.4.1 *)



(* ================================================== thm:lequiv-contr-hae *)
(* Theorem 4.4.3 *)



(* ================================================== thm:contr-hprop *)
(* Lemma 4.4.4 *)



(* ================================================== thm:equiv-contr-hae *)
(* Theorem 4.4.5 *)



(* ================================================== thm:equiv-inhabcod *)
(* Corollary 4.4.6 *)



(* ================================================== thm:mono-surj-equiv *)
(* Theorem 4.6.3 *)



(* ================================================== thm:two-out-of-three *)
(* Theorem 4.7.1 *)



(* ================================================== defn:retract *)
(* Definition 4.7.2 *)



(* ================================================== lem:func_retract_to_fiber_retract *)
(* Lemma 4.7.3 *)



(* ================================================== thm:retract-equiv *)
(* Theorem 4.7.4 *)



(* ================================================== defn:total-map *)
(* Definition 4.7.5 *)



(* ================================================== fibwise-fiber-total-fiber-equiv *)
(* Theorem 4.7.6 *)



(* ================================================== thm:total-fiber-equiv *)
(* Theorem 4.7.7 *)



(* ================================================== thm:fiber-of-a-fibration *)
(* Lemma 4.8.1 *)



(* ================================================== thm:total-space-of-the-fibers *)
(* Lemma 4.8.2 *)



(* ================================================== thm:nobject-classifier-appetizer *)
(* Theorem 4.8.3 *)



(* ================================================== thm:object-classifier *)
(* Theorem 4.8.4 *)



(* ================================================== weakfunext *)
(* Definition 4.9.1 *)



(* ================================================== UA-eqv-hom-eqv *)
(* Lemma 4.9.2 *)



(* ================================================== contrfamtotalpostcompequiv *)
(* Corollary 4.9.3 *)



(* ================================================== uatowfe *)
(* Theorem 4.9.4 *)



(* ================================================== wfetofe *)
(* Theorem 4.9.5 *)



(* ================================================== ex:symmetric-equiv *)
(* Exercise 4.2 *)



(* ================================================== ex:qinv-autohtpy-no-univalence *)
(* Exercise 4.3 *)



(* ================================================== ex:unstable-octahedron *)
(* Exercise 4.4 *)



(* ================================================== ex:2-out-of-6 *)
(* Exercise 4.5 *)



(* ================================================== thm:nat-uniq *)
(* Theorem 5.1.1 *)



(* ================================================== thm:w-uniq *)
(* Theorem 5.3.1 *)



(* ================================================== defn:nalg *)
(* Definition 5.4.1 *)



(* ================================================== defn:nhom *)
(* Definition 5.4.2 *)



(* ================================================== thm:nat-hinitial *)
(* Theorem 5.4.5 *)



(* ================================================== thm:w-hinit *)
(* Theorem 5.4.7 *)



(* ================================================== lem:homotopy-induction-times-3 *)
(* Lemma 5.5.4 *)



(* ================================================== defn:identity-systems *)
(* Definition 5.8.1 *)



(* ================================================== thm:identity-systems *)
(* Theorem 5.8.2 *)



(* ================================================== thm:ML-identity-systems *)
(* Theorem 5.8.4 *)



(* ================================================== thm:equiv-induction *)
(* Corollary 5.8.5 *)



(* ================================================== thm:htpy-induction *)
(* Corollary 5.8.6 *)



(* ================================================== ex:same-recurrence-not-defeq *)
(* Exercise 5.2 *)



(* ================================================== ex:one-function-two-recurrences *)
(* Exercise 5.3 *)



(* ================================================== ex:bool *)
(* Exercise 5.4 *)



(* ================================================== ex:loop *)
(* Exercise 5.7 *)



(* ================================================== ex:loop2 *)
(* Exercise 5.8 *)



(* ================================================== thm:S1rec *)
(* Lemma 6.2.5 *)



(* ================================================== thm:S1ump *)
(* Lemma 6.2.9 *)



(* ================================================== thm:interval-funext *)
(* Lemma 6.3.2 *)



(* ================================================== thm:loop-nontrivial *)
(* Lemma 6.4.1 *)



(* ================================================== thm:S1-autohtpy *)
(* Lemma 6.4.2 *)



(* ================================================== thm:ap2 *)
(* Lemma 6.4.4 *)



(* ================================================== thm:transport2 *)
(* Lemma 6.4.5 *)



(* ================================================== thm:apd2 *)
(* Lemma 6.4.6 *)



(* ================================================== thm:suspbool *)
(* Lemma 6.5.1 *)



(* ================================================== lem:susp-loop-adj *)
(* Lemma 6.5.4 *)



(* ================================================== defn:cocone *)
(* Definition 6.8.1 *)



(* ================================================== thm:pushout-ump *)
(* Lemma 6.8.2 *)



(* ================================================== thm:trunc0-ind *)
(* Lemma 6.9.1 *)



(* ================================================== thm:trunc0-lump *)
(* Lemma 6.9.2 *)



(* ================================================== thm:set-pushout *)
(* Lemma 6.9.3 *)



(* ================================================== thm:quotient-surjective *)
(* Lemma 6.10.2 *)



(* ================================================== thm:quotient-ump *)
(* Lemma 6.10.3 *)



(* ================================================== def:VVquotient *)
(* Definition 6.10.5 *)



(* ================================================== lem:quotient-when-canonical-representatives *)
(* Lemma 6.10.8 *)



(* ================================================== thm:retraction-quotient *)
(* Corollary 6.10.10 *)



(* ================================================== thm:sign-induction *)
(* Lemma 6.10.12 *)



(* ================================================== thm:looptothe *)
(* Corollary 6.10.13 *)



(* ================================================== thm:homotopy-groups *)
(* Example 6.11.4 *)



(* ================================================== thm:free-monoid *)
(* Lemma 6.11.5 *)



(* ================================================== thm:transport-is-given *)
(* Lemma 6.12.1 *)



(* ================================================== thm:flattening *)
(* Lemma 6.12.2 *)



(* ================================================== thm:flattening-rect *)
(* Lemma 6.12.4 *)



(* ================================================== thm:flattening-rectnd *)
(* Lemma 6.12.5 *)



(* ================================================== thm:ap-sigma-rect-path-pair *)
(* Lemma 6.12.7 *)



(* ================================================== thm:flattening-rectnd-beta-ppt *)
(* Lemma 6.12.8 *)



(* ================================================== eg:unnatural-hit *)
(* Example 6.13.1 *)



(* ================================================== ex:torus *)
(* Exercise 6.1 *)



(* ================================================== ex:suspS1 *)
(* Exercise 6.2 *)



(* ================================================== ex:torus-s1-times-s1 *)
(* Exercise 6.3 *)



(* ================================================== ex:nspheres *)
(* Exercise 6.4 *)



(* ================================================== ex:free-monoid *)
(* Exercise 6.8 *)



(* ================================================== ex:unnatural-endomorphisms *)
(* Exercise 6.9 *)



(* ================================================== ex:funext-from-interval *)
(* Exercise 6.10 *)



(* ================================================== def:hlevel *)
(* Definition 7.1.1 *)



(* ================================================== thm:h-level-retracts *)
(* Theorem 7.1.4 *)



(* ================================================== cor:preservation-hlevels-weq *)
(* Corollary 7.1.5 *)



(* ================================================== thm:isntype-mono *)
(* Theorem 7.1.6 *)



(* ================================================== thm:hlevel-cumulative *)
(* Theorem 7.1.7 *)



(* ================================================== thm:ntypes-sigma *)
(* Theorem 7.1.8 *)



(* ================================================== thm:hlevel-prod *)
(* Theorem 7.1.9 *)



(* ================================================== thm:isaprop-isofhlevel *)
(* Theorem 7.1.10 *)



(* ================================================== thm:hleveln-of-hlevelSn *)
(* Theorem 7.1.11 *)



(* ================================================== thm:h-set-uip-K *)
(* Theorem 7.2.1 *)



(* ================================================== thm:h-set-refrel-in-paths-sets *)
(* Theorem 7.2.2 *)



(* ================================================== notnotstable-equality-to-set *)
(* Corollary 7.2.3 *)



(* ================================================== thm:hedberg *)
(* Theorem 7.2.5 *)



(* ================================================== prop:nat-is-set *)
(* Theorem 7.2.6 *)



(* ================================================== thm:hlevel-loops *)
(* Theorem 7.2.7 *)



(* ================================================== lem:hlevel-if-inhab-hlevel *)
(* Lemma 7.2.8 *)



(* ================================================== thm:ntype-nloop *)
(* Theorem 7.2.9 *)



(* ================================================== thm:truncn-ind *)
(* Theorem 7.3.2 *)



(* ================================================== thm:trunc-reflective *)
(* Lemma 7.3.3 *)



(* ================================================== thm:trunc-htpy *)
(* Lemma 7.3.5 *)



(* ================================================== cor:trunc-prod *)
(* Theorem 7.3.8 *)



(* ================================================== thm:trunc-in-truncated-sigma *)
(* Theorem 7.3.9 *)



(* ================================================== thm:refl-over-ntype-base *)
(* Corollary 7.3.10 *)



(* ================================================== thm:path-truncation *)
(* Theorem 7.3.12 *)



(* ================================================== lem:truncation-le *)
(* Lemma 7.3.15 *)



(* ================================================== thm:conemap-funct *)
(* Lemma 7.4.10 *)



(* ================================================== reflectcommutespushout *)
(* Theorem 7.4.12 *)



(* ================================================== thm:minusoneconn-surjective *)
(* Lemma 7.5.2 *)



(* ================================================== lem:nconnected_postcomp *)
(* Lemma 7.5.6 *)



(* ================================================== cor:totrunc-is-connected *)
(* Corollary 7.5.8 *)



(* ================================================== thm:nconn-to-ntype-const *)
(* Corollary 7.5.9 *)



(* ================================================== connectedtotruncated *)
(* Corollary 7.5.9 *)



(* ================================================== lem:nconnected_to_leveln_to_equiv *)
(* Lemma 7.5.10 *)



(* ================================================== thm:connected-pointed *)
(* Lemma 7.5.11 *)



(* ================================================== lem:nconnected_postcomp_variation *)
(* Lemma 7.5.12 *)



(* ================================================== prop:nconn_fiber_to_total *)
(* Lemma 7.5.13 *)



(* ================================================== lem:connected-map-equiv-truncation *)
(* Lemma 7.5.14 *)



(* ================================================== thm:modal-mono *)
(* Lemma 7.6.2 *)



(* ================================================== defn:modal-image *)
(* Definition 7.6.3 *)



(* ================================================== prop:to_image_is_connected *)
(* Lemma 7.6.4 *)



(* ================================================== prop:factor_equiv_fiber *)
(* Lemma 7.6.5 *)



(* ================================================== thm:orth-fact *)
(* Theorem 7.6.6 *)



(* ================================================== lem:hfiber_wrt_pullback *)
(* Lemma 7.6.8 *)



(* ================================================== thm:stable-images *)
(* Theorem 7.6.9 *)



(* ================================================== defn:reflective-subuniverse *)
(* Definition 7.7.1 *)



(* ================================================== thm:reflsubunv-forall *)
(* Theorem 7.7.2 *)



(* ================================================== cor:trunc_prod *)
(* Corollary 7.7.3 *)



(* ================================================== thm:modal-char *)
(* Theorem 7.7.4 *)



(* ================================================== defn:modality *)
(* Definition 7.7.5 *)



(* ================================================== prop:lv_n_deptype_sec_equiv_by_precomp *)
(* Theorem 7.7.7 *)



(* ================================================== ex:s2-colim-unit *)
(* Exercise 7.2 *)



(* ================================================== ex:ntypes-closed-under-wtypes *)
(* Exercise 7.3 *)



(* ================================================== ex:ntype-from-nconn-const *)
(* Exercise 7.5 *)



(* ================================================== ex:connectivity-inductively *)
(* Exercise 7.6 *)



(* ================================================== ex:lemnm *)
(* Exercise 7.7 *)



(* ================================================== ex:acnm *)
(* Exercise 7.8 *)



(* ================================================== ex:acnm-surjset *)
(* Exercise 7.9 *)



(* ================================================== ex:acconn *)
(* Exercise 7.10 *)



(* ================================================== def-of-homotopy-groups *)
(* Definition 8.0.1 *)



(* ================================================== S1-universal-cover *)
(* Definition 8.1.1 *)



(* ================================================== lem:transport-s1-code *)
(* Lemma 8.1.2 *)



(* ================================================== thm:pi1s1-decode *)
(* Definition 8.1.6 *)



(* ================================================== lem:s1-decode-encode *)
(* Lemma 8.1.7 *)



(* ================================================== lem:s1-encode-decode *)
(* Lemma 8.1.8 *)



(* ================================================== cor:omega-s1 *)
(* Corollary 8.1.10 *)



(* ================================================== cor:pi1s1 *)
(* Corollary 8.1.11 *)



(* ================================================== thm:encode-total-equiv *)
(* Corollary 8.1.13 *)



(* ================================================== thm:suspension-increases-connectedness *)
(* Theorem 8.2.1 *)



(* ================================================== cor:sn-connected *)
(* Corollary 8.2.2 *)



(* ================================================== lem:pik-nconnected *)
(* Lemma 8.3.2 *)



(* ================================================== def:pointedmap *)
(* Definition 8.4.1 *)



(* ================================================== thm:fiber-of-the-fiber *)
(* Lemma 8.4.4 *)



(* ================================================== thm:les *)
(* Theorem 8.4.6 *)



(* ================================================== thm:ses *)
(* Lemma 8.4.7 *)



(* ================================================== thm:conn-pik *)
(* Corollary 8.4.8 *)



(* ================================================== thm:hopf-fibration *)
(* Theorem 8.5.1 *)



(* ================================================== cor:pis2-hopf *)
(* Corollary 8.5.2 *)



(* ================================================== lem:fibration-over-pushout *)
(* Lemma 8.5.3 *)



(* ================================================== lem:hopf-construction *)
(* Lemma 8.5.7 *)



(* ================================================== lem:hspace-S1 *)
(* Lemma 8.5.8 *)



(* ================================================== thm:conn-trunc-variable-ind *)
(* Lemma 8.6.1 *)



(* ================================================== thm:wedge-connectivity *)
(* Lemma 8.6.2 *)



(* ================================================== thm:freudenthal *)
(* Theorem 8.6.4 *)



(* ================================================== thm:freudcode *)
(* Definition 8.6.5 *)



(* ================================================== thm:freudlemma *)
(* Lemma 8.6.10 *)



(* ================================================== cor:freudenthal-equiv *)
(* Corollary 8.6.14 *)



(* ================================================== cor:stability-spheres *)
(* Corollary 8.6.15 *)



(* ================================================== thm:naive-van-kampen *)
(* Theorem 8.7.4 *)



(* ================================================== eg:circle *)
(* Example 8.7.6 *)



(* ================================================== eg:suspension *)
(* Example 8.7.7 *)



(* ================================================== eg:wedge *)
(* Example 8.7.8 *)



(* ================================================== thm:kbar *)
(* Lemma 8.7.9 *)



(* ================================================== thm:van-Kampen *)
(* Theorem 8.7.12 *)



(* ================================================== eg:clvk *)
(* Example 8.7.13 *)



(* ================================================== eg:cofiber *)
(* Example 8.7.14 *)



(* ================================================== eg:torus *)
(* Example 8.7.15 *)



(* ================================================== eg:kg1 *)
(* Example 8.7.17 *)



(* ================================================== thm:whitehead0 *)
(* Theorem 8.8.1 *)



(* ================================================== thm:whitehead1 *)
(* Corollary 8.8.2 *)



(* ================================================== thm:whiteheadn *)
(* Theorem 8.8.3 *)



(* ================================================== thm:whitehead-contr *)
(* Corollary 8.8.4 *)



(* ================================================== thm:pik-conn *)
(* Corollary 8.8.5 *)



(* ================================================== Blakers-Massey *)
(* Theorem 8.10.2 *)



(* ================================================== Eilenberg-Mac-Lane-Spaces *)
(* Theorem 8.10.3 *)



(* ================================================== thm:covering-spaces *)
(* Theorem 8.10.4 *)



(* ================================================== ex:unique-fiber *)
(* Exercise 8.5 *)



(* ================================================== ex:ap-path-inversion *)
(* Exercise 8.6 *)



(* ================================================== ex:pointed-equivalences *)
(* Exercise 8.7 *)



(* ================================================== ex:HopfJr *)
(* Exercise 8.8 *)



(* ================================================== ex:SuperHopf *)
(* Exercise 8.9 *)



(* ================================================== ex:vksusppt *)
(* Exercise 8.10 *)



(* ================================================== ex:vksuspnopt *)
(* Exercise 8.11 *)



(* ================================================== ct:precategory *)
(* Definition 9.1.1 *)



(* ================================================== ct:isomorphism *)
(* Definition 9.1.2 *)



(* ================================================== ct:isoprop *)
(* Lemma 9.1.3 *)



(* ================================================== ct:precatset *)
(* Example 9.1.5 *)



(* ================================================== ct:category *)
(* Definition 9.1.6 *)



(* ================================================== ct:eg:set *)
(* Example 9.1.7 *)



(* ================================================== ct:obj-1type *)
(* Lemma 9.1.8 *)



(* ================================================== ct:idtoiso-trans *)
(* Lemma 9.1.9 *)



(* ================================================== ct:orders *)
(* Example 9.1.14 *)



(* ================================================== ct:gaunt *)
(* Example 9.1.15 *)



(* ================================================== ct:discrete *)
(* Example 9.1.16 *)



(* ================================================== ct:fundgpd *)
(* Example 9.1.17 *)



(* ================================================== ct:hoprecat *)
(* Example 9.1.18 *)



(* ================================================== ct:rel *)
(* Example 9.1.19 *)



(* ================================================== ct:functor *)
(* Definition 9.2.1 *)



(* ================================================== ct:nattrans *)
(* Definition 9.2.2 *)



(* ================================================== ct:functor-precat *)
(* Definition 9.2.3 *)



(* ================================================== ct:natiso *)
(* Lemma 9.2.4 *)



(* ================================================== ct:functor-cat *)
(* Theorem 9.2.5 *)



(* ================================================== ct:interchange *)
(* Lemma 9.2.8 *)



(* ================================================== ct:functor-assoc *)
(* Lemma 9.2.9 *)



(* ================================================== ct:pentagon *)
(* Lemma 9.2.10 *)



(* ================================================== ct:units *)
(* Lemma 9.2.11 *)



(* ================================================== ct:adjprop *)
(* Lemma 9.3.2 *)



(* ================================================== ct:equiv *)
(* Definition 9.4.1 *)



(* ================================================== ct:adjointification *)
(* Lemma 9.4.2 *)



(* ================================================== ct:ffeso *)
(* Lemma 9.4.5 *)



(* ================================================== ct:catweq *)
(* Lemma 9.4.7 *)



(* ================================================== ct:isocat *)
(* Definition 9.4.8 *)



(* ================================================== ct:isoprecat *)
(* Lemma 9.4.9 *)



(* ================================================== ct:chaotic *)
(* Example 9.4.13 *)



(* ================================================== ct:eqv-levelwise *)
(* Lemma 9.4.14 *)



(* ================================================== ct:cat-eq-iso *)
(* Lemma 9.4.15 *)



(* ================================================== ct:cat-2cat *)
(* Theorem 9.4.16 *)



(* ================================================== ct:opposite-category *)
(* Definition 9.5.1 *)



(* ================================================== ct:functorexpadj *)
(* Lemma 9.5.3 *)



(* ================================================== ct:yoneda *)
(* Theorem 9.5.4 *)



(* ================================================== ct:yoneda-embedding *)
(* Corollary 9.5.6 *)



(* ================================================== ct:yoneda-mono *)
(* Corollary 9.5.7 *)



(* ================================================== ct:representable *)
(* Definition 9.5.8 *)



(* ================================================== ct:representable-prop *)
(* Theorem 9.5.9 *)



(* ================================================== ct:adj-repr *)
(* Lemma 9.5.10 *)



(* ================================================== ct:adjprop2 *)
(* Corollary 9.5.11 *)



(* ================================================== ct:galois *)
(* Example 9.6.3 *)



(* ================================================== ct:unitary *)
(* Definition 9.7.2 *)



(* ================================================== ct:idtounitary *)
(* Lemma 9.7.3 *)



(* ================================================== ct:hilb *)
(* Example 9.7.7 *)



(* ================================================== ct:sig *)
(* Definition 9.8.1 *)



(* ================================================== thm:sip *)
(* Theorem 9.8.2 *)



(* ================================================== ct:sip-functor-cat *)
(* Example 9.8.3 *)



(* ================================================== defn:fo-notion-of-structure *)
(* Definition 9.8.4 *)



(* ================================================== ct:esofull-precomp-ff *)
(* Lemma 9.9.2 *)



(* ================================================== ct:cat-weq-eq *)
(* Theorem 9.9.4 *)



(* ================================================== thm:rezk-completion *)
(* Theorem 9.9.5 *)



(* ================================================== ct:rezk-fundgpd-trunc1 *)
(* Example 9.9.6 *)



(* ================================================== ct:hocat *)
(* Example 9.9.7 *)



(* ================================================== ct:pre2cat *)
(* Exercise 9.4 *)



(* ================================================== ct:2cat *)
(* Exercise 9.5 *)



(* ================================================== ct:groupoids *)
(* Exercise 9.6 *)



(* ================================================== ct:ex:hocat *)
(* Exercise 9.9 *)



(* ================================================== ex:rezk-vankampen *)
(* Exercise 9.11 *)



(* ================================================== ex:stack *)
(* Exercise 9.12 *)



(* ================================================== thm:mono *)
(* Lemma 10.1.1 *)



(* ================================================== epis-surj *)
(* Lemma 10.1.4 *)



(* ================================================== lem:images_are_coequalizers *)
(* Theorem 10.1.5 *)



(* ================================================== thm:set_regular *)
(* Theorem 10.1.5 *)



(* ================================================== lem:pb_of_coeq_is_coeq *)
(* Lemma 10.1.6 *)



(* ================================================== lem:sets_exact *)
(* Lemma 10.1.8 *)



(* ================================================== prop:kernels_are_effective *)
(* Theorem 10.1.9 *)



(* ================================================== thm:settopos *)
(* Theorem 10.1.12 *)



(* ================================================== prop:trunc_of_prop_is_set *)
(* Lemma 10.1.13 *)



(* ================================================== thm:1surj_to_surj_to_pem *)
(* Theorem 10.1.14 *)



(* ================================================== thm:ETCS *)
(* Theorem 10.1.15 *)



(* ================================================== defn:card *)
(* Definition 10.2.1 *)



(* ================================================== card:semiring *)
(* Lemma 10.2.4 *)



(* ================================================== card:exp *)
(* Lemma 10.2.6 *)



(* ================================================== thm:injsurj *)
(* Lemma 10.2.9 *)



(* ================================================== defn:accessibility *)
(* Definition 10.3.1 *)



(* ================================================== thm:nat-wf *)
(* Example 10.3.5 *)



(* ================================================== thm:wtype-wf *)
(* Example 10.3.6 *)



(* ================================================== thm:wfrec *)
(* Lemma 10.3.7 *)



(* ================================================== thm:wfmin *)
(* Lemma 10.3.8 *)



(* ================================================== def:simulation *)
(* Definition 10.3.11 *)



(* ================================================== thm:wfcat *)
(* Corollary 10.3.15 *)



(* ================================================== thm:ordord *)
(* Theorem 10.3.20 *)



(* ================================================== thm:ordsucc *)
(* Lemma 10.3.21 *)



(* ================================================== thm:ordunion *)
(* Lemma 10.3.22 *)



(* ================================================== thm:wellorder *)
(* Theorem 10.4.3 *)



(* ================================================== thm:wop *)
(* Theorem 10.4.4 *)



(* ================================================== defn:V *)
(* Definition 10.5.1 *)



(* ================================================== def:bisimulation *)
(* Definition 10.5.4 *)



(* ================================================== lem:BisimEqualsId *)
(* Lemma 10.5.5 *)



(* ================================================== lem:MonicSetPresent *)
(* Lemma 10.5.6 *)



(* ================================================== def:TypeOfElements *)
(* Definition 10.5.7 *)



(* ================================================== thm:VisCST *)
(* Theorem 10.5.8 *)



(* ================================================== cor:Delta0sep *)
(* Corollary 10.5.9 *)



(* ================================================== lem:fullsep *)
(* Lemma 10.5.10 *)



(* ================================================== thm:zfc *)
(* Theorem 10.5.11 *)



(* ================================================== ex:well-pointed *)
(* Exercise 10.3 *)



(* ================================================== ex:prop-ord *)
(* Exercise 10.7 *)



(* ================================================== ex:ninf-ord *)
(* Exercise 10.8 *)



(* ================================================== ex:choice-function *)
(* Exercise 10.10 *)



(* ================================================== ex:cumhierhit *)
(* Exercise 10.11 *)



(* ================================================== defn:dedekind-reals *)
(* Definition 11.2.1 *)



(* ================================================== dedekind-in-cut-as-le *)
(* Lemma 11.2.2 *)



(* ================================================== RD-inverse-apart-0 *)
(* Theorem 11.2.4 *)



(* ================================================== RD-archimedean *)
(* Theorem 11.2.6 *)



(* ================================================== ordered-field *)
(* Definition 11.2.7 *)



(* ================================================== RD-archimedean-ordered-field *)
(* Theorem 11.2.8 *)



(* ================================================== defn:cauchy-approximation *)
(* Definition 11.2.10 *)



(* ================================================== RD-cauchy-complete *)
(* Theorem 11.2.12 *)



(* ================================================== RD-final-field *)
(* Theorem 11.2.14 *)



(* ================================================== lem:cuts-preserve-admissibility *)
(* Lemma 11.2.15 *)



(* ================================================== RD-dedekind-complete *)
(* Corollary 11.2.16 *)



(* ================================================== defn:cauchy-reals *)
(* Definition 11.3.2 *)



(* ================================================== thm:Cauchy-reals-are-a-set *)
(* Theorem 11.3.9 *)



(* ================================================== RC-lim-onto *)
(* Lemma 11.3.10 *)



(* ================================================== RC-lim-factor *)
(* Lemma 11.3.11 *)



(* ================================================== thm:RCsim-symmetric *)
(* Lemma 11.3.12 *)



(* ================================================== defn:lipschitz *)
(* Definition 11.3.14 *)



(* ================================================== RC-extend-Q-Lipschitz *)
(* Lemma 11.3.15 *)



(* ================================================== defn:RC-approx *)
(* Theorem 11.3.16 *)



(* ================================================== thm:RC-sim-characterization *)
(* Theorem 11.3.32 *)



(* ================================================== thm:RC-sim-lim *)
(* Lemma 11.3.36 *)



(* ================================================== thm:RC-sim-lim-term *)
(* Lemma 11.3.37 *)



(* ================================================== RC-continuous-eq *)
(* Lemma 11.3.39 *)



(* ================================================== RC-binary-nonexpanding-extension *)
(* Lemma 11.3.40 *)



(* ================================================== RC-archimedean *)
(* Theorem 11.3.41 *)



(* ================================================== thm:RC-le-grow *)
(* Lemma 11.3.42 *)



(* ================================================== thm:RC-lt-open *)
(* Lemma 11.3.43 *)



(* ================================================== RC-sim-eqv-le *)
(* Theorem 11.3.44 *)



(* ================================================== RC-squaring *)
(* Theorem 11.3.46 *)



(* ================================================== RC-archimedean-ordered-field *)
(* Theorem 11.3.48 *)



(* ================================================== RC-initial-Cauchy-complete *)
(* Theorem 11.3.50 *)



(* ================================================== lem:untruncated-linearity-reals-coincide *)
(* Lemma 11.4.1 *)



(* ================================================== when-reals-coincide *)
(* Corollary 11.4.3 *)



(* ================================================== defn:metric-space *)
(* Definition 11.5.1 *)



(* ================================================== defn:complete-metric-space *)
(* Definition 11.5.2 *)



(* ================================================== defn:total-bounded-metric-space *)
(* Definition 11.5.3 *)



(* ================================================== defn:uniformly-continuous *)
(* Definition 11.5.5 *)



(* ================================================== analysis-interval-ctb *)
(* Theorem 11.5.6 *)



(* ================================================== ctb-uniformly-continuous-sup *)
(* Theorem 11.5.7 *)



(* ================================================== analysis-bw-lpo *)
(* Theorem 11.5.9 *)



(* ================================================== classical-Heine-Borel *)
(* Theorem 11.5.11 *)



(* ================================================== defn:inductive-cover *)
(* Definition 11.5.13 *)



(* ================================================== reals-formal-topology-locally-compact *)
(* Lemma 11.5.14 *)



(* ================================================== interval-Heine-Borel *)
(* Corollary 11.5.15 *)



(* ================================================== inductive-cover-classical *)
(* Theorem 11.5.16 *)



(* ================================================== defn:surreals *)
(* Definition 11.6.1 *)



(* ================================================== thm:NO-simplicity *)
(* Theorem 11.6.2 *)



(* ================================================== thm:NO-refl-opt *)
(* Theorem 11.6.4 *)



(* ================================================== thm:NO-set *)
(* Corollary 11.6.5 *)



(* ================================================== defn:No-codes *)
(* Theorem 11.6.7 *)



(* ================================================== thm:NO-encode-decode *)
(* Theorem 11.6.16 *)



(* ================================================== thm:NO-unstrict-transitive *)
(* Corollary 11.6.17 *)



(* ================================================== ex:RD-extended-reals *)
(* Exercise 11.2 *)



(* ================================================== ex:RD-lower-cuts *)
(* Exercise 11.3 *)



(* ================================================== ex:RD-interval-arithmetic *)
(* Exercise 11.4 *)



(* ================================================== ex:RD-lt-vs-le *)
(* Exercise 11.5 *)



(* ================================================== ex:reals-non-constant-into-Z *)
(* Exercise 11.6 *)



(* ================================================== ex:traditional-archimedean *)
(* Exercise 11.7 *)



(* ================================================== RC-Lipschitz-on-interval *)
(* Exercise 11.8 *)



(* ================================================== ex:metric-completion *)
(* Exercise 11.9 *)



(* ================================================== ex:reals-apart-neq-MP *)
(* Exercise 11.10 *)



(* ================================================== ex:reals-apart-zero-divisors *)
(* Exercise 11.11 *)



(* ================================================== ex:finite-cover-lebesgue-number *)
(* Exercise 11.12 *)



(* ================================================== ex:mean-value-theorem *)
(* Exercise 11.13 *)



