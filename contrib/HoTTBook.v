(** The HoTT Book formalization. *)

(** This file links the results of the HoTT Book with their formalizations
    in the HoTT library. You can lookup definitions and theorems by their
    number in the HoTT Book.

    IMPORTANT NOTE FOR THE HoTT DEVELOPERS:

    This files is processed automagically by the etc/Book.py script. The
    script parses the file according to the markers present in it (the
    comment lines with many = signs followed by a LaTeX label). It
    reorders the entries according to page numbers and it inserts
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
(* Exercise 1.1, page 55 *)

Definition Book_1_1 := @compose.

(* ================================================== ex:pr-to-rec *)
(* Exercise 1.2, page 55 *)



(* ================================================== ex:pr-to-ind *)
(* Exercise 1.3, page 55 *)



(* ================================================== ex:iterator *)
(* Exercise 1.4, page 55 *)

(* ================================================== ex:ackermann *)
(* Exercise 1.10, page 56 *)

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
(* Exercise 1.11, page 56 *)



(* ================================================== ex:tautologies *)
(* Exercise 1.12, page 56 *)



(* ================================================== ex:not-not-lem *)
(* Exercise 1.13, page 56 *)



(* ================================================== ex:without-K *)
(* Exercise 1.14, page 56 *)



(* ================================================== ex:subtFromPathInd *)
(* Exercise 1.15, page 56 *)



(* ================================================== ex:sum-via-bool *)
(* Exercise 1.5, page 56 *)



(* ================================================== ex:prod-via-bool *)
(* Exercise 1.6, page 56 *)



(* ================================================== ex:pm-to-ml *)
(* Exercise 1.7, page 56 *)



(* ================================================== ex:fin *)
(* Exercise 1.9, page 56 *)



(* ================================================== lem:opp *)
(* Lemma 2.1.1, page 60 *)

Definition Book_2_1_1 := @HoTT.Overture.inverse.

(* ================================================== lem:concat *)
(* Lemma 2.1.2, page 61 *)

Definition Book_2_1_2 := @HoTT.Overture.concat.

(* ================================================== thm:omg *)
(* Lemma 2.1.4, page 63 *)

Definition Book_2_1_4_item_i := @HoTT.PathGroupoids.concat_p1.
Definition Book_2_1_4_item_i' := @HoTT.PathGroupoids.concat_1p.
Definition Book_2_1_4_item_ii := @HoTT.PathGroupoids.concat_Vp.
Definition Book_2_1_4_item_ii' := @HoTT.PathGroupoids.concat_pV.
Definition Book_2_1_4_item_iii := @HoTT.PathGroupoids.inv_V.
Definition Book_2_1_4_item_iv := @HoTT.PathGroupoids.concat_p_pp.

(* ================================================== thm:EckmannHilton *)
(* Theorem 2.1.6, page 66 *)

Definition Book_2_1_6 := @HoTT.PathGroupoids.eckmann_hilton.

(* ================================================== def:pointedtype *)
(* Definition 2.1.7, page 68 *)

Definition Book_2_1_7 := @HoTT.Overture.pointedType.

(* ================================================== def:loopspace *)
(* Definition 2.1.8, page 68 *)



(* ================================================== lem:map *)
(* Lemma 2.2.1, page 68 *)

Definition Book_2_2_1 := @HoTT.Overture.ap.

(* ================================================== lem:ap-functor *)
(* Lemma 2.2.2, page 69 *)

Definition Book_2_2_2_item_i   := @HoTT.PathGroupoids.ap_pp.
Definition Book_2_2_2_item_ii  := @HoTT.PathGroupoids.inverse_ap.
Definition Book_2_2_2_item_iii := @HoTT.PathGroupoids.ap_compose.
Definition Book_2_2_2_item_iv  := @HoTT.PathGroupoids.ap_idmap.

(* ================================================== lem:transport *)
(* Lemma 2.3.1, page 69 *)

Definition Book_2_3_1 := @HoTT.Overture.transport.

(* ================================================== thm:path-lifting *)
(* Lemma 2.3.2, page 70 *)

(* special case of *)
Definition Book_2_3_2 := @HoTT.types.Sigma.equiv_path_sigma.


(* ================================================== lem:mapdep *)
(* Lemma 2.3.4, page 71 *)

Definition Book_2_3_4 := @HoTT.Overture.apD.

(* ================================================== thm:trans-trivial *)
(* Lemma 2.3.5, page 72 *)

Definition Book_2_3_5 := @HoTT.PathGroupoids.transport_const.

(* ================================================== thm:apd-const *)
(* Lemma 2.3.8, page 72 *)

Definition Book_2_3_8 := @HoTT.PathGroupoids.apD_const.

(* ================================================== thm:transport-compose *)
(* Lemma 2.3.10, page 73 *)

Definition Book_2_3_10 := @HoTT.PathGroupoids.transport_compose.

(* ================================================== thm:ap-transport *)
(* Lemma 2.3.11, page 73 *)

Definition Book_2_3_11 := @HoTT.PathGroupoids.ap_transport.

(* ================================================== thm:transport-concat *)
(* Lemma 2.3.9, page 73 *)

Definition Book_2_3_9 := @HoTT.PathGroupoids.transport_pp.

(* ================================================== defn:homotopy *)
(* Definition 2.4.1, page 74 *)



(* ================================================== lem:homotopy-props *)
(* Lemma 2.4.2, page 74 *)



(* ================================================== lem:htpy-natural *)
(* Lemma 2.4.3, page 74 *)



(* ================================================== cor:hom-fg *)
(* Corollary 2.4.4, page 74 *)



(* ================================================== eg:idequiv *)
(* Example 2.4.7, page 75 *)



(* ================================================== eg:concatequiv *)
(* Example 2.4.8, page 75 *)



(* ================================================== thm:transportequiv *)
(* Example 2.4.9, page 75 *)



(* ================================================== thm:equiv-eqrel *)
(* Lemma 2.4.12, page 76 *)



(* ================================================== thm:path-prod *)
(* Theorem 2.6.2, page 78 *)



(* ================================================== thm:trans-prod *)
(* Theorem 2.6.4, page 80 *)



(* ================================================== thm:ap-prod *)
(* Theorem 2.6.5, page 80 *)



(* ================================================== thm:path-sigma *)
(* Theorem 2.7.2, page 81 *)

Definition Book_2_7_2 := @HoTT.types.Sigma.equiv_path_sigma.

(* ================================================== thm:eta-sigma *)
(* Corollary 2.7.3, page 82 *)



(* ================================================== transport-Sigma *)
(* Theorem 2.7.4, page 82 *)



(* ================================================== thm:path-unit *)
(* Theorem 2.8.1, page 83 *)



(* ================================================== thm:dpath-arrow *)
(* Lemma 2.9.6, page 85 *)



(* ================================================== thm:dpath-forall *)
(* Lemma 2.9.7, page 85 *)



(* ================================================== thm:transport-is-ap *)
(* Lemma 2.10.5, page 87 *)



(* ================================================== thm:paths-respects-equiv *)
(* Theorem 2.11.1, page 87 *)



(* ================================================== cor:transport-path-prepost *)
(* Lemma 2.11.2, page 88 *)



(* ================================================== thm:transport-path *)
(* Theorem 2.11.3, page 88 *)



(* ================================================== thm:transport-path2 *)
(* Theorem 2.11.4, page 89 *)



(* ================================================== thm:dpath-path *)
(* Theorem 2.11.5, page 89 *)



(* ================================================== thm:path-coprod *)
(* Theorem 2.12.5, page 90 *)



(* ================================================== thm:path-nat *)
(* Theorem 2.13.1, page 92 *)



(* ================================================== thm:prod-ump *)
(* Theorem 2.15.2, page 97 *)



(* ================================================== thm:prod-umpd *)
(* Theorem 2.15.5, page 97 *)



(* ================================================== thm:ttac *)
(* Theorem 2.15.7, page 97 *)



(* ================================================== ex:basics:concat *)
(* Exercise 2.1, page 100 *)



(* ================================================== ex:npaths *)
(* Exercise 2.4, page 100 *)



(* ================================================== ex:equiv-concat *)
(* Exercise 2.6, page 100 *)



(* ================================================== ex:sigma-assoc *)
(* Exercise 2.10, page 101 *)



(* ================================================== ex:pullback *)
(* Exercise 2.11, page 101 *)



(* ================================================== ex:pullback-pasting *)
(* Exercise 2.12, page 101 *)



(* ================================================== ex:eqvboolbool *)
(* Exercise 2.13, page 101 *)



(* ================================================== ex:equality-reflection *)
(* Exercise 2.14, page 101 *)



(* ================================================== ex:ap-sigma *)
(* Exercise 2.7, page 101 *)



(* ================================================== ex:coprod-ump *)
(* Exercise 2.9, page 101 *)



(* ================================================== defn:set *)
(* Definition 3.1.1, page 103 *)



(* ================================================== thm:nat-set *)
(* Example 3.1.4, page 104 *)



(* ================================================== thm:isset-prod *)
(* Example 3.1.5, page 104 *)



(* ================================================== thm:isset-forall *)
(* Example 3.1.6, page 104 *)



(* ================================================== defn:1type *)
(* Definition 3.1.7, page 104 *)



(* ================================================== thm:isset-is1type *)
(* Lemma 3.1.8, page 105 *)



(* ================================================== thm:type-is-not-a-set *)
(* Example 3.1.9, page 105 *)



(* ================================================== thm:not-dneg *)
(* Theorem 3.2.2, page 106 *)



(* ================================================== thm:not-lem *)
(* Corollary 3.2.7, page 107 *)



(* ================================================== defn:isprop *)
(* Definition 3.3.1, page 107 *)



(* ================================================== thm:inhabprop-eqvunit *)
(* Lemma 3.3.2, page 108 *)



(* ================================================== lem:equiv-iff-hprop *)
(* Lemma 3.3.3, page 108 *)



(* ================================================== thm:prop-set *)
(* Lemma 3.3.4, page 108 *)



(* ================================================== thm:isprop-isset *)
(* Lemma 3.3.5, page 108 *)



(* ================================================== thm:isprop-isprop *)
(* Lemma 3.3.5, page 108 *)



(* ================================================== defn:decidable-equality *)
(* Definition 3.4.3, page 110 *)



(* ================================================== defn:setof *)
(* Lemma 3.5, page 111 *)



(* ================================================== thm:path-subset *)
(* Lemma 3.5.1, page 111 *)



(* ================================================== thm:isprop-forall *)
(* Example 3.6.2, page 112 *)



(* ================================================== defn:logical-notation *)
(* Definition 3.7.1, page 114 *)



(* ================================================== thm:ac-epis-split *)
(* Lemma 3.8.2, page 115 *)



(* ================================================== thm:no-higher-ac *)
(* Lemma 3.8.5, page 116 *)



(* ================================================== cor:UC *)
(* Corollary 3.9.2, page 117 *)



(* ================================================== defn:contractible *)
(* Definition 3.11.1, page 120 *)



(* ================================================== thm:contr-unit *)
(* Lemma 3.11.3, page 120 *)



(* ================================================== thm:isprop-iscontr *)
(* Lemma 3.11.4, page 120 *)



(* ================================================== thm:contr-contr *)
(* Corollary 3.11.5, page 120 *)



(* ================================================== thm:contr-forall *)
(* Lemma 3.11.6, page 121 *)



(* ================================================== thm:retract-contr *)
(* Lemma 3.11.7, page 121 *)



(* ================================================== thm:contr-paths *)
(* Lemma 3.11.8, page 121 *)



(* ================================================== thm:omit-contr *)
(* Lemma 3.11.9, page 121 *)



(* ================================================== thm:prop-minusonetype *)
(* Lemma 3.11.10, page 122 *)



(* ================================================== ex:lem-impred *)
(* Exercise 3.10, page 123 *)



(* ================================================== ex:lem-brck *)
(* Exercise 3.14, page 123 *)



(* ================================================== ex:isset-coprod *)
(* Exercise 3.2, page 123 *)



(* ================================================== ex:isset-sigma *)
(* Exercise 3.3, page 123 *)



(* ================================================== ex:prop-endocontr *)
(* Exercise 3.4, page 123 *)



(* ================================================== ex:prop-inhabcontr *)
(* Exercise 3.5, page 123 *)



(* ================================================== ex:lem-mereprop *)
(* Exercise 3.6, page 123 *)



(* ================================================== ex:disjoint-or *)
(* Exercise 3.7, page 123 *)



(* ================================================== ex:brck-qinv *)
(* Exercise 3.8, page 123 *)



(* ================================================== ex:impred-brck *)
(* Exercise 3.15, page 124 *)



(* ================================================== ex:prop-trunc-ind *)
(* Exercise 3.17, page 124 *)



(* ================================================== ex:lem-ldn *)
(* Exercise 3.18, page 124 *)



(* ================================================== ex:decidable-choice *)
(* Exercise 3.19, page 124 *)



(* ================================================== ex:omit-contr2 *)
(* Exercise 3.20, page 124 *)



(* ================================================== lem:qinv-autohtpy *)
(* Lemma 4.1.1, page 126 *)



(* ================================================== lem:autohtpy *)
(* Lemma 4.1.2, page 126 *)



(* ================================================== defn:ishae *)
(* Definition 4.2.1, page 128 *)



(* ================================================== lem:coh-equiv *)
(* Lemma 4.2.2, page 128 *)



(* ================================================== thm:equiv-iso-adj *)
(* Theorem 4.2.3, page 129 *)



(* ================================================== defn:homotopy-fiber *)
(* Definition 4.2.4, page 130 *)



(* ================================================== lem:hfib *)
(* Lemma 4.2.5, page 130 *)



(* ================================================== thm:contr-hae *)
(* Theorem 4.2.6, page 130 *)



(* ================================================== defn:lcoh-rcoh *)
(* Definition 4.2.10, page 131 *)



(* ================================================== lem:coh-hfib *)
(* Lemma 4.2.11, page 131 *)



(* ================================================== defn:linv-rinv *)
(* Definition 4.2.7, page 131 *)



(* ================================================== thm:equiv-compose-equiv *)
(* Lemma 4.2.8, page 131 *)



(* ================================================== lem:inv-hprop *)
(* Lemma 4.2.9, page 131 *)



(* ================================================== lem:coh-hprop *)
(* Lemma 4.2.12, page 132 *)



(* ================================================== thm:hae-hprop *)
(* Theorem 4.2.13, page 132 *)



(* ================================================== defn:biinv *)
(* Definition 4.3.1, page 132 *)



(* ================================================== thm:isprop-biinv *)
(* Theorem 4.3.2, page 132 *)



(* ================================================== thm:equiv-biinv-isequiv *)
(* Corollary 4.3.3, page 132 *)



(* ================================================== defn:equivalence *)
(* Definition 4.4.1, page 133 *)



(* ================================================== thm:lequiv-contr-hae *)
(* Theorem 4.4.3, page 133 *)



(* ================================================== thm:contr-hprop *)
(* Lemma 4.4.4, page 133 *)



(* ================================================== thm:equiv-contr-hae *)
(* Theorem 4.4.5, page 133 *)



(* ================================================== thm:equiv-inhabcod *)
(* Corollary 4.4.6, page 134 *)



(* ================================================== thm:mono-surj-equiv *)
(* Theorem 4.6.3, page 135 *)



(* ================================================== thm:two-out-of-three *)
(* Theorem 4.7.1, page 135 *)



(* ================================================== defn:retract *)
(* Definition 4.7.2, page 136 *)



(* ================================================== lem:func_retract_to_fiber_retract *)
(* Lemma 4.7.3, page 136 *)



(* ================================================== thm:retract-equiv *)
(* Theorem 4.7.4, page 137 *)



(* ================================================== defn:total-map *)
(* Definition 4.7.5, page 137 *)



(* ================================================== fibwise-fiber-total-fiber-equiv *)
(* Theorem 4.7.6, page 137 *)



(* ================================================== thm:total-fiber-equiv *)
(* Theorem 4.7.7, page 138 *)



(* ================================================== thm:fiber-of-a-fibration *)
(* Lemma 4.8.1, page 138 *)



(* ================================================== thm:total-space-of-the-fibers *)
(* Lemma 4.8.2, page 139 *)



(* ================================================== thm:nobject-classifier-appetizer *)
(* Theorem 4.8.3, page 139 *)



(* ================================================== thm:object-classifier *)
(* Theorem 4.8.4, page 140 *)



(* ================================================== weakfunext *)
(* Definition 4.9.1, page 141 *)



(* ================================================== UA-eqv-hom-eqv *)
(* Lemma 4.9.2, page 141 *)



(* ================================================== contrfamtotalpostcompequiv *)
(* Corollary 4.9.3, page 141 *)



(* ================================================== uatowfe *)
(* Theorem 4.9.4, page 141 *)



(* ================================================== wfetofe *)
(* Theorem 4.9.5, page 142 *)



(* ================================================== ex:symmetric-equiv *)
(* Exercise 4.2, page 143 *)



(* ================================================== ex:qinv-autohtpy-no-univalence *)
(* Exercise 4.3, page 143 *)



(* ================================================== ex:unstable-octahedron *)
(* Exercise 4.4, page 143 *)



(* ================================================== ex:2-out-of-6 *)
(* Exercise 4.5, page 143 *)



(* ================================================== thm:nat-uniq *)
(* Theorem 5.1.1, page 147 *)



(* ================================================== thm:w-uniq *)
(* Theorem 5.3.1, page 153 *)



(* ================================================== defn:nalg *)
(* Definition 5.4.1, page 153 *)



(* ================================================== defn:nhom *)
(* Definition 5.4.2, page 154 *)



(* ================================================== thm:nat-hinitial *)
(* Theorem 5.4.5, page 154 *)



(* ================================================== thm:w-hinit *)
(* Theorem 5.4.7, page 156 *)



(* ================================================== lem:homotopy-induction-times-3 *)
(* Lemma 5.5.4, page 159 *)



(* ================================================== defn:identity-systems *)
(* Definition 5.8.1, page 168 *)



(* ================================================== thm:identity-systems *)
(* Theorem 5.8.2, page 168 *)



(* ================================================== thm:ML-identity-systems *)
(* Theorem 5.8.4, page 169 *)



(* ================================================== thm:equiv-induction *)
(* Corollary 5.8.5, page 170 *)



(* ================================================== thm:htpy-induction *)
(* Corollary 5.8.6, page 170 *)



(* ================================================== ex:same-recurrence-not-defeq *)
(* Exercise 5.2, page 171 *)



(* ================================================== ex:one-function-two-recurrences *)
(* Exercise 5.3, page 171 *)



(* ================================================== ex:bool *)
(* Exercise 5.4, page 171 *)



(* ================================================== ex:loop *)
(* Exercise 5.7, page 171 *)



(* ================================================== ex:loop2 *)
(* Exercise 5.8, page 171 *)



(* ================================================== thm:S1rec *)
(* Lemma 6.2.5, page 177 *)



(* ================================================== thm:S1ump *)
(* Lemma 6.2.9, page 179 *)



(* ================================================== thm:interval-funext *)
(* Lemma 6.3.2, page 180 *)



(* ================================================== thm:loop-nontrivial *)
(* Lemma 6.4.1, page 181 *)



(* ================================================== thm:S1-autohtpy *)
(* Lemma 6.4.2, page 181 *)



(* ================================================== thm:ap2 *)
(* Lemma 6.4.4, page 182 *)



(* ================================================== thm:transport2 *)
(* Lemma 6.4.5, page 182 *)



(* ================================================== thm:apd2 *)
(* Lemma 6.4.6, page 182 *)



(* ================================================== thm:suspbool *)
(* Lemma 6.5.1, page 184 *)



(* ================================================== lem:susp-loop-adj *)
(* Lemma 6.5.4, page 185 *)



(* ================================================== defn:cocone *)
(* Definition 6.8.1, page 191 *)



(* ================================================== thm:pushout-ump *)
(* Lemma 6.8.2, page 191 *)



(* ================================================== thm:trunc0-ind *)
(* Lemma 6.9.1, page 194 *)



(* ================================================== thm:trunc0-lump *)
(* Lemma 6.9.2, page 194 *)



(* ================================================== thm:set-pushout *)
(* Lemma 6.9.3, page 195 *)



(* ================================================== thm:quotient-surjective *)
(* Lemma 6.10.2, page 196 *)



(* ================================================== thm:quotient-ump *)
(* Lemma 6.10.3, page 196 *)



(* ================================================== def:VVquotient *)
(* Definition 6.10.5, page 197 *)



(* ================================================== lem:quotient-when-canonical-representatives *)
(* Lemma 6.10.8, page 197 *)



(* ================================================== thm:retraction-quotient *)
(* Corollary 6.10.10, page 198 *)



(* ================================================== thm:sign-induction *)
(* Lemma 6.10.12, page 199 *)



(* ================================================== thm:looptothe *)
(* Corollary 6.10.13, page 199 *)



(* ================================================== thm:homotopy-groups *)
(* Example 6.11.4, page 200 *)



(* ================================================== thm:free-monoid *)
(* Lemma 6.11.5, page 201 *)



(* ================================================== thm:transport-is-given *)
(* Lemma 6.12.1, page 205 *)



(* ================================================== thm:flattening *)
(* Lemma 6.12.2, page 206 *)



(* ================================================== thm:flattening-rect *)
(* Lemma 6.12.4, page 206 *)



(* ================================================== thm:flattening-rectnd *)
(* Lemma 6.12.5, page 207 *)



(* ================================================== thm:ap-sigma-rect-path-pair *)
(* Lemma 6.12.7, page 208 *)



(* ================================================== thm:flattening-rectnd-beta-ppt *)
(* Lemma 6.12.8, page 208 *)



(* ================================================== eg:unnatural-hit *)
(* Example 6.13.1, page 210 *)



(* ================================================== ex:torus *)
(* Exercise 6.1, page 212 *)



(* ================================================== ex:suspS1 *)
(* Exercise 6.2, page 212 *)



(* ================================================== ex:torus-s1-times-s1 *)
(* Exercise 6.3, page 212 *)



(* ================================================== ex:nspheres *)
(* Exercise 6.4, page 212 *)



(* ================================================== ex:free-monoid *)
(* Exercise 6.8, page 213 *)



(* ================================================== ex:unnatural-endomorphisms *)
(* Exercise 6.9, page 213 *)



(* ================================================== def:hlevel *)
(* Definition 7.1.1, page 215 *)



(* ================================================== thm:h-level-retracts *)
(* Theorem 7.1.4, page 216 *)



(* ================================================== cor:preservation-hlevels-weq *)
(* Corollary 7.1.5, page 216 *)



(* ================================================== thm:isntype-mono *)
(* Theorem 7.1.6, page 216 *)



(* ================================================== thm:hlevel-cumulative *)
(* Theorem 7.1.7, page 217 *)



(* ================================================== thm:ntypes-sigma *)
(* Theorem 7.1.8, page 217 *)



(* ================================================== thm:hlevel-prod *)
(* Theorem 7.1.9, page 217 *)



(* ================================================== thm:isaprop-isofhlevel *)
(* Theorem 7.1.10, page 218 *)



(* ================================================== thm:hleveln-of-hlevelSn *)
(* Theorem 7.1.11, page 218 *)



(* ================================================== thm:h-set-uip-K *)
(* Theorem 7.2.1, page 219 *)



(* ================================================== thm:h-set-refrel-in-paths-sets *)
(* Theorem 7.2.2, page 219 *)



(* ================================================== notnotstable-equality-to-set *)
(* Corollary 7.2.3, page 220 *)



(* ================================================== thm:hedberg *)
(* Theorem 7.2.5, page 220 *)



(* ================================================== prop:nat-is-set *)
(* Theorem 7.2.6, page 221 *)



(* ================================================== thm:hlevel-loops *)
(* Theorem 7.2.7, page 221 *)



(* ================================================== lem:hlevel-if-inhab-hlevel *)
(* Lemma 7.2.8, page 221 *)



(* ================================================== thm:ntype-nloop *)
(* Theorem 7.2.9, page 222 *)



(* ================================================== thm:truncn-ind *)
(* Theorem 7.3.2, page 223 *)



(* ================================================== thm:trunc-reflective *)
(* Lemma 7.3.3, page 224 *)



(* ================================================== thm:trunc-htpy *)
(* Lemma 7.3.5, page 224 *)



(* ================================================== cor:trunc-prod *)
(* Theorem 7.3.8, page 225 *)



(* ================================================== thm:trunc-in-truncated-sigma *)
(* Theorem 7.3.9, page 225 *)



(* ================================================== thm:refl-over-ntype-base *)
(* Corollary 7.3.10, page 226 *)



(* ================================================== thm:path-truncation *)
(* Theorem 7.3.12, page 226 *)



(* ================================================== lem:truncation-le *)
(* Lemma 7.3.15, page 227 *)



(* ================================================== thm:conemap-funct *)
(* Lemma 7.4.10, page 230 *)



(* ================================================== reflectcommutespushout *)
(* Theorem 7.4.12, page 230 *)



(* ================================================== thm:minusoneconn-surjective *)
(* Lemma 7.5.2, page 232 *)



(* ================================================== lem:nconnected_postcomp *)
(* Lemma 7.5.6, page 232 *)



(* ================================================== lem:nconnected_to_leveln_to_equiv *)
(* Lemma 7.5.10, page 234 *)



(* ================================================== thm:connected-pointed *)
(* Lemma 7.5.11, page 234 *)



(* ================================================== cor:totrunc-is-connected *)
(* Corollary 7.5.8, page 234 *)



(* ================================================== thm:nconn-to-ntype-const *)
(* Corollary 7.5.9, page 234 *)



(* ================================================== connectedtotruncated *)
(* Corollary 7.5.9, page 234 *)



(* ================================================== lem:nconnected_postcomp_variation *)
(* Lemma 7.5.12, page 235 *)



(* ================================================== prop:nconn_fiber_to_total *)
(* Lemma 7.5.13, page 235 *)



(* ================================================== lem:connected-map-equiv-truncation *)
(* Lemma 7.5.14, page 235 *)



(* ================================================== thm:modal-mono *)
(* Lemma 7.6.2, page 237 *)



(* ================================================== defn:modal-image *)
(* Definition 7.6.3, page 237 *)



(* ================================================== prop:to_image_is_connected *)
(* Lemma 7.6.4, page 237 *)



(* ================================================== prop:factor_equiv_fiber *)
(* Lemma 7.6.5, page 237 *)



(* ================================================== thm:orth-fact *)
(* Theorem 7.6.6, page 239 *)



(* ================================================== lem:hfiber_wrt_pullback *)
(* Lemma 7.6.8, page 240 *)



(* ================================================== thm:stable-images *)
(* Theorem 7.6.9, page 240 *)



(* ================================================== defn:reflective-subuniverse *)
(* Definition 7.7.1, page 241 *)



(* ================================================== thm:reflsubunv-forall *)
(* Theorem 7.7.2, page 242 *)



(* ================================================== cor:trunc_prod *)
(* Corollary 7.7.3, page 242 *)



(* ================================================== thm:modal-char *)
(* Theorem 7.7.4, page 242 *)



(* ================================================== defn:modality *)
(* Definition 7.7.5, page 243 *)



(* ================================================== prop:lv_n_deptype_sec_equiv_by_precomp *)
(* Theorem 7.7.7, page 244 *)



(* ================================================== ex:s2-colim-unit *)
(* Exercise 7.2, page 246 *)



(* ================================================== ex:ntypes-closed-under-wtypes *)
(* Exercise 7.3, page 246 *)



(* ================================================== ex:ntype-from-nconn-const *)
(* Exercise 7.5, page 246 *)



(* ================================================== ex:connectivity-inductively *)
(* Exercise 7.6, page 246 *)



(* ================================================== ex:lemnm *)
(* Exercise 7.7, page 246 *)



(* ================================================== ex:acconn *)
(* Exercise 7.10, page 247 *)



(* ================================================== ex:acnm *)
(* Exercise 7.8, page 247 *)



(* ================================================== ex:acnm-surjset *)
(* Exercise 7.9, page 247 *)



(* ================================================== def-of-homotopy-groups *)
(* Definition 8.0.1, page 254 *)



(* ================================================== S1-universal-cover *)
(* Definition 8.1.1, page 256 *)



(* ================================================== lem:transport-s1-code *)
(* Lemma 8.1.2, page 257 *)



(* ================================================== thm:pi1s1-decode *)
(* Definition 8.1.6, page 259 *)



(* ================================================== lem:s1-decode-encode *)
(* Lemma 8.1.7, page 259 *)



(* ================================================== lem:s1-encode-decode *)
(* Lemma 8.1.8, page 259 *)



(* ================================================== cor:omega-s1 *)
(* Corollary 8.1.10, page 260 *)



(* ================================================== cor:pi1s1 *)
(* Corollary 8.1.11, page 260 *)



(* ================================================== thm:encode-total-equiv *)
(* Corollary 8.1.13, page 261 *)



(* ================================================== thm:suspension-increases-connectedness *)
(* Theorem 8.2.1, page 263 *)



(* ================================================== cor:sn-connected *)
(* Corollary 8.2.2, page 264 *)



(* ================================================== lem:pik-nconnected *)
(* Lemma 8.3.2, page 264 *)



(* ================================================== def:pointedmap *)
(* Definition 8.4.1, page 265 *)



(* ================================================== thm:fiber-of-the-fiber *)
(* Lemma 8.4.4, page 266 *)



(* ================================================== thm:les *)
(* Theorem 8.4.6, page 267 *)



(* ================================================== thm:ses *)
(* Lemma 8.4.7, page 268 *)



(* ================================================== thm:conn-pik *)
(* Corollary 8.4.8, page 269 *)



(* ================================================== thm:hopf-fibration *)
(* Theorem 8.5.1, page 269 *)



(* ================================================== cor:pis2-hopf *)
(* Corollary 8.5.2, page 270 *)



(* ================================================== lem:fibration-over-pushout *)
(* Lemma 8.5.3, page 270 *)



(* ================================================== lem:hopf-construction *)
(* Lemma 8.5.7, page 272 *)



(* ================================================== lem:hspace-S1 *)
(* Lemma 8.5.8, page 272 *)



(* ================================================== thm:conn-trunc-variable-ind *)
(* Lemma 8.6.1, page 275 *)



(* ================================================== thm:wedge-connectivity *)
(* Lemma 8.6.2, page 275 *)



(* ================================================== thm:freudenthal *)
(* Theorem 8.6.4, page 276 *)



(* ================================================== thm:freudcode *)
(* Definition 8.6.5, page 277 *)



(* ================================================== thm:freudlemma *)
(* Lemma 8.6.10, page 278 *)



(* ================================================== cor:freudenthal-equiv *)
(* Corollary 8.6.14, page 279 *)



(* ================================================== cor:stability-spheres *)
(* Corollary 8.6.15, page 280 *)



(* ================================================== thm:naive-van-kampen *)
(* Theorem 8.7.4, page 284 *)



(* ================================================== eg:circle *)
(* Example 8.7.6, page 285 *)



(* ================================================== eg:suspension *)
(* Example 8.7.7, page 285 *)



(* ================================================== eg:wedge *)
(* Example 8.7.8, page 286 *)



(* ================================================== thm:kbar *)
(* Lemma 8.7.9, page 286 *)



(* ================================================== thm:van-Kampen *)
(* Theorem 8.7.12, page 288 *)



(* ================================================== eg:clvk *)
(* Example 8.7.13, page 288 *)



(* ================================================== eg:cofiber *)
(* Example 8.7.14, page 289 *)



(* ================================================== eg:torus *)
(* Example 8.7.15, page 289 *)



(* ================================================== eg:kg1 *)
(* Example 8.7.17, page 289 *)



(* ================================================== thm:whitehead0 *)
(* Theorem 8.8.1, page 290 *)



(* ================================================== thm:whitehead1 *)
(* Corollary 8.8.2, page 291 *)



(* ================================================== thm:whiteheadn *)
(* Theorem 8.8.3, page 291 *)



(* ================================================== thm:whitehead-contr *)
(* Corollary 8.8.4, page 292 *)



(* ================================================== thm:pik-conn *)
(* Corollary 8.8.5, page 292 *)



(* ================================================== Blakers-Massey *)
(* Theorem 8.10.2, page 295 *)



(* ================================================== Eilenberg-Mac-Lane-Spaces *)
(* Theorem 8.10.3, page 295 *)



(* ================================================== thm:covering-spaces *)
(* Theorem 8.10.4, page 295 *)



(* ================================================== ex:unique-fiber *)
(* Exercise 8.5, page 297 *)



(* ================================================== ex:ap-path-inversion *)
(* Exercise 8.6, page 297 *)



(* ================================================== ex:pointed-equivalences *)
(* Exercise 8.7, page 297 *)



(* ================================================== ex:vksusppt *)
(* Exercise 8.10, page 298 *)



(* ================================================== ex:vksuspnopt *)
(* Exercise 8.11, page 298 *)



(* ================================================== ex:HopfJr *)
(* Exercise 8.8, page 298 *)



(* ================================================== ex:SuperHopf *)
(* Exercise 8.9, page 298 *)



(* ================================================== ct:precategory *)
(* Definition 9.1.1, page 300 *)



(* ================================================== ct:isomorphism *)
(* Definition 9.1.2, page 300 *)



(* ================================================== ct:isoprop *)
(* Lemma 9.1.3, page 301 *)



(* ================================================== ct:precatset *)
(* Example 9.1.5, page 301 *)



(* ================================================== ct:category *)
(* Definition 9.1.6, page 301 *)



(* ================================================== ct:eg:set *)
(* Example 9.1.7, page 301 *)



(* ================================================== ct:obj-1type *)
(* Lemma 9.1.8, page 301 *)



(* ================================================== ct:orders *)
(* Example 9.1.14, page 302 *)



(* ================================================== ct:gaunt *)
(* Example 9.1.15, page 302 *)



(* ================================================== ct:discrete *)
(* Example 9.1.16, page 302 *)



(* ================================================== ct:fundgpd *)
(* Example 9.1.17, page 302 *)



(* ================================================== ct:hoprecat *)
(* Example 9.1.18, page 302 *)



(* ================================================== ct:idtoiso-trans *)
(* Lemma 9.1.9, page 302 *)



(* ================================================== ct:rel *)
(* Example 9.1.19, page 303 *)



(* ================================================== ct:functor *)
(* Definition 9.2.1, page 303 *)



(* ================================================== ct:nattrans *)
(* Definition 9.2.2, page 304 *)



(* ================================================== ct:functor-precat *)
(* Definition 9.2.3, page 304 *)



(* ================================================== ct:natiso *)
(* Lemma 9.2.4, page 304 *)



(* ================================================== ct:functor-cat *)
(* Theorem 9.2.5, page 304 *)



(* ================================================== ct:pentagon *)
(* Lemma 9.2.10, page 306 *)



(* ================================================== ct:interchange *)
(* Lemma 9.2.8, page 306 *)



(* ================================================== ct:functor-assoc *)
(* Lemma 9.2.9, page 306 *)



(* ================================================== ct:units *)
(* Lemma 9.2.11, page 307 *)



(* ================================================== ct:adjprop *)
(* Lemma 9.3.2, page 307 *)



(* ================================================== ct:equiv *)
(* Definition 9.4.1, page 308 *)



(* ================================================== ct:adjointification *)
(* Lemma 9.4.2, page 308 *)



(* ================================================== ct:ffeso *)
(* Lemma 9.4.5, page 308 *)



(* ================================================== ct:catweq *)
(* Lemma 9.4.7, page 310 *)



(* ================================================== ct:isocat *)
(* Definition 9.4.8, page 310 *)



(* ================================================== ct:isoprecat *)
(* Lemma 9.4.9, page 310 *)



(* ================================================== ct:chaotic *)
(* Example 9.4.13, page 312 *)



(* ================================================== ct:eqv-levelwise *)
(* Lemma 9.4.14, page 312 *)



(* ================================================== ct:cat-eq-iso *)
(* Lemma 9.4.15, page 313 *)



(* ================================================== ct:cat-2cat *)
(* Theorem 9.4.16, page 313 *)



(* ================================================== ct:opposite-category *)
(* Definition 9.5.1, page 314 *)



(* ================================================== ct:functorexpadj *)
(* Lemma 9.5.3, page 314 *)



(* ================================================== ct:yoneda *)
(* Theorem 9.5.4, page 315 *)



(* ================================================== ct:yoneda-embedding *)
(* Corollary 9.5.6, page 315 *)



(* ================================================== ct:yoneda-mono *)
(* Corollary 9.5.7, page 315 *)



(* ================================================== ct:representable *)
(* Definition 9.5.8, page 315 *)



(* ================================================== ct:representable-prop *)
(* Theorem 9.5.9, page 315 *)



(* ================================================== ct:adj-repr *)
(* Lemma 9.5.10, page 316 *)



(* ================================================== ct:adjprop2 *)
(* Corollary 9.5.11, page 317 *)



(* ================================================== ct:galois *)
(* Example 9.6.3, page 317 *)



(* ================================================== ct:unitary *)
(* Definition 9.7.2, page 318 *)



(* ================================================== ct:idtounitary *)
(* Lemma 9.7.3, page 318 *)



(* ================================================== ct:hilb *)
(* Example 9.7.7, page 318 *)



(* ================================================== ct:sig *)
(* Definition 9.8.1, page 319 *)



(* ================================================== thm:sip *)
(* Theorem 9.8.2, page 319 *)



(* ================================================== ct:sip-functor-cat *)
(* Example 9.8.3, page 320 *)



(* ================================================== defn:fo-notion-of-structure *)
(* Definition 9.8.4, page 321 *)



(* ================================================== ct:esofull-precomp-ff *)
(* Lemma 9.9.2, page 322 *)



(* ================================================== ct:cat-weq-eq *)
(* Theorem 9.9.4, page 323 *)



(* ================================================== thm:rezk-completion *)
(* Theorem 9.9.5, page 325 *)



(* ================================================== ct:rezk-fundgpd-trunc1 *)
(* Example 9.9.6, page 327 *)



(* ================================================== ct:hocat *)
(* Example 9.9.7, page 328 *)



(* ================================================== ct:pre2cat *)
(* Exercise 9.4, page 330 *)



(* ================================================== ct:2cat *)
(* Exercise 9.5, page 330 *)



(* ================================================== ct:groupoids *)
(* Exercise 9.6, page 330 *)



(* ================================================== ct:ex:hocat *)
(* Exercise 9.9, page 330 *)



(* ================================================== ex:rezk-vankampen *)
(* Exercise 9.11, page 331 *)



(* ================================================== ex:stack *)
(* Exercise 9.12, page 331 *)



(* ================================================== thm:mono *)
(* Lemma 10.1.1, page 335 *)



(* ================================================== epis-surj *)
(* Lemma 10.1.4, page 335 *)



(* ================================================== lem:images_are_coequalizers *)
(* Theorem 10.1.5, page 337 *)



(* ================================================== thm:set_regular *)
(* Theorem 10.1.5, page 337 *)



(* ================================================== lem:pb_of_coeq_is_coeq *)
(* Lemma 10.1.6, page 337 *)



(* ================================================== lem:sets_exact *)
(* Lemma 10.1.8, page 338 *)



(* ================================================== prop:kernels_are_effective *)
(* Theorem 10.1.9, page 338 *)



(* ================================================== thm:settopos *)
(* Theorem 10.1.12, page 340 *)



(* ================================================== prop:trunc_of_prop_is_set *)
(* Lemma 10.1.13, page 341 *)



(* ================================================== thm:1surj_to_surj_to_pem *)
(* Theorem 10.1.14, page 341 *)



(* ================================================== thm:ETCS *)
(* Theorem 10.1.15, page 342 *)



(* ================================================== defn:card *)
(* Definition 10.2.1, page 342 *)



(* ================================================== card:semiring *)
(* Lemma 10.2.4, page 343 *)



(* ================================================== card:exp *)
(* Lemma 10.2.6, page 343 *)



(* ================================================== thm:injsurj *)
(* Lemma 10.2.9, page 344 *)



(* ================================================== defn:accessibility *)
(* Definition 10.3.1, page 345 *)



(* ================================================== thm:nat-wf *)
(* Example 10.3.5, page 347 *)



(* ================================================== thm:wtype-wf *)
(* Example 10.3.6, page 347 *)



(* ================================================== thm:wfrec *)
(* Lemma 10.3.7, page 347 *)



(* ================================================== thm:wfmin *)
(* Lemma 10.3.8, page 348 *)



(* ================================================== def:simulation *)
(* Definition 10.3.11, page 349 *)



(* ================================================== thm:wfcat *)
(* Corollary 10.3.15, page 350 *)



(* ================================================== thm:ordord *)
(* Theorem 10.3.20, page 350 *)



(* ================================================== thm:ordsucc *)
(* Lemma 10.3.21, page 351 *)



(* ================================================== thm:ordunion *)
(* Lemma 10.3.22, page 351 *)



(* ================================================== thm:wellorder *)
(* Theorem 10.4.3, page 352 *)



(* ================================================== thm:wop *)
(* Theorem 10.4.4, page 353 *)



(* ================================================== defn:V *)
(* Definition 10.5.1, page 354 *)



(* ================================================== def:bisimulation *)
(* Definition 10.5.4, page 356 *)



(* ================================================== lem:BisimEqualsId *)
(* Lemma 10.5.5, page 356 *)



(* ================================================== lem:MonicSetPresent *)
(* Lemma 10.5.6, page 356 *)



(* ================================================== def:TypeOfElements *)
(* Definition 10.5.7, page 357 *)



(* ================================================== thm:VisCST *)
(* Theorem 10.5.8, page 357 *)



(* ================================================== cor:Delta0sep *)
(* Corollary 10.5.9, page 358 *)



(* ================================================== lem:fullsep *)
(* Lemma 10.5.10, page 359 *)



(* ================================================== thm:zfc *)
(* Theorem 10.5.11, page 359 *)



(* ================================================== ex:well-pointed *)
(* Exercise 10.3, page 360 *)



(* ================================================== ex:choice-function *)
(* Exercise 10.10, page 361 *)



(* ================================================== ex:cumhierhit *)
(* Exercise 10.11, page 361 *)



(* ================================================== ex:prop-ord *)
(* Exercise 10.7, page 361 *)



(* ================================================== ex:ninf-ord *)
(* Exercise 10.8, page 361 *)



(* ================================================== defn:dedekind-reals *)
(* Definition 11.2.1, page 366 *)



(* ================================================== dedekind-in-cut-as-le *)
(* Lemma 11.2.2, page 367 *)



(* ================================================== RD-inverse-apart-0 *)
(* Theorem 11.2.4, page 368 *)



(* ================================================== RD-archimedean *)
(* Theorem 11.2.6, page 368 *)



(* ================================================== ordered-field *)
(* Definition 11.2.7, page 368 *)



(* ================================================== defn:cauchy-approximation *)
(* Definition 11.2.10, page 369 *)



(* ================================================== RD-cauchy-complete *)
(* Theorem 11.2.12, page 369 *)



(* ================================================== RD-archimedean-ordered-field *)
(* Theorem 11.2.8, page 369 *)



(* ================================================== RD-final-field *)
(* Theorem 11.2.14, page 370 *)



(* ================================================== lem:cuts-preserve-admissibility *)
(* Lemma 11.2.15, page 371 *)



(* ================================================== RD-dedekind-complete *)
(* Corollary 11.2.16, page 371 *)



(* ================================================== defn:cauchy-reals *)
(* Definition 11.3.2, page 373 *)



(* ================================================== RC-lim-onto *)
(* Lemma 11.3.10, page 376 *)



(* ================================================== thm:Cauchy-reals-are-a-set *)
(* Theorem 11.3.9, page 376 *)



(* ================================================== RC-lim-factor *)
(* Lemma 11.3.11, page 377 *)



(* ================================================== thm:RCsim-symmetric *)
(* Lemma 11.3.12, page 377 *)



(* ================================================== defn:lipschitz *)
(* Definition 11.3.14, page 378 *)



(* ================================================== RC-extend-Q-Lipschitz *)
(* Lemma 11.3.15, page 379 *)



(* ================================================== defn:RC-approx *)
(* Theorem 11.3.16, page 380 *)



(* ================================================== thm:RC-sim-characterization *)
(* Theorem 11.3.32, page 383 *)



(* ================================================== thm:RC-sim-lim *)
(* Lemma 11.3.36, page 384 *)



(* ================================================== thm:RC-sim-lim-term *)
(* Lemma 11.3.37, page 384 *)



(* ================================================== RC-continuous-eq *)
(* Lemma 11.3.39, page 384 *)



(* ================================================== RC-binary-nonexpanding-extension *)
(* Lemma 11.3.40, page 385 *)



(* ================================================== RC-archimedean *)
(* Theorem 11.3.41, page 386 *)



(* ================================================== thm:RC-le-grow *)
(* Lemma 11.3.42, page 386 *)



(* ================================================== thm:RC-lt-open *)
(* Lemma 11.3.43, page 387 *)



(* ================================================== RC-sim-eqv-le *)
(* Theorem 11.3.44, page 387 *)



(* ================================================== RC-squaring *)
(* Theorem 11.3.46, page 388 *)



(* ================================================== RC-archimedean-ordered-field *)
(* Theorem 11.3.48, page 389 *)



(* ================================================== RC-initial-Cauchy-complete *)
(* Theorem 11.3.50, page 389 *)



(* ================================================== lem:untruncated-linearity-reals-coincide *)
(* Lemma 11.4.1, page 390 *)



(* ================================================== when-reals-coincide *)
(* Corollary 11.4.3, page 390 *)



(* ================================================== defn:metric-space *)
(* Definition 11.5.1, page 391 *)



(* ================================================== defn:complete-metric-space *)
(* Definition 11.5.2, page 391 *)



(* ================================================== defn:total-bounded-metric-space *)
(* Definition 11.5.3, page 391 *)



(* ================================================== defn:uniformly-continuous *)
(* Definition 11.5.5, page 392 *)



(* ================================================== analysis-interval-ctb *)
(* Theorem 11.5.6, page 392 *)



(* ================================================== ctb-uniformly-continuous-sup *)
(* Theorem 11.5.7, page 392 *)



(* ================================================== analysis-bw-lpo *)
(* Theorem 11.5.9, page 393 *)



(* ================================================== classical-Heine-Borel *)
(* Theorem 11.5.11, page 394 *)



(* ================================================== defn:inductive-cover *)
(* Definition 11.5.13, page 395 *)



(* ================================================== reals-formal-topology-locally-compact *)
(* Lemma 11.5.14, page 396 *)



(* ================================================== interval-Heine-Borel *)
(* Corollary 11.5.15, page 396 *)



(* ================================================== inductive-cover-classical *)
(* Theorem 11.5.16, page 396 *)



(* ================================================== defn:surreals *)
(* Definition 11.6.1, page 398 *)



(* ================================================== thm:NO-simplicity *)
(* Theorem 11.6.2, page 400 *)



(* ================================================== thm:NO-refl-opt *)
(* Theorem 11.6.4, page 402 *)



(* ================================================== thm:NO-set *)
(* Corollary 11.6.5, page 402 *)



(* ================================================== defn:No-codes *)
(* Theorem 11.6.7, page 404 *)



(* ================================================== thm:NO-encode-decode *)
(* Theorem 11.6.16, page 406 *)



(* ================================================== thm:NO-unstrict-transitive *)
(* Corollary 11.6.17, page 406 *)



(* ================================================== ex:RD-extended-reals *)
(* Exercise 11.2, page 409 *)



(* ================================================== ex:RD-lower-cuts *)
(* Exercise 11.3, page 409 *)



(* ================================================== ex:RD-interval-arithmetic *)
(* Exercise 11.4, page 409 *)



(* ================================================== ex:RD-lt-vs-le *)
(* Exercise 11.5, page 410 *)



(* ================================================== ex:reals-non-constant-into-Z *)
(* Exercise 11.6, page 410 *)



(* ================================================== ex:traditional-archimedean *)
(* Exercise 11.7, page 410 *)



(* ================================================== RC-Lipschitz-on-interval *)
(* Exercise 11.8, page 410 *)



(* ================================================== ex:metric-completion *)
(* Exercise 11.9, page 410 *)



(* ================================================== ex:reals-apart-neq-MP *)
(* Exercise 11.10, page 411 *)



(* ================================================== ex:reals-apart-zero-divisors *)
(* Exercise 11.11, page 411 *)



(* ================================================== ex:finite-cover-lebesgue-number *)
(* Exercise 11.12, page 411 *)



(* ================================================== ex:mean-value-theorem *)
(* Exercise 11.13, page 411 *)



