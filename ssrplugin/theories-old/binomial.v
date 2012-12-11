(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path div.
Require Import fintype tuple finfun bigop prime finset.

(******************************************************************************)
(* This files contains the definition of:                                     *)
(*     n ^_ m == the falling (or lower) factorial of n with m terms, i.e.,    *)
(*               the product n * (n - 1) * ... * (n - m + 1)                  *)
(*               Note that n ^_ m = 0 if m > n.                               *)
(*   'C(n, m) == the binomial coeficient n choose m                           *)
(*            := n ^_ m %/ fact m                                             *)
(*                                                                            *)
(* In additions to the properties of these functions, triangular_sum, Wilson  *)
(* and Pascal are examples of how to manipulate expressions with bigops.      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** More properties of the factorial **)

Lemma fact_smonotone m n : 0 < m -> m < n -> m`! < n`!.
Proof.
case: m => // m _; elim: n m => // n IHn [|m] lt_m_n.
  by rewrite -[_.+1]muln1 leq_mul ?fact_gt0.
by rewrite ltn_mul ?IHn.
Qed.

Lemma fact_prod n : n`! = \prod_(1 <= i < n.+1) i.
Proof.
elim: n => [|n IHn] //; first by rewrite big_nil.
by apply: identity_sym; rewrite factS IHn // !big_add1 big_nat_recr /= mulnC.
Qed.

Lemma logn_fact p n : prime p -> logn p n`! = \sum_(1 <= k < n.+1) n %/ p ^ k.
Proof.
move=> p_prime; transitivity (\sum_(1 <= i < n.+1) logn p i).
  rewrite big_add1; elim: n => /= [|n IHn]; first by rewrite logn1 big_geq.
  by rewrite big_nat_recr -IHn /= factS mulnC lognM ?fact_gt0.
transitivity (\sum_(1 <= i < n.+1) \sum_(1 <= k < n.+1) (p ^ k %| i)).
  apply: eq_big_nat => i /andP[i_gt0 le_i_n]; rewrite logn_count_dvd //.
  rewrite -!big_mkcond (big_nat_widen _ _ n.+1) 1?ltnW //; apply: eq_bigl => k.
  by apply: andb_idr => /dvdn_leq/(leq_trans (ltn_expl _ (prime_gt1 _)))->.
by rewrite exchange_big_nat; apply: eq_bigr => i _; rewrite divn_count_dvd.
Qed.
 
Theorem Wilson p : p > 1 -> prime p = (p %| ((p.-1)`!).+1).
Proof.
have dFact n: 0 < n -> (n.-1)`! = \prod_(0 <= i < n | i != 0) i.
  move=> n_gt0; rewrite -big_filter fact_prod; symmetry; apply: congr_big => //.
  rewrite /index_iota subn1 -[n]prednK //=; apply/all_filterP.
  by rewrite all_predC has_pred1 mem_iota.
move=> lt1p; have p_gt0 := ltnW lt1p.
apply/idP/idP=> [pr_p | dv_pF]; last first.
  apply/primeP; split=> // d dv_dp; have: d <= p by exact: dvdn_leq.
  rewrite orbC leq_eqVlt => /orP[-> // | ltdp].
  have:= dvdn_trans dv_dp dv_pF; rewrite dFact // big_mkord.
  rewrite (bigD1 (Ordinal ltdp)) /=; last by rewrite -lt0n (dvdn_gt0 p_gt0).
  by rewrite orbC -addn1 dvdn_addr ?dvdn_mulr // dvdn1 => ->.
pose Fp1 := Ordinal lt1p; pose Fp0 := Ordinal p_gt0.
have ltp1p: p.-1 < p by [rewrite prednK]; pose Fpn1 := Ordinal ltp1p.
case eqF1n1: (Fp1 == Fpn1); first by rewrite -{1}[p]prednK -1?((1 =P p.-1) _).
have toFpP m: m %% p < p by rewrite ltn_mod.
pose toFp := Ordinal (toFpP _); pose mFp (i j : 'I_p) := toFp (i * j).
have Fp_mod (i : 'I_p) : i %% p = i by exact: modn_small.
have mFpA: associative mFp.
  by move=> i j k; apply: val_inj; rewrite /= modnMml modnMmr mulnA.
have mFpC: commutative mFp by move=> i j; apply: val_inj; rewrite /= mulnC.
have mFp1: left_id Fp1 mFp by move=> i; apply: val_inj; rewrite /= mul1n.
have mFp1r: right_id Fp1 mFp by move=> i; apply: val_inj; rewrite /= muln1.
pose mFpLaw := Monoid.Law mFpA mFp1 mFp1r.
pose mFpM := Monoid.operator (@Monoid.ComLaw _ _ mFpLaw mFpC).
pose vFp (i : 'I_p) := toFp (egcdn i p).1.
have vFpV i: i != Fp0 -> mFp (vFp i) i = Fp1.
  rewrite -val_eqE /= -lt0n => i_gt0; apply: val_inj => /=.
  rewrite modnMml; case: egcdnP => //= _ km -> _; rewrite {km}modnMDl.
  suffices: coprime i p by move/eqnP->; rewrite modn_small.
  rewrite coprime_sym prime_coprime //; apply/negP=> /(dvdn_leq i_gt0).
  by rewrite leqNgt ltn_ord.
have vFp0 i: i != Fp0 -> vFp i != Fp0.
  move/vFpV=> inv_i; apply/eqP=> vFp0.
  by have:= congr1 val inv_i; rewrite vFp0 /= mod0n.
have vFpK: {in predC1 Fp0, involutive vFp}.
  move=> i n0i; rewrite /= -[vFp _]mFp1r -(vFpV _ n0i) mFpA.
  by rewrite vFpV (vFp0, mFp1).
have le_pmFp (i : 'I_p) m: i <= p + m.
  by apply: leq_trans (ltnW _) (leq_addr _ _).
have eqFp (i j : 'I_p): (i == j) = (p %| p + i - j).
  by rewrite -eqn_mod_dvd ?(modnDl, Fp_mod).
have vFpId i: (vFp i == i :> nat) = xpred2 Fp1 Fpn1 i.
  symmetry; have [->{i} | /eqP ni0] := i =P Fp0.
    by rewrite /= -!val_eqE /= -{2}[p]prednK //= modn_small //= -(subnKC lt1p).
  rewrite 2!eqFp -Euclid_dvdM //= -[_ - p.-1]subSS prednK //.
  have lt0i: 0 < i by rewrite lt0n.
  rewrite -addnS addKn -addnBA // mulnDl -{2}(addn1 i) -subn_sqr.
  rewrite addnBA ?leq_sqr // mulnS -addnA -mulnn -mulnDl.
  rewrite -(subnK (le_pmFp (vFp i) i)) mulnDl addnCA.
  rewrite -[1 ^ 2]/(Fp1 : nat) -addnBA // dvdn_addl.
    by rewrite Euclid_dvdM // -eqFp eq_sym orbC /dvdn Fp_mod eqn0Ngt lt0i.
  by rewrite -eqn_mod_dvd // Fp_mod modnDl -(vFpV _ ni0) eqxx.
(* assia : same problem as in prime : injection does not work ... *)
suffices : toFp (p.-1)`! = Fpn1.
  rewrite /toFp /Fpn1; move/(f_equal (@nat_of_ord _)) => /= mod_fact.
  by rewrite /dvdn -addn1 -modnDml mod_fact addn1 prednK // modnn.
(* suffices [mod_fact]: toFp (p.-1)`! = Fpn1. *)
(*   by rewrite /dvdn -addn1 -modnDml mod_fact addn1 prednK // modnn. *)
rewrite dFact //; rewrite ((big_morph toFp) Fp1 mFpM) //; first last.
- by apply: val_inj; rewrite /= modn_small.
- by move=> i j; apply: val_inj; rewrite /= modnMm.
rewrite big_mkord (eq_bigr id) => [|i _]; last by apply: val_inj => /=.
pose ltv i := vFp i < i; rewrite (bigID ltv) -/mFpM [mFpM _ _]mFpC.
rewrite (bigD1 Fp1) -/mFpM; last by rewrite [ltv _]ltn_neqAle vFpId.
rewrite [mFpM _ _]mFp1 (bigD1 Fpn1) -?mFpA -/mFpM; last first.
  rewrite -lt0n -ltnS prednK // lt1p.
  by rewrite [ltv _]ltn_neqAle vFpId eqxx orbT eq_sym eqF1n1.
rewrite (reindex_onto vFp vFp) -/mFpM => [|i]; last by do 3!case/andP; auto.
rewrite (eq_bigl (xpredD1 ltv Fp0)) => [|i]; last first.
  rewrite andbC -!andbA -2!negb_or -vFpId orbC -leq_eqVlt.
  rewrite andbA -ltnNge; symmetry; case: (altP eqP) => [->|ni0].
    by case: eqP => // E; rewrite ?E !andbF.
  by rewrite vFpK //eqxx vFp0.
rewrite -{2}[mFp]/mFpM -[mFpM _ _]big_split -/mFpM.
by rewrite big1 ?mFp1r //= => i /andP[]; auto.
Qed.

(** The falling factorial *)

Fixpoint ffact_rec n m := if m is m'.+1 then n * ffact_rec n.-1 m' else 1.

Definition falling_factorial := nosimpl ffact_rec.

Notation "n ^_ m" := (falling_factorial n m)
  (at level 30, right associativity) : nat_scope.

Lemma ffactE : falling_factorial = ffact_rec. Proof. by []. Qed.

Lemma ffactn0 n : n ^_ 0 = 1. Proof. by []. Qed.

Lemma ffact0n m : 0 ^_ m = (m == 0). Proof. by case: m. Qed.

Lemma ffactnS n m : n ^_ m.+1 = n * n.-1 ^_ m. Proof. by []. Qed.

Lemma ffactSS n m : n.+1 ^_ m.+1 = n.+1 * n ^_ m. Proof. by []. Qed.

Lemma ffactn1 n : n ^_ 1 = n. Proof. exact: muln1. Qed.

Lemma ffactnSr n m : n ^_ m.+1 = n ^_ m * (n - m).
Proof.
elim: n m => [|n IHn] [|m] //=; first by rewrite ffactn1 mul1n.
by rewrite !ffactSS IHn mulnA.
Qed.

Lemma ffact_gt0 n m : (0 < n ^_ m) = (m <= n).
Proof. by elim: n m => [|n IHn] [|m] //=; rewrite ffactSS muln_gt0 IHn. Qed.

Lemma ffact_small n m : n < m -> n ^_ m = 0.
Proof. by rewrite ltnNge -ffact_gt0; case: posnP. Qed.

Lemma ffactnn n : n ^_ n = n`!.
Proof. by elim: n => [|n IHn] //; rewrite ffactnS IHn. Qed.

Lemma ffact_fact n m : m <= n -> n ^_ m * (n - m)`! = n`!.
Proof.
by elim: n m => [|n IHn] [|m] //= le_m_n; rewrite ?mul1n // -mulnA IHn.
Qed.

Lemma ffact_factd n m : m <= n -> n ^_ m = n`! %/ (n - m)`!.
Proof. by move/ffact_fact <-; rewrite mulnK ?fact_gt0. Qed.

(** Binomial coefficients *)

Fixpoint binomial_rec n m :=
  match n, m with
  | n'.+1, m'.+1 => binomial_rec n' m + binomial_rec n' m'
  | _, 0 => 1
  | 0, _.+1 => 0
  end.

Definition binomial := nosimpl binomial_rec.

Notation "''C' ( n , m )" := (binomial n m)
  (at level 8, format "''C' ( n ,  m )") : nat_scope.

Lemma binE : binomial = binomial_rec. Proof. by []. Qed.

Lemma bin0 n : 'C(n, 0) = 1. Proof. by case: n. Qed.

Lemma bin0n m : 'C(0, m) = (m == 0). Proof. by case: m. Qed.

Lemma binS n m : 'C(n.+1, m.+1) = 'C(n, m.+1) + 'C(n, m). Proof. by []. Qed.

Lemma bin1 n : 'C(n, 1) = n.
Proof. by elim: n => //= n IHn; rewrite binS bin0 IHn addn1. Qed.

Lemma bin_gt0 m n : (0 < 'C(m, n)) = (n <= m).
Proof.
elim: m n => [|m IHm] [|n] //.
by rewrite binS addn_gt0 !IHm orbC ltn_neqAle andKb.
Qed.

Lemma leq_bin2l m1 m2 n : m1 <= m2 -> 'C(m1, n) <= 'C(m2, n).
Proof.
elim: m1 m2 n => [m2 | m1 IHm [|m2] //] [|n] le_m12; rewrite ?bin0 //.
by rewrite !binS leq_add // IHm.
Qed.

Lemma bin_small n m : n < m -> 'C(n, m) = 0.
Proof. by rewrite ltnNge -bin_gt0; case: posnP. Qed.

Lemma binn n : 'C(n, n) = 1.
Proof. by elim: n => [|n IHn] //; rewrite binS bin_small. Qed.

Lemma mul_Sm_binm m n : m.+1 * 'C(m, n) = n.+1 * 'C(m.+1, n.+1).
Proof.
elim: m n => [|m IHm] [|n] //; first by rewrite bin0 bin1 muln1 mul1n.
by rewrite mulSn {2}binS mulnDr addnCA !IHm -mulnDr.
Qed.

Lemma bin_fact m n : n <= m -> 'C(m, n) * (n`! * (m - n)`!) = m`!.
Proof.
move/subnKC; move: (m - n) => m0 <-{m}.
elim: n => [|n IHn]; first by rewrite bin0 !mul1n.
by rewrite -mulnA mulnCA mulnA -mul_Sm_binm -mulnA IHn.
Qed.

(* In fact the only exception is n = 0 and m = 1 *)
Lemma bin_factd n m : 0 < n -> 'C(n, m)  = n`! %/ (m`! * (n - m)`!).
Proof.
move=> n_gt0; have [/bin_fact <-|lt_n_m] := leqP m n.
  by rewrite mulnK // muln_gt0 !fact_gt0.
by rewrite bin_small // divnMA !divn_small ?fact_gt0 // fact_smonotone.
Qed.

Lemma bin_ffact n m : 'C(n, m) * m`! = n ^_ m.
Proof.
apply/eqP; have [lt_n_m | le_m_n] := ltnP n m.
  by rewrite bin_small ?ffact_small.
by rewrite -(eqn_pmul2r (fact_gt0 (n - m))) ffact_fact // -mulnA bin_fact.
Qed.

Lemma bin_ffactd n m : 'C(n, m) = n ^_ m %/ m`!.
Proof. by rewrite -bin_ffact mulnK ?fact_gt0. Qed.

Lemma bin_sub n m : m <= n -> 'C(n, n - m) = 'C(n, m).
Proof.
move=> le_m_n; apply/eqP; move/eqP: (bin_fact (leq_subr m n)).
by rewrite subKn // -(bin_fact le_m_n) !mulnA mulnAC !eqn_pmul2r // fact_gt0.
Qed.

Lemma binSn n : 'C(n.+1, n) = n.+1.
Proof. by rewrite -bin_sub ?leqnSn // subSnn bin1. Qed.

Lemma bin2 n : 'C(n, 2) = (n * n.-1)./2.
Proof.
by case: n => //= n; rewrite -{3}[n]bin1 mul_Sm_binm mul2n half_double.
Qed.

Lemma bin2odd n : odd n -> 'C(n, 2) = n * n.-1./2.
Proof. by case: n => // n oddn; rewrite bin2 -!divn2 muln_divA ?dvdn2. Qed.

Lemma prime_dvd_bin k p : prime p -> 0 < k < p -> p %| 'C(p, k).
Proof.
move=> p_pr /andP[k_gt0 lt_k_p]; have def_p := ltn_predK lt_k_p.
have: p %| p * 'C(p.-1, k.-1) by rewrite dvdn_mulr.
by rewrite -def_p mul_Sm_binm def_p prednK // Euclid_dvdM // gtnNdvd.
Qed.

Lemma triangular_sum n : \sum_(0 <= i < n) i = 'C(n, 2).
Proof.
by elim: n => [|n IHn]; [rewrite big_geq | rewrite big_nat_recr IHn binS bin1].
Qed.

Lemma textbook_triangular_sum n : \sum_(0 <= i < n) i = 'C(n, 2).
Proof.
rewrite bin2; apply: canRL half_double _.
rewrite -addnn {1}big_nat_rev -big_split big_mkord /= ?add0n.
rewrite (eq_bigr (fun _ => n.-1)); first by rewrite sum_nat_const card_ord.
by case: n => [|n] [i le_i_n] //=; rewrite subSS subnK.
Qed.

Theorem Pascal a b n :
  (a + b) ^ n = \sum_(i < n.+1) 'C(n, i) * (a ^ (n - i) * b ^ i).
Proof.
elim: n => [|n IHn]; rewrite big_ord_recl muln1 ?big_ord0 //.
rewrite expnS {}IHn /= mulnDl !big_distrr /= big_ord_recl muln1 subn0.
rewrite !big_ord_recr /= !binn !subnn bin0 !subn0 !mul1n -!expnS -addnA.
congr (_ + _); rewrite addnA -big_split /=; congr (_ + _).
apply: eq_bigr => i _; rewrite mulnCA (mulnA a) -expnS subnSK //.
by rewrite (mulnC b) -2!mulnA -expnSr -mulnDl.
Qed.
Definition expnDn := Pascal.

Lemma Vandermonde k l i :
  \sum_(j < i.+1) 'C(k, j) * 'C(l, i - j) = 'C(k + l , i).
Proof.
pose f k i := \sum_(j < i.+1) 'C(k, j) * 'C(l, i - j).
suffices{k i} fxx k i: f k.+1 i.+1 = f k i.+1 + f k i.
  elim: k i => [i | k IHk [|i]]; last by rewrite -/(f _ _) fxx /f !IHk -binS.
    by rewrite big_ord_recl big1_eq addn0 mul1n subn0.
  by rewrite big_ord_recl big_ord0 addn0 !bin0 muln1.
rewrite {}/f big_ord_recl (big_ord_recl (i.+1)) !bin0 !mul1n.
rewrite -addnA -big_split /=; congr (_ + _).
by apply: eq_bigr => j _ ; rewrite -mulnDl.
Qed.

Lemma subn_exp m n k :
  m ^ k - n ^ k = (m - n) * (\sum_(i < k) m ^ (k.-1 -i) * n ^ i).
Proof.
case: k => [|k]; first by rewrite big_ord0.
rewrite mulnBl !big_distrr big_ord_recl big_ord_recr /= subn0 muln1.
rewrite subnn mul1n -!expnS subnDA; congr (_ - _).
set F := fun _ => n * _; rewrite (eq_bigr F) ?addnK {}/F // => i _.
by rewrite (mulnCA n) -expnS mulnA -expnS subnSK.
Qed.

Lemma predn_exp m k : (m ^ k).-1 = m.-1 * (\sum_(i < k) m ^ i).
Proof.
rewrite -!subn1 -{1}(exp1n k) subn_exp; congr (_ * _).
symmetry; rewrite (reindex_inj rev_ord_inj); apply: eq_bigr => i _ /=.
by rewrite -subn1 -subnDA exp1n muln1.
Qed.

Lemma dvdn_pred_predX n e : (n.-1 %| (n ^ e).-1)%N.
Proof. by rewrite predn_exp dvdn_mulr. Qed.

Lemma modn_summ I r (P : pred I) F d :
  \sum_(i <- r | P i) F i %% d = \sum_(i <- r | P i) F i %[mod d].
Proof.
by apply/eqP; elim/big_rec2: _ => // i m n _; rewrite modnDml eqn_modDl.
Qed.

(* Combinatorial characterizations. *)

Section Combinations.

Implicit Types T D : finType.

Lemma card_uniq_tuples T n (A : pred T) :
  #|[set t : n.-tuple T | all A t & uniq t]| = #|A| ^_ n.
Proof.
elim: n A => [|n IHn] A.
  by rewrite (@eq_card1 _ [tuple]) // => t; rewrite [t]tuple0 inE.
rewrite -sum1dep_card (partition_big (@thead _ _) A) /= => [|t]; last first.
  by case/tupleP: t => x t; do 2!case/andP.
transitivity (#|A| * #|A|.-1 ^_ n)%N; last by case: #|A|.
rewrite -sum_nat_const; apply: eq_bigr => x Ax.
rewrite (cardD1 x) [x \in A]Ax /= -(IHn [predD1 A & x]) -sum1dep_card.
rewrite (reindex (fun t : n.-tuple T => [tuple of x :: t])) /=; last first.
  pose ttail (t : n.+1.-tuple T) := [tuple of behead t].
  exists ttail => [t _ | t /andP[_ /eqP <-]]; first exact: val_inj.
  by rewrite -tuple_eta.
apply: eq_bigl=> t; rewrite Ax theadE eqxx andbT /= andbA; congr (_ && _).
by rewrite all_predI all_predC has_pred1 andbC.
Qed.

Lemma card_inj_ffuns_on D T (R : pred T) :
  #|[set f : {ffun D -> T} in ffun_on R | injectiveb f]| = #|R| ^_ #|D|.
Proof.
rewrite -card_uniq_tuples.
have bijFF: {on (_ : pred _), bijective (@Finfun D T)}.
  by exists val => // x _; exact: val_inj.
rewrite -(on_card_preimset (bijFF _)); apply: eq_card => t.
rewrite !inE -(codom_ffun (Finfun t)); congr (_ && _); apply: negb_inj.
by rewrite -has_predC has_map enumT has_filter -size_eq0 -cardE.
Qed.

Lemma card_inj_ffuns D T :
  #|[set f : {ffun D -> T} | injectiveb f]| = #|T| ^_ #|D|.
Proof.
rewrite -card_inj_ffuns_on; apply: eq_card => f.
by rewrite 2!inE; case: ffun_onP => // [].
Qed.

Lemma card_draws T k : #|[set A : {set T} | #|A| == k]| = 'C(#|T|, k).
Proof.
have [ltTk | lekT] := ltnP #|T| k.
  rewrite bin_small // eq_card0 // => A.
  by rewrite inE eqn_leq andbC leqNgt (leq_ltn_trans (max_card _)).
apply/eqP; rewrite -(eqn_pmul2r (fact_gt0 k)) bin_ffact // eq_sym.
rewrite -sum_nat_dep_const -{1 3}(card_ord k) -card_inj_ffuns -sum1dep_card.
pose imIk (f : {ffun 'I_k -> T}) := f @: 'I_k.
rewrite (partition_big imIk (fun A => #|A| == k)) /= => [|f]; last first.
  by move/injectiveP=> inj_f; rewrite card_imset ?card_ord.
apply/eqP; apply: eq_bigr => A /eqP cardAk.
have [f0 inj_f0 im_f0]: exists2 f, injective f & f @: 'I_k = A.
  rewrite -cardAk; exists enum_val; first exact: enum_val_inj.
  apply/setP=> a; apply/imsetP/idP=> [[i _ ->] | Aa]; first exact: enum_valP.
  by exists (enum_rank_in Aa a); rewrite ?enum_rankK_in.
rewrite (reindex (fun p : {ffun _} => [ffun i => f0 (p i)])) /=; last first.
  pose ff0' f i := odflt i [pick j | f i == f0 j].
  exists (fun f => [ffun i => ff0' f i]) => [p _ | f].
    apply/ffunP=> i; rewrite ffunE /ff0'; case: pickP => [j | /(_ (p i))].
      by rewrite ffunE (inj_eq inj_f0) => /eqP.
    by rewrite ffunE eqxx.
  rewrite -im_f0 => /andP[/injectiveP injf /eqP im_f].
  apply/ffunP=> i; rewrite !ffunE /ff0'; case: pickP => [y /eqP //|].
  have /imsetP[j _ eq_f0j_fi]: f i \in f0 @: 'I_k by rewrite -im_f mem_imset.
  by move/(_ j)=> /eqP[].
rewrite -ffactnn -card_inj_ffuns -sum1dep_card; apply: eq_bigl => p.
apply/andP/injectiveP=> [[/injectiveP inj_f0p _] i j eq_pij | inj_p].
  by apply: inj_f0p; rewrite !ffunE eq_pij.
set f := finfun _.
have injf: injective f by move=> i j; rewrite !ffunE => /inj_f0; exact: inj_p.
split; first exact/injectiveP.
rewrite eqEcard card_imset // cardAk card_ord leqnn andbT -im_f0.
by apply/subsetP=> x /imsetP[i _ ->]; rewrite ffunE mem_imset.
Qed.

Lemma card_ltn_sorted_tuples m n :
  #|[set t : m.-tuple 'I_n | sorted ltn (map val t)]| = 'C(n, m).
Proof.
have [-> | n_gt0] := posnP n; last pose i0 := Ordinal n_gt0.
  case: m => [|m]; last by apply: eq_card0; case/tupleP=> [[]].
  by apply: (@eq_card1 _ [tuple]) => t; rewrite [t]tuple0 inE.
rewrite -{12}[n]card_ord -card_draws.
pose f_t (t : m.-tuple 'I_n) := [set i in t].
pose f_A (A : {set 'I_n}) := [tuple of mkseq (nth i0 (enum A)) m].
have val_fA (A : {set 'I_n}) : #|A| = m -> val (f_A A) = enum A.
  by move=> Am; rewrite -[enum _](mkseq_nth i0) -cardE Am.
have inc_A (A : {set 'I_n}) : sorted ltn (map val (enum A)).
  rewrite -[enum _](eq_filter (mem_enum _)).
  rewrite -(eq_filter (mem_map val_inj _)) -filter_map.
  by rewrite (sorted_filter ltn_trans) // unlock val_ord_enum iota_ltn_sorted.
rewrite -!sum1dep_card (reindex_onto f_t f_A) /= => [|A]; last first.
  by move/eqP=> cardAm; apply/setP=> x; rewrite inE -(mem_enum (mem A)) -val_fA.
apply: eq_bigl => t; apply/idP/idP=> [inc_t|]; last first.
  by case/andP; move/eqP=> t_m; move/eqP=> <-; rewrite val_fA.
have ft_m: #|f_t t| = m.
  rewrite cardsE (card_uniqP _) ?size_tuple // -(map_inj_uniq val_inj).
  exact: (sorted_uniq ltn_trans ltnn).
rewrite ft_m eqxx -val_eqE val_fA // -(inj_eq (inj_map val_inj)) /=.
apply/eqP; apply: (eq_sorted_irr ltn_trans ltnn) => // y.
by apply/mapP/mapP=> [] [x t_x ->]; exists x; rewrite // mem_enum inE in t_x *.
Qed.

Lemma card_sorted_tuples m n :
  #|[set t : m.-tuple 'I_n.+1 | sorted leq (map val t)]| = 'C(m + n, m).
Proof.
set In1 := 'I_n.+1; pose x0 : In1 := ord0.
have add_mnP (i : 'I_m) (x : In1) : i + x < m + n.
  by rewrite -ltnS -addSn -!addnS leq_add.
pose add_mn t i := Ordinal (add_mnP i (tnth t i)).
pose add_mn_nat (t : m.-tuple In1) i := i + nth x0 t i.
have add_mnC t: val \o add_mn t =1 add_mn_nat t \o val.
  by move=> i; rewrite /= (tnth_nth x0).
pose f_add t := [tuple of map (add_mn t) (ord_tuple m)].
rewrite -card_ltn_sorted_tuples -!sum1dep_card (reindex f_add) /=.
  apply: eq_bigl => t; rewrite -map_comp (eq_map (add_mnC t)) map_comp.
  rewrite enumT unlock val_ord_enum -{1}(drop0 t).
  have [m0 | m_gt0] := posnP m.
    by rewrite {2}m0 /= drop_oversize // size_tuple m0.
  have def_m := subnK m_gt0; rewrite -{2}def_m addn1 /= {1}/add_mn_nat.
  move: 0 (m - 1) def_m => i k; rewrite -{1}(size_tuple t) => def_m.
  rewrite (drop_nth x0) /=; last by rewrite -def_m leq_addl.
  elim: k i (nth x0 t i) def_m => [|k IHk] i x /=.
    by rewrite add0n => ->; rewrite drop_size.
  rewrite addSnnS => def_m; rewrite -addSn leq_add2l -IHk //.
  by rewrite (drop_nth x0) // -def_m leq_addl.
pose sub_mn (t : m.-tuple 'I_(m + n)) i : In1 := inord (tnth t i - i).
exists (fun t => [tuple of map (sub_mn t) (ord_tuple m)]) => [t _ | t].
  apply: eq_from_tnth => i; apply: val_inj.
  by rewrite /sub_mn !(tnth_ord_tuple, tnth_map) addKn inord_val.
rewrite inE /= => inc_t; apply: eq_from_tnth => i; apply: val_inj.
rewrite tnth_map tnth_ord_tuple /= tnth_map tnth_ord_tuple.
suffices [le_i_ti le_ti_ni]: i <= tnth t i /\ tnth t i <= i + n.
  by rewrite /sub_mn inordK ?subnKC // ltnS leq_subLR.
pose y0 := tnth t i; rewrite (tnth_nth y0) -(nth_map _ (val i)) ?size_tuple //.
case def_e: (map _ _) => [|x e] /=; first by rewrite nth_nil ?leq_addr.
rewrite def_e in inc_t; split.
  case: {-2}i; rewrite /= -{1}(size_tuple t) -(size_map val) def_e.
  elim=> //= j IHj lt_j_t; apply: leq_trans (pathP (val i) inc_t _ lt_j_t).
  by rewrite ltnS IHj 1?ltnW.
move: (_ - _) (subnK (valP i)) => k /=.
elim: k {-2}(val i) => /= [|k IHk] j def_m; rewrite -ltnS -addSn.
  by rewrite [j.+1]def_m -def_e (nth_map y0) ?ltn_ord // size_tuple -def_m.
rewrite (leq_trans _ (IHk _ _)) -1?addSnnS //; apply: (pathP _ inc_t).
rewrite -ltnS (leq_trans (leq_addl k _)) // -addSnnS def_m.
by rewrite -(size_tuple t) -(size_map val) def_e.
Qed.

Lemma card_partial_ord_partitions m n :
  #|[set t : m.-tuple 'I_n.+1 | \sum_(i <- t) i <= n]| = 'C(m + n, m).
Proof.
symmetry; set In1 := 'I_n.+1; pose x0 : In1 := ord0. 
pose add_mn (i j : In1) : In1 := inord (i + j).
pose f_add (t : m.-tuple In1) := [tuple of scanl add_mn x0 t].
rewrite -card_sorted_tuples -!sum1dep_card (reindex f_add) /=.
  apply: eq_bigl => t; rewrite -[\sum_(i <- t) i]add0n.
  transitivity (path leq x0 (map val (f_add t))) => /=; first by case: map.
  rewrite -{1 2}[0]/(val x0); elim: {t}(val t) (x0) => /= [|x t IHt] s.
    by rewrite big_nil addn0 -ltnS ltn_ord.
  rewrite big_cons addnA IHt /= val_insubd ltnS.
  have [_ | ltn_n_sx] := leqP (s + x) n; first by rewrite leq_addr.
  rewrite -(leq_add2r x) leqNgt (leq_trans (valP x)) //=.
  by rewrite leqNgt (leq_trans ltn_n_sx) ?leq_addr.
pose sub_mn (i j : In1) := Ordinal (leq_ltn_trans (leq_subr i j) (valP j)).
exists (fun t : m.-tuple In1 => [tuple of pairmap sub_mn x0 t]) => /= t inc_t.
  apply: val_inj => /=; have{inc_t}: path leq x0 (map val (f_add t)).
    by move: inc_t; rewrite inE /=; case: map.
  rewrite [map _ _]/=; elim: {t}(val t) (x0) => //= x t IHt s.
  case/andP=> le_s_sx /IHt->; congr (_ :: _); apply: val_inj => /=.
  move: le_s_sx; rewrite val_insubd.
  case le_sx_n: (_ < n.+1); first by rewrite addKn.
  by case: (val s) le_sx_n; rewrite ?ltn_ord.
apply: val_inj => /=; have{inc_t}: path leq x0 (map val t).
  by move: inc_t; rewrite inE /=; case: map.
elim: {t}(val t) (x0) => //= x t IHt s /andP[le_s_sx inc_t].
suffices ->: add_mn s (sub_mn s x) = x by rewrite IHt.
by apply: val_inj; rewrite /add_mn /= subnKC ?inord_val.
Qed.

Lemma card_ord_partitions m n :
  #|[set t : m.+1.-tuple 'I_n.+1 | \sum_(i <- t) i == n]| = 'C(m + n, m).
Proof.
symmetry; set In1 := 'I_n.+1; pose x0 : In1 := ord0. 
pose f_add (t : m.-tuple In1) := [tuple of sub_ord (\sum_(x <- t) x) :: t].
rewrite -card_partial_ord_partitions -!sum1dep_card (reindex f_add) /=.
  by apply: eq_bigl => t; rewrite big_cons /= addnC (sameP maxn_idPr eqP) maxnE.
exists (fun t : m.+1.-tuple In1 => [tuple of behead t]) => [t _|].
  exact: val_inj.
case/tupleP=> x t; rewrite inE /= big_cons => /eqP def_n.
by apply: val_inj; congr (_ :: _); apply: val_inj; rewrite /= -{1}def_n addnK.
Qed.

End Combinations.

