(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(******************************************************************************)
(* This file deals with divisibility for natural numbers.                     *)
(* It contains the definitions of:                                            *)
(*      edivn m d   == the pair composed of the quotient and remainder        *)
(*                     of the Euclidean division of m by d.                   *)
(*          m %/ d  == quotient of m by d.                                    *)
(*          m %% d  == remainder of m by d.                                   *)
(*  m = n %[mod d]  <-> m equals n modulo d.                                  *)
(*  m == n %[mod d] <=> m equals n modulo d (boolean version).                *)
(*  m <> n %[mod d] <-> m differs from n modulo d.                            *)
(*  m != n %[mod d] <=> m differs from n modulo d (boolean version).          *)
(*           d %| m <=> d divides m.                                          *)
(*         gcdn m n == the GCD of m and n.                                    *)
(*        egcdn m n == the extended GCD of m and n.                           *)
(*         lcmn m n == the LCM of m and n.                                    *)
(*      coprime m n <=> m and n are coprime (:= gcdn m n == 1).               *)
(*  chinese m n r s == witness of the chinese remainder theorem.              *)
(* We adjoin an m to operator suffixes to indicate a nested %% (modn), as in  *)
(*   modnDml : m %% d + n = m + n %[mod d].                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Euclidean division *)

Definition edivn_rec d :=
  fix loop m q := if m - d is m'.+1 then loop m' q.+1 else (q, m).

Definition edivn m d := if d > 0 then edivn_rec d.-1 m 0 else (0, m).

CoInductive edivn_spec m d : nat * nat -> Type :=
  EdivnSpec q r of m = q * d + r & (d > 0) ==> (r < d) : edivn_spec m d (q, r).

Lemma edivnP m d : edivn_spec m d (edivn m d).
Proof.
rewrite -{1}[m]/(0 * d + m) /edivn; case: d => //= d.
elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //= le_mn.
have le_m'n: m - d <= n by rewrite (leq_trans (leq_subr d m)).
rewrite subn_if_gt; case: ltnP => [// | le_dm].
by rewrite -{1}(subnKC le_dm) -addSn addnA -mulSnr; exact: IHn.
Qed.

Lemma edivn_eq d q r : r < d -> edivn (q * d + r) d = (q, r).
Proof.
move=> lt_rd; have d_gt0: 0 < d by exact: leq_trans lt_rd.
case: edivnP lt_rd => q' r'; rewrite d_gt0 /=.
wlog: q q' r r' / q <= q' by case/orP: (leq_total q q'); last symmetry; eauto.
rewrite leq_eqVlt; case/predU1P => [-> /addnI-> |] //=.
rewrite -(leq_pmul2r d_gt0) => /leq_add lt_qr eq_qr _ /lt_qr {lt_qr}.
by rewrite addnS ltnNge mulSn -addnA eq_qr addnCA addnA leq_addr.
Qed.

Definition divn m d := (edivn m d).1.

Notation "m %/ d" := (divn m d) : nat_scope.

(* We redefine modn so that it is structurally decreasing. *)

Definition modn_rec d := fix loop m := if m - d is m'.+1 then loop m' else m.

Definition modn m d := if d > 0 then modn_rec d.-1 m else m.

Notation "m %% d" := (modn m d) : nat_scope.
Notation "m = n %[mod d ]" := (m %% d = n %% d) : nat_scope.
Notation "m == n %[mod d ]" := (m %% d == n %% d) : nat_scope.
Notation "m <> n %[mod d ]" := (m %% d <> n %% d) : nat_scope.
Notation "m != n %[mod d ]" := (m %% d != n %% d) : nat_scope.

Lemma modn_def m d : m %% d = (edivn m d).2.
Proof.
case: d => //= d; rewrite /modn /edivn /=.
elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=.
rewrite ltnS !subn_if_gt; case: (d <= m) => // le_mn.
by apply: IHn; apply: leq_trans le_mn; exact: leq_subr.
Qed.

Lemma edivn_def m d : edivn m d = (m %/ d, m %% d).
Proof. by rewrite /divn modn_def; case: (edivn m d). Qed.

Lemma divn_eq m d : m = m %/ d * d + m %% d.
Proof. by rewrite /divn modn_def; case: edivnP. Qed.

Lemma div0n d : 0 %/ d = 0. Proof. by case: d. Qed.
Lemma divn0 m : m %/ 0 = 0. Proof. by []. Qed.
Lemma mod0n d : 0 %% d = 0. Proof. by case: d. Qed.
Lemma modn0 m : m %% 0 = m. Proof. by []. Qed.

Lemma divn_small m d : m < d -> m %/ d = 0.
Proof. by move=> lt_md; rewrite /divn (edivn_eq 0). Qed.

Lemma divnMDl q m d : 0 < d -> (q * d + m) %/ d = q + m %/ d.
Proof.
move=> d_gt0; rewrite {1}(divn_eq m d) addnA -mulnDl.
by rewrite /divn edivn_eq // modn_def; case: edivnP; rewrite d_gt0.
Qed.

Lemma mulnK m d : 0 < d -> m * d %/ d = m.
Proof. by move=> d_gt0; rewrite -[m * d]addn0 divnMDl // div0n addn0. Qed.

Lemma mulKn m d : 0 < d -> d * m %/ d = m.
Proof. by move=> d_gt0; rewrite mulnC mulnK. Qed.

Lemma expnB p m n : p > 0 -> m >= n -> p ^ (m - n) = p ^ m %/ p ^ n.
Proof.
by move=> p_gt0 /subnK{2}<-; rewrite expnD mulnK // expn_gt0 p_gt0.
Qed.

Lemma modn1 m : m %% 1 = 0.
Proof. by rewrite modn_def; case: edivnP => ? []. Qed.

Lemma divn1 m : m %/ 1 = m.
Proof. by rewrite {2}(@divn_eq m 1) // modn1 addn0 muln1. Qed.

Lemma divnn d : d %/ d = (0 < d).
Proof. by case: d => // d; rewrite -{1}[d.+1]muln1 mulKn. Qed.

Lemma divnMl p m d : p > 0 -> p * m %/ (p * d) = m %/ d.
Proof.
move=> p_gt0; case: (posnP d) => [-> | d_gt0]; first by rewrite muln0.
rewrite {2}/divn; case: edivnP; rewrite d_gt0 /= => q r ->{m} lt_rd.
rewrite mulnDr mulnCA divnMDl; last by rewrite muln_gt0 p_gt0.
by rewrite addnC divn_small // ltn_pmul2l.
Qed.
Implicit Arguments divnMl [p m d].

Lemma divnMr p m d : p > 0 -> m * p %/ (d * p) = m %/ d.
Proof. by move=> p_gt0; rewrite -!(mulnC p) divnMl. Qed.
Implicit Arguments divnMr [p m d].

Lemma ltn_mod m d : (m %% d < d) = (0 < d).
Proof. by case: d => // d; rewrite modn_def; case: edivnP. Qed.

Lemma ltn_pmod m d : 0 < d -> m %% d < d.
Proof. by rewrite ltn_mod. Qed.

Lemma leq_trunc_div m d : m %/ d * d <= m.
Proof. by rewrite {2}(divn_eq m d) leq_addr. Qed.

Lemma leq_mod m d : m %% d  <= m.
Proof. by rewrite {2}(divn_eq m d) leq_addl. Qed.

Lemma leq_div m d : m %/ d <= m.
Proof.
by case: d => // d; apply: leq_trans (leq_pmulr _ _) (leq_trunc_div _ _).
Qed.

Lemma ltn_ceil m d : 0 < d -> m < (m %/ d).+1 * d.
Proof.
by move=> d_gt0; rewrite {1}(divn_eq m d) -addnS mulSnr leq_add2l ltn_mod.
Qed.

Lemma ltn_divLR m n d : d > 0 -> (m %/ d < n) = (m < n * d).
Proof.
move=> d_gt0; apply/idP/idP.
  by rewrite -(leq_pmul2r d_gt0); apply: leq_trans (ltn_ceil _ _).
rewrite !ltnNge -(@leq_pmul2r d n) //; apply: contra => le_nd_floor.
exact: leq_trans le_nd_floor (leq_trunc_div _ _).
Qed.

Lemma leq_divRL m n d : d > 0 -> (m <= n %/ d) = (m * d <= n).
Proof. by move=> d_gt0; rewrite leqNgt ltn_divLR // -leqNgt. Qed.

Lemma ltn_Pdiv m d : 1 < d -> 0 < m -> m %/ d < m.
Proof. by move=> d_gt1 m_gt0; rewrite ltn_divLR ?ltn_Pmulr // ltnW. Qed.

Lemma divn_gt0 d m : 0 < d -> (0 < m %/ d) = (d <= m).
Proof. by move=> d_gt0; rewrite leq_divRL ?mul1n. Qed.

Lemma leq_div2r d m n : m <= n -> m %/ d <= n %/ d.
Proof.
have [-> //| d_gt0 le_mn] := posnP d.
by rewrite leq_divRL // (leq_trans _ le_mn) -?leq_divRL.
Qed.

Lemma leq_div2l m d e : 0 < d -> d <= e -> m %/ e <= m %/ d.
Proof.
move/leq_divRL=> -> le_de.
by apply: leq_trans (leq_trunc_div m e); apply: leq_mul.
Qed.

Lemma leq_divDl p m n : (m + n) %/ p <= m %/ p + n %/ p + 1.
Proof.
have [-> //| p_gt0] := posnP p; rewrite -ltnS -addnS ltn_divLR // ltnW //.
rewrite {1}(divn_eq n p) {1}(divn_eq m p) addnACA !mulnDl -3!addnS leq_add2l.
by rewrite mul2n -addnn -addSn leq_add // ltn_mod.
Qed.

Lemma geq_divBl k m p : k %/ p - m %/ p <= (k - m) %/ p + 1.
Proof.
rewrite leq_subLR addnA; apply: leq_trans (leq_divDl _ _ _).
by rewrite -maxnE leq_div2r ?leq_maxr.
Qed.

Lemma divnMA m n p : m %/ (n * p) = m %/ n %/ p. 
Proof.
case: n p => [|n] [|p]; rewrite ?muln0 ?div0n //.
rewrite {2}(divn_eq m (n.+1 * p.+1)) mulnA mulnAC !divnMDl //.
by rewrite [_ %/ p.+1]divn_small ?addn0 // ltn_divLR // mulnC ltn_mod.
Qed.

Lemma divnAC m n p : m %/ n %/ p =  m %/ p %/ n.
Proof. by rewrite -!divnMA mulnC. Qed.

Lemma modn_small m d : m < d -> m %% d = m.
Proof. by move=> lt_md; rewrite {2}(divn_eq m d) divn_small. Qed.

Lemma modn_mod m d : m %% d = m %[mod d].
Proof. by case: d => // d; apply: modn_small; rewrite ltn_mod. Qed.

Lemma modnMDl p m d : p * d + m = m %[mod d].
Proof.
case: (posnP d) => [-> | d_gt0]; first by rewrite muln0.
by rewrite {1}(divn_eq m d) addnA -mulnDl modn_def edivn_eq // ltn_mod.
Qed.

Lemma muln_modr {p m d} : 0 < p -> p * (m %% d) = (p * m) %% (p * d).
Proof.
move=> p_gt0; apply: (@addnI (p * (m %/ d * d))).
by rewrite -mulnDr -divn_eq mulnCA -(divnMl p_gt0) -divn_eq.
Qed.

Lemma muln_modl {p m d} : 0 < p -> (m %% d) * p = (m * p) %% (d * p).
Proof. by rewrite -!(mulnC p); apply: muln_modr. Qed.

Lemma modnDl m d : d + m = m %[mod d].
Proof. by rewrite -{1}[d]mul1n modnMDl. Qed.

Lemma modnDr m d : m + d = m %[mod d].
Proof. by rewrite addnC modnDl. Qed.

Lemma modnn d : d %% d = 0.
Proof. by rewrite -{1}[d]addn0 modnDl mod0n. Qed.

Lemma modnMl p d : p * d %% d = 0.
Proof. by rewrite -[p * d]addn0 modnMDl mod0n. Qed.

Lemma modnMr p d : d * p %% d = 0.
Proof. by rewrite mulnC modnMl. Qed.

Lemma modnDml m n d : m %% d + n = m + n %[mod d].
Proof. by rewrite {2}(divn_eq m d) -addnA modnMDl. Qed.

Lemma modnDmr m n d : m + n %% d = m + n %[mod d].
Proof. by rewrite !(addnC m) modnDml. Qed.

Lemma modnDm m n d : m %% d  + n %% d = m + n %[mod d].
Proof. by rewrite modnDml modnDmr. Qed.

Lemma eqn_modDl p m n d : (p + m == p + n %[mod d]) = (m == n %[mod d]).
Proof.
case: d => [|d]; first by rewrite !modn0 eqn_add2l.
apply/eqP/eqP=> eq_mn; last by rewrite -modnDmr eq_mn modnDmr.
rewrite -(modnMDl p m) -(modnMDl p n) !mulnSr -!addnA.
by rewrite -modnDmr eq_mn modnDmr.
Qed.

Lemma eqn_modDr p m n d : (m + p == n + p %[mod d]) = (m == n %[mod d]).
Proof. by rewrite -!(addnC p) eqn_modDl. Qed.

Lemma modnMml m n d : m %% d * n = m * n %[mod d].
Proof. by rewrite {2}(divn_eq m d) mulnDl mulnAC modnMDl. Qed.

Lemma modnMmr m n d : m * (n %% d) = m * n %[mod d].
Proof. by rewrite !(mulnC m) modnMml. Qed.

Lemma modnMm m n d : m %% d * (n %% d) = m * n %[mod d].
Proof. by rewrite modnMml modnMmr. Qed.

Lemma modn2 m : m %% 2 = odd m.
Proof. by elim: m => //= m IHm; rewrite -addn1 -modnDml IHm; case odd. Qed.

Lemma divn2 m : m %/ 2 = m./2.
Proof. by rewrite {2}(divn_eq m 2) modn2 muln2 addnC half_bit_double. Qed.

Lemma odd_mod m d : odd d = false -> odd (m %% d) = odd m.
Proof.
by move=> d_even; rewrite {2}(divn_eq m d) odd_add odd_mul d_even andbF.
Qed.

Lemma modnXm m n a : (a %% n) ^ m = a ^ m %[mod n].
Proof.
by elim: m => // m IHm; rewrite !expnS -modnMmr IHm modnMml modnMmr.
Qed.

(** Divisibility **)

Definition dvdn d m := m %% d == 0.

Notation "m %| d" := (dvdn m d) : nat_scope.

Lemma dvdnP d m : reflect (exists k, m = k * d) (d %| m).
Proof.
apply: (iffP eqP) => [md0 | [k ->]]; last by rewrite modnMl.
by exists (m %/ d); rewrite {1}(divn_eq m d) md0 addn0.
Qed.
Implicit Arguments dvdnP [d m].
Prenex Implicits dvdnP.

Lemma dvdn0 d : d %| 0.
Proof. by case: d. Qed.

Lemma dvd0n n : (0 %| n) = (n == 0).
Proof. by case: n. Qed.

Lemma dvdn1 d : (d %| 1) = (d == 1).
Proof. by case: d => [|[|d]] //; rewrite /dvdn modn_small. Qed.

Lemma dvd1n m : 1 %| m.
Proof. by rewrite /dvdn modn1. Qed.

Lemma dvdn_gt0 d m : m > 0 -> d %| m -> d > 0.
Proof. by case: d => // /prednK <-. Qed.

Lemma dvdnn m : m %| m.
Proof. by rewrite /dvdn modnn. Qed.

Lemma dvdn_mull d m n : d %| n -> d %| m * n.
Proof. by case/dvdnP=> n' ->; rewrite /dvdn mulnA modnMl. Qed.

Lemma dvdn_mulr d m n : d %| m -> d %| m * n.
Proof. by move=> d_m; rewrite mulnC dvdn_mull. Qed.
Hint Resolve dvdn0 dvd1n dvdnn dvdn_mull dvdn_mulr.

Lemma dvdn_mul d1 d2 m1 m2 : d1 %| m1 -> d2 %| m2 -> d1 * d2 %| m1 * m2.
Proof.
by move=> /dvdnP[q1 ->] /dvdnP[q2 ->]; rewrite mulnCA -mulnA 2?dvdn_mull.
Qed.

Lemma dvdn_trans n d m : d %| n -> n %| m -> d %| m.
Proof. by move=> d_dv_n /dvdnP[n1 ->]; exact: dvdn_mull. Qed.

Lemma dvdn_eq d m : (d %| m) = (m %/ d * d == m).
Proof.
apply/eqP/eqP=> [modm0 | <-]; last exact: modnMl.
by rewrite {2}(divn_eq m d) modm0 addn0.
Qed.

Lemma dvdn2 n : (2 %| n) = ~~ odd n.
Proof. by rewrite /dvdn modn2; case (odd n). Qed.

Lemma dvdn_odd m n : m %| n -> odd n -> odd m.
Proof.
by move=> m_dv_n; apply: contraTT; rewrite -!dvdn2 => /dvdn_trans->.
Qed.

Lemma divnK d m : d %| m -> m %/ d * d = m.
Proof. by rewrite dvdn_eq; move/eqP. Qed.

Lemma leq_divLR d m n : d %| m -> (m %/ d <= n) = (m <= n * d).
Proof. by case: d m => [|d] [|m] ///divnK=> {2}<-; rewrite leq_pmul2r. Qed.

Lemma ltn_divRL d m n : d %| m -> (n < m %/ d) = (n * d < m).
Proof. by move=> dv_d_m; rewrite !ltnNge leq_divLR. Qed.

Lemma eqn_div d m n : d > 0 -> d %| m -> (n == m %/ d) = (n * d == m).
Proof. by move=> d_gt0 dv_d_m; rewrite -(eqn_pmul2r d_gt0) divnK. Qed.

Lemma eqn_mul d m n : d > 0 -> d %| m -> (m == n * d) = (m %/ d == n).
Proof. by move=> d_gt0 dv_d_m; rewrite eq_sym -eqn_div // eq_sym. Qed.

Lemma divn_mulAC d m n : d %| m -> m %/ d * n = m * n %/ d.
Proof.
case: d m => [[] //| d m] dv_d_m; apply/eqP.
by rewrite eqn_div ?dvdn_mulr // mulnAC divnK.
Qed.

Lemma muln_divA d m n : d %| n -> m * (n %/ d) = m * n %/ d.
Proof. by move=> dv_d_m; rewrite !(mulnC m) divn_mulAC. Qed.

Lemma muln_divCA d m n : d %| m -> d %| n -> m * (n %/ d) = n * (m %/ d).
Proof. by move=> dv_d_m dv_d_n; rewrite mulnC divn_mulAC ?muln_divA. Qed.

Lemma divnA m n p : p %| n -> m %/ (n %/ p) = m * p %/ n.
Proof. by case: p => [|p] dv_n; rewrite -{2}(divnK dv_n) // divnMr. Qed.

Lemma modn_dvdm m n d : d %| m -> n %% m = n %[mod d].
Proof.
by case/dvdnP=> q def_m; rewrite {2}(divn_eq n m) {3}def_m mulnA modnMDl.
Qed.

Lemma dvdn_leq d m : 0 < m -> d %| m -> d <= m.
Proof. by move=> m_gt0 /dvdnP[[|k] Dm]; rewrite Dm // leq_addr in m_gt0 *. Qed.

Lemma gtnNdvd n d : 0 < n -> n < d -> (d %| n) = false.
Proof. by move=> n_gt0 lt_nd; rewrite /dvdn eqn0Ngt modn_small ?n_gt0. Qed.

Lemma eqn_dvd m n : (m == n) = (m %| n) && (n %| m).
Proof.
case: m n => [|m] [|n] //; apply/idP/andP; first by move/eqP->; auto.
rewrite eqn_leq => [[Hmn Hnm]]; apply/andP; have:= dvdn_leq; auto.
Qed.

Lemma dvdn_pmul2l p d m : 0 < p -> (p * d %| p * m) = (d %| m).
Proof. by case: p => // p _; rewrite /dvdn -muln_modr // muln_eq0. Qed.
Implicit Arguments dvdn_pmul2l [p m d].

Lemma dvdn_pmul2r p d m : 0 < p -> (d * p %| m * p) = (d %| m).
Proof. by move=> p_gt0; rewrite -!(mulnC p) dvdn_pmul2l. Qed.
Implicit Arguments dvdn_pmul2r [p m d].

Lemma dvdn_divLR p d m : 0 < p -> p %| d -> (d %/ p %| m) = (d %| m * p).
Proof. by move=> /(@dvdn_pmul2r p _ m) <- /divnK->. Qed.

Lemma dvdn_divRL p d m : p %| m -> (d %| m %/ p) = (d * p %| m).
Proof.
have [-> | /(@dvdn_pmul2r p d) <- /divnK-> //] := posnP p.
by rewrite divn0 muln0 dvdn0.
Qed.

Lemma dvdn_div d m : d %| m -> m %/ d %| m.
Proof. by move/divnK=> {2}<-; apply: dvdn_mulr. Qed.

Lemma dvdn_exp2l p m n : m <= n -> p ^ m %| p ^ n.
Proof. by move/subnK <-; rewrite expnD dvdn_mull. Qed.

Lemma dvdn_Pexp2l p m n : p > 1 -> (p ^ m %| p ^ n) = (m <= n).
Proof.
move=> p_gt1; case: leqP => [|gt_n_m]; first exact: dvdn_exp2l.
by rewrite gtnNdvd ?ltn_exp2l ?expn_gt0 // ltnW.
Qed.

Lemma dvdn_exp2r m n k : m %| n -> m ^ k %| n ^ k.
Proof. by case/dvdnP=> q ->; rewrite expnMn dvdn_mull. Qed.

Lemma dvdn_addr m d n : d %| m -> (d %| m + n) = (d %| n).
Proof. by case/dvdnP=> q ->; rewrite /dvdn modnMDl. Qed.

Lemma dvdn_addl n d m : d %| n -> (d %| m + n) = (d %| m).
Proof. by rewrite addnC; exact: dvdn_addr. Qed.

Lemma dvdn_add d m n : d %| m -> d %| n -> d %| m + n.
Proof. by move/dvdn_addr->. Qed.

Lemma dvdn_add_eq d m n : d %| m + n -> (d %| m) = (d %| n).
Proof. by move=> dv_d_mn; apply/idP/idP => [/dvdn_addr | /dvdn_addl] <-. Qed.

Lemma dvdn_subr d m n : n <= m -> d %| m -> (d %| m - n) = (d %| n).
Proof. by move=> le_n_m dv_d_m; apply: dvdn_add_eq; rewrite subnK. Qed.

Lemma dvdn_subl d m n : n <= m -> d %| n -> (d %| m - n) = (d %| m).
Proof. by move=> le_n_m dv_d_m; rewrite -(dvdn_addl _ dv_d_m) subnK. Qed.

Lemma dvdn_sub d m n : d %| m -> d %| n -> d %| m - n.
Proof.
by case: (leqP n m) => [le_nm /dvdn_subr <- // | /ltnW/eqnP ->]; rewrite dvdn0.
Qed.

Lemma dvdn_exp k d m : 0 < k -> d %| m -> d %| (m ^ k).
Proof. by case: k => // k _ d_dv_m; rewrite expnS dvdn_mulr. Qed.

Hint Resolve dvdn_add dvdn_sub dvdn_exp.

Lemma eqn_mod_dvd d m n : n <= m -> (m == n %[mod d]) = (d %| m - n).
Proof.
by move=> le_mn; rewrite -{1}[n]add0n -{1}(subnK le_mn) eqn_modDr mod0n.
Qed.

Lemma divnDl m n d : d %| m -> (m + n) %/ d = m %/ d + n %/ d.
Proof. by case: d => // d /divnK{1}<-; rewrite divnMDl. Qed.

Lemma divnDr m n d : d %| n -> (m + n) %/ d = m %/ d + n %/ d.
Proof. by move=> dv_n; rewrite addnC divnDl // addnC. Qed.

(***********************************************************************)
(*   A function that computes the gcd of 2 numbers                     *)
(***********************************************************************)

Fixpoint gcdn_rec m n :=
  let n' := n %% m in if n' is 0 then m else
  if m - n'.-1 is m'.+1 then gcdn_rec (m' %% n') n' else n'.

Definition gcdn := nosimpl gcdn_rec.

Lemma gcdnE m n : gcdn m n = if m == 0 then n else gcdn (n %% m) m.
Proof.
rewrite /gcdn; elim: m {-2}m (leqnn m) n => [|s IHs] [|m] le_ms [|n] //=.
case def_n': (_ %% _) => // [n'].
have{def_n'} lt_n'm: n' < m by rewrite -def_n' -ltnS ltn_pmod.
rewrite {}IHs ?(leq_trans lt_n'm) // subn_if_gt ltnW //=; congr gcdn_rec.
by rewrite -{2}(subnK (ltnW lt_n'm)) -addnS modnDr.
Qed.

Lemma gcdnn : idempotent gcdn.
Proof. by case=> // n; rewrite gcdnE modnn. Qed.

Lemma gcdnC : commutative gcdn.
Proof.
move=> m n; wlog lt_nm: m n / n < m.
  by case: (ltngtP n m) => [||-> //]; last symmetry; auto.
by rewrite gcdnE -{1}(ltn_predK lt_nm) modn_small.
Qed.

Lemma gcd0n : left_id 0 gcdn. Proof. by case. Qed.
Lemma gcdn0 : right_id 0 gcdn. Proof. by case. Qed.

Lemma gcd1n : left_zero 1 gcdn.
Proof. by move=> n; rewrite gcdnE modn1. Qed.

Lemma gcdn1 : right_zero 1 gcdn.
Proof. by move=> n; rewrite gcdnC gcd1n. Qed.

Lemma dvdn_gcdr m n : gcdn m n %| n.
Proof.
elim: m {-2}m (leqnn m) n => [|s IHs] [|m] le_ms [|n] //.
rewrite gcdnE; case def_n': (_ %% _) => [|n']; first by rewrite /dvdn def_n'.
have lt_n's: n' < s by rewrite -ltnS (leq_trans _ le_ms) // -def_n' ltn_pmod.
rewrite /= (divn_eq n.+1 m.+1) def_n' dvdn_addr ?dvdn_mull //; last exact: IHs.
by rewrite gcdnE /= IHs // (leq_trans _ lt_n's) // ltnW // ltn_pmod.
Qed.

Lemma dvdn_gcdl m n : gcdn m n %| m.
Proof. by rewrite gcdnC dvdn_gcdr. Qed.

Lemma gcdn_gt0 m n : (0 < gcdn m n) = (0 < m) || (0 < n).
Proof.
by case: m n => [|m] [|n] //; apply: (@dvdn_gt0 _ m.+1) => //; exact: dvdn_gcdl.
Qed.

Lemma gcdnMDl k m n : gcdn m (k * m + n) = gcdn m n.
Proof. by rewrite !(gcdnE m) modnMDl mulnC; case: m. Qed.

Lemma gcdnDl m n : gcdn m (m + n) = gcdn m n.
Proof. by rewrite -{2}(mul1n m) gcdnMDl. Qed.

Lemma gcdnDr m n : gcdn m (n + m) = gcdn m n.
Proof. by rewrite addnC gcdnDl. Qed.

Lemma gcdnMl n m : gcdn n (m * n) = n.
Proof. by case: n => [|n]; rewrite gcdnE modnMl gcd0n. Qed.

Lemma gcdnMr n m : gcdn n (n * m) = n.
Proof. by rewrite mulnC gcdnMl. Qed.

Lemma gcdn_idPl {m n} : reflect (gcdn m n = m) (m %| n).
Proof.
by apply: (iffP idP) => [/dvdnP[q ->] | <-]; rewrite (gcdnMl, dvdn_gcdr).
Qed.

Lemma gcdn_idPr {m n} : reflect (gcdn m n = n) (n %| m).
Proof. by rewrite gcdnC; apply: gcdn_idPl. Qed.

Lemma expn_min e m n : e ^ minn m n = gcdn (e ^ m) (e ^ n).
Proof.
rewrite /minn; case: leqP; [rewrite gcdnC | move/ltnW];
  by move/(dvdn_exp2l e)/gcdn_idPl.
Qed.

Lemma gcdn_modr m n : gcdn m (n %% m) = gcdn m n.
Proof. by rewrite {2}(divn_eq n m) gcdnMDl. Qed.

Lemma gcdn_modl m n : gcdn (m %% n) n = gcdn m n.
Proof. by rewrite !(gcdnC _ n) gcdn_modr. Qed.

(* Extended gcd, which computes Bezout coefficients. *)

Fixpoint Bezout_rec km kn qs :=
  if qs is q :: qs' then Bezout_rec kn (NatTrec.add_mul q kn km) qs'
  else (km, kn).

Fixpoint egcdn_rec m n s qs :=
  if s is s'.+1 then
    let: (q, r) := edivn m n in
    if r > 0 then egcdn_rec n r s' (q :: qs) else
    if odd (size qs) then qs else q.-1 :: qs
  else [::0].

Definition egcdn m n := Bezout_rec 0 1 (egcdn_rec m n n [::]).

CoInductive egcdn_spec m n : nat * nat -> Type :=
  EgcdnSpec km kn of km * m = kn * n + gcdn m n & kn * gcdn m n < m :
    egcdn_spec m n (km, kn).

Lemma egcd0n n : egcdn 0 n = (1, 0).
Proof. by case: n. Qed.

Lemma egcdnP m n : m > 0 -> egcdn_spec m n (egcdn m n).
Proof.
rewrite /egcdn; have: (n, m) = Bezout_rec n m [::] by [].
case: (posnP n) => [-> /=|]; first by split; rewrite // mul1n gcdn0.
move: {2 6}n {4 6}n {1 4}m [::] (ltnSn n) => s n0 m0.
elim: s n m => [[]//|s IHs] n m qs /= le_ns n_gt0 def_mn0 m_gt0.
case: edivnP => q r def_m; rewrite n_gt0 /= => lt_rn.
case: posnP => [r0 {s le_ns IHs lt_rn}|r_gt0]; last first.
  by apply: IHs => //=; [rewrite (leq_trans lt_rn) | rewrite natTrecE -def_m].
rewrite {r}r0 addn0 in def_m; set b := odd _; pose d := gcdn m n.
pose km := ~~ b : nat; pose kn := if b then 1 else q.-1.
rewrite (_ : Bezout_rec _ _ _ = Bezout_rec km kn qs); last first.
  by rewrite /kn /km; case: (b) => //=; rewrite natTrecE addn0 muln1.
have def_d: d = n by rewrite /d def_m gcdnC gcdnE modnMl gcd0n -[n]prednK.
have: km * m + 2 * b * d = kn * n + d.
  rewrite {}/kn {}/km def_m def_d -mulSnr; case: b; rewrite //= addn0 mul1n.
  by rewrite prednK //; apply: dvdn_gt0 m_gt0 _; rewrite def_m dvdn_mulr.
have{def_m}: kn * d <= m.
  have q_gt0 : 0 < q by rewrite def_m muln_gt0 n_gt0 ?andbT in m_gt0.
  by rewrite /kn; case b; rewrite def_d def_m leq_pmul2r // leq_pred.
have{def_d}: km * d <= n by rewrite -[n]mul1n def_d leq_pmul2r // leq_b1.
move: km {q}kn m_gt0 n_gt0 def_mn0; rewrite {}/d {}/b.
elim: qs m n => [|q qs IHq] n r kn kr n_gt0 r_gt0 /=.
  case=> -> -> {m0 n0}; rewrite !addn0 => le_kn_r _ def_d; split=> //.
  have d_gt0: 0 < gcdn n r by rewrite gcdn_gt0 n_gt0.
  have: 0 < kn * n by rewrite def_d addn_gt0 d_gt0 orbT.
  rewrite muln_gt0 n_gt0 andbT; move/ltn_pmul2l <-.
  by rewrite def_d -addn1 leq_add // mulnCA leq_mul2l le_kn_r orbT.
rewrite !natTrecE; set m:= _ + r; set km := _ * _ + kn; pose d := gcdn m n.
have ->: gcdn n r = d by rewrite [d]gcdnC gcdnMDl.
have m_gt0: 0 < m by rewrite addn_gt0 r_gt0 orbT.
have d_gt0: 0 < d by rewrite gcdn_gt0 m_gt0.
move/IHq=> {IHq} IHq le_kn_r le_kr_n def_d; apply: IHq => //; rewrite -/d.
  by rewrite mulnDl leq_add // -mulnA leq_mul2l le_kr_n orbT.
apply: (@addIn d); rewrite -!addnA addnn addnCA mulnDr -addnA addnCA.
rewrite /km mulnDl mulnCA mulnA -addnA; congr (_ + _).
by rewrite -def_d addnC -addnA -mulnDl -mulnDr addn_negb -mul2n.
Qed.

Lemma Bezoutl m n : m > 0 -> {a | a < m & m %| gcdn m n + a * n}.
Proof.
move=> m_gt0; case: (egcdnP n m_gt0) => km kn def_d lt_kn_m.
exists kn; last by rewrite addnC -def_d dvdn_mull.
apply: leq_ltn_trans lt_kn_m.
by rewrite -{1}[kn]muln1 leq_mul2l gcdn_gt0 m_gt0 orbT.
Qed.

Lemma Bezoutr m n : n > 0 -> {a | a < n & n %| gcdn m n + a * m}.
Proof. by rewrite gcdnC; exact: Bezoutl. Qed.

(* Back to the gcd. *)

Lemma dvdn_gcd p m n : p %| gcdn m n = (p %| m) && (p %| n).
Proof.
apply/idP/andP=> [dv_pmn | [dv_pm dv_pn]].
  by rewrite !(dvdn_trans dv_pmn) ?dvdn_gcdl ?dvdn_gcdr.
case (posnP n) => [->|n_gt0]; first by rewrite gcdn0.
case: (Bezoutr m n_gt0) => // km _ /(dvdn_trans dv_pn).
by rewrite dvdn_addl // dvdn_mull.
Qed.

Lemma gcdnAC : right_commutative gcdn.
Proof.
suffices dvd m n p: gcdn (gcdn m n) p %| gcdn (gcdn m p) n.
  by move=> m n p; apply/eqP; rewrite eqn_dvd !dvd.
rewrite !dvdn_gcd dvdn_gcdr.
by rewrite !(dvdn_trans (dvdn_gcdl _ p)) ?dvdn_gcdl ?dvdn_gcdr.
Qed.

Lemma gcdnA : associative gcdn.
Proof. by move=> m n p; rewrite !(gcdnC m) gcdnAC. Qed.

Lemma gcdnCA : left_commutative gcdn.
Proof. by move=> m n p; rewrite !gcdnA (gcdnC m). Qed.

Lemma gcdnACA : interchange gcdn gcdn.
Proof. by move=> m n p q; rewrite -!gcdnA (gcdnCA n). Qed.

Lemma muln_gcdr : right_distributive muln gcdn.
Proof.
move=> p m n; case: (posnP p) => [-> //| p_gt0].
elim: {m}m.+1 {-2}m n (ltnSn m) => // s IHs m n; rewrite ltnS => le_ms.
rewrite gcdnE [rhs in _ = rhs]gcdnE muln_eq0 (gtn_eqF p_gt0) -muln_modr //=.
by case: posnP => // m_gt0; apply: IHs; apply: leq_trans le_ms; apply: ltn_pmod.
Qed.

Lemma muln_gcdl : left_distributive muln gcdn.
Proof. by move=> m n p; rewrite -!(mulnC p) muln_gcdr. Qed.

Lemma gcdn_def d m n :
    d %| m -> d %| n -> (forall d', d' %| m -> d' %| n -> d' %| d) ->
  gcdn m n = d.
Proof.
move=> dv_dm dv_dn gdv_d; apply/eqP.
by rewrite eqn_dvd dvdn_gcd dv_dm dv_dn gdv_d ?dvdn_gcdl ?dvdn_gcdr.
Qed.

Lemma muln_divCA_gcd n m : n * (m %/ gcdn n m)  = m * (n %/ gcdn n m).
Proof. by rewrite muln_divCA ?dvdn_gcdl ?dvdn_gcdr. Qed.

(* We derive the lcm directly. *)

Definition lcmn m n := m * n %/ gcdn m n.

Lemma lcmnC : commutative lcmn.
Proof. by move=> m n; rewrite /lcmn mulnC gcdnC. Qed.

Lemma lcm0n : left_zero 0 lcmn.  Proof. by move=> n; exact: div0n. Qed.
Lemma lcmn0 : right_zero 0 lcmn. Proof. by move=> n; rewrite lcmnC lcm0n. Qed.

Lemma lcm1n : left_id 1 lcmn.
Proof. by move=> n; rewrite /lcmn gcd1n mul1n divn1. Qed.

Lemma lcmn1 : right_id 1 lcmn.
Proof. by move=> n; rewrite lcmnC lcm1n. Qed.

Lemma muln_lcm_gcd m n : lcmn m n * gcdn m n = m * n.
Proof. by apply/eqP; rewrite divnK ?dvdn_mull ?dvdn_gcdr. Qed.

Lemma lcmn_gt0 m n : (0 < lcmn m n) = (0 < m) && (0 < n).
Proof. by rewrite -muln_gt0 ltn_divRL ?dvdn_mull ?dvdn_gcdr. Qed.

Lemma muln_lcmr : right_distributive muln lcmn.
Proof.
case=> // m n p; rewrite /lcmn -muln_gcdr -!mulnA divnMl // mulnCA.
by rewrite muln_divA ?dvdn_mull ?dvdn_gcdr.
Qed.

Lemma muln_lcml : left_distributive muln lcmn.
Proof. by move=> m n p; rewrite -!(mulnC p) muln_lcmr. Qed.

Lemma lcmnA : associative lcmn.
Proof.
move=> m n p; rewrite {1 3}/lcmn mulnC !divn_mulAC ?dvdn_mull ?dvdn_gcdr //.
rewrite -!divnMA ?dvdn_mulr ?dvdn_gcdl // mulnC mulnA !muln_gcdr.
by rewrite ![_ * lcmn _ _]mulnC !muln_lcm_gcd !muln_gcdl -!(mulnC m) gcdnA.
Qed.

Lemma lcmnCA : left_commutative lcmn.
Proof. by move=> m n p; rewrite !lcmnA (lcmnC m). Qed.

Lemma lcmnAC : right_commutative lcmn.
Proof. by move=> m n p; rewrite -!lcmnA (lcmnC n). Qed.

Lemma lcmnACA : interchange lcmn lcmn.
Proof. by move=> m n p q; rewrite -!lcmnA (lcmnCA n). Qed.

Lemma dvdn_lcml d1 d2 : d1 %| lcmn d1 d2.
Proof. by rewrite /lcmn -muln_divA ?dvdn_gcdr ?dvdn_mulr. Qed.

Lemma dvdn_lcmr d1 d2 : d2 %| lcmn d1 d2.
Proof. by rewrite lcmnC dvdn_lcml. Qed.

Lemma dvdn_lcm d1 d2 m : lcmn d1 d2 %| m = (d1 %| m) && (d2 %| m).
Proof.
case: d1 d2 => [|d1] [|d2]; try by case: m => [|m]; rewrite ?lcmn0 ?andbF.
rewrite -(@dvdn_pmul2r (gcdn d1.+1 d2.+1)) ?gcdn_gt0 // muln_lcm_gcd.
by rewrite muln_gcdr dvdn_gcd {1}mulnC andbC !dvdn_pmul2r.
Qed.

Lemma lcmnMl m n : lcmn m (m * n) = m * n.
Proof. by case: m => // m; rewrite /lcmn gcdnMr mulKn. Qed.

Lemma lcmnMr m n : lcmn n (m * n) = m * n.
Proof. by rewrite mulnC lcmnMl. Qed.

Lemma lcmn_idPr {m n} : reflect (lcmn m n = n) (m %| n).
Proof.
by apply: (iffP idP) => [/dvdnP[q ->] | <-]; rewrite (lcmnMr, dvdn_lcml).
Qed.

Lemma lcmn_idPl {m n} : reflect (lcmn m n = m) (n %| m).
Proof. by rewrite lcmnC; apply: lcmn_idPr. Qed.

Lemma expn_max e m n : e ^ maxn m n = lcmn (e ^ m) (e ^ n).
Proof.
rewrite /maxn; case: leqP; [rewrite lcmnC | move/ltnW];
 by move/(dvdn_exp2l e)/lcmn_idPr.
Qed.

(* Coprime factors *)

Definition coprime m n := gcdn m n == 1.

Lemma coprime1n n : coprime 1 n.
Proof. by rewrite /coprime gcd1n. Qed.

Lemma coprimen1 n : coprime n 1.
Proof. by rewrite /coprime gcdn1. Qed.

Lemma coprime_sym m n : coprime m n = coprime n m.
Proof. by rewrite /coprime gcdnC. Qed.

Lemma coprime_modl m n : coprime (m %% n) n = coprime m n.
Proof. by rewrite /coprime gcdn_modl. Qed.

Lemma coprime_modr m n : coprime m (n %% m) = coprime m n.
Proof. by rewrite /coprime gcdn_modr. Qed.

Lemma coprime2n n : coprime 2 n = odd n.
Proof. by rewrite -coprime_modr modn2; case: (odd n). Qed.

Lemma coprimen2 n : coprime n 2 = odd n.
Proof. by rewrite coprime_sym coprime2n. Qed.

Lemma coprimeSn n : coprime n.+1 n.
Proof. by rewrite -coprime_modl (modnDr 1) coprime_modl coprime1n. Qed.

Lemma coprimenS n : coprime n n.+1.
Proof. by rewrite coprime_sym coprimeSn. Qed.

Lemma coprimePn n : n > 0 -> coprime n.-1 n.
Proof. by case: n => // n _; rewrite coprimenS. Qed.

Lemma coprimenP n : n > 0 -> coprime n n.-1.
Proof. by case: n => // n _; rewrite coprimeSn. Qed.

Lemma coprimeP n m :
  n > 0 -> reflect (exists u, u.1 * n - u.2 * m = 1) (coprime n m).
Proof.
move=> n_gt0; apply: (iffP eqP) => [<-| [[kn km] /= kn_km_1]].
  by have [kn km kg _] := egcdnP m n_gt0; exists (kn, km); rewrite kg addKn.
apply gcdn_def; rewrite ?dvd1n // => d dv_d_n dv_d_m.
by rewrite -kn_km_1 dvdn_subr ?dvdn_mull // ltnW // -subn_gt0 kn_km_1.
Qed.

Lemma modn_coprime k n : 0 < k -> (exists u, (k * u) %% n = 1) -> coprime k n.
Proof.
move=> k_gt0 [u Hu]; apply/coprimeP=> //.
by exists (u, k * u %/ n); rewrite /= mulnC {1}(divn_eq (k * u) n) addKn.
Qed.

Lemma Gauss_dvd m n p : coprime m n -> (m * n %| p) = (m %| p) && (n %| p).
Proof. by move=> co_mn; rewrite -muln_lcm_gcd (eqnP co_mn) muln1 dvdn_lcm. Qed.

Lemma Gauss_dvdr m n p : coprime m n -> (m %| n * p) = (m %| p).
Proof.
case: n => [|n] co_mn; first by case: m co_mn => [|[]] // _; rewrite !dvd1n.
by symmetry; rewrite mulnC -(@dvdn_pmul2r n.+1) ?Gauss_dvd // andbC dvdn_mull.
Qed.

Lemma Gauss_dvdl m n p : coprime m p -> (m %| n * p) = (m %| n).
Proof. by rewrite mulnC; apply: Gauss_dvdr. Qed.

Lemma Gauss_gcdr p m n : coprime p m -> gcdn p (m * n) = gcdn p n.
Proof.
move=> co_pm; apply/eqP; rewrite eqn_dvd !dvdn_gcd !dvdn_gcdl /=.
rewrite andbC dvdn_mull ?dvdn_gcdr //= -(@Gauss_dvdr _ m) ?dvdn_gcdr //.
by rewrite /coprime gcdnAC (eqnP co_pm) gcd1n.
Qed.

Lemma Gauss_gcdl p m n : coprime p n -> gcdn p (m * n) = gcdn p m.
Proof. by move=> co_pn; rewrite mulnC Gauss_gcdr. Qed.

Lemma coprime_mulr p m n : coprime p (m * n) = coprime p m && coprime p n.
Proof.
case co_pm: (coprime p m) => /=; first by rewrite /coprime Gauss_gcdr.
apply/eqP=> co_p_mn; case/eqnP: co_pm; apply gcdn_def => // d dv_dp dv_dm.
by rewrite -co_p_mn dvdn_gcd dv_dp dvdn_mulr.
Qed.

Lemma coprime_mull p m n : coprime (m * n) p = coprime m p && coprime n p.
Proof. by rewrite -!(coprime_sym p) coprime_mulr. Qed.

Lemma coprime_pexpl k m n : 0 < k -> coprime (m ^ k) n = coprime m n.
Proof.
case: k => // k _; elim: k => [|k IHk]; first by rewrite expn1.
by rewrite expnS coprime_mull -IHk; case coprime.
Qed.

Lemma coprime_pexpr k m n : 0 < k -> coprime m (n ^ k) = coprime m n.
Proof. by move=> k_gt0; rewrite !(coprime_sym m) coprime_pexpl. Qed.

Lemma coprime_expl k m n : coprime m n -> coprime (m ^ k) n.
Proof. by case: k => [|k] co_pm; rewrite ?coprime1n // coprime_pexpl. Qed.

Lemma coprime_expr k m n : coprime m n -> coprime m (n ^ k).
Proof. by rewrite !(coprime_sym m); exact: coprime_expl. Qed.

Lemma coprime_dvdl m n p : m %| n -> coprime n p -> coprime m p.
Proof. by case/dvdnP=> d ->; rewrite coprime_mull => /andP[]. Qed.

Lemma coprime_dvdr m n p : m %| n -> coprime p n -> coprime p m.
Proof. by rewrite !(coprime_sym p); exact: coprime_dvdl. Qed.

Lemma coprime_egcdn n m : n > 0 -> coprime (egcdn n m).1 (egcdn n m).2.
Proof.
move=> n_gt0; case: (egcdnP m n_gt0) => kn km /= /eqP.
have [/dvdnP[u defn] /dvdnP[v defm]] := (dvdn_gcdl n m, dvdn_gcdr n m).
rewrite -[gcdn n m]mul1n {1}defm {1}defn !mulnA -mulnDl addnC.
rewrite eqn_pmul2r ?gcdn_gt0 ?n_gt0 //; case: kn => // kn /eqP def_knu _.
by apply/coprimeP=> //; exists (u, v); rewrite mulnC def_knu mulnC addnK.
Qed.

Lemma dvdn_pexp2r m n k : k > 0 -> (m ^ k %| n ^ k) = (m %| n).
Proof.
move=> k_gt0; apply/idP/idP=> [dv_mn_k|]; last exact: dvdn_exp2r.
case: (posnP n) => [-> | n_gt0]; first by rewrite dvdn0.
have [n' def_n] := dvdnP (dvdn_gcdr m n); set d := gcdn m n in def_n.
have [m' def_m] := dvdnP (dvdn_gcdl m n); rewrite -/d in def_m.
have d_gt0: d > 0 by rewrite gcdn_gt0 n_gt0 orbT.
rewrite def_m def_n !expnMn dvdn_pmul2r ?expn_gt0 ?d_gt0 // in dv_mn_k.
have: coprime (m' ^ k) (n' ^ k).
  rewrite coprime_pexpl // coprime_pexpr // /coprime -(eqn_pmul2r d_gt0) mul1n.
  by rewrite muln_gcdl -def_m -def_n.
rewrite /coprime -gcdn_modr (eqnP dv_mn_k) gcdn0 -(exp1n k).
by rewrite (inj_eq (expIn k_gt0)) def_m; move/eqP->; rewrite mul1n dvdn_gcdr.
Qed.

Section Chinese.

(***********************************************************************)
(*   The chinese remainder theorem                                     *)
(***********************************************************************)

Variables m1 m2 : nat.
Hypothesis co_m12 : coprime m1 m2.

Lemma chinese_remainder x y :
  (x == y %[mod m1 * m2]) = (x == y %[mod m1]) && (x == y %[mod m2]).
Proof.
wlog le_yx : x y / y <= x; last by rewrite !eqn_mod_dvd // Gauss_dvd.
by case/orP: (leq_total y x); last rewrite !(eq_sym (x %% _)); auto.
Qed.

(***********************************************************************)
(*   A function that solves the chinese remainder problem              *)
(***********************************************************************)

Definition chinese r1 r2 :=
  r1 * m2 * (egcdn m2 m1).1 + r2 * m1 * (egcdn m1 m2).1.

Lemma chinese_modl r1 r2 : chinese r1 r2 = r1 %[mod m1].
Proof.
rewrite /chinese; case: (posnP m2) co_m12 => [-> /eqnP | m2_gt0 _].
  by rewrite gcdn0 => ->; rewrite !modn1.
case: egcdnP => // k2 k1 def_m1 _.
rewrite mulnAC -mulnA def_m1 gcdnC (eqnP co_m12) mulnDr mulnA muln1.
by rewrite addnAC (mulnAC _ m1) -mulnDl modnMDl.
Qed.

Lemma chinese_modr r1 r2 : chinese r1 r2 = r2 %[mod m2].
Proof.
rewrite /chinese; case: (posnP m1) co_m12 => [-> /eqnP | m1_gt0 _].
  by rewrite gcd0n => ->; rewrite !modn1.
case: (egcdnP m2) => // k1 k2 def_m2 _.
rewrite addnC mulnAC -mulnA def_m2 (eqnP co_m12) mulnDr mulnA muln1.
by rewrite addnAC (mulnAC _ m2) -mulnDl modnMDl.
Qed.

Lemma chinese_mod x : x = chinese (x %% m1) (x %% m2) %[mod m1 * m2].
Proof.
apply/eqP; rewrite chinese_remainder //.
by rewrite chinese_modl chinese_modr !modn_mod !eqxx.
Qed.

End Chinese.
