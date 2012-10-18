(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype.
(* Require Import BinNat.*)
(* Require BinPos Ndec. *)
(* Require Export Ring. *)
Require Peano.
(******************************************************************************)
(* A version of arithmetic on nat (natural numbers) that is better suited to  *)
(* small scale reflection than the Coq Arith library. It contains an          *)
(* extensive equational theory (including, e.g., the AGM inequality), as well *)
(* as support for the ring tactic, and congruence tactics.                    *)
(*   The following operations and notations are provided:                     *)
(*                                                                            *)
(*   successor and predecessor                                                *)
(*     n.+1, n.+2, n.+3, n.+4 and n.-1, n.-2                                  *)
(*     this frees the names "S" and "pred"                                    *)
(*                                                                            *)
(*   basic arithmetic                                                         *)
(*     m + n, m - n, m * n                                                    *)
(*   Important: m - n denotes TRUNCATED substraction: m - n = 0 if m <= n.    *)
(*   The definitions use the nosimpl tag to prevent undesirable computation   *)
(*   computation during simplification, but remain compatible with the ones   *)
(*   provided in the Coq.Init.Peano prelude.                                  *)
(*     For computation, a module NatTrec rebinds all arithmetic notations     *)
(*   to less convenient but also less inefficient tail-recursive functions;   *)
(*   the auxiliary functions used by these versions are flagged with %Nrec.   *)
(*     Also, there is support for input and output of large nat values.       *)
(*       Num 3 082 241 inputs the number 3082241                              *)
(*         [Num of n]  outputs the value n                                    *)
(*   There are coercions num >-> BinNat.N >-> nat; ssrnat rebinds the scope   *)
(*   delimter for BinNat.N to %num, as it uses the shorter %N for its own     *)
(*   notations (Peano notations are flagged with %coq_nat).                   *)
(*                                                                            *)
(*   doubling, halving, and parity                                            *)
(*      n.*2, n./2, odd n, uphalf n,  with uphalf n = n.+1./2                 *)
(*   bool coerces to nat so we can write, e.g., n = odd n + n./2.*2.          *)
(*                                                                            *)
(*   iteration                                                                *)
(*             iter n f x0  == f ( .. (f x0))                                 *)
(*             iteri n g x0 == g n.-1 (g ... (g 0 x0))                        *)
(*         iterop n op x x0 == op x (... op x x) (n x's) or x0 if n = 0       *)
(*                                                                            *)
(*   exponentiation, factorial                                                *)
(*        m ^ n, n`!                                                          *)
(*        m ^ 1 is convertible to m, and m ^ 2 to m * m                       *)
(*                                                                            *)
(*   comparison                                                               *)
(*      m <= n, m < n, m >= n, m > n, m == n, m <= n <= p, etc.,              *)
(*   comparisons are BOOLEAN operators, and m == n is the generic eqType      *)
(*   operation.                                                               *)
(*     Most compatibility lemmas are stated as boolean equalities; this keeps *)
(*   the size of the library down. All the inequalities refer to the same     *)
(*   constant "leq"; in particular m < n is identical to m.+1 <= n.           *)
(*                                                                            *)
(*   conditionally strict inequality `leqif'                                  *)
(*      m <= n ?= iff condition   ==   (m <= n) and ((m == n) = condition)    *)
(*   This is actually a pair of boolean equalities, so rewriting with an      *)
(*   `leqif' lemma can affect several kinds of comparison. The transitivity   *)
(*   lemma for leqif aggregates the conditions, allowing for arguments of     *)
(*   the form ``m <= n <= p <= m, so equality holds throughout''.             *)
(*                                                                            *)
(*   maximum and minimum                                                      *)
(*      maxn m n, minn m n                                                    *)
(*   Note that maxn m n = m + (m - n), due to the truncating subtraction.     *)
(*   Absolute difference (linear distance) between nats is defined in the int *)
(*   library (in the int.IntDist sublibrary), with the syntax `|m - n|. The   *)
(*   '-' in this notation is the signed integer difference.                   *)
(*                                                                            *)
(*   countable choice                                                         *)
(*     ex_minn : forall P : pred nat, (exists n, P n) -> nat                  *)
(*   This returns the smallest n such that P n holds.                         *)
(*     ex_maxn : forall (P : pred nat) m,                                     *)
(*        (exists n, P n) -> (forall n, P n -> n <= m) -> nat                 *)
(*   This returns the largest n such that P n holds (given an explicit upper  *)
(*   bound).                                                                  *)
(*                                                                            *)
(*  This file adds the following suffix conventions to those documented in    *)
(* ssrbool.v and eqtype.v:                                                    *)
(*   A (infix) -- conjunction, as in                                          *)
(*      ltn_neqAle : (m < n) = (m != n) && (m <= n).                          *)
(*   B -- subtraction, as in subBn : (m - n) - p = m - (n + p).               *)
(*   D -- addition, as in mulnDl : (m + n) * p = m * p + n * p.               *)
(*   M -- multiplication, as in expnMn : (m * n) ^ p = m ^ p * n ^ p.         *)
(*   p (prefix) -- positive, as in                                            *)
(*      eqn_pmul2l : m > 0 -> (m * n1 == m * n2) = (n1 == n2).                *)
(*   P  -- greater than 1, as in                                              *)
(*      ltn_Pmull : 1 < n -> 0 < m -> m < n * m.                              *)
(*   S -- successor, as in addSn : n.+1 + m = (n + m).+1.                     *)
(*   V (infix) -- disjunction, as in                                          *)
(*      leq_eqVlt : (m <= n) = (m == n) || (m < n).                           *)
(*   X - exponentiation, as in lognX : logn p (m ^ n) = logn p m * n in       *)
(*         file prime.v (the suffix is not used in ths file).                 *)
(* Suffixes that abreviate operations (D, B, M and X) are used to abbreviate  *)
(* second-rank operations in equational lemma names that describe left-hand   *)
(* sides (e.g., mulnDl); they are not used to abbreviate the main operation   *)
(* of relational lemmas (e.g., leq_add2l).                                    *)
(*   For the asymmetrical exponentiation operator expn (m ^ n) a right suffix *)
(* indicates an operation on the exponent, e.g., expnM : m ^ (n1 * n2) = ...; *)
(* a trailing "n" is used to indicate the left operand, e.g.,                 *)
(* expnMn : (m1 * m2) ^ n = ... The operands of other operators a selected    *)
(* using the l/r suffixes.                                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Declare legacy Arith operators in new scope. *)

Delimit Scope coq_nat_scope with coq_nat.

Notation "m + n" := (Peano.plus m n) : coq_nat_scope.
Notation "m - n" := (Peano.minus m n) : coq_nat_scope.
Notation "m * n" := (Peano.mult m n) : coq_nat_scope.
Notation "m <= n" := (Peano.le m n) : coq_nat_scope.
Notation "m < n" := (Peano.lt m n) : coq_nat_scope.
Notation "m >= n" := (Peano.ge m n) : coq_nat_scope.
Notation "m > n" := (Peano.gt m n) : coq_nat_scope.

(* Rebind scope delimiters, reserving a scope for the "recursive",     *)
(* i.e., unprotected version of operators.                             *)

Delimit Scope N_scope with num.
Delimit Scope nat_scope with N.
Delimit Scope nat_rec_scope with Nrec.

(* Postfix notation for the successor and predecessor functions.  *)
(* SSreflect uses "pred" for the generic predicate type, and S as *)
(* a local bound variable.                                        *)

Notation succn := Datatypes.S.
Notation predn := Peano.pred.

Notation "n .+1" := (succn n) (at level 2, left associativity,
  format "n .+1") : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2, left associativity,
  format "n .+2") : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2, left associativity,
  format "n .+3") : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2, left associativity,
  format "n .+4") : nat_scope.

Notation "n .-1" := (predn n) (at level 2, left associativity,
  format "n .-1") : nat_scope.
Notation "n .-2" := n.-1.-1 (at level 2, left associativity,
  format "n .-2") : nat_scope.

Lemma succnK : cancel succn predn. Proof. by []. Qed.
Lemma succn_inj : injective succn. Proof. by move=> n m []. Qed.

(* Predeclare postfix doubling/halving operators. *)

Reserved Notation "n .*2" (at level 2, format "n .*2").
Reserved Notation "n ./2" (at level 2, format "n ./2").

(* Canonical comparison and eqType for nat.                                *)

Fixpoint eqn m n {struct m} :=
  match m, n with
  | 0, 0 => true
  | m'.+1, n'.+1 => eqn m' n'
  | _, _ => false
  end.

Lemma eqnP : Equality.axiom eqn.
Proof.
move=> n m; apply: (iffP idP) => [|<-]; last by elim n.
by elim: n m => [|n IHn] [|m] //= /IHn->.
Qed.

Canonical nat_eqMixin := EqMixin eqnP.
Canonical nat_eqType := Eval hnf in EqType nat nat_eqMixin.

Implicit Arguments eqnP [x y].
Prenex Implicits eqnP.

Lemma eqnE : eqn = eq_op. Proof. by []. Qed.

Lemma eqSS m n : (m.+1 == n.+1) = (m == n). Proof. by []. Qed.

Lemma nat_irrelevance (x y : nat) (E E' : x = y) : E = E'.
Proof. exact: eq_irrelevance. Qed.

(* Protected addition, with a more systematic set of lemmas.                *)

Definition addn_rec := Peano.plus.
Notation "m + n" := (addn_rec m n) : nat_rec_scope.

Definition addn := nosimpl addn_rec.
Notation "m + n" := (addn m n) : nat_scope.

Lemma addnE : addn = addn_rec. Proof. by []. Qed.

Lemma plusE : Peano.plus = addn. Proof. by []. Qed.

Lemma add0n : left_id 0 addn.            Proof. by []. Qed.
Lemma addSn m n : m.+1 + n = (m + n).+1. Proof. by []. Qed.
Lemma add1n n : 1 + n = n.+1.            Proof. by []. Qed.

Lemma addn0 : right_id 0 addn. Proof. by move=> n; apply/eqP; elim: n. Qed.

Lemma addnS m n : m + n.+1 = (m + n).+1. Proof. by elim: m. Qed.

Lemma addSnnS m n : m.+1 + n = m + n.+1. Proof. by rewrite addnS. Qed.

Lemma addnCA : left_commutative addn.
Proof. by move=> m n p; elim: m => //= m; rewrite addnS => <-. Qed.

Lemma addnC : commutative addn.
Proof. by move=> m n; rewrite -{1}[n]addn0 addnCA addn0. Qed.

Lemma addn1 n : n + 1 = n.+1. Proof. by rewrite addnC. Qed.

Lemma addnA : associative addn.
Proof. by move=> m n p; rewrite (addnC n) addnCA addnC. Qed.

Lemma addnAC : right_commutative addn.
Proof. by move=> m n p; rewrite -!addnA (addnC n). Qed.

Lemma addnACA : interchange addn addn.
Proof. by move=> m n p q; rewrite -!addnA (addnCA n). Qed.

Lemma addn_eq0 m n : (m + n == 0) = (m == 0) && (n == 0).
Proof. by case: m; case: n. Qed.

Lemma eqn_add2l p m n : (p + m == p + n) = (m == n).
Proof. by elim: p. Qed.

Lemma eqn_add2r p m n : (m + p == n + p) = (m == n).
Proof. by rewrite -!(addnC p) eqn_add2l. Qed.

Lemma addnI : right_injective addn.
Proof. by move=> p m n Heq; apply: eqP; rewrite -(eqn_add2l p) Heq eqxx. Qed.

Lemma addIn : left_injective addn.
Proof. move=> p m n; rewrite -!(addnC p); apply addnI. Qed.

Lemma addn2 m : m + 2 = m.+2. Proof. by rewrite addnC. Qed.
Lemma add2n m : 2 + m = m.+2. Proof. by []. Qed.
Lemma addn3 m : m + 3 = m.+3. Proof. by rewrite addnC. Qed.
Lemma add3n m : 3 + m = m.+3. Proof. by []. Qed.
Lemma addn4 m : m + 4 = m.+4. Proof. by rewrite addnC. Qed.
Lemma add4n m : 4 + m = m.+4. Proof. by []. Qed.

(* Protected, structurally decreasing substraction, and basic lemmas. *)
(* Further properties depend on ordering conditions.                  *)

Definition subn_rec := Peano.minus.
Notation "m - n" := (subn_rec m n) : nat_rec_scope.

Definition subn := nosimpl subn_rec.
Notation "m - n" := (subn m n) : nat_scope.

Lemma subnE : subn = subn_rec. Proof. by []. Qed.
Lemma minusE : Peano.minus = subn.   Proof. by []. Qed.

Lemma sub0n : left_zero 0 subn.    Proof. by []. Qed.
Lemma subn0 : right_id 0 subn.   Proof. by case. Qed.
Lemma subnn : self_inverse 0 subn. Proof. by elim. Qed.

Lemma subSS n m : m.+1 - n.+1 = m - n. Proof. by []. Qed.
Lemma subn1 n : n - 1 = n.-1.          Proof. by case: n => [|[]]. Qed.
Lemma subn2 n : (n - 2)%N = n.-2.      Proof. by case: n => [|[|[]]]. Qed.

Lemma subnDl p m n : (p + m) - (p + n) = m - n.
Proof. by elim: p. Qed.

Lemma subnDr p m n : (m + p) - (n + p) = m - n.
Proof. by rewrite -!(addnC p) subnDl. Qed.

Lemma addKn n : cancel (addn n) (subn^~ n).
Proof. by move=> m; rewrite /= -{2}[n]addn0 subnDl subn0. Qed.

Lemma addnK n : cancel (addn^~ n) (subn^~ n).
Proof. by move=> m; rewrite /= (addnC m) addKn. Qed.

Lemma subSnn n : n.+1 - n = 1.
Proof. exact (addnK n 1). Qed.

Lemma subnDA m n p : n - (m + p) = (n - m) - p.
Proof. by elim: m n => [|m IHm] [|n]; try exact (IHm n). Qed.

Lemma subnAC : right_commutative subn.
Proof. by move=> m n p; rewrite -!subnDA addnC. Qed.

Lemma subnS m n : m - n.+1 = (m - n).-1.
Proof. by rewrite -addn1 subnDA subn1. Qed.

Lemma subSKn m n : (m.+1 - n).-1 = m - n.
Proof. by rewrite -subnS. Qed.

(* Integer ordering, and its interaction with the other operations.       *)

Definition leq m n := m - n == 0.

Notation "m <= n" := (leq m n) : nat_scope.
Notation "m < n"  := (m.+1 <= n) : nat_scope.
Notation "m >= n" := (n <= m) (only parsing) : nat_scope.
Notation "m > n"  := (n < m) (only parsing)  : nat_scope.

(* For sorting, etc. *)
Definition geq := [rel m n | m >= n].
Definition ltn := [rel m n | m < n].
Definition gtn := [rel m n | m > n].

Notation "m <= n <= p" := ((m <= n) && (n <= p)) : nat_scope.
Notation "m < n <= p" := ((m < n) && (n <= p)) : nat_scope.
Notation "m <= n < p" := ((m <= n) && (n < p)) : nat_scope.
Notation "m < n < p" := ((m < n) && (n < p)) : nat_scope.

Lemma ltnS m n : (m < n.+1) = (m <= n). Proof. by []. Qed.
Lemma leq0n n : 0 <= n.                 Proof. by []. Qed.
Lemma ltn0Sn n : 0 < n.+1.              Proof. by []. Qed.
Lemma ltn0 n : n < 0 = false.           Proof. by []. Qed.
Lemma leqnn n : n <= n.                 Proof. by elim: n. Qed.
Hint Resolve leqnn.
Lemma ltnSn n : n < n.+1.               Proof. by []. Qed.
Lemma eq_leq m n : m = n -> m <= n.     Proof. by move->. Qed.
Lemma leqnSn n : n <= n.+1.             Proof. by elim: n. Qed.
Hint Resolve leqnSn.
Lemma leq_pred n : n.-1 <= n.           Proof. by case: n => /=. Qed.
Lemma leqSpred n : n <= n.-1.+1.        Proof. by case: n => /=. Qed.

Lemma ltn_predK m n : m < n -> n.-1.+1 = n.
Proof. by case: n. Qed.

Lemma prednK n : 0 < n -> n.-1.+1 = n.
Proof. exact: ltn_predK. Qed.

Lemma leqNgt m n : (m <= n) = ~~ (n < m).
Proof. by elim: m n => [|m IHm] [|n] //; exact: IHm n. Qed.

Lemma ltnNge m n : (m < n) = ~~ (n <= m).
Proof. by rewrite leqNgt. Qed.

Lemma ltnn n : n < n = false.
Proof. by rewrite ltnNge leqnn. Qed.

Lemma leqn0 n : (n <= 0) = (n == 0).           Proof. by case: n. Qed.
Lemma lt0n n : (0 < n) = (n != 0).             Proof. by case: n. Qed.
Lemma lt0n_neq0 n : 0 < n -> n != 0.           Proof. by case: n. Qed.
Lemma eqn0Ngt n : (n == 0) = ~~ (n > 0).       Proof. by case: n. Qed.
Lemma neq0_lt0n n : (n == 0) = false -> 0 < n. Proof. by case: n. Qed.
Hint Resolve lt0n_neq0 neq0_lt0n.

Lemma eqn_leq m n : (m == n) = (m <= n <= m).
Proof. elim: m n => [|m IHm] [|n] //; exact: IHm n. Qed.

Lemma anti_leq : antisymmetric leq.
Proof. by move=> m n; rewrite -eqn_leq => /eqP. Qed.

Lemma neq_ltn m n : (m != n) = (m < n) || (n < m).
Proof. by rewrite eqn_leq negb_and orbC -!ltnNge. Qed.

Lemma gtn_eqF m n : m < n -> n == m = false.
Proof. by rewrite eqn_leq (leqNgt n) => ->. Qed.

Lemma ltn_eqF m n : m < n -> m == n = false.
Proof. by move/gtn_eqF; rewrite eq_sym. Qed.

Lemma leq_eqVlt m n : (m <= n) = (m == n) || (m < n).
Proof. elim: m n => [|m IHm] [|n] //; exact: IHm n. Qed.

Lemma ltn_neqAle m n : (m < n) = (m != n) && (m <= n).
Proof. by rewrite ltnNge leq_eqVlt negb_or -leqNgt eq_sym. Qed.

Lemma leq_trans n m p : m <= n -> n <= p -> m <= p.
Proof. by elim: n m p => [|i IHn] [|m] [|p] //; exact: IHn m p. Qed.

Lemma leq_ltn_trans n m p : m <= n -> n < p -> m < p.
Proof. move=> Hmn; exact: leq_trans. Qed.

Lemma ltnW m n : m < n -> m <= n.
Proof. exact: leq_trans. Qed.
Hint Resolve ltnW.

Lemma leqW m n : m <= n -> m <= n.+1.
Proof. by move=> le_mn; exact: ltnW. Qed.

Lemma ltn_trans n m p : m < n -> n < p -> m < p.
Proof. by move=> lt_mn /ltnW; exact: leq_trans. Qed.

Lemma leq_total m n : (m <= n) || (m >= n).
Proof. by rewrite -implyNb -ltnNge; apply/implyP; exact: ltnW. Qed.

(* Link to the legacy comparison predicates. *)

Lemma leP m n : reflect (m <= n)%coq_nat (m <= n).
Proof.
apply: (iffP idP); last by elim: n / => // n _ /leq_trans->.
elim: n => [|n IHn]; first by case: m.
by rewrite leq_eqVlt ltnS => /predU1P[<- // | /IHn]; right.
Qed.
Implicit Arguments leP [m n].

Lemma le_irrelevance m n le_mn1 le_mn2 : le_mn1 = le_mn2 :> (m <= n)%coq_nat.
Proof.
elim: {n}n.+1 {-1}n (erefl n.+1) => // n IHn _ [<-] in le_mn1 le_mn2 *.
pose def_n2 := erefl n; transitivity (identity_nondep_rect _ _ le_mn2 _ def_n2) => //.
move def_n1: {1 4 5 7}n le_mn1 le_mn2 def_n2 => n1 le_mn1.
case: n1 / le_mn1 def_n1 => [|n1 le_mn1] def_n1 [|n2 le_mn2] def_n2.
- by rewrite [def_n2]eq_axiomK.
- by move/leP: (le_mn2); rewrite -{1}def_n2 ltnn.
- by move/leP: (le_mn1); rewrite {1}def_n2 ltnn.
case: def_n2 (def_n2) => ->{n2} def_n2 in le_mn2 *.
by rewrite [def_n2]eq_axiomK /=; congr Peano.le_S; exact: IHn.
Qed.

Lemma ltP m n : reflect (m < n)%coq_nat (m < n).
Proof. exact leP. Qed.
Implicit Arguments ltP [m n].

Lemma lt_irrelevance m n lt_mn1 lt_mn2 : lt_mn1 = lt_mn2 :> (m < n)%coq_nat.
Proof. exact: (@le_irrelevance m.+1). Qed.

(* Comparison predicates. *)

CoInductive leq_xor_gtn m n : bool -> bool -> Type :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n true false
  | GtnNotLeq of n < m  : leq_xor_gtn m n false true.

Lemma leqP m n : leq_xor_gtn m n (m <= n) (n < m).
Proof.
by rewrite ltnNge; case le_mn: (m <= n); constructor; rewrite // ltnNge le_mn.
Qed.

CoInductive ltn_xor_geq m n : bool -> bool -> Type :=
  | LtnNotGeq of m < n  : ltn_xor_geq m n false true
  | GeqNotLtn of n <= m : ltn_xor_geq m n true false.

Lemma ltnP m n : ltn_xor_geq m n (n <= m) (m < n).
Proof. by rewrite -(ltnS n); case: leqP; constructor. Qed.

CoInductive eqn0_xor_gt0 n : bool -> bool -> Type :=
  | Eq0NotPos of n = 0 : eqn0_xor_gt0 n true false
  | PosNotEq0 of n > 0 : eqn0_xor_gt0 n false true.

Lemma posnP n : eqn0_xor_gt0 n (n == 0) (0 < n).
Proof. by case: n; constructor. Qed.

CoInductive compare_nat m n : bool -> bool -> bool -> Type :=
  | CompareNatLt of m < n : compare_nat m n true false false
  | CompareNatGt of m > n : compare_nat m n false true false
  | CompareNatEq of m = n : compare_nat m n false false true.

Lemma ltngtP m n : compare_nat m n (m < n) (n < m) (m == n).
Proof.
rewrite ltn_neqAle eqn_leq; case: ltnP; first by constructor.
by rewrite leq_eqVlt orbC; case: leqP; constructor; first exact/eqnP.
Qed.

(* Monotonicity lemmas *)

Lemma leq_add2l p m n : (p + m <= p + n) = (m <= n).
Proof. by elim: p. Qed.

Lemma ltn_add2l p m n : (p + m < p + n) = (m < n).
Proof. by rewrite -addnS; exact: leq_add2l. Qed.

Lemma leq_add2r p m n : (m + p <= n + p) = (m <= n).
Proof. by rewrite -!(addnC p); exact: leq_add2l. Qed.

Lemma ltn_add2r p m n : (m + p < n + p) = (m < n).
Proof. exact: leq_add2r p m.+1 n. Qed.

Lemma leq_add m1 m2 n1 n2 : m1 <= n1 -> m2 <= n2 -> m1 + m2 <= n1 + n2.
Proof.
by move=> le_mn1 le_mn2; rewrite (@leq_trans (m1 + n2)) ?leq_add2l ?leq_add2r.
Qed.

Lemma leq_addr m n : n <= n + m.
Proof. by rewrite -{1}[n]addn0 leq_add2l. Qed.

Lemma leq_addl m n : n <= m + n.
Proof. by rewrite addnC leq_addr. Qed.

Lemma ltn_addr m n p : m < n -> m < n + p.
Proof. by move/leq_trans=> -> //; exact: leq_addr. Qed.

Lemma ltn_addl m n p : m < n -> m < p + n.
Proof. by move/leq_trans=> -> //; exact: leq_addl. Qed.

Lemma addn_gt0 m n : (0 < m + n) = (0 < m) || (0 < n).
Proof. by rewrite !lt0n -negb_and addn_eq0. Qed.

Lemma subn_gt0 m n : (0 < n - m) = (m < n).
Proof. by elim: m n => [|m IHm] [|n] //; exact: IHm n. Qed.

Lemma subn_eq0 m n : (m - n == 0) = (m <= n).
Proof. by []. Qed.

Lemma leq_subLR m n p : (m - n <= p) = (m <= n + p).
Proof. by rewrite -subn_eq0 -subnDA. Qed.

Lemma leq_subr m n : n - m <= n.
Proof. by rewrite leq_subLR leq_addl. Qed.

Lemma subnKC m n : m <= n -> m + (n - m) = n.
Proof. by elim: m n => [|m IHm] [|n] // /(IHm n) {2}<-. Qed.

Lemma subnK m n : m <= n -> (n - m) + m = n.
Proof. by rewrite addnC; exact: subnKC. Qed.

Lemma addnBA m n p : p <= n -> m + (n - p) = m + n - p.
Proof. by move=> le_pn; rewrite -{2}(subnK le_pn) addnA addnK. Qed.

Lemma subnBA m n p : p <= n -> m - (n - p) = m + p - n.
Proof. by move=> le_pn; rewrite -{2}(subnK le_pn) subnDr. Qed.

Lemma subKn m n : m <= n -> n - (n - m) = m.
Proof. by move/subnBA->; rewrite addKn. Qed.

Lemma subSn m n : m <= n -> n.+1 - m = (n - m).+1.
Proof. by rewrite -add1n => /addnBA <-. Qed.

Lemma subnSK m n : m < n -> (n - m.+1).+1 = n - m.
Proof. by move/subSn. Qed.

Lemma leq_sub2r p m n : m <= n -> m - p <= n - p.
Proof.
by move=> le_mn; rewrite leq_subLR (leq_trans le_mn) // -leq_subLR.
Qed.

Lemma leq_sub2l p m n : m <= n -> p - n <= p - m.
Proof.
rewrite -(leq_add2r (p - m)) leq_subLR.
by apply: leq_trans; rewrite -leq_subLR.
Qed.

Lemma leq_sub m1 m2 n1 n2 : m1 <= m2 -> n2 <= n1 -> m1 - n1 <= m2 - n2.
Proof. by move/(leq_sub2r n1)=> le_m12 /(leq_sub2l m2); apply: leq_trans. Qed.

Lemma ltn_sub2r p m n : p < n -> m < n -> m - p < n - p.
Proof. by move/subnSK <-; exact: (@leq_sub2r p.+1). Qed.

Lemma ltn_sub2l p m n : m < p -> m < n -> p - n < p - m.
Proof. by move/subnSK <-; exact: leq_sub2l. Qed.

Lemma ltn_subRL m n p : (n < p - m) = (m + n < p).
Proof. by rewrite !ltnNge leq_subLR. Qed.

(* Eliminating the idiom for structurally decreasing compare and subtract. *)
Lemma subn_if_gt T m n F (E : T) :
  (if m.+1 - n is m'.+1 then F m' else E) = (if n <= m then F (m - n) else E).
Proof.
by case: leqP => [le_nm | /eqnP-> //]; rewrite -{1}(subnK le_nm) -addSn addnK.
Qed.

(* Max and min. *)

Definition maxn m n := if m < n then n else m.

Definition minn m n := if m < n then m else n.

Lemma max0n : left_id 0 maxn.  Proof. by case. Qed.
Lemma maxn0 : right_id 0 maxn. Proof. by []. Qed.

Lemma maxnC : commutative maxn.
Proof. by move=> m n; rewrite /maxn; case ltngtP. Qed.

Lemma maxnE m n : maxn m n = m + (n - m).
Proof. by rewrite /maxn addnC; case: leqP => [/eqnP-> | /ltnW/subnK]. Qed.

Lemma maxnAC : right_commutative maxn.
Proof. by move=> m n p; rewrite !maxnE -!addnA !subnDA -!maxnE maxnC. Qed.

Lemma maxnA : associative maxn.
Proof. by move=> m n p; rewrite !(maxnC m) maxnAC. Qed.

Lemma maxnCA : left_commutative maxn.
Proof. by move=> m n p; rewrite !maxnA (maxnC m). Qed.

Lemma maxnACA : interchange maxn maxn.
Proof. by move=> m n p q; rewrite -!maxnA (maxnCA n). Qed.

Lemma maxn_idPl {m n} : reflect (maxn m n = m) (m >= n).
Proof. by rewrite -subn_eq0 -(eqn_add2l m) addn0 -maxnE; apply: eqP. Qed.

Lemma maxn_idPr {m n} : reflect (maxn m n = n) (m <= n).
Proof. by rewrite maxnC; apply: maxn_idPl. Qed.

Lemma maxnn : idempotent maxn.
Proof. by move=> n; apply/maxn_idPl. Qed.

Lemma leq_max m n1 n2 : (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
without loss le_n21: n1 n2 / n2 <= n1.
  by case/orP: (leq_total n2 n1) => le_n12; last rewrite maxnC orbC; apply.
by rewrite (maxn_idPl le_n21) orb_idr // => /leq_trans->.
Qed.
Lemma leq_maxl m n : m <= maxn m n. Proof. by rewrite leq_max leqnn. Qed.
Lemma leq_maxr m n : n <= maxn m n. Proof. by rewrite maxnC leq_maxl. Qed.

Lemma gtn_max m n1 n2 : (m > maxn n1 n2) = (m > n1) && (m > n2).
Proof. by rewrite !ltnNge leq_max negb_or. Qed.

Lemma geq_max m n1 n2 : (m >= maxn n1 n2) = (m >= n1) && (m >= n2).
Proof. by rewrite -ltnS gtn_max. Qed.

Lemma maxnSS m n : maxn m.+1 n.+1 = (maxn m n).+1.
Proof. by rewrite !maxnE. Qed.

Lemma addn_maxl : left_distributive addn maxn.
Proof. by move=> m1 m2 n; rewrite !maxnE subnDr addnAC. Qed.

Lemma addn_maxr : right_distributive addn maxn.
Proof. by move=> m n1 n2; rewrite !(addnC m) addn_maxl. Qed.

Lemma min0n : left_zero 0 minn. Proof. by case. Qed.
Lemma minn0 : right_zero 0 minn. Proof. by []. Qed.

Lemma minnC : commutative minn.
Proof. by move=> m n; rewrite /minn; case ltngtP. Qed.

Lemma addn_min_max m n : minn m n + maxn m n = m + n.
Proof. by rewrite /minn /maxn; case: ltngtP => // [_|->] //; exact: addnC. Qed.

Lemma minnE m n : minn m n = m - (m - n).
Proof. by rewrite -(subnDl n) -maxnE -addn_min_max addnK minnC. Qed.

Lemma minnAC : right_commutative minn.
Proof.
by move=> m n p; rewrite !minnE -subnDA subnAC -maxnE maxnC maxnE subnAC subnDA.
Qed.

Lemma minnA : associative minn.
Proof. by move=> m n p; rewrite minnC minnAC (minnC n). Qed.

Lemma minnCA : left_commutative minn.
Proof. by move=> m n p; rewrite !minnA (minnC n). Qed.

Lemma minnACA : interchange minn minn.
Proof. by move=> m n p q; rewrite -!minnA (minnCA n). Qed.

Lemma minn_idPl {m n} : reflect (minn m n = m) (m <= n).
Proof.
rewrite (sameP maxn_idPr eqP) -(eqn_add2l m) eq_sym -addn_min_max eqn_add2r.
exact: eqP.
Qed.

Lemma minn_idPr {m n} : reflect (minn m n = n) (m >= n).
Proof. by rewrite minnC; apply: minn_idPl. Qed.

Lemma minnn : idempotent minn.
Proof. by move=> n; apply/minn_idPl. Qed.

Lemma leq_min m n1 n2 : (m <= minn n1 n2) = (m <= n1) && (m <= n2).
Proof.
wlog le_n21: n1 n2 / n2 <= n1.
  by case/orP: (leq_total n2 n1) => ?; last rewrite minnC andbC; auto.
by rewrite /minn ltnNge le_n21 /= andbC; case: leqP => // /leq_trans->.
Qed.

Lemma gtn_min m n1 n2 : (m > minn n1 n2) = (m > n1) || (m > n2).
Proof. by rewrite !ltnNge leq_min negb_and. Qed.

Lemma geq_min m n1 n2 : (m >= minn n1 n2) = (m >= n1) || (m >= n2).
Proof. by rewrite -ltnS gtn_min. Qed.

Lemma geq_minl m n : minn m n <= m. Proof. by rewrite geq_min leqnn. Qed.
Lemma geq_minr m n : minn m n <= n. Proof. by rewrite minnC geq_minl. Qed.

Lemma addn_minr : right_distributive addn minn.
Proof. by move=> m1 m2 n; rewrite !minnE subnDl addnBA ?leq_subr. Qed.

Lemma addn_minl : left_distributive addn minn.
Proof. by move=> m1 m2 n; rewrite -!(addnC n) addn_minr. Qed.

Lemma minnSS m n : minn m.+1 n.+1 = (minn m n).+1.
Proof. by rewrite -(addn_minr 1). Qed.

(* Quasi-cancellation (really, absorption) lemmas *)
Lemma maxnK m n : minn (maxn m n) m = m.
Proof. exact/minn_idPr/leq_maxl. Qed.

Lemma maxKn m n : minn n (maxn m n) = n.
Proof. exact/minn_idPl/leq_maxr. Qed.

Lemma minnK m n : maxn (minn m n) m = m.
Proof. exact/maxn_idPr/geq_minl. Qed.

Lemma minKn m n : maxn n (minn m n) = n.
Proof. exact/maxn_idPl/geq_minr. Qed.

(* Distributivity. *)
Lemma maxn_minl : left_distributive maxn minn.
Proof.
move=> m1 m2 n; wlog le_m21: m1 m2 / m2 <= m1.
  move=> IH; case/orP: (leq_total m2 m1) => /IH //.
  by rewrite minnC [in R in _ = R]minnC.
rewrite (minn_idPr le_m21); apply/esym/minn_idPr.
by rewrite geq_max leq_maxr leq_max le_m21.
Qed.

Lemma maxn_minr : right_distributive maxn minn.
Proof. by move=> m n1 n2; rewrite !(maxnC m) maxn_minl. Qed.

Lemma minn_maxl : left_distributive minn maxn.
Proof.
by move=> m1 m2 n; rewrite maxn_minr !maxn_minl -minnA maxnn (maxnC _ n) !maxnK.
Qed.

Lemma minn_maxr : right_distributive minn maxn.
Proof. by move=> m n1 n2; rewrite !(minnC m) minn_maxl. Qed.

(* Getting a concrete value from an abstract existence proof. *)

Section ExMinn.

Variable P : pred nat.
Hypothesis exP : exists n, P n.

Inductive acc_nat i : Type := AccNat0 of P i | AccNatS of acc_nat i.+1.

Lemma find_ex_minn : {m | P m & forall n, P n -> n >= m}.
Proof.
have: forall n, P n -> n >= 0 by [].
have: acc_nat 0.
  case exP => n; rewrite -(addn0 n); elim: n 0 => [|n IHn] j; first by left.
  rewrite addSnnS; right; exact: IHn.
move: 0; fix 2 => m IHm m_lb; case Pm: (P m); first by exists m.
apply: find_ex_minn m.+1 _ _ => [|n Pn]; first by case: IHm; rewrite ?Pm.
by rewrite ltn_neqAle m_lb //; case: eqP Pm => // -> /idP[].
Qed.

Definition ex_minn := s2val find_ex_minn.

Inductive ex_minn_spec : nat -> Type :=
  ExMinnSpec m of P m & (forall n, P n -> n >= m) : ex_minn_spec m.

Lemma ex_minnP : ex_minn_spec ex_minn.
Proof. by rewrite /ex_minn; case: find_ex_minn. Qed.

End ExMinn.

Section ExMaxn.

Variables (P : pred nat) (m : nat).
Hypotheses (exP : exists i, P i) (ubP : forall i, P i -> i <= m).

Lemma ex_maxn_subproof : exists i, P (m - i).
Proof. by case: exP => i Pi; exists (m - i); rewrite subKn ?ubP. Qed.

Definition ex_maxn := m - ex_minn ex_maxn_subproof.

CoInductive ex_maxn_spec : nat -> Type :=
  ExMaxnSpec i of P i & (forall j, P j -> j <= i) : ex_maxn_spec i.

Lemma ex_maxnP : ex_maxn_spec ex_maxn.
Proof.
rewrite /ex_maxn; case: ex_minnP => i Pmi min_i; split=> // j Pj.
have le_i_mj: i <= m - j by rewrite min_i // subKn // ubP.
rewrite -subn_eq0 subnBA ?(leq_trans le_i_mj) ?leq_subr //.
by rewrite addnC -subnBA ?ubP.
Qed.

End ExMaxn.

Lemma eq_ex_minn P Q exP exQ : P =1 Q -> @ex_minn P exP = @ex_minn Q exQ.
Proof.
move=> eqPQ; case: ex_minnP => m1 Pm1 m1_lb; case: ex_minnP => m2 Pm2 m2_lb.
by apply/eqP; rewrite eqn_leq m1_lb (m2_lb, eqPQ) // -eqPQ.
Qed.

Lemma eq_ex_maxn (P Q : pred nat) m n exP ubP exQ ubQ :
  P =1 Q -> @ex_maxn P m exP ubP = @ex_maxn Q n exQ ubQ.
Proof.
move=> eqPQ; case: ex_maxnP => i Pi max_i; case: ex_maxnP => j Pj max_j.
by apply/eqP; rewrite eqn_leq max_i ?eqPQ // max_j -?eqPQ.
Qed.

Section Iteration.

Variable T : Type.
Implicit Types m n : nat.
Implicit Types x y : T.

Definition iter n f x :=
  let fix loop m := if m is i.+1 then f (loop i) else x in loop n.

Definition iteri n f x :=
  let fix loop m := if m is i.+1 then f i (loop i) else x in loop n.

Definition iterop n op x :=
  let f i y := if i is 0 then x else op x y in iteri n f.

Lemma iterSr n f x : iter n.+1 f x = iter n f (f x).
Proof. by elim: n => //= n <-. Qed.

Lemma iterS n f x : iter n.+1 f x = f (iter n f x). Proof. by []. Qed.

Lemma iter_add n m f x : iter (n + m) f x = iter n f (iter m f x).
Proof. by elim: n => //= n ->. Qed.

Lemma iteriS n f x : iteri n.+1 f x = f n (iteri n f x).
Proof. by []. Qed.

Lemma iteropS idx n op x : iterop n.+1 op x idx = iter n (op x) x.
Proof. by elim: n => //= n ->. Qed.

Lemma eq_iter f f' : f =1 f' -> forall n, iter n f =1 iter n f'.
Proof. by move=> eq_f n x; elim: n => //= n ->; rewrite eq_f. Qed.

Lemma eq_iteri f f' : f =2 f' -> forall n, iteri n f =1 iteri n f'.
Proof. by move=> eq_f n x; elim: n => //= n ->; rewrite eq_f. Qed.

Lemma eq_iterop n op op' : op =2 op' -> iterop n op =2 iterop n op'.
Proof. by move=> eq_op x; apply: eq_iteri; case. Qed.

End Iteration.

Lemma iter_succn m n : iter n succn m = m + n.
Proof. by elim: n => //= n ->. Qed.

Lemma iter_succn_0 n : iter n succn 0 = n.
Proof. exact: iter_succn. Qed.

Lemma iter_predn m n : iter n predn m = m - n.
Proof. by elim: n m => /= [|n IHn] m; rewrite ?subn0 // IHn subnS. Qed.

(* Multiplication. *)

Definition muln_rec := Peano.mult.
Notation "m * n" := (muln_rec m n) : nat_rec_scope.

Definition muln := nosimpl muln_rec.
Notation "m * n" := (muln m n) : nat_scope.

Lemma multE : Peano.mult = muln.     Proof. by []. Qed.
Lemma mulnE : muln = muln_rec. Proof. by []. Qed.

Lemma mul0n : left_zero 0 muln.          Proof. by []. Qed.
Lemma muln0 : right_zero 0 muln.         Proof. by elim. Qed.
Lemma mul1n : left_id 1 muln.            Proof. exact: addn0. Qed.
Lemma mulSn m n : m.+1 * n = n + m * n.  Proof. by []. Qed.
Lemma mulSnr m n : m.+1 * n = m * n + n. Proof. exact: addnC. Qed.

Lemma mulnS m n : m * n.+1 = m + m * n.
Proof. by elim: m => // m; rewrite !mulSn !addSn addnCA => ->. Qed.
Lemma mulnSr m n : m * n.+1 = m * n + m.
Proof. by rewrite addnC mulnS. Qed.

Lemma iter_addn m n p : iter n (addn m) p = m * n + p.
Proof. by elim: n => /= [|n ->]; rewrite ?muln0 // mulnS addnA. Qed.

Lemma iter_addn_0 m n : iter n (addn m) 0 = m * n.
Proof. by rewrite iter_addn addn0. Qed.

Lemma muln1 : right_id 1 muln.
Proof. by move=> n; rewrite mulnSr muln0. Qed.

Lemma mulnC : commutative muln.
Proof.
by move=> m n; elim: m => [|m]; rewrite (muln0, mulnS) // mulSn => ->.
Qed.

Lemma mulnDl : left_distributive muln addn.
Proof. by move=> m1 m2 n; elim: m1 => //= m1 IHm; rewrite -addnA -IHm. Qed.

Lemma mulnDr : right_distributive muln addn.
Proof. by move=> m n1 n2; rewrite !(mulnC m) mulnDl. Qed.

Lemma mulnBl : left_distributive muln subn.
Proof.
move=> m n [|p]; first by rewrite !muln0.
by elim: m n => // [m IHm] [|n] //; rewrite mulSn subnDl -IHm.
Qed.

Lemma mulnBr : right_distributive muln subn.
Proof. by move=> m n p; rewrite !(mulnC m) mulnBl. Qed.

Lemma mulnA : associative muln.
Proof. by move=> m n p; elim: m => //= m; rewrite mulSn mulnDl => ->. Qed.

Lemma mulnCA : left_commutative muln.
Proof. by move=> m n1 n2; rewrite !mulnA (mulnC m). Qed.

Lemma mulnAC : right_commutative muln.
Proof. by move=> m n p; rewrite -!mulnA (mulnC n). Qed.

Lemma mulnACA : interchange muln muln.
Proof. by move=> m n p q; rewrite -!mulnA (mulnCA n). Qed.

Lemma muln_eq0 m n : (m * n == 0) = (m == 0) || (n == 0).
Proof. by case: m n => // m [|n] //=; rewrite muln0. Qed.

Lemma muln_eq1 m n : (m * n == 1) = (m == 1) && (n == 1).
Proof. by case: m n => [|[|m]] [|[|n]] //; rewrite muln0. Qed.

Lemma muln_gt0 m n : (0 < m * n) = (0 < m) && (0 < n).
Proof. by case: m n => // m [|n] //=; rewrite muln0. Qed.

Lemma leq_pmull m n : n > 0 -> m <= n * m.
Proof. by move/prednK <-; exact: leq_addr. Qed.

Lemma leq_pmulr m n : n > 0 -> m <= m * n.
Proof. by move/leq_pmull; rewrite mulnC. Qed.

Lemma leq_mul2l m n1 n2 : (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof. by rewrite {1}/leq -mulnBr muln_eq0. Qed.

Lemma leq_mul2r m n1 n2 : (n1 * m <= n2 * m) = (m == 0) || (n1 <= n2).
Proof. by rewrite -!(mulnC m) leq_mul2l. Qed.

Lemma leq_mul m1 m2 n1 n2 : m1 <= n1 -> m2 <= n2 -> m1 * m2 <= n1 * n2.
Proof.
move=> le_mn1 le_mn2; apply (@leq_trans (m1 * n2)).
  by rewrite leq_mul2l le_mn2 orbT.
by rewrite leq_mul2r le_mn1 orbT.
Qed.

Lemma eqn_mul2l m n1 n2 : (m * n1 == m * n2) = (m == 0) || (n1 == n2).
Proof. by rewrite eqn_leq !leq_mul2l -orb_andr -eqn_leq. Qed.

Lemma eqn_mul2r m n1 n2 : (n1 * m == n2 * m) = (m == 0) || (n1 == n2).
Proof. by rewrite eqn_leq !leq_mul2r -orb_andr -eqn_leq. Qed.

Lemma leq_pmul2l m n1 n2 : 0 < m -> (m * n1 <= m * n2) = (n1 <= n2).
Proof. by move/prednK=> <-; rewrite leq_mul2l. Qed.
Implicit Arguments leq_pmul2l [m n1 n2].

Lemma leq_pmul2r m n1 n2 : 0 < m -> (n1 * m <= n2 * m) = (n1 <= n2).
Proof. by move/prednK <-; rewrite leq_mul2r. Qed.
Implicit Arguments leq_pmul2r [m n1 n2].

Lemma eqn_pmul2l m n1 n2 : 0 < m -> (m * n1 == m * n2) = (n1 == n2).
Proof. by move/prednK <-; rewrite eqn_mul2l. Qed.
Implicit Arguments eqn_pmul2l [m n1 n2].

Lemma eqn_pmul2r m n1 n2 : 0 < m -> (n1 * m == n2 * m) = (n1 == n2).
Proof. by move/prednK <-; rewrite eqn_mul2r. Qed.
Implicit Arguments eqn_pmul2r [m n1 n2].

Lemma ltn_mul2l m n1 n2 : (m * n1 < m * n2) = (0 < m) && (n1 < n2).
Proof. by rewrite lt0n !ltnNge leq_mul2l negb_or. Qed.

Lemma ltn_mul2r m n1 n2 : (n1 * m < n2 * m) = (0 < m) && (n1 < n2).
Proof. by rewrite lt0n !ltnNge leq_mul2r negb_or. Qed.

Lemma ltn_pmul2l m n1 n2 : 0 < m -> (m * n1 < m * n2) = (n1 < n2).
Proof. by move/prednK <-; rewrite ltn_mul2l. Qed.
Implicit Arguments ltn_pmul2l [m n1 n2].

Lemma ltn_pmul2r m n1 n2 : 0 < m -> (n1 * m < n2 * m) = (n1 < n2).
Proof. by move/prednK <-; rewrite ltn_mul2r. Qed.
Implicit Arguments ltn_pmul2r [m n1 n2].

Lemma ltn_Pmull m n : 1 < n -> 0 < m -> m < n * m.
Proof. by move=> lt1n m_gt0; rewrite -{1}[m]mul1n ltn_pmul2r. Qed.

Lemma ltn_Pmulr m n : 1 < n -> 0 < m -> m < m * n.
Proof. by move=> lt1n m_gt0; rewrite mulnC ltn_Pmull. Qed.

Lemma ltn_mul m1 m2 n1 n2 : m1 < n1 -> m2 < n2 -> m1 * m2 < n1 * n2.
Proof.
move=> lt_mn1 lt_mn2; apply (@leq_ltn_trans (m1 * n2)).
  by rewrite leq_mul2l orbC ltnW.
by rewrite ltn_pmul2r // (leq_trans _ lt_mn2).
Qed.

Lemma maxn_mulr : right_distributive muln maxn.
Proof. by case=> // m n1 n2; rewrite /maxn (fun_if (muln _)) ltn_pmul2l. Qed.

Lemma maxn_mull : left_distributive muln maxn.
Proof. by move=> m1 m2 n; rewrite -!(mulnC n) maxn_mulr. Qed.

Lemma minn_mulr : right_distributive muln minn.
Proof. by case=> // m n1 n2; rewrite /minn (fun_if (muln _)) ltn_pmul2l. Qed.

Lemma minn_mull : left_distributive muln minn.
Proof. by move=> m1 m2 n; rewrite -!(mulnC n) minn_mulr. Qed.

(* Exponentiation. *)

Definition expn_rec m n := iterop n muln m 1.
Notation "m ^ n" := (expn_rec m n) : nat_rec_scope.
Definition expn := nosimpl expn_rec.
Notation "m ^ n" := (expn m n) : nat_scope.

Lemma expnE : expn = expn_rec. Proof. by []. Qed.

Lemma expn0 m : m ^ 0 = 1. Proof. by []. Qed.
Lemma expn1 m : m ^ 1 = m. Proof. by []. Qed.
Lemma expnS m n : m ^ n.+1 = m * m ^ n. Proof. by case: n; rewrite ?muln1. Qed.
Lemma expnSr m n : m ^ n.+1 = m ^ n * m. Proof. by rewrite mulnC expnS. Qed.

Lemma iter_muln m n p : iter n (muln m) p = m ^ n * p.
Proof. by elim: n => /= [|n ->]; rewrite ?mul1n // expnS mulnA. Qed.

Lemma iter_muln_1 m n : iter n (muln m) 1 = m ^ n.
Proof. by rewrite iter_muln muln1. Qed.

Lemma exp0n n : 0 < n -> 0 ^ n = 0. Proof. by case: n => [|[]]. Qed.

Lemma exp1n n : 1 ^ n = 1.
Proof. by elim: n => // n; rewrite expnS mul1n. Qed.

Lemma expnD m n1 n2 : m ^ (n1 + n2) = m ^ n1 * m ^ n2.
Proof. by elim: n1 => [|n1 IHn]; rewrite !(mul1n, expnS) // IHn mulnA. Qed.

Lemma expnMn m1 m2 n : (m1 * m2) ^ n = m1 ^ n * m2 ^ n.
Proof. by elim: n => // n IHn; rewrite !expnS IHn -!mulnA (mulnCA m2). Qed.

Lemma expnM m n1 n2 : m ^ (n1 * n2) = (m ^ n1) ^ n2.
Proof.
elim: n1 => [|n1 IHn]; first by rewrite exp1n.
by rewrite expnD expnS expnMn IHn.
Qed.

Lemma expnAC m n1 n2 : (m ^ n1) ^ n2 = (m ^ n2) ^ n1.
Proof. by rewrite -!expnM mulnC. Qed.

Lemma expn_gt0 m n : (0 < m ^ n) = (0 < m) || (n == 0).
Proof.
by case: m => [|m]; elim: n => //= n IHn; rewrite expnS // addn_gt0 IHn.
Qed.

Lemma expn_eq0 m e : (m ^ e == 0) = (m == 0) && (e > 0).
Proof. by rewrite !eqn0Ngt expn_gt0 negb_or -lt0n. Qed.

Lemma ltn_expl m n : 1 < m -> n < m ^ n.
Proof.
move=> m_gt1; elim: n => //= n; rewrite -(leq_pmul2l (ltnW m_gt1)) expnS.
by apply: leq_trans; exact: ltn_Pmull.
Qed.

Lemma leq_exp2l m n1 n2 : 1 < m -> (m ^ n1 <= m ^ n2) = (n1 <= n2).
Proof.
move=> m_gt1; elim: n1 n2 => [|n1 IHn] [|n2] //; last 1 first.
- by rewrite !expnS leq_pmul2l ?IHn // ltnW.
- by rewrite expn_gt0 ltnW.
by rewrite leqNgt (leq_trans m_gt1) // expnS leq_pmulr // expn_gt0 ltnW.
Qed.

Lemma ltn_exp2l m n1 n2 : 1 < m -> (m ^ n1 < m ^ n2) = (n1 < n2).
Proof. by move=> m_gt1; rewrite !ltnNge leq_exp2l. Qed.

Lemma eqn_exp2l m n1 n2 : 1 < m -> (m ^ n1 == m ^ n2) = (n1 == n2).
Proof. by move=> m_gt1; rewrite !eqn_leq !leq_exp2l. Qed.

Lemma expnI m : 1 < m -> injective (expn m).
Proof. by move=> m_gt1 e1 e2 /eqP; rewrite eqn_exp2l // => /eqP. Qed.

Lemma leq_pexp2l m n1 n2 : 0 < m -> n1 <= n2 -> m ^ n1 <= m ^ n2.
Proof. by case: m => [|[|m]] // _; [rewrite !exp1n | rewrite leq_exp2l]. Qed.

Lemma ltn_pexp2l m n1 n2 : 0 < m -> m ^ n1 < m ^ n2 -> n1 < n2.
Proof. by case: m => [|[|m]] // _; [rewrite !exp1n | rewrite ltn_exp2l]. Qed.

Lemma ltn_exp2r m n e : e > 0 -> (m ^ e < n ^ e) = (m < n).
Proof.
move=> e_gt0; apply/idP/idP=> [|ltmn].
  rewrite !ltnNge; apply: contra => lemn.
  by elim: e {e_gt0} => // e IHe; rewrite !expnS leq_mul.
by elim: e e_gt0 => // [[|e] IHe] _; rewrite ?expn1 // ltn_mul // IHe.
Qed.

Lemma leq_exp2r m n e : e > 0 -> (m ^ e <= n ^ e) = (m <= n).
Proof. by move=> e_gt0; rewrite leqNgt ltn_exp2r // -leqNgt. Qed.

Lemma eqn_exp2r m n e : e > 0 -> (m ^ e == n ^ e) = (m == n).
Proof. by move=> e_gt0; rewrite !eqn_leq !leq_exp2r. Qed.

Lemma expIn e : e > 0 -> injective (expn^~ e).
Proof. by move=> e_gt1 m n /eqP; rewrite eqn_exp2r // => /eqP. Qed.

(* Factorial. *)

Fixpoint fact_rec n := if n is n'.+1 then n * fact_rec n' else 1.

Definition factorial := nosimpl fact_rec.

Notation "n `!" := (factorial n) (at level 2, format "n `!") : nat_scope.

Lemma factE : factorial = fact_rec. Proof. by []. Qed.

Lemma fact0 : 0`! = 1. Proof. by []. Qed.

Lemma factS n : (n.+1)`!  = n.+1 * n`!. Proof. by []. Qed.

Lemma fact_gt0 n : n`! > 0.
Proof. by elim: n => //= n IHn; rewrite muln_gt0. Qed.

(* Parity and bits. *)

Coercion nat_of_bool (b : bool) := if b then 1 else 0.

Lemma leq_b1 (b : bool) : b <= 1. Proof. by case: b. Qed.

Lemma addn_negb (b : bool) : ~~ b + b = 1. Proof. by case: b. Qed.

Lemma eqb0 (b : bool) : (b == 0 :> nat) = ~~ b. Proof. by case: b. Qed.

Lemma eqb1 (b : bool) : (b == 1 :> nat) = b. Proof. by case: b. Qed.

Lemma lt0b (b : bool) : (b > 0) = b. Proof. by case: b. Qed.

Lemma sub1b (b : bool) : 1 - b = ~~ b. Proof. by case: b. Qed.

Lemma mulnb (b1 b2 : bool) : b1 * b2 = b1 && b2.
Proof. by case: b1; case: b2. Qed.

Lemma mulnbl (b : bool) n : b * n = (if b then n else 0).
Proof. by case: b; rewrite ?mul1n. Qed.

Lemma mulnbr (b : bool) n : n * b = (if b then n else 0).
Proof. by rewrite mulnC mulnbl. Qed.

Fixpoint odd n := if n is n'.+1 then ~~ odd n' else false.

Lemma oddb (b : bool) : odd b = b. Proof. by case: b. Qed.

Lemma odd_add m n : odd (m + n) = odd m (+) odd n.
Proof. by elim: m => [|m IHn] //=; rewrite -addTb IHn addbA addTb. Qed.

Lemma odd_sub m n : n <= m -> odd (m - n) = odd m (+) odd n.
Proof.
by move=> le_nm; apply: (@canRL bool) (addbK _) _; rewrite -odd_add subnK.
Qed.

Lemma odd_opp i m : odd m = false -> i < m -> odd (m - i) = odd i.
Proof. by move=> oddm lt_im; rewrite (odd_sub (ltnW lt_im)) oddm. Qed.

Lemma odd_mul m n : odd (m * n) = odd m && odd n.
Proof. by elim: m => //= m IHm; rewrite odd_add -addTb andb_addl -IHm. Qed.

Lemma odd_exp m n : odd (m ^ n) = (n == 0) || odd m.
Proof. by elim: n => // n IHn; rewrite expnS odd_mul {}IHn orbC; case odd. Qed.

(* Doubling. *)

Fixpoint double_rec n := if n is n'.+1 then n'.*2%Nrec.+2 else 0
where "n .*2" := (double_rec n) : nat_rec_scope.

Definition double := nosimpl double_rec.
Notation "n .*2" := (double n) : nat_scope.

Lemma doubleE : double = double_rec. Proof. by []. Qed.

Lemma double0 : 0.*2 = 0. Proof. by []. Qed.

Lemma doubleS n : n.+1.*2 = n.*2.+2. Proof. by []. Qed.

Lemma addnn n : n + n = n.*2.
Proof. by apply: eqP; elim: n => // n IHn; rewrite addnS. Qed.

Lemma mul2n m : 2 * m = m.*2.
Proof. by rewrite mulSn mul1n addnn. Qed.

Lemma muln2 m : m * 2 = m.*2.
Proof. by rewrite mulnC mul2n. Qed.

Lemma doubleD m n : (m + n).*2 = m.*2 + n.*2.
Proof. by rewrite -!addnn -!addnA (addnCA n). Qed.

Lemma doubleB m n : (m - n).*2 = m.*2 - n.*2.
Proof. elim: m n => [|m IHm] [|n] //; exact: IHm n. Qed.

Lemma leq_double m n : (m.*2 <= n.*2) = (m <= n).
Proof. by rewrite /leq -doubleB; case (m - n). Qed.

Lemma ltn_double m n : (m.*2 < n.*2) = (m < n).
Proof. by rewrite 2!ltnNge leq_double. Qed.

Lemma ltn_Sdouble m n : (m.*2.+1 < n.*2) = (m < n).
Proof. by rewrite -doubleS leq_double. Qed.

Lemma leq_Sdouble m n : (m.*2 <= n.*2.+1) = (m <= n).
Proof. by rewrite leqNgt ltn_Sdouble -leqNgt. Qed.

Lemma odd_double n : odd n.*2 = false.
Proof. by rewrite -addnn odd_add addbb. Qed.

Lemma double_gt0 n : (0 < n.*2) = (0 < n).
Proof. by case: n. Qed.

Lemma double_eq0 n : (n.*2 == 0) = (n == 0).
Proof. by case: n. Qed.

Lemma doubleMl m n : (m * n).*2 = m.*2 * n.
Proof. by rewrite -!mul2n mulnA. Qed.

Lemma doubleMr m n : (m * n).*2 = m * n.*2.
Proof. by rewrite -!muln2 mulnA. Qed.

(* Halving. *)

Fixpoint half (n : nat) : nat := if n is n'.+1 then uphalf n' else n
with   uphalf (n : nat) : nat := if n is n'.+1 then n'./2.+1 else n
where "n ./2" := (half n) : nat_scope.

Lemma doubleK : cancel double half.
Proof. by elim=> //= n ->. Qed.

Definition half_double := doubleK.
Definition double_inj := can_inj doubleK.

Lemma uphalf_double n : uphalf n.*2 = n.
Proof. by elim: n => //= n ->. Qed.

Lemma uphalf_half n : uphalf n = odd n + n./2.
Proof. by elim: n => //= n ->; rewrite addnA addn_negb. Qed.

Lemma odd_double_half n : odd n + n./2.*2 = n.
Proof.
by elim: n => //= n {3}<-; rewrite uphalf_half doubleD; case (odd n).
Qed.

Lemma half_bit_double n (b : bool) : (b + n.*2)./2 = n.
Proof. by case: b; rewrite /= (half_double, uphalf_double). Qed.

Lemma halfD m n : (m + n)./2 = (odd m && odd n) + (m./2 + n./2).
Proof.
rewrite -{1}[n]odd_double_half addnCA -{1}[m]odd_double_half -addnA -doubleD.
by do 2!case: odd; rewrite /= ?add0n ?half_double ?uphalf_double.
Qed.

Lemma half_leq m n : m <= n -> m./2 <= n./2.
Proof. by move/subnK <-; rewrite halfD addnA leq_addl. Qed.

Lemma half_gt0 n : (0 < n./2) = (1 < n).
Proof. by case: n => [|[]]. Qed.

Lemma odd_geq m n : odd n -> (m <= n) = (m./2.*2 <= n).
Proof.
move=> odd_n; rewrite -{1}[m]odd_double_half -[n]odd_double_half odd_n.
by case: (odd m); rewrite // leq_Sdouble ltnS leq_double.
Qed.

Lemma odd_ltn m n : odd n -> (n < m) = (n < m./2.*2).
Proof. by move=> odd_n; rewrite !ltnNge odd_geq. Qed.

Lemma odd_gt0 n : odd n -> n > 0. Proof. by case: n. Qed.

Lemma odd_gt2 n : odd n -> n > 1 -> n > 2.
Proof. by move=> odd_n n_gt1; rewrite odd_geq. Qed.

(* Squares and square identities. *)

Lemma mulnn m : m * m = m ^ 2.
Proof. by rewrite !expnS muln1. Qed.

Lemma sqrnD m n : (m + n) ^ 2 = m ^ 2 + n ^ 2 + 2 * (m * n).
Proof.
rewrite -!mulnn mul2n mulnDr !mulnDl (mulnC n) -!addnA.
by congr (_ + _); rewrite addnA addnn addnC.
Qed.

Lemma sqrn_sub m n : n <= m -> (m - n) ^ 2 = m ^ 2 + n ^ 2 - 2 * (m * n).
Proof.
move/subnK=> def_m; rewrite -{2}def_m sqrnD -addnA addnAC.
by rewrite -2!addnA addnn -mul2n -mulnDr -mulnDl def_m addnK.
Qed.

Lemma sqrnD_sub m n : n <= m -> (m + n) ^ 2 - 4 * (m * n) = (m - n) ^ 2.
Proof.
move=> le_nm; rewrite -[4]/(2 * 2) -mulnA mul2n -addnn subnDA.
by rewrite sqrnD addnK sqrn_sub.
Qed.

Lemma subn_sqr m n : m ^ 2 - n ^ 2 = (m - n) * (m + n).
Proof. by rewrite mulnBl !mulnDr addnC (mulnC m) subnDl !mulnn. Qed.

Lemma ltn_sqr m n : (m ^ 2 < n ^ 2) = (m < n).
Proof. by rewrite ltn_exp2r. Qed.

Lemma leq_sqr m n : (m ^ 2 <= n ^ 2) = (m <= n).
Proof. by rewrite leq_exp2r. Qed.

Lemma sqrn_gt0 n : (0 < n ^ 2) = (0 < n).
Proof. exact: (ltn_sqr 0). Qed.

Lemma eqn_sqr m n : (m ^ 2 == n ^ 2) = (m == n).
Proof. by rewrite eqn_exp2r. Qed.

Lemma sqrn_inj : injective (expn ^~ 2).
Proof. exact: expIn. Qed.

(* Almost strict inequality: an inequality that is strict unless some    *)
(* specific condition holds, such as the Cauchy-Schwartz or the AGM      *)
(* inequality (we only prove the order-2 AGM here; the general one       *)
(* requires sequences).                                                  *)
(*   We formalize the concept as a rewrite multirule, that can be used   *)
(* both to rewrite the non-strict inequality to true, and the equality   *)
(* to the specific condition (for strict inequalities use the ltn_neqAle *)
(* lemma); in addition, the conditional equality also coerces to a       *)
(* non-strict one.                                                       *)

Definition leqif m n C := ((m <= n) * ((m == n) = C))%type.

Notation "m <= n ?= 'iff' C" := (leqif m n C) : nat_scope.

Coercion leq_of_leqif m n C (H : m <= n ?= iff C) := H.1 : m <= n.

Lemma leqifP m n C : reflect (m <= n ?= iff C) (if C then m == n else m < n).
Proof.
rewrite ltn_neqAle; apply: (iffP idP) => [|lte]; last by rewrite !lte; case C.
by case C => [/eqP-> | /andP[/negPf]]; split=> //; exact: eqxx.
Qed.

Lemma leqif_refl m C : reflect (m <= m ?= iff C) C.
Proof. by apply: (iffP idP) => [-> | <-] //; split; rewrite ?eqxx. Qed.

Lemma leqif_trans m1 m2 m3 C12 C23 :
  m1 <= m2 ?= iff C12 -> m2 <= m3 ?= iff C23 -> m1 <= m3 ?= iff C12 && C23.
Proof.
move=> ltm12 ltm23; apply/leqifP; rewrite -ltm12.
case eqm12: (m1 == m2).
  by rewrite (eqP eqm12) ltn_neqAle !ltm23 andbT; case C23.
by rewrite (@leq_trans m2) ?ltm23 // ltn_neqAle eqm12 ltm12.
Qed.

Lemma mono_leqif f : {mono f : m n / m <= n} ->
  forall m n C, (f m <= f n ?= iff C) = (m <= n ?= iff C).
Proof. by move=> f_mono m n C; rewrite /leqif !eqn_leq !f_mono. Qed.

Lemma leqif_geq m n : m <= n -> m <= n ?= iff (m >= n).
Proof. by move=> lemn; split=> //; rewrite eqn_leq lemn. Qed.

Lemma leqif_eq m n : m <= n -> m <= n ?= iff (m == n).
Proof. by []. Qed.

Lemma geq_leqif a b C : a <= b ?= iff C -> (b <= a) = C.
Proof. by case=> le_ab; rewrite eqn_leq le_ab. Qed.

Lemma ltn_leqif a b C : a <= b ?= iff C -> (a < b) = ~~ C.
Proof. by move=> le_ab; rewrite ltnNge (geq_leqif le_ab). Qed.

Lemma leqif_add m1 n1 C1 m2 n2 C2 :
    m1 <= n1 ?= iff C1 -> m2 <= n2 ?= iff C2 ->
  m1 + m2 <= n1 + n2 ?= iff C1 && C2.
Proof.
rewrite -(mono_leqif (leq_add2r m2)) -(mono_leqif (leq_add2l n1) m2).
exact: leqif_trans.
Qed.

Lemma leqif_mul m1 n1 C1 m2 n2 C2 :
    m1 <= n1 ?= iff C1 -> m2 <= n2 ?= iff C2 ->
  m1 * m2 <= n1 * n2 ?= iff (n1 * n2 == 0) || (C1 && C2).
Proof.
move=> le1 le2; case: posnP => [n12_0 | ].
  rewrite n12_0; move/eqP: n12_0 {le1 le2}le1.1 le2.1; rewrite muln_eq0.
  by case/orP=> /eqP->; case: m1 m2 => [|m1] [|m2] // _ _; 
    rewrite ?muln0; exact/leqif_refl.
rewrite muln_gt0 => /andP[n1_gt0 n2_gt0].
have [m2_0 | m2_gt0] := posnP m2.
  apply/leqifP; rewrite -le2 andbC eq_sym eqn_leq leqNgt m2_0 muln0.
  by rewrite muln_gt0 n1_gt0 n2_gt0.
have mono_n1 := leq_pmul2l n1_gt0; have mono_m2 := leq_pmul2r m2_gt0.
rewrite -(mono_leqif mono_m2) in le1; rewrite -(mono_leqif mono_n1) in le2.
exact: leqif_trans le1 le2.
Qed.

Lemma nat_Cauchy m n : 2 * (m * n) <= m ^ 2 + n ^ 2 ?= iff (m == n).
Proof.
wlog le_nm: m n / n <= m.
  by case: (leqP m n); auto; rewrite eq_sym addnC (mulnC m); auto.
apply/leqifP; case: ifP => [/eqP-> | ne_mn]; first by rewrite mulnn addnn mul2n.
by rewrite -subn_gt0 -sqrn_sub // sqrn_gt0 subn_gt0 ltn_neqAle eq_sym ne_mn.
Qed.

Lemma nat_AGM2 m n : 4 * (m * n) <= (m + n) ^ 2 ?= iff (m == n).
Proof.
rewrite -[4]/(2 * 2) -mulnA mul2n -addnn sqrnD; apply/leqifP.
by rewrite ltn_add2r eqn_add2r ltn_neqAle !nat_Cauchy; case: ifP => ->.
Qed.

(* Support for larger integers. The normal definitions of +, - and even  *)
(* IO are unsuitable for Peano integers larger than 2000 or so because   *)
(* they are not tail-recursive. We provide a workaround module, along    *)
(* with a rewrite multirule to change the tailrec operators to the       *)
(* normal ones. We handle IO via the NatBin module, but provide our      *)
(* own (more efficient) conversion functions.                            *)

Module NatTrec.

(*   Usage:                                             *)
(*     Import NatTrec.                                  *)
(*        in section definining functions, rebinds all  *)
(*        non-tail recursive operators.                 *)
(*     rewrite !trecE.                                  *)
(*        in the correctness proof, restores operators  *)

Fixpoint add m n := if m is m'.+1 then m' + n.+1 else n
where "n + m" := (add n m) : nat_scope.

Fixpoint add_mul m n s := if m is m'.+1 then add_mul m' n (n + s) else s.

Definition mul m n := if m is m'.+1 then add_mul m' n n else 0.

Notation "n * m" := (mul n m) : nat_scope.

Fixpoint mul_exp m n p := if n is n'.+1 then mul_exp m n' (m * p) else p.

Definition exp m n := if n is n'.+1 then mul_exp m n' m else 1.

Notation "n ^ m" := (exp n m) : nat_scope.

Notation Local oddn := odd.
Fixpoint odd n := if n is n'.+2 then odd n' else eqn n 1.

Notation Local doublen := double.
Definition double n := if n is n'.+1 then n' + n.+1 else 0.
Notation "n .*2" := (double n) : nat_scope.

Lemma addE : add =2 addn.
Proof. by elim=> //= n IHn m; rewrite IHn addSnnS. Qed.

Lemma doubleE : double =1 doublen.
Proof. by case=> // n; rewrite -addnn -addE. Qed.

Lemma add_mulE n m s : add_mul n m s = addn (muln n m) s.
Proof. by elim: n => //= n IHn in m s *; rewrite IHn addE addnCA addnA. Qed.

Lemma mulE : mul =2 muln.
Proof. by case=> //= n m; rewrite add_mulE addnC. Qed.

Lemma mul_expE m n p : mul_exp m n p = muln (expn m n) p.
Proof.
by elim: n => [|n IHn] in p *; rewrite ?mul1n //= expnS IHn mulE mulnCA mulnA.
Qed.

Lemma expE : exp =2 expn.
Proof. by move=> m [|n] //=; rewrite mul_expE expnS mulnC. Qed.

Lemma oddE : odd =1 oddn.
Proof.
move=> n; rewrite -{1}[n]odd_double_half addnC.
by elim: n./2 => //=; case (oddn n).
Qed.

Definition trecE := (addE, (doubleE, oddE), (mulE, add_mulE, (expE, mul_expE))).

End NatTrec.

Notation natTrecE := NatTrec.trecE.

(* assia : we drop this for the moment in HoTT no to depend on the std lib of coq 
Lemma eq_binP : Equality.axiom Ndec.Neqb.
Proof.
move=> p q; apply: (iffP idP) => [|<-]; last by case: p => //; elim.
by case: q; case: p => //; elim=> [p IHp|p IHp|] [q|q|] //=; case/IHp=> ->.
Qed.

Canonical bin_nat_eqMixin := EqMixin eq_binP.
Canonical bin_nat_eqType := Eval hnf in EqType N bin_nat_eqMixin.

Section NumberInterpretation.

Import BinPos.

Section Trec.

Import NatTrec.

Fixpoint nat_of_pos p0 :=
  match p0 with
  | xO p => (nat_of_pos p).*2
  | xI p => (nat_of_pos p).*2.+1
  | xH   => 1
  end.

End Trec.

Coercion Local nat_of_pos : positive >-> nat.

Coercion nat_of_bin b := if b is Npos p then p : nat else 0.

Fixpoint pos_of_nat n0 m0 :=
  match n0, m0 with
  | n.+1, m.+2 => pos_of_nat n m
  | n.+1,    1 => xO (pos_of_nat n n)
  | n.+1,    0 => xI (pos_of_nat n n)
  |    0,    _ => xH
  end.

Definition bin_of_nat n0 := if n0 is n.+1 then Npos (pos_of_nat n n) else 0%num.

Lemma bin_of_natK : cancel bin_of_nat nat_of_bin.
Proof.
have sub2nn n : n.*2 - n = n by rewrite -addnn addKn.
case=> //= n; rewrite -{3}[n]sub2nn.
by elim: n {2 4}n => // m IHm [|[|n]] //=; rewrite IHm // natTrecE sub2nn.
Qed.

Lemma nat_of_binK : cancel nat_of_bin bin_of_nat.
Proof.
case=> //=; elim=> //= p; case: (nat_of_pos p) => //= n [<-].
  by rewrite natTrecE !addnS {2}addnn; elim: {1 3}n.
by rewrite natTrecE addnS /= addnS {2}addnn; elim: {1 3}n.
Qed.

Lemma nat_of_succ_gt0 p : Psucc p = p.+1 :> nat.
Proof. by elim: p => //= p ->; rewrite !natTrecE. Qed.

Lemma nat_of_addn_gt0 p q : (p + q)%positive = p + q :> nat.
Proof.
apply: fst (Pplus_carry p q = (p + q).+1 :> nat) _.
elim: p q => [p IHp|p IHp|] [q|q|] //=; rewrite !natTrecE //;
  by rewrite ?IHp ?nat_of_succ_gt0 ?(doubleS, doubleD, addn1, addnS).
Qed.

Lemma nat_of_add_bin b1 b2 : (b1 + b2)%num = b1 + b2 :> nat.
Proof. case: b1 b2 => [|p] [|q] //=; exact: nat_of_addn_gt0. Qed.

Lemma nat_of_mul_bin b1 b2 : (b1 * b2)%num = b1 * b2 :> nat.
Proof.
case: b1 b2 => [|p] [|q] //=; elim: p => [p IHp|p IHp|] /=;
  by rewrite ?(mul1n, nat_of_addn_gt0, mulSn) //= !natTrecE IHp doubleMl.
Qed.

Lemma nat_of_exp_bin n (b : N) : n ^ b = pow_N 1 muln n b.
Proof.
case: b => [|p] /=; first exact: expn0.
by elim: p => //= p <-; rewrite natTrecE mulnn -expnM muln2 ?expnS.
Qed.

End NumberInterpretation.

(* Big(ger) nat IO; usage:                              *)
(*     Num 1 072 399                                    *)
(*        to create large numbers for test cases        *)
(* Eval compute in [Num of some expression]             *)
(*        to display the resut of an expression that    *)
(*        returns a larger integer.                     *)

Record number : Type := Num {bin_of_number :> N}.

Definition extend_number (nn : number) m := Num (nn * 1000 + bin_of_nat m).

Coercion extend_number : number >-> Funclass.

Canonical number_subType := [newType for bin_of_number].
Definition number_eqMixin := Eval hnf in [eqMixin of number by <:].
Canonical number_eqType := Eval hnf in EqType number number_eqMixin.

Notation "[ 'Num' 'of' e ]" := (Num (bin_of_nat e))
  (at level 0, format "[ 'Num'  'of'  e ]") : nat_scope.

(* Interface to ring/ring_simplify tactics *)

Lemma nat_semi_ring : semi_ring_theory 0 1 addn muln (@eq _).
Proof. exact: mk_srt add0n addnC addnA mul1n mul0n mulnC mulnA mulnDl. Qed.

Lemma nat_semi_morph :
  semi_morph 0 1 addn muln (@eq _) 0%num 1%num Nplus Nmult pred1 nat_of_bin.
Proof.
by move: nat_of_add_bin nat_of_mul_bin; split=> //= m n; move/eqP->.
Qed.

Lemma nat_power_theory : power_theory 1 muln (@eq _) nat_of_bin expn.
Proof. split; exact: nat_of_exp_bin. Qed.

(* Interface to the ring tactic machinery. *)

Fixpoint pop_succn e := if e is e'.+1 then fun n => pop_succn e' n.+1 else id.

Ltac pop_succn e := eval lazy beta iota delta [pop_succn] in (pop_succn e 1).

Ltac nat_litteral e :=
  match pop_succn e with
  | ?n.+1 => constr: (bin_of_nat n)
  |     _ => NotConstant
  end.

Ltac succn_to_add :=
  match goal with
  | |- context G [?e.+1] =>
    let x := fresh "NatLit0" in
    match pop_succn e with
    | ?n.+1 => pose x := n.+1; let G' := context G [x] in change G'
    | _ ?e' ?n => pose x := n; let G' := context G [x + e'] in change G'
    end; succn_to_add; rewrite {}/x
  | _ => idtac
  end.

Add Ring nat_ring_ssr : nat_semi_ring (morphism nat_semi_morph,
   constants [nat_litteral], preprocess [succn_to_add],
   power_tac nat_power_theory [nat_litteral]).

(* A congruence tactic, similar to the boolean one, along with an .+1/+  *)
(* normalization tactic.                                                 *)


Ltac nat_norm :=
  succn_to_add; rewrite ?add0n ?addn0 -?addnA ?(addSn, addnS, add0n, addn0).
*)
Ltac nat_congr := first
 [ apply: (congr1 succn _)
 | apply: (congr1 predn _)
 | apply: (congr1 (addn _) _)
 | apply: (congr1 (subn _) _)
 | apply: (congr1 (addn^~ _) _)
 | match goal with |- (?X1 + ?X2 = ?X3) =>
     symmetry;
     rewrite -1?(addnC X1) -?(addnCA X1);
     apply: (congr1 (addn X1) _);
     symmetry
   end ].
