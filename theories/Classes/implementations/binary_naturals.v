Require Import
        Coq.Init.Peano.
Require Import
        HoTT.Basics.Decidable
        HoTT.Basics.Equivalences
        HoTT.Types.Sum
        HoTT.Types.Paths
        HoTT.Tactics.
Require Import
        HoTT.Classes.interfaces.abstract_algebra
        HoTT.Classes.interfaces.naturals
        HoTT.Classes.interfaces.orders
        HoTT.Classes.implementations.peano_naturals
        HoTT.Classes.theory.rings
        HoTT.Classes.orders.semirings
        HoTT.Classes.theory.apartness.

Inductive binnat : Type :=
| zero    :           binnat  (* zero *)
| double1 : binnat -> binnat  (* 2n+1 *)
| double2 : binnat -> binnat. (* 2n+2 *)

Definition Succ (n : binnat) : binnat.
Proof.
  induction n.
  - (* compute S O as 2*O + 1 *)
    exact (double1 zero).
  - (* compute S (2n + 1) as 2n + 2 *)
    exact (double2 n).
  - (* compute S (2n + 2) as 2(n+1) + 1 *)
    exact (double1 IHn).
Defined.

Eval compute in Succ (Succ (Succ zero)).

Definition double (n : binnat) : binnat.
Proof.
  induction n.
  - (* compute 2 * O as O*)
    exact zero.
  - (* compute 2 * (2n + 1) as 2*2*n + 2 *)
    exact (double2 IHn).
  - (* IHn = 2*n *)
    (* compute 2 * (2n + 2) as (2*(2n) + 2) + 2 *)
    exact (Succ (Succ (double2 IHn))).
Defined.

(* Perhaps Double, Double1 and Double2 should be defined algebraically instead... *)

Definition Double (n : nat) : nat.
Proof.
  induction n.
  - exact 0%nat.
  - (* NB IHn = 2*n *)
    (* compute 2*(S n) as 2*n + 2 *)
    exact (S (S IHn)).
Defined.

Definition Double1 (n : nat) : nat := S (Double n).

Definition Double2 (n : nat) : nat := S (S (Double n)).

Definition binary (n : nat) : binnat.
Proof.
  induction n.
  - exact zero.
  - exact (Succ IHn).
Defined.

(* Eval vm_compute in (binary ( (Double (Double (Double (Double (Double (Double (Double (Double (Double (Double (Double (Double (Double (S (S (S 0%nat)))))))))))))))))). *)

Section binary_equiv.

  Let unary' (n : binnat) : nat.
  Proof.
    induction n.
    - exact O.
    - exact (Double1 IHn).
    - exact (Double2 IHn).
  Defined.

  Let succunary (n : binnat) : unary' (Succ n) = S (unary' n).
  Proof.
    induction n.
    - reflexivity.
    - reflexivity.
    - simpl. now rewrite IHn.
  Qed.

  Let unarybinary : Sect binary unary'.
  Proof.
    intros n; induction n.
    - reflexivity.
    - simpl. rewrite succunary. now rewrite IHn.
  Qed.

  Definition double1binary (n : nat) : binary (Double1 n) = double1 (binary n).
  Proof.
    induction n.
    - reflexivity.
    - assert (H : binary (Double1 n.+1) = Succ (Succ (binary (Double n).+1))) by reflexivity;
        rewrite H; clear H; fold (Double1 n).
      now rewrite IHn.
  Qed.

  Definition double2binary (n : nat) : binary (Double2 n) = double2 (binary n).
  Proof.
    induction n.
    - reflexivity.
    - assert (H : binary (Double2 n.+1) = Succ (Succ (binary (Double n).+2))) by reflexivity;
        rewrite H; clear H; fold (Double2 n).
      now rewrite IHn.
  Qed.

  Let binaryunary : Sect unary' binary.
  Proof.
    intros n; induction n.
    - reflexivity.
    - simpl unary'.
      rewrite double1binary. now rewrite IHn.
    - simpl unary'.
      rewrite double2binary. now rewrite IHn.
  Qed.

  Global Instance isequiv_binary : IsEquiv@{N N} binary.
  Proof.
    apply isequiv_adjointify with unary'.
    - exact binaryunary.
    - exact unarybinary.
  Defined.

  Definition equiv_binary : nat <~> binnat := BuildEquiv _ _  binary isequiv_binary.

End binary_equiv.


(* Definition equiv_unary : binnat <~> nat := BuildEquiv binnat nat unary' (isequiv_inverse equiv_binary). *)

Notation equiv_unary  := equiv_binary ^-1.
Notation unary := equiv_unary.

Global Instance isequiv_unary : IsEquiv@{N N} unary.
Proof.
  apply _.
Defined.

Definition double1unary (n : binnat) : unary (double1 n) = Double1 (unary n).
Proof.
  rewrite <- (eisretr binary n), <- double1binary, (eisretr binary n).
  now rewrite (eissect binary _).
Qed.

Definition double2unary (n : binnat) : unary (double2 n) = Double2 (unary n).
Proof.
  rewrite <- (eisretr binary n), <- double2binary, (eisretr binary n).
  now rewrite (eissect binary _).
Qed.

Global Instance binnat_0 : Zero binnat := zero.
Global Instance binnat_1 : One binnat := double1 zero.

Global Instance binnat_plus : Plus binnat.
Proof.
  intros m.
  induction m.
  - (* m' = 0 *)
    intros n; exact n.
  - (* m' = 2m + 1 *)
    (* NB IHm n = m + n *)
    intros n. induction n.
    (* NB IHm n' = m + n' *)
    + (* n' = 0 *)
      (* IHm 0 = m + 0 *)
      exact (double1 m).
    + (* n' = 2n + 1 *)
      (* compute m' + n' as 2m+1 + 2n+1 = 2(m+n) + 2 *)
      (* NB: IHm n = m + n *)
      (* IHn =  *)
      exact (double2 (IHm n)).
    + (* n' = 2n + 2 *)
      (* compute m' + n' as 2m+1 + 2n+2 = 2(m+n)+2 + 1 = 2(m + n + 1) + 1*)
      exact (double1 (Succ (IHm n))).
  - intros n. induction n.
    + exact (double2 m).
    + (* compute m' + n' as 2m+2 + 2n+1 = 2(m+n)+2 + 1 = 2(m + n + 1) + 1 *)
      exact (double1 (Succ (IHm n))).
    + (* compute m' + n' as 2m+2 + 2n+2 = 2(m+n)+2 + 2 = 2(m + n + 1) + 2*)
      exact (double2 (Succ (IHm n))).
Defined.

Eval compute in (double1 zero) + (double1 zero).

(* Definition binaryplussucc (m n : binnat) :  *)

Definition binarysucc (n : nat) : binary n.+1 = Succ (binary n).
Proof.
  induction n; simpl; auto.
Qed.

Definition unarysucc : forall m, unary (Succ m) = S (unary m).
Proof.
  refine (equiv_ind binary _ _).
  intros n.
  rewrite <- binarysucc.
  rewrite eissect, eissect.
  reflexivity.
Qed.

Definition equiv_ind2 `{IsEquiv A B f} (P : B -> B -> Type)
  : (forall x y :A, P (f x) (f y)) -> forall u v :B, P u v.
Proof.
  intros g.
  refine (equiv_ind f _ _).
  intros x.
  refine (equiv_ind f _ _).
  intros y.
  exact (g x y).
Defined.

Arguments equiv_ind2 {A B} f {_} P _ _.

Definition binnatplussucc : forall (m n : binnat), (Succ m) + n = Succ (m + n).
Proof.
  induction m; induction n; auto; simpl; try now rewrite <- IHm.
Qed.

Definition binaryplus (m n : nat) : binary m + binary n = binary (m + n).
Proof.
  induction m; induction n; auto.
  - simpl. rewrite binnatplussucc. now apply ap.
  - simpl. rewrite <- IHm. now rewrite binnatplussucc.
Qed.

Definition unaryplus (m n : binnat) : unary m + unary n = unary (m + n).
Proof.
  rewrite <- (eisretr binary m), <- (eisretr binary n).
  rewrite binaryplus.
  rewrite (eisretr binary m), (eisretr binary n).
  apply ((eissect binary (unary m + unary n)) ^).
Qed.

Definition equiv_ind3 `{IsEquiv A B f} (P : B -> B -> B -> Type)
  : (forall x y z :A, P (f x) (f y) (f z)) -> forall u v w :B, P u v w.
Proof.
  intros g.
  refine (equiv_ind f _ _).
  intros x.
  refine (equiv_ind f _ _).
  intros y.
  refine (equiv_ind f _ _).
  intros z.
  exact (g x y z).
Defined.

Arguments equiv_ind3 {A B} f {_} P _ _.

Local Instance binnat_add_assoc : Associative binnat_plus.
Proof.
  refine (equiv_ind3 binary _ _).
  intros x y z.
  enough (binnat_plus = fun u v => u + v) as ->; [> |reflexivity].
  rewrite binaryplus, binaryplus, binaryplus, binaryplus.
  apply ap.
  apply associativity.
Qed.

Local Instance binnat_add_comm : Commutative binnat_plus.
Proof.
  refine (equiv_ind2 binary _ _).
  intros x y.
  enough (binnat_plus = fun u v => u + v) as ->; [|reflexivity].
  rewrite binaryplus, binaryplus.
  apply ap.
  apply commutativity.
Qed.

Global Instance binnat_mult : Mult binnat.
Proof.
  intros m.
  induction m; intros n.
  - (* m' = 0 *)
    exact 0.
  - (* m' = 2m + 1 *)
    (* IHm n = m * n *)
    (* compute (2m+1)*n as 2mn+n *)
    exact (IHm n + IHm n + n).
    (* exact ((double (IHm n)) + n). *)
  - (* m' = 2m + 2 *)
    exact (IHm n + IHm n + n + n).
    (* exact (double ((IHm n) + n)). *)
Defined.

Definition binnatmultsucc : forall (m n : binnat), (Succ m) * n = n + (m * n).
Proof.
  induction m.
  - intros n. simpl.
    assert (H : double1 zero * n = zero + n) by reflexivity; rewrite H; clear H.
    assert (H : n + zero * n = n + zero) by reflexivity; rewrite H; clear H.
    apply commutativity.
  - intros n. simpl.
    assert (H : double2 m * n = (m * n) + (m * n) + n + n) by reflexivity; rewrite H; clear H.
    assert (H : n + double1 m * n = (m * n) + m * n + n + n) by apply commutativity; rewrite H; clear H.
    reflexivity.
  - intros n. simpl.
    assert (H : double1 (Succ m) * n = (Succ m) * n + (Succ m) * n + n) by reflexivity; rewrite H; clear H.
    rewrite IHm.
    assert (H : n + double2 m * n = m * n + m * n + n + n + n) by apply commutativity; rewrite H; clear H.
    apply (ap (fun z => z + n)).
    rewrite (commutativity n (m * n)).
    rewrite <- (associativity (m * n) n (m * n + n)).
    rewrite (commutativity n (m * n + n)).
    rewrite (associativity (m * n) _ _).
    now rewrite (associativity (m * n) (m * n) n).
Qed.

Definition binarymult (m n : nat) : binary m * binary n = binary (m * n).
Proof.
  induction m; induction n; auto.
  - rewrite binnatmultsucc. rewrite IHm. now rewrite binaryplus.
  - rewrite binnatmultsucc. rewrite IHm. rewrite binaryplus. now apply ap.
Qed.

Definition unarymult (m n : binnat) : unary m * unary n = unary (m * n).
Proof.
  rewrite <- (eisretr binary m), <- (eisretr binary n).
  rewrite binarymult.
  rewrite (eisretr binary m), (eisretr binary n).
  apply ((eissect binary (unary m + unary n)) ^).
Qed.

Local Instance binnat_mult_assoc : Associative binnat_mult.
Proof.
  refine (equiv_ind3 binary _ _).
  intros x y z.
  enough (binnat_mult = fun u v => u * v) as ->; [|reflexivity].
  rewrite binarymult, binarymult, binarymult, binarymult.
  apply ap.
  apply associativity.
Qed.

Local Instance binnat_mult_comm : Commutative binnat_mult.
Proof.
  refine (equiv_ind2 binary _ _).
  intros x y.
  enough (binnat_mult = fun u v => u * v) as ->; [|reflexivity].
  rewrite binarymult, binarymult.
  apply ap.
  apply commutativity.
Qed.

Local Instance binnat_distr_l : LeftDistribute binnat_mult binnat_plus.
Proof.
  refine (equiv_ind3 binary _ _).
  intros x y z.
  enough (binnat_plus = fun u v => u + v) as ->; [|reflexivity].
  enough (binnat_mult = fun u v => u * v) as ->; [|reflexivity].
  rewrite binaryplus, binarymult, binarymult, binarymult, binaryplus.
  apply ap.
  apply simple_distribute_l.
Qed.

Local Instance binnat_distr_r : RightDistribute binnat_mult binnat_plus.
Proof.
  refine (equiv_ind3 binary _ _).
  intros x y z.
  enough (binnat_plus = fun u v => u + v) as ->; [|reflexivity].
  enough (binnat_mult = fun u v => u * v) as ->; [|reflexivity].
  rewrite binaryplus, binarymult, binarymult, binarymult, binaryplus.
  apply ap.
  apply simple_distribute_r.
Qed.

Global Instance binnat_set : IsHSet binnat.
Proof.
  apply (trunc_equiv nat binary).
Qed.

Global Instance binnat_semiring : SemiRing binnat.
Proof.
  hnf. split; try split; try split; try split; hnf; intros.
  1, 5: exact (binnat_set x y).
  all: apply (equiv_inj unary).
  1, 2, 3, 7: repeat rewrite <- unaryplus.
  4, 5, 6, 7: repeat rewrite <- unarymult.
  4: rewrite <- unaryplus.
  all: apply nat_semiring.
Qed.

Local Instance binary_preserving : SemiRingPreserving binary.
Proof.
  split; split.
  1, 3: hnf; intros x y; [> apply (binaryplus x y) ^ | apply (binarymult x y) ^ ].
  all: reflexivity.
Qed.

Global Instance binnat_le : Le binnat := fun m n => unary m <= unary n.
Global Instance binnat_lt : Lt binnat := fun m n => unary m < unary n.
Global Instance binnat_apart : Apart binnat := fun m n => unary m ≶ unary n.
Local Instance binnart_apart_symmetric : IsApart binnat.
Proof.
  split.
  - apply _.
  - intros x y. apply nat_full.
  - intros x y. apply nat_full.
  - intros x y z w. by apply nat_full.
  - intros m n. split.
    + intros E. apply (equiv_inj unary). by apply nat_full.
    + intros p. apply nat_full. exact (ap unary p).
Qed.

Local Instance binnat_full : FullPseudoSemiRingOrder binnat_le binnat_lt.
Proof.
  split.
  - intros m n; apply nat_le_hprop.
  - split; try intros m n; try apply nat_full'.
    + split; try intros m n; try apply nat_full'.
      * split; try intros m n; try apply nat_full'.
        -- apply _.
        -- apply cotransitive.
        -- split; intros E.
           ++ assert (X : unary m = unary n).
              ** now apply tight_apart.
              ** apply (((equiv_ap unary m n) ^-1) X).
           ++ rewrite E. now apply nat_full'.
      * intros E k. now apply nat_full'.
    + intros E.
      assert (H : exists w, (unary n) = (unary m) + w) by now apply nat_full'.
      destruct H as [w L].
      exists (binary w).
      rewrite <- (eisretr unary w), unaryplus in L.
      now apply (equiv_inj unary).
    + intros m. split; intros k l E; unfold lt, binnat_lt in *.
      * rewrite <- unaryplus, <- unaryplus. now apply nat_full'.
      * rewrite <- unaryplus, <- unaryplus in E.
        now apply (strictly_order_reflecting (plus (unary m))).
    + intros k l E. apply nat_full'.
      unfold apart, binnat_apart in E.
      now rewrite <- unarymult, <- unarymult in E.
    + intros E F. unfold lt, binnat_lt. rewrite <- unarymult.
      now apply nat_full'.
  - intros m n. apply nat_full'.
Qed.

Local Instance binnat_naturals_to_semiring : NaturalsToSemiRing binnat:=
  fun _ _ _ _ _ _ => fix f (n: binnat) :=
    match n with
      | zero => 0
      | double1 n' => 2 * (f n') + 1
      | double2 n' => 2 * (f n') + 2 end.

Definition nat_to_semiring_helper : NaturalsToSemiRing nat :=
  fun _ _ _ _ _ _ => fix f (n: nat) :=
    match n with
    | 0%nat => 0
    | S n' => 1 + f n'
    end.

Section for_another_semiring.
  Universe U.
  Context {R:Type@{U} } `{SemiRing R}.

  Notation toR := (naturals_to_semiring binnat R).
  Notation toR_fromnat := (naturals_to_semiring nat R).
  Notation toR_vianat := (toR_fromnat ∘ unary).

  Definition f_suc (m : binnat) : toR (Succ m) = (toR m)+1.
  Proof.
    induction m.
    - compute. assert (L : Amult (Aplus Aone Aone) Azero = Azero).
      {
        rewrite (@commutativity _ _ Amult _ _ _).
        refine (semiring_left_absorb _ _).
      }
      now rewrite L.
    - assert (T : Succ (double1 m) = double2 m) by reflexivity.
      rewrite T.
      unfold toR.
      simpl.
      generalize (binnat_naturals_to_semiring R Aplus Amult Azero Aone H m); intros r.
      apply simple_associativity.
    - induction m as [|m|m]; try clear IHm0.
      + unfold toR. simpl. admit.
      + unfold toR. simpl. admit.
      + unfold toR in *. simpl in *.
        rewrite IHm. admit.
  Admitted.

  Definition f_nat (m : binnat) : toR m = toR_vianat m.
  Proof.
    refine (equiv_ind binary (fun m => toR m = toR_vianat m) _ m).
    intros n. induction n as [|n IHn].
    - reflexivity.
    - induction n as [|n _].
      + compute. fold plus. fold mult. rewrite mult_0_r. apply plus_0_l.
      + rewrite f_suc. rewrite IHn.
        assert (L : (toR_fromnat ∘ binary^-1) (binary n.+1) + 1 = toR_fromnat ((binary^-1 (binary n.+1)).+1)%nat).
        {
          simpl rewrite (commutativity _ 1).
          simpl rewrite unarysucc.
          reflexivity.
        }
        rewrite L; clear L.
        rewrite <- unarysucc.
        rewrite <- binarysucc.
        reflexivity.
  Qed.

  Let f_preserves_0: toR 0 =  0.
  Proof. reflexivity. Qed.

  Let f_preserves_1: toR 1 = 1.
  Proof.
    rewrite (f_nat 1).
    reflexivity.
  Qed.

  Let f_preserves_plus (a a' : binnat) : toR (a + a') = toR a + toR a'.
  Proof.
    rewrite f_nat, f_nat, f_nat.
    unfold toR_vianat.
    rewrite <- (unaryplus a a').
    apply nat_to_sr_morphism.
  Qed.

  Let f_preserves_mult (a a' : binnat) : toR (a * a') = toR a * toR a'.
  Proof.
    rewrite f_nat, f_nat, f_nat.
    unfold toR_vianat.
    rewrite <- (unarymult a a').
    apply nat_to_sr_morphism.
  Qed.

  Global Instance binnat_to_sr_morphism
    : SemiRingPreserving toR.
  Proof.
  repeat (split;try apply _);trivial.
  Qed.

  Lemma binnat_toR_unique (h : binnat -> R) `{!SemiRingPreserving h} : forall x,
    toR x = h x.
  Proof.
    apply (equiv_ind binary).
    intros n.
    rewrite f_nat; unfold toR_vianat.
    assert (L : unary (binary n) = n).
    {
      apply (eissect binary n).
    }
    rewrite L; clear L.
    refine (toR_unique (h ∘ binary) n).
  Qed.
End for_another_semiring.

Lemma binnat_naturals : Naturals binnat.
Proof.
  split.
  - apply binnat_semiring.
  - apply binnat_full.
  - intros. apply binnat_to_sr_morphism.
  - intros. by apply binnat_toR_unique.
Qed.
