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

Section basics.

  (* This definition of binary naturals is due to Martín Escardó and
     Cory Knapp *)

  Inductive binnat : Type :=
  | bzero   :           binnat  (* zero *)
  | double1 : binnat -> binnat  (* 2n+1 *)
  | double2 : binnat -> binnat. (* 2n+2 *)

  Fixpoint Succ (n : binnat) : binnat :=
    match n with
    | bzero      => double1 bzero
    | double1 n' => double2 n'
    | double2 n' => double1 (Succ n')
    end.

  Fixpoint double (n : binnat) : binnat :=
    match n with
    | bzero      => bzero
    | double1 n' => double2 (double n')
    | double2 n' => double2 (Succ (double n'))
    end.

  Fixpoint Double (n : nat) : nat :=
    match n with
    | O    => O
    | S n' => S (S (Double n'))
    end.

  Definition Double1 (n : nat) : nat := S (Double n).

  Definition Double2 (n : nat) : nat := S (S (Double n)).

  Fixpoint binary (n : nat) : binnat :=
    match n with
    | O    => bzero
    | S n' => Succ (binary n')
    end.

End basics.

Section binary_equiv.

  Local Fixpoint unary' (n : binnat) : nat :=
    match n with
    | bzero      => O
    | double1 n' => Double1 (unary' n')
    | double2 n' => Double2 (unary' n')
    end.

  Let succunary (n : binnat) : unary' (Succ n) = S (unary' n).
  Proof.
    induction n.
    - reflexivity.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Qed.

  Let unarybinary : Sect binary unary'.
  Proof.
    intros n; induction n as [|n IHn].
    - reflexivity.
    - simpl. rewrite succunary. apply ap. exact IHn.
  Qed.

  Definition double1binary (n : nat) : binary (Double1 n) = double1 (binary n).
  Proof.
    induction n.
    - reflexivity.
    - change (binary (Double1 n.+1)) with (Succ (Succ (binary (Double n).+1))).
      rewrite IHn. reflexivity.
  Qed.

  Definition double2binary (n : nat) : binary (Double2 n) = double2 (binary n).
  Proof.
    induction n.
    - reflexivity.
    - change (binary (Double2 n.+1)) with (Succ (Succ (binary (Double n).+2))).
      rewrite IHn. reflexivity.
  Qed.

  Let binaryunary : Sect unary' binary.
  Proof.
    intros n; induction n.
    - reflexivity.
    - rewrite double1binary. apply ap. exact IHn.
    - rewrite double2binary. apply ap. exact IHn.
  Qed.

  Global Instance isequiv_binary : IsEquiv binary :=
    isequiv_adjointify binary unary' binaryunary unarybinary.

  Definition equiv_binary : nat <~> binnat :=
    BuildEquiv _ _  binary isequiv_binary.

End binary_equiv.

Notation equiv_unary  := equiv_binary ^-1.
Notation unary := equiv_unary.

Section semiring_struct.

  Global Instance binnat_0 : Zero binnat := bzero.
  Global Instance binnat_1 : One binnat := double1 bzero.

  Local Fixpoint binnat_plus' (m n : binnat) : binnat :=
    match m, n with
    | bzero      , n'         => n'
    | double1 m' , bzero      => double1 m'
    (* compute m + n as 2m'+1 + 2n'+1 = 2(m'+n') + 2 *)
    | double1 m' , double1 n' => double2 (binnat_plus' m' n')
    (* compute m + n as 2m'+1 + 2n'+2 = 2(m'+n')+2 + 1 = 2(m' + n' + 1) + 1 *)
    | double1 m' , double2 n' => double1 (Succ (binnat_plus' m' n'))
    | double2 m' , bzero      => double2 m'
    (* compute m + n as 2m'+2 + 2n'+1 = 2(m'+n')+2 + 1 = 2(m' + n' + 1) + 1 *)
    | double2 m' , double1 n' => double1 (Succ (binnat_plus' m' n'))
    (* compute m + n as 2m'+2 + 2n'+2 = 2(m'+n')+2 + 2 = 2(m' + n' + 1) + 2*)
    | double2 m' , double2 n' => double2 (Succ (binnat_plus' m' n'))
    end.
  Global Instance binnat_plus : Plus binnat := binnat_plus'.

  Local Fixpoint binnat_mult' (m n : binnat) : binnat :=
    match m with
    | bzero      => bzero
    (* compute (2m'+1)*n as 2m'n+n *)
    | double1 m' => (binnat_mult' m' n) + (binnat_mult' m' n) + n
    | double2 m' => (binnat_mult' m' n) + (binnat_mult' m' n) + n + n
    end.
  Global Instance binnat_mult : Mult binnat := binnat_mult'.

End semiring_struct.

Section semiring_laws.

  Definition binarysucc (n : nat) : binary n.+1 = Succ (binary n).
  Proof.
    reflexivity.
  Qed.

  Definition unarysucc : forall m, unary (Succ m) = S (unary m).
  Proof.
    equiv_intros binary n.
    rewrite <- binarysucc.
    rewrite eissect, eissect.
    reflexivity.
  Qed.

  Definition binnatplussucc : forall (m n : binnat), (Succ m) + n = Succ (m + n).
  Proof.
    induction m; induction n; try reflexivity; simpl; rewrite <- IHm; done.
  Qed.

  Definition binaryplus (m n : nat) : binary m + binary n = binary (m + n).
  Proof.
    induction m; induction n; try reflexivity.
    - simpl. rewrite binnatplussucc. apply ap. done.
    - simpl. rewrite <- IHm. rewrite binnatplussucc. done.
  Qed.

  Definition unaryplus (m n : binnat) : unary m + unary n = unary (m + n).
  Proof.
    etransitivity (unary (binary (_^-1 m + _^-1 n))).
    - apply ((eissect binary (unary m + unary n)) ^).
    - rewrite <- binaryplus.
      rewrite (eisretr binary m), (eisretr binary n).
      reflexivity.
  Qed.

  Local Instance binnat_add_assoc : Associative binnat_plus.
  Proof.
    hnf; equiv_intros binary x y z.
    change binnat_plus with plus.
    rewrite binaryplus, binaryplus, binaryplus, binaryplus.
    apply ap.
    apply associativity.
  Qed.

  Local Instance binnat_add_comm : Commutative binnat_plus.
  Proof.
    hnf; equiv_intros binary x y.
    change binnat_plus with plus.
    rewrite binaryplus, binaryplus.
    apply ap.
    apply plus_comm.
  Qed.

  Definition binnatmultsucc : forall (m n : binnat), (Succ m) * n = n + (m * n).
  Proof.
    induction m.
    - intros n. change (bzero + n = n + bzero).
      apply commutativity.
    - intros n. simpl.
      change (double2 m * n) with ((m * n) + (m * n) + n + n).
      apply commutativity.
    - intros n. simpl.
      change (double1 (Succ m) * n) with ((Succ m) * n + (Succ m) * n + n).
      rewrite IHm.
      rewrite (commutativity n (double2 m * n)).
      rewrite (commutativity n (m * n)).
      rewrite <- (associativity (m * n) n (m * n + n)).
      rewrite (commutativity n (m * n + n)).
      rewrite (associativity (m * n) _ _).
      rewrite (associativity (m * n) (m * n) n).
      done.
  Qed.

  Definition binarymult (m n : nat) : binary m * binary n = binary (m * n).
  Proof.
    induction m; induction n; try reflexivity; rewrite binnatmultsucc, IHm, binaryplus; done.
  Qed.

  Definition unarymult (m n : binnat) : unary m * unary n = unary (m * n).
  Proof.
    etransitivity (unary (binary (_^-1 m * _^-1 n))).
    - apply ((eissect binary (unary m * unary n)) ^).
    - rewrite <- binarymult.
      rewrite (eisretr binary m), (eisretr binary n).
      reflexivity.
  Qed.

  Local Instance binnat_mult_assoc : Associative binnat_mult.
  Proof.
    hnf; equiv_intros binary x y z.
    change binnat_mult with mult.
    rewrite binarymult, binarymult, binarymult, binarymult.
    apply ap.
    apply associativity.
  Qed.

  Local Instance binnat_mult_comm : Commutative binnat_mult.
  Proof.
    hnf; equiv_intros binary x y.
    change binnat_mult with mult.
    rewrite binarymult, binarymult.
    apply ap.
    apply commutativity.
  Qed.

  Local Instance binnat_distr_l : LeftDistribute binnat_mult binnat_plus.
  Proof.
    hnf; equiv_intros binary x y z.
    change binnat_plus with plus.
    change binnat_mult with mult.
    rewrite binaryplus, binarymult, binarymult, binarymult, binaryplus.
    apply ap.
    apply plus_mult_distr_l.
  Qed.

  Local Instance binnat_distr_r : RightDistribute binnat_mult binnat_plus.
  Proof.
    hnf; equiv_intros binary x y z.
    change binnat_plus with plus.
    change binnat_mult with mult.
    rewrite binaryplus, binarymult, binarymult, binarymult, binaryplus.
    apply ap.
    apply plus_mult_distr_r.
  Qed.

  Global Instance binnat_set : IsHSet binnat.
  Proof.
    apply (trunc_equiv nat binary).
  Qed.

  Global Instance binnat_semiring : SemiRing binnat.
  Proof.
    split; try split; try split; try split; hnf; intros.
    1, 5: exact (binnat_set x y).
    all: apply (equiv_inj unary).
    1, 2, 3, 7: repeat rewrite <- unaryplus.
    4, 5, 6, 7: rewrite <- unarymult.
    4, 5, 7: rewrite <- unarymult.
    4, 5: rewrite <- unarymult.
    4: rewrite <- unaryplus.
    5: rewrite <- unarymult.
    all: apply nat_semiring.
  Qed.

End semiring_laws.

Section naturals.

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
    - intros x y z w. apply nat_full. assumption.
    - intros m n. split.
      + intros E. apply (equiv_inj unary). apply nat_full. assumption.
      + intros p. apply nat_full. exact (ap unary p).
  Qed.

  Local Instance binnat_full : FullPseudoSemiRingOrder binnat_le binnat_lt.
  Proof.
    split.
    - intros m n; apply nat_le_hprop.
    - split; try intros m n; try apply nat_full.
      + split; try intros m n; try apply nat_full.
        * split; try intros m n; try apply nat_full.
          -- apply _.
          -- apply cotransitive.
          -- split; intros E.
             ++ assert (X : unary m = unary n) by by apply tight_apart.
                apply (((equiv_ap unary m n) ^-1) X).
             ++ rewrite E. apply nat_full. reflexivity.
        * intros E k. apply nat_full. exact E.
      + intros E.
        assert (H : exists w, (unary n) = (unary m) + w) by by apply nat_full.
        destruct H as [w L].
        exists (binary w).
        rewrite <- (eisretr unary w), unaryplus in L.
        apply (equiv_inj unary). exact L.
      + intros m. split; intros k l E; unfold lt, binnat_lt in *.
        * rewrite <- unaryplus, <- unaryplus. apply nat_full. exact E.
        * rewrite <- unaryplus, <- unaryplus in E.
          apply (strictly_order_reflecting (plus (unary m))). exact E.
      + intros k l E. apply nat_full.
        unfold apart, binnat_apart in E.
        rewrite <- (unarymult m n), <- (unarymult k l) in E. exact E.
      + intros E F. unfold lt, binnat_lt. rewrite <- (unarymult m n).
        apply nat_full; assumption.
    - intros m n. apply nat_full.
  Qed.

  Global Instance binnat_naturals_to_semiring : NaturalsToSemiRing binnat:=
    fun _ _ _ _ _ _ => fix f (n: binnat) :=
      match n with
      | bzero => 0
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
    Context {R:Type} `{SemiRing R}.

    Notation toR := (naturals_to_semiring binnat R).
    Notation toR_fromnat := (naturals_to_semiring nat R).
    Notation toR_vianat := (toR_fromnat ∘ unary).

    Definition f_suc (m : binnat) : toR (Succ m) = (toR m)+1.
    Proof.
      induction m.
      - change (2 * 0 + 1 = 0 + 1).
        rewrite mult_comm.
        rewrite mult_0_l.
        done.
      - change (2 * (toR m) + 2 = 2 * (toR m) + 1 + 1).
        apply plus_assoc.
      - induction m as [|m _|m _].
        + change (2 * (2 * 0 + 1) + 1 = 2 * 0 + 2 + 1).
          rewrite plus_mult_distr_l.
          rewrite (@mult_1_r _ Aplus Amult Azero Aone H _).
          rewrite mult_0_r, mult_0_r.
          reflexivity.
        + change (2 * (2 * (toR m) + 2) + 1 = 2 * (2 * (toR m) + 1 ) + 2 + 1).
          apply (ap (fun z => z + 1)).
          assert (L : 2 * toR m + 2 = 2 * toR m + 1 + 1) by by rewrite plus_assoc.
          rewrite L; clear L.
          rewrite plus_mult_distr_l.
          rewrite mult_1_r.
          reflexivity.
        + simpl in IHm.
          change ((2 * (toR (double1 (Succ m))) + 1 = 2 * (toR (double2 m)) + 2 + 1)).
          rewrite IHm; clear IHm.
          rewrite plus_mult_distr_l.
          rewrite mult_1_r.
          reflexivity.
    Qed.

    Definition f_nat : forall m : binnat, toR m = toR_vianat m.
    Proof.
      equiv_intro binary n.
      induction n as [|n IHn].
      - reflexivity.
      - induction n as [|n _].
        + change ((1 + 1) * 0 + 1 = 1).
          rewrite mult_0_r. apply plus_0_l.
        + rewrite f_suc. rewrite IHn.
          assert (L : (toR_fromnat ∘ binary^-1) (binary n.+1) + 1
                      = toR_fromnat ((binary^-1 (binary n.+1)).+1)%nat).
          {
            simpl rewrite (plus_comm _ 1).
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
      unfold Compose.
      rewrite <- (unaryplus a a').
      apply nat_to_sr_morphism.
    Qed.

    Let f_preserves_mult (a a' : binnat) : toR (a * a') = toR a * toR a'.
    Proof.
      rewrite f_nat, f_nat, f_nat.
      unfold Compose.
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
      equiv_intro binary n.
      rewrite f_nat; unfold Compose.
      rewrite eissect.
      refine (toR_unique (h ∘ binary) n).
    Qed.
  End for_another_semiring.

  Global Instance binnat_naturals : Naturals binnat.
  Proof.
    split.
    - exact binnat_semiring.
    - exact binnat_full.
    - intros. apply binnat_to_sr_morphism.
    - intros. apply binnat_toR_unique. assumption.
  Qed.

End naturals.

Section decidable.

  Let ineq_bzero_double1 n : bzero <> double1 n.
  Proof.
    intros p.
    change ((fun x => match x with | double1 y => Unit | _ => Empty end) bzero).
    rapply (@transport binnat).
    - exact p^.
    - exact tt.
  Qed.

  Let ineq_bzero_double2 n : bzero <> double2 n.
  Proof.
    intros p.
    change ((fun x => match x with | double2 y => Unit | _ => Empty end) bzero).
    rapply (@transport binnat).
    - exact p^.
    - exact tt.
  Qed.

  Let ineq_double1_double2 m n : double1 m <> double2 n.
  Proof.
    intros p.
    change ((fun x => match x with | double2 y => Unit | _ => Empty end) (double1 m)).
    rapply (@transport binnat).
    - exact p^.
    - exact tt.
  Qed.

  Let undouble (m : binnat) : binnat :=
    match m with
    | bzero => bzero
    | double1 k => k
    | double2 k => k
    end.

  Local Instance double1_inj : Injective double1
  := { injective := fun a b E => ap undouble E }.

  Local Instance double2_inj : Injective double2
  := { injective := fun a b E => ap undouble E }.

  Global Instance binnat_dec : DecidablePaths binnat.
  Proof.
    intros m; induction m as [|m IHm|m IHm]; intros n; induction n as [|n IHn|n IHn].
    all:
      first
        [ left ; reflexivity
        | right ; (idtac + apply symmetric_neq);
          first
               [ apply ineq_bzero_double1
               | apply ineq_bzero_double2
               | apply ineq_double1_double2
               ]
        | destruct (IHm n) as [eq | ineq];
          [ left; apply ap; exact eq
          | right; intros E;
            first
              [ apply (injective double1) in E
              | apply (injective double2) in E
              ]; auto
          ]
        ].
  Defined.

End decidable.

Section other_laws.

Instance binnat_plus_cancel_l (z:binnat) : LeftCancellation plus z.
Proof.
  intros x y p.
  apply (equiv_inj unary).
  apply (ap unary) in p.
  rewrite <- unaryplus, <- unaryplus in p.
  exact (left_cancellation _ _ _ _ p).
Qed.

Instance binnat_mult_cancel_l (z : binnat): PropHolds (z <> 0) -> LeftCancellation (.*.) z.
Proof.
  intros E. hnf in E.
  assert (H : unary z <> unary 0).
  {
    intros q.
    apply (equiv_inj unary) in q.
    exact (E q).
  }
  intros x y p.
  apply (ap unary) in p.
  rewrite <- unarymult, <- unarymult in p.
  exact (equiv_inj unary (nat_mult_cancel_l (unary z) H _ _ p)).
Qed.

Local Instance binnat_le_total : TotalRelation (_:Le binnat).
Proof.
  intros x y. apply nat_le_total.
Qed.
Local Instance binnat_lt_irrefl : Irreflexive (_:Lt binnat).
Proof.
  intros x. apply nat_lt_irrefl.
Qed.

End other_laws.

Section trichotomy.

  (* TODO this is an inefficient implementation. Instead, write this
  without going via the unary naturals. *)
  Instance binnat_trichotomy : Trichotomy (lt:Lt binnat).
  Proof.
    intros x y.
    pose (T := nat_trichotomy (unary x) (unary y)).
    destruct T as [l|[c|r]].
    - left; assumption.
    - right; left. apply (equiv_inj unary); assumption.
    - right; right; assumption.
  Defined.

End trichotomy.

Section minus.

  Local Fixpoint Pred (m : binnat) : binnat :=
    match m with
    | bzero      => bzero
    | double1 m' => double m'
    | double2 m' => double1 m'
    end.

  Let succ_double (m : binnat) : Succ (double m) = double1 m.
  Proof.
    induction m.
    - reflexivity.
    - change (double1 (Succ (double m)) = double1 (double1 m)).
      rewrite IHm; reflexivity.
    - change (double1 (Succ (Succ (double m))) = double1 (double2 m)).
      rewrite IHm; reflexivity.
  Qed.

  Let double_succ (m : binnat) : double (Succ m) = double2 m.
  Proof.
    induction m.
    - reflexivity.
    - change (double2 (Succ (double m)) = double2 (double1 m)).
      rewrite succ_double; reflexivity.
    - change (double2 (double (Succ m)) = double2 (double2 m)).
      rewrite IHm; reflexivity.
  Qed.

  Let pred_succ (m : binnat) : Pred (Succ m) = m.
  Proof.
    induction m; try reflexivity.
    - exact (double_succ m).
  Qed.

  Let double_pred (m : binnat) : double (Pred m) = Pred (Pred (double m)).
  Proof.
    induction m; try reflexivity.
    - exact (double_succ (double m))^.
  Qed.

  Let pred_double2 (m : binnat) : Pred (double2 m) = double1 m.
  Proof.
    induction m; reflexivity.
  Qed.

  Let pred_double1 (m : binnat) : Pred (double1 m) = double m.
  Proof.
    induction m; reflexivity.
  Qed.

  (*     2*(m-1)+1 = 2*m - 1 *)

  Local Fixpoint binnat_cut_minus' (m n : binnat) : binnat :=
    match m, n with
    | bzero      , n'         => bzero
    | m'         , bzero      => m'
    (* compute m - n as 2m'+1 - 2n'+1 = 2(m'-n') *)
    | double1 m' , double1 n' => double (binnat_cut_minus' m' n')
    (* compute m - n as 2m'+1 - 2n'+2 = 2(m'-n') - 1 = Pred (double (m' - n')) *)
    | double1 m' , double2 n' => Pred (double (binnat_cut_minus' m' n'))
    (* compute m - n as 2m'+2 - 2n'+1 *)
    | double2 m' , double1 n' => Pred (double (binnat_cut_minus' (Succ m') n'))
    (* compute m - n as 2m'+2 - 2n'+2 = 2(m'-n') = double (m' - n') *)
    | double2 m' , double2 n' => double (binnat_cut_minus' m' n')
    end.

  Global Instance binnat_cut_minus: CutMinus binnat := binnat_cut_minus'.

  Let binnat_minus_zero (m : binnat) : m ∸ bzero = m.
  Proof.
    induction m; reflexivity.
  Qed.

  Let binnat_zero_minus (m : binnat) : bzero ∸ m = bzero.
  Proof.
    induction m; reflexivity.
  Qed.

  Let pred_succ_minus (m n : binnat) : Pred (Succ m ∸ n) = m ∸ n.
  Proof.
    revert n; induction m; intros n; induction n; try reflexivity.
    - change (Pred (double (bzero ∸ n)) = bzero).
      rewrite binnat_zero_minus; reflexivity.
    - change (Pred (Pred (double (bzero ∸ n))) = bzero ∸ double2 n).
      rewrite binnat_zero_minus, binnat_zero_minus; reflexivity.
    - change (Pred (Pred (double (Succ m ∸ n))) = double (m ∸ n)).
      rewrite <- double_pred.
      apply ap.
      exact (IHm n).
    - change (double (Succ m) = double2 m ∸ bzero).
      rewrite binnat_minus_zero.
      exact (double_succ m).
    - change (Pred (Pred (double (Succ m ∸ n))) = double (m ∸ n)).
      rewrite <- double_pred.
      apply ap.
      exact (IHm n).
  Qed.

  Let double_cases (m : binnat) : (bzero = double m) + hfiber double2 (double m).
  Proof.
    induction m.
    - left; reflexivity.
    - right; exists (double m); reflexivity.
    - right; exists (Succ (double m)); reflexivity.
  Defined.

  Let binnat_minus_succ (m n : binnat) : Succ m ∸ Succ n = m ∸ n.
  Proof.
    revert n; induction m; intros n; induction n; try reflexivity.
    - change (Pred (double (bzero ∸ n)) = bzero ∸ double1 n).
      rewrite binnat_zero_minus, binnat_zero_minus. reflexivity.
    - change (double (bzero ∸ (Succ n)) = bzero ∸ double2 n).
      rewrite binnat_zero_minus, binnat_zero_minus. reflexivity.
    - change (Pred (double (Succ m ∸ bzero)) = double1 m ∸ bzero).
      rewrite binnat_minus_zero, binnat_minus_zero.
      rewrite double_succ, pred_double2. reflexivity.
    - change (Pred (double (Succ m ∸ Succ n)) = Pred (double (m ∸ n))).
      rewrite IHm. reflexivity.
    - change (double (Succ m ∸ bzero) = double2 m ∸ bzero).
      rewrite binnat_minus_zero, binnat_minus_zero, double_succ.
      reflexivity.
    - change (double (Succ m ∸ Succ n) = double (m ∸ n)).
      rewrite IHm. reflexivity.
  Qed.

  Let binaryminus (x y : nat) : binary x ∸ binary y = binary (x ∸ y).
  Proof.
    revert y; induction x; intros y; induction y; try reflexivity.
    - apply binnat_zero_minus.
    - apply binnat_minus_zero.
    - simpl in *. rewrite binnat_minus_succ.
      rewrite IHx. reflexivity.
  Qed.

  Let unaryminus (m n : binnat) : unary m ∸ unary n = unary (m ∸ n).
  Proof.
    etransitivity (unary (binary (_^-1 m ∸ _^-1 n))).
    - apply ((eissect binary (unary m ∸ unary n)) ^).
    - rewrite <- binaryminus.
      rewrite (eisretr binary m), (eisretr binary n).
      reflexivity.
  Qed.

  Global Instance binnat_cut_minus_spec : CutMinusSpec binnat binnat_cut_minus.
  Proof.
    split.
    - intros m n E. apply (equiv_inj unary).
      rewrite <- unaryplus, <- unaryminus.
      apply nat_cut_minus_spec.
      assumption.
    - intros m n E. apply (equiv_inj unary).
      rewrite <- unaryminus.
      apply nat_cut_minus_spec.
      assumption.
  Qed.

End minus.
