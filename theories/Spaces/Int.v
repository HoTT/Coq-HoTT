From HoTT.Basics Require Import Overture Numeral Tactics Decidable.
From HoTT.Basics Require Import Equivalences PathGroupoids Trunc Iff.
Require Import Types.Paths Types.Universe.
Require Import Spaces.Nat.Core Spaces.SInt.
(** Users of this file likely want the instances in Equiv.BiInv, such as [isequiv_isbiinv], so we export this file. *)
Require Export Equiv.BiInv.

(** * The integers, defined as a HIT *)

(** Following "The integers as a higher inductive type" by Altenkirch and Scoccola, we define the integers as a higher inductive type.  Morally it is the free pointed type with a biinvertible self-map.  This representation leads to more convenient induction and recursion principles that avoid needing to split into many cases as happens with the signed integers [SInt].  Moreover, many results hold definitionally instead of requiring lengthy proofs.  Examples include results about addition, multiplication, iteration of equivalences and exponentiation of loops such as [int_add_succ_l], [int_mul_pred_l], [int_iter_succ_l], and [loopexp_pred_r] to name just a few.  We also have a convenient lemma [int_homotopic] for proving that two functions [Int -> P] are homotopic.  Part of what makes it easy to use is that the functions being compared often compute definitionally on [zero] and [int_succ].

One difference compared to the Altenkirch-Scoccola paper is that we prove additional induction principles, [int_ind_biinv] and [int_ind_equiv].  The key to these is a carefully chosen proof of [int_succ_pred] that satisfies the half-adjoint law.  Then, using [int_ind_equiv], we are able to trivially prove [int_homotopic] (their Theorem 2.4) without using univalence or needing to introduce "prBiInv" (squares preserving bi-invertible maps).  As a result, we don't need univalence for any fundamental results about the integers.

One thing to be aware of is that the representation of integers is no longer definitionally unique. For example, [2 - 3] is not definitionally equal to [-1].  [int_reduce] or [ltac:(decide)] can be used to show that these are equal, with [int_reduce] being faster, as illustrated in test/Spaces/Int.v. *)

Set Universe Minimization ToSet.

Declare Scope int_scope.
Delimit Scope int_scope with int.
Local Open Scope int_scope.

(** ** The definition of [Int] *)

Module Export Int.
  Section Int.

    (** Here we are modeling the HIT which has a point [zero] and a successor map [int_succ] which is a biinvertible equivalence.  [int_pred] and [int_pred2] are its left and right inverses. *)

    Private Inductive Int : Type0 :=
    | zero : Int
    | int_succ : Int -> Int
    | int_pred : Int -> Int
    | int_pred2 : Int -> Int.

    Axiom int_pred_succ : int_pred o int_succ == idmap.

    Axiom int_succ_pred2 : int_succ o int_pred2 == idmap.

    Context {P : Int -> Type} (t0 : P zero) (e : forall z : Int, P z -> P (int_succ z))
      (r : forall z : Int, P z -> P (int_pred z)) (s : forall z : Int, P z -> P (int_pred2 z))
      (re : forall (z : Int) (t : P z), int_pred_succ z # (r (int_succ z) (e z t)) = t)
      (es : forall (z : Int) (t : P z), int_succ_pred2 z # (e (int_pred2 z) (s z t)) = t).

    Fixpoint int_ind (z : Int) : P z
      := match z with
      | zero => fun _ _ => t0
      | int_succ z => fun _ _ => e z (int_ind z)
      | int_pred z => fun _ _ => r z (int_ind z)
      | int_pred2 z => fun _ _ => s z (int_ind z)
      end re es.
      (** We make sure that this depends on [re] and [es] as well. *)

    (** The beta principles for [int_ind] on [int_pred_succ] and [int_succ_pred2]. *)
    Axiom int_ind_beta_int_pred_succ
      : forall (z : Int), apD int_ind (int_pred_succ z) = re z (int_ind z).

    Axiom int_ind_beta_int_succ_pred2
      : forall (z : Int), apD int_ind (int_succ_pred2 z) = es z (int_ind z).

  End Int.
End Int.

(** We sometimes want to treat the integers as a pointed type with basepoint given by 0. *)
Instance ispointed_int : IsPointed Int := zero.

(** Successor is biinvertible.  It follows from typeclass inference that it is an equivalence. *)
Instance isbiinv_int_succ : IsBiInv int_succ
  := Build_IsBiInv _ _ _ int_pred2 int_pred int_succ_pred2 int_pred_succ.

Definition biinv_int_succ : BiInv Int Int
  := Build_BiInv _ _ int_succ _.

(** The predecessor is an equivalence on [Int]. *)
Instance isequiv_int_pred : IsEquiv int_pred
  := isequiv_retr_biinv int_succ.

Notation "z .+1" := (int_succ z) : int_scope.
Notation "z .-1" := (int_pred z) : int_scope.

(** [int_pred] is a section of [int_succ]. *)
Definition int_succ_pred : int_succ o int_pred == idmap
  := retr_is_sect_isbiinv int_succ.

(** [int_pred2] is a retraction of [int_succ]. *)
Definition int_pred2_succ : int_pred2 o int_succ == idmap
  := sect_is_retr_isbiinv int_succ.

(** Our proof of [retr_is_sect_isbiinv] was carefully chosen so that the data showing that [int_succ] and [int_pred] form an equivalence satisfies the adjoint law. *)
Definition int_succ_isadj (z : Int)
  : int_succ_pred (int_succ z) = ap int_succ (int_pred_succ z)
  := eisadj int_succ z.

(** ** Induction and recursion principles for Int *)

Definition int_ind_biinv {P : Int -> Type} (t0 : P zero)
  (e : forall z : Int, P z -> P z.+1) {iseq : forall z, IsBiInv (e z)}
  : forall z, P z.
Proof.
  snapply (int_ind t0 e).
  - intro z.
    exact ((retr_biinv (e z.-1)) o transport P (int_succ_pred z)^).
  - intro z.
    exact ((e (int_pred2 z))^-1 o transport P (int_succ_pred2 z)^).
  - intros z p; cbn beta.
    lhs_V napply (ap_transport _ (fun z => retr_biinv (e z))).
    lhs napply (ap (retr_biinv (e z))).
    { lhs napply transport_compose.
      lhs_V napply transport_pp.
      apply transport2.
      lhs napply (ap inverse (int_succ_isadj z) @@ 1).
      apply concat_Vp. }
    cbn. apply eissect_biinv.
  - intros z p; cbn beta.
    rewrite eisretr.
    apply transport_pV.
Defined.

Definition int_ind_equiv {P : Int -> Type} (t0 : P zero)
  (e : forall z : Int, P z -> P z.+1) {iseq : forall z, IsEquiv (e z)}
  : forall z, P z
  := @int_ind_biinv P t0 e (fun z => isbiinv_isequiv _ (iseq z)).

Section RecursionPrinciple.

  Context {P : Type} (t0 : P) (f : P -> P) (g1 g2 : P -> P)
    (s : g1 o f == idmap) (r : f o g2 == idmap).

  (** The recursion principle. *)
  Definition int_rec : Int -> P.
  Proof.
    snapply (int_ind t0 (fun _ => f) (fun _ => g1) (fun _ => g2)).
    all: intros z t; cbn.
    all: lhs napply transport_const.
    - apply s.
    - apply r.
  Defined.

  Definition int_rec_beta_int_pred_succ
    : forall z, ap int_rec (int_pred_succ z) = s (int_rec z).
  Proof.
    intro z.
    napply (cancelL (transport_const (int_pred_succ z) _)).
    lhs_V napply apD_const.
    napply int_ind_beta_int_pred_succ.
  Defined.

  Definition int_rec_beta_int_succ_pred2
    : forall z, ap int_rec (int_succ_pred2 z) = r (int_rec z).
  Proof.
    intro z.
    napply (cancelL (transport_const (int_succ_pred2 z) _)).
    lhs_V napply apD_const.
    napply int_ind_beta_int_succ_pred2.
  Defined.

End RecursionPrinciple.

(** The recursion principle phrased using a biinvertible map. *)
Definition int_rec_biinv {P : Type} (t0 : P) (f : P -> P) `{IsBiInv P P f}
  : Int -> P
  := int_rec t0 f (retr_biinv f) (sect_biinv f) (eissect_biinv f) (eisretr_biinv f).

(** The recursion principle phrased using a half-adjoint equivalence. *)
Definition int_rec_equiv {P : Type} (t0 : P) (f : P -> P) `{IsEquiv P P f}
  : Int -> P
  := @int_rec_biinv P t0 f (isbiinv_isequiv _ _).

(** Equivalence iteration.  The properties of this are proved later in the file. *)
Definition int_iter {A} (f : A -> A) `{!IsEquiv f} (z : Int) (a0 : A) : A
  := int_rec_equiv a0 f z.

Section Uniqueness.

  Context {P : Type} (e : BiInv P P).

  (** The following uniqueness principle states that if two maps out of [Int] agree on 0 and commute with the successor, then they are homotopic. *)
  Definition int_homotopic_biinv (k1 : Int -> P) (k2 : Int -> P)
    (p0 : k1 zero = k2 zero) (pf1 : k1 o int_succ == e o k1) (pf2 : k2 o int_succ == e o k2)
    : k1 == k2.
  Proof.
    snapply int_ind_equiv; cbn beta.
    - exact p0.
    - intro z.
      exact (equiv_concat_l (pf1 z) _ oE equiv_concat_r (pf2 z)^ _ oE equiv_ap e _ _).
    - exact _.
  Defined.

  (** As a special case, we can characterize the recursor. *)
  Definition int_homotopic_rec (t0 : P) (k : Int -> P)
    (p0 : k zero = t0) (pf : k o int_succ == e o k)
    (rec := int_rec_biinv t0 e)
    : k == rec
    := int_homotopic_biinv k rec p0 pf (fun _ => idpath).

End Uniqueness.

(** The same uniqueness principle but for half-adjoint equivalences. *)
Definition int_homotopic {P : Type} (f : P -> P)
  {e' : IsEquiv f} (k1 : Int -> P) (k2 : Int -> P)
  (p0 : k1 zero = k2 zero) (pf1 : k1 o int_succ == f o k1)
  (pf2 : k2 o int_succ == f o k2)
  : forall (z : Int), k1 z = k2 z
  := int_homotopic_biinv (Build_BiInv P P _ (isbiinv_isequiv f e')) k1 k2 p0 pf1 pf2.

(** ** [Int] is equivalent to [SInt] *)

Definition int_to_sint : Int -> SInt
  := int_rec sint_zero sint_succ sint_pred sint_pred sint_pred_succ sint_succ_pred.

Definition sint_to_int : SInt -> Int.
Proof.
  intro s; induction s as [|n IHz|n IHz].
  - exact zero.
  - exact (int_succ IHz).
  - exact (int_pred IHz).
Defined.

Definition sint_to_int_issect : int_to_sint o sint_to_int == idmap.
Proof.
  intro s; induction s as [|[|n] IHz|[|n] IHz].
  1, 2, 4: reflexivity.
  - exact (ap sint_succ IHz).
  - exact (ap sint_pred IHz).
Defined.

Definition sint_to_int_succ : sint_to_int o sint_succ == int_succ o sint_to_int.
Proof.
  intro s; induction s as [|[|n] IHz|[|n] IHz].
  1-3: reflexivity.
  all: symmetry; exact (int_succ_pred _).
Defined.

Definition sint_to_int_isretr : sint_to_int o int_to_sint == idmap.
Proof.
  napply (int_homotopic_biinv biinv_int_succ).
  1,3: reflexivity.
  intro z; simpl.
  apply sint_to_int_succ.
Defined.

(** [sint_to_int] is biinvertible.  It follows from typeclass inference that it is an equivalence. *)
Instance isbiinv_sint_to_int : IsBiInv sint_to_int
  := Build_IsBiInv _ _ _ _ _ sint_to_int_isretr sint_to_int_issect.

(** Since [SInt] has decidable equality, so does [Int]. *)
Instance decidablepaths_int@{} : DecidablePaths Int
  := decidablepaths_equiv SInt _ _.

(** Since [SInt] is a set, therefore also [Int] is a set. *)
Instance ishset_int : IsHSet Int
  := istrunc_isequiv_istrunc SInt _.

(** The following function reduces an integer expression by cancelling successive successor and predecessor terms. It is homotopic to the identity by [sint_to_int_isretr]. *)
Definition int_reduce : Int -> Int := sint_to_int o int_to_sint.

(** From the equivalence to [SInt] we can deduce another induction principle for [Int].  This one has weak hypotheses, but since [HN 1 (HP 0 t)] doesn't necessarily transport to [t] along [int_pred_succ 0], it is impossible for it to compute well on general [int_pred] and [int_succ] operations.  Passing through [SInt] normalizes terms giving us a canonical choice. *)
Definition int_ind_sint (P : Int -> Type)
  (H0 : P zero)
  (HP : forall z, P z -> P z.+1)
  (HN : forall z, P z -> P z.-1)
  : forall z, P z.
Proof.
  equiv_intro sint_to_int s.
  induction s as [|n IHz|n IHz].
  - exact H0.
  - destruct n as [|n].
    all: apply HP, IHz.
  - destruct n as [|n].
    all: apply HN, IHz.
Defined.

Definition int_ind_iff (P : Int -> Type)
  (t0 : P zero) (f : forall z : Int, P z <-> P z.+1)
  : forall z, P z.
Proof.
  srapply (int_ind_sint P t0).
  - intro z.  exact (fst (f z)).
  - equiv_intro int_succ z.
    refine (_ o snd (f z)).
    exact (transport P (int_pred_succ z)^).
Defined.

(** ** Printing and parsing *)

(** We pass through [SInt] for printing and parsing. *)
Definition int_to_number_int : Int -> Numeral.int := sint_to_number_int o int_to_sint.

Definition int_of_number_int : Numeral.int -> Int := sint_to_int o sint_of_number_int.

Number Notation Int int_of_number_int int_to_number_int : int_scope.

(** ** Integer arithmetic *)

(** *** Negation *)

Definition int_neg (z : Int) : Int
  := int_rec_equiv zero int_pred z.

Notation "- z" := (int_neg z) : int_scope.

(** Negation is involutive. *)
Definition int_neg_neg (z : Int) : --z = z.
Proof.
  revert z.
  by srapply (int_homotopic int_succ).
Defined.

(** Negation is an equivalence. *)
Instance isequiv_int_neg : IsEquiv int_neg.
Proof.
  snapply (isequiv_adjointify int_neg int_neg).
  1,2: napply int_neg_neg.
Defined.

(** Negation is injective. *)
Definition isinj_int_neg (x y : Int) : -x = -y -> x = y
  := equiv_inj int_neg.

(** The negation of a successor is the predecessor of the negation. *)
Definition int_neg_succ (z : Int) : -(z.+1) = (-z).-1
  := idpath.

(** The negation of a predecessor is the successor of the negation. *)
Definition int_neg_pred (z : Int) : -(z.-1) = (-z).+1
  := idpath.

(** *** Addition *)

(** We define addition by recursion on the first argument. *)
Definition int_add (x y : Int) : Int
  := int_iter int_succ x y.

Infix "+" := int_add : int_scope.
Infix "-" := (fun x y => x + -y) : int_scope.

(** Integer addition with zero on the left is the identity by definition. *)
Definition int_add_0_l (z : Int) : 0 + z = z
  := idpath.

(** Adding a successor on the left is the successor of the sum. *)
Definition int_add_succ_l (x y : Int) : x.+1 + y = (x + y).+1
  := idpath.

(** Adding a predecessor on the left is the predecessor of the sum. *)
Definition int_add_pred_l (x y : Int) : x.-1 + y = (x + y).-1
  := idpath.

(** Integer addition with 1 on the left is the successor. *)
Definition int_add_1_l (z : Int) : 1 + z = z.+1
  := idpath.

(** Integer addition with zero on the right is the identity. *)
Definition int_add_0_r (z : Int) : z + 0 = z.
Proof.
  revert z.
  by srapply (int_homotopic int_succ).
Defined.

(** Adding a successor on the right is the successor of the sum. *)
Definition int_add_succ_r (x y : Int) : x + y.+1 = (x + y).+1.
Proof.
  revert x.
  by srapply (int_homotopic int_succ).
Defined.

(** Integer addition is commutative. *)
Definition int_add_comm (x y : Int) : x + y = y + x.
Proof.
  revert x.
  srapply (int_homotopic int_succ); cbn beta.
  - by rewrite int_add_0_r.
  - reflexivity.
  - intro z.
    by rewrite int_add_succ_r.
Defined.

(** Adding a predecessor on the right is the predecessor of the sum. *)
Definition int_add_pred_r (x y : Int) : x + y.-1 = (x + y).-1
  := int_add_comm x y.-1 @ ap int_pred (int_add_comm y x).

(** Integer addition with 1 on the right is the successor. *)
Definition int_add_1_r (z : Int) : z + 1 = z.+1.
Proof.
  revert z.
  by srapply (int_homotopic int_succ).
Defined.

(** Integer addition is associative. *)
Definition int_add_assoc (x y z : Int) : x + (y + z) = x + y + z.
Proof.
  revert x.
  by srapply (int_homotopic int_succ).
Defined.

(** Negation is a left inverse with respect to integer addition. *)
Definition int_add_neg_l (z : Int) : -z + z = 0.
Proof.
  revert z.
  srapply (int_homotopic idmap); cbn beta.
  1,3: reflexivity.
  simpl; intro s.
  rewrite int_add_succ_r.
  apply int_pred_succ.
Defined.

(** Negation is a right inverse with respect to integer addition. *)
Definition int_add_neg_r (z : Int) : z - z = 0
  := int_add_comm _ _ @ int_add_neg_l _.

(** Negation distributes over addition. *)
Definition int_neg_add (x y : Int) : -(x + y) = -x - y.
Proof.
  revert x.
  by srapply (int_homotopic int_pred).
Defined.

(** Addition is an equivalence with first argument fixed. *)
Instance isequiv_int_add_l (x : Int) : IsEquiv (int_add x).
Proof.
  srapply (isequiv_adjointify _ (int_add (-x))).
  all: simpl; intro y.
  all: lhs napply int_add_assoc.
  - by rewrite int_add_neg_r.
  - by rewrite int_add_neg_l.
Defined.

(** Addition is an equivalence with second argument fixed.  This also follows from the previous result and [int_add_comm], but this proof computes better. *)
Instance isequiv_int_add_r (y : Int) : IsEquiv (fun x => x + y).
Proof.
  snapply (isequiv_adjointify _ (fun x => x - y)).
  all: simpl; intro x.
  all: lhs_V napply int_add_assoc.
  - rewrite int_add_neg_l.
    apply int_add_0_r.
  - rewrite int_add_neg_r.
    apply int_add_0_r.
Defined.

(** *** Multiplication *)

(** We define multiplication by recursion on the first argument.  This depends on the proof that addition is an equivalence. *)
Definition int_mul (x y : Int) : Int
  := int_iter (fun z => z + y) x 0.

Infix "*" := int_mul : int_scope.

(** Integer multiplication with zero on the left is zero by definition. *)
Definition int_mul_0_l (z : Int) : 0 * z = 0
  := idpath.

(** Multiplication with a successor on the left adds the other argument. *)
Definition int_mul_succ_l (x y : Int) : x.+1 * y = x * y + y
  := idpath.

(** Multiplication with a predecessor on the left subtracts the other argument. *)
Definition int_mul_pred_l (x y : Int) : x.-1 * y = x * y - y
  := idpath.

(** Integer multiplication with one on the left is the identity. *)
Definition int_mul_1_l (z : Int) : 1 * z = z
  := idpath.

(** Integer multiplication with [-1] on the left is negation. *)
Definition int_mul_neg1_l (z : Int) : -1 * z = -z
  := idpath.

(** Multiplying with a negation on the left is the same as negating the product. *)
Definition int_mul_neg_l (x y : Int) : -x * y = -(x * y).
Proof.
  revert x.
  rapply (int_homotopic (fun x => x - y)); cbn beta.
  1,2: reflexivity.
  simpl; intro x.
  apply int_neg_add.
Defined.

(** Multiplication distributes over addition on the left. *)
Definition int_dist_l (x y z : Int) : x * (y + z) = x * y + x * z.
Proof.
  revert x.
  srapply (int_homotopic (fun x => x + (y + z))); cbn beta.
  1,2: reflexivity.
  simpl; intro x.
  lhs_V napply int_add_assoc.
  rewrite (int_add_comm y (x * z + z)).
  rewrite (int_add_comm y z).
  by rewrite <- 2 int_add_assoc.
Defined.

(** Integer multiplication with zero on the right is zero. *)
Definition int_mul_0_r (z : Int) : z * 0 = 0.
Proof.
  revert z.
  rapply (int_homotopic idmap); cbn beta.
  1,3: reflexivity.
  simpl; intro z.
  apply int_add_0_r.
Defined.

(** Multiplying with a successor on the right adds the other argument. *)
Definition int_mul_succ_r (x y : Int) : x * y.+1 = x + x * y.
Proof.
  revert x.
  rapply (int_homotopic (fun x => x + y.+1)); cbn beta.
  1,2: reflexivity.
  simpl; intro z.
  rewrite int_add_succ_r.
  by rewrite int_add_assoc.
Defined.

(** Multiplication is commutative. *)
Definition int_mul_comm (x y : Int) : x * y = y * x.
Proof.
  revert x.
  srapply (int_homotopic (fun x => x + y)); cbn beta.
  - symmetry; apply int_mul_0_r.
  - reflexivity.
  - intro z.
    rewrite int_add_comm.
    apply int_mul_succ_r.
Defined.

(** Multiplying with a predecessor on the right subtracts the other argument. *)
Definition int_mul_pred_r (x y : Int) : x * y.-1 = x * y - x
  := int_mul_comm x y.-1 @ ap _ (int_mul_comm y x).

(** Integer multiplication with one on the right is the identity. *)
Definition int_mul_1_r (z : Int) : z * 1 = z
  := int_mul_comm _ _.

(** Multiplying with a negation on the right is the same as negating the product. *)
Definition int_mul_neg_r (x y : Int) : x * -y = -(x * y)
  := int_mul_comm _ _ @ int_mul_neg_l _ _ @ ap _ (int_mul_comm _ _).

(** Multiplication distributes over addition on the right. *)
Definition int_dist_r (x y z : Int) : (x + y) * z = x * z + y * z.
Proof.
  by rewrite int_mul_comm, int_dist_l, !(int_mul_comm z).
Defined.

(** Multiplication is associative. *)
Definition int_mul_assoc (x y z : Int) : x * (y * z) = x * y * z.
Proof.
  revert x.
  srapply (int_homotopic (fun x => x + (y * z))); cbn beta.
  1,2: reflexivity.
  simpl; intro x.
  by rewrite int_dist_r.
Defined.

(** ** Results about iteration of equivalences *)

Definition int_iter_neg {A} (f : A -> A) `{IsEquiv _ _ f} (z : Int) (a : A)
  : int_iter f (int_neg z) a = int_iter f^-1 z a.
Proof.
  revert z.
  by srapply (int_homotopic f^-1).
Defined.

Definition int_iter_succ_l {A} (f : A -> A) `{IsEquiv _ _ f} (z : Int) (a : A)
  : int_iter f z.+1 a = f (int_iter f z a)
  := idpath.

Definition int_iter_succ_r {A} (f : A -> A) `{IsEquiv _ _ f} (z : Int) (a : A)
  : int_iter f z.+1 a = int_iter f z (f a).
Proof.
  revert z.
  by srapply (int_homotopic f).
Defined.

Definition int_iter_pred_l {A} (f : A -> A) `{IsEquiv _ _ f} (z : Int) (a : A)
  : int_iter f z.-1 a = f^-1 (int_iter f z a)
  := idpath.

Definition int_iter_pred_r {A} (f : A -> A) `{IsEquiv _ _ f} (z : Int) (a : A)
  : int_iter f z.-1 a = int_iter f z (f^-1 a).
Proof.
  revert z.
  srapply (int_homotopic f); cbn beta.
  1,3: reflexivity.
  intro z; simpl.
  exact (eissect f (int_iter f z a) @ (eisretr f (int_iter f z a))^).
Defined.

Definition int_iter_add {A} (f : A -> A) `{IsEquiv _ _ f} (x y : Int)
  : int_iter f (x + y) == int_iter f x o int_iter f y.
Proof.
  intro a; revert x.
  by srapply (int_homotopic f).
Defined.

(** If [g : A -> A'] commutes with automorphisms of [A] and [A'], then it commutes with iteration. *)
Definition int_iter_commute_map {A A'} (f : A -> A) `{!IsEquiv f}
  (f' : A' -> A') `{!IsEquiv f'}
  (g : A -> A') (p : g o f == f' o g) (z : Int) (a : A)
  : g (int_iter f z a) = int_iter f' z (g a).
Proof.
  revert z.
  srapply (int_homotopic f'); cbn beta.
  1,3: reflexivity.
  intro x; apply p.
Defined.

(** In particular, homotopic maps have homotopic iterations. *)
Definition int_iter_homotopic (z : Int) {A} (f f' : A -> A) `{!IsEquiv f} `{!IsEquiv f'}
  (h : f == f')
  : int_iter f z == int_iter f' z
  := int_iter_commute_map f f' idmap h z.

(** [int_iter f n x] doesn't depend on the proof that [f] is an equivalence. *)
Definition int_iter_agree (z : Int) {A} (f : A -> A) {ief ief' : IsEquiv f}
  : forall x, @int_iter A f ief z x = @int_iter A f ief' z x
  := int_iter_homotopic z f f (fun _ => idpath).

(** An important invariance property of iteration.  The most obvious proof attempts fail, for the reasons described in the comment for [int_ind_sint]. *)
Definition int_iter_invariant {A} (f : A -> A) `{!IsEquiv f}
  (P : A -> Type)
  (Psucc : forall a, P a -> P (f a))
  (Ppred : forall a, P a -> P (f^-1 a))
  (a0 : A) (Pa0 : P a0)
  : forall z, P (int_iter f z a0).
Proof.
  snapply int_ind_sint; cbn.
  - exact Pa0.
  - intros z IH. apply Psucc, IH.
  - intros z IH. apply Ppred, IH.
Defined.

(** ** Exponentiation of loops *)

Definition loopexp {A : Type} {a : A} (p : a = a) (z : Int) : (a = a)
  := int_iter (equiv_concat_r p a) z idpath.

Definition loopexp_succ_r {A : Type} {a : A} (p : a = a) (z : Int)
  : loopexp p z.+1 = loopexp p z @ p
  := idpath.

Definition loopexp_pred_r {A : Type} {a : A} (p : a = a) (z : Int)
  : loopexp p z.-1 = loopexp p z @ p^
  := idpath.

Definition loopexp_succ_l {A : Type} {a : A} (p : a = a) (z : Int)
  : loopexp p z.+1 = p @ loopexp p z.
Proof.
  simpl; revert z.
  rapply (int_homotopic (equiv_concat_r p a)); cbn beta.
  - napply concat_1p_p1.
  - reflexivity.
  - intro z; simpl.
    apply concat_p_pp.
Defined.

Definition loopexp_pred_l {A : Type} {a : A} (p : a = a) (z : Int)
  : loopexp p z.-1 = p^ @ loopexp p z.
Proof.
  simpl; revert z.
  rapply (int_homotopic (equiv_concat_r p a)); cbn beta.
  - napply concat_1p_p1.
  - intro z; simpl.
    exact (concat_pp_V _ _ @ (concat_pV_p _ _)^).
  - intro z; simpl.
    apply concat_p_pp.
Defined.

Definition ap_loopexp {A B} (f : A -> B) {a : A} (p : a = a) (z : Int)
  : ap f (loopexp p z) = loopexp (ap f p) z.
Proof.
  napply int_iter_commute_map.
  intro q; apply ap_pp.
Defined.

Definition loopexp_add {A : Type} {a : A} (p : a = a) x y
  : loopexp p (x + y) = loopexp p x @ loopexp p y.
Proof.
  revert x.
  rapply (int_homotopic (equiv_concat_r p a)); cbn beta.
  - symmetry; apply concat_1p.
  - reflexivity.
  - intro z; simpl.
    rewrite 2 concat_pp_p.
    by rewrite <- loopexp_succ_l.
Defined.

(** Under univalence, exponentiation of loops corresponds to iteration of auto-equivalences. *)

Definition equiv_path_loopexp {A : Type} (p : A = A) (z : Int) (a : A)
  : equiv_path A A (loopexp p z) a = int_iter (equiv_path A A p) z a.
Proof.
  apply int_iter_commute_map with (g:=fun p => equiv_path A A p a).
  intro q; cbn.
  napply transport_pp.
Defined.

Definition loopexp_path_universe `{Univalence} {A : Type} (f : A <~> A)
  (z : Int) (a : A)
  : transport idmap (loopexp (path_universe f) z) a = int_iter f z a.
Proof.
  revert f; equiv_intro (equiv_path A A) p.
  rhs_V napply equiv_path_loopexp.
  nrefine (ap (fun q => equiv_path A A (loopexp q z) a) _).
  apply eissect.
Defined.

(** ** Converting between integers and naturals *)

(** We can convert a [nat] to an [Int] by mapping [0] to [zero] and [S n] to [int_succ n].  Various operations on [nat] are preserved by this function.  We will make this into a coercion later; we delay doing so to ensure that the lemmas about [int_of_nat] are interpreted as we want them to be. *)
Definition int_of_nat (n : nat) : Int
  := nat_iter n int_succ zero.

(** [int_of_nat] preserves zero. *)
Definition int_of_nat_zero : int_of_nat 0 = 0
  := idpath.

(** [int_of_nat] preserves successors. *)
Definition int_of_nat_succ (n : nat)
  : int_of_nat (n.+1) = (int_of_nat n).+1
  := idpath.

(** [int_of_nat] preserves predecessors of positive naturals. *)
Definition int_of_nat_pred (n : nat) (npos : (0 < n)%nat)
  : int_of_nat (nat_pred n) = (int_of_nat n).-1.
Proof.
  rhs_V napply (ap (fun _ => _.-1) (nat_succ_pred n npos)).
  simpl; symmetry.
  apply int_pred_succ.
Defined.

(** [int_of_nat] preserves addition. *)
Definition int_of_nat_add (n m : nat)
  : int_of_nat (n + m) = int_of_nat n + int_of_nat m.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - exact (ap _ IHn).
Defined.

(** [int_of_nat] preserves subtraction when not truncated. *)
Definition int_of_nat_sub (n m : nat) (ngeq : (m <= n)%nat)
  : int_of_nat (n - m) = int_of_nat n - int_of_nat m.
Proof.
  induction ngeq as [|n H IHn].
  - rhs napply int_add_neg_r.
    by rewrite nat_sub_cancel.
  - rewrite nat_sub_succ_l; only 2: exact _; simpl.
    exact (ap _ IHn).
Defined.

(** [int_of_nat] preserves multiplication. This makes [int_of_nat] a semiring homomorphism. *)
Definition int_of_nat_mul (n m : nat)
  : int_of_nat (n * m) = int_of_nat n * int_of_nat m.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - simpl; rewrite <- IHn.
    rhs_V napply int_of_nat_add.
    by rewrite nat_add_comm.
Defined.

Coercion int_of_nat : nat >-> Int.
