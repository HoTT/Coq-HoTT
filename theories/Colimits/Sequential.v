(** * Sequential colimits *)

(** We present a proof of the conjecture that sequential colimits in HoTT appropriately commute with Σ-types. As a corollary, we characterize the path space of a sequential colimit as a sequential colimit of path spaces. For the written account of these results see https://www.cs.cornell.edu/~ks858/papers/sequential_colimits_homotopy.pdf. *)

From HoTT Require Import Basics.
Require Import Types.
Require Import Diagrams.Diagram.
Require Import Diagrams.Sequence.
Require Import Diagrams.Cocone.
Require Import Colimits.Colimit.
Require Import Spaces.Nat.Core.
Require Import Homotopy.IdentitySystems.

Local Open Scope nat_scope.
Local Open Scope path_scope.

(** [coe] is [transport idmap : (A = B) -> (A -> B)], but is described as the underlying map of an equivalence so that Coq knows that it is an equivalence. *)
Notation coe := (fun p => equiv_fun (equiv_path _ _ p)).
Notation "a ^+" := (@arr sequence_graph _ _ _ 1 a).

(** Mapping spaces into hprops from colimits of sequences can be characterized. *)
Lemma equiv_colim_seq_rec `{Funext} (A : Sequence) (P : Type) `{IsHProp P}
  : (Colimit A -> P) <~> (forall n, A n -> P).
Proof.
  symmetry.
  refine (equiv_colimit_rec P oE _).
  refine (issig_Cocone _ _ oE _).
  symmetry.
  srapply Build_Equiv.
  1: exact pr1.
  exact _.
Defined.

(** If a sequential colimit has maps homotopic to a constant map then the colimit is contractible. *)
Instance contr_colim_seq_into_prop {funext : Funext} (A : Sequence)
  (a : forall n, A n) (H : forall n, const (a n.+1) == A _f idpath)
  : Contr (Colimit A).
Proof.
  transparent assert (B : Sequence).
  { srapply Build_Sequence.
    1: exact A.
    intros n.
    exact (const (a n.+1)). }
  rapply contr_equiv'.
  1: rapply equiv_functor_colimit.
  1: rapply (equiv_sequence B A).
  1: reflexivity.
  { intros n e.
    exists equiv_idmap.
    intros x.
    symmetry.
    exact (H _ (e x)). }
  srapply Build_Contr.
  1: exact (colim (D:=B) 1%nat (a 1%nat)).
  srapply Colimit_ind.
  { intros i x.
    induction i.
    1: exact (colimp (D:=B) _ _ idpath x).
    refine (IHi (a i) @ _).
    refine ((colimp (D:=B) _ _ idpath (a i))^ @ _).
    refine ((colimp (D:=B) _ _ idpath (a i.+1))^ @ _).
    exact (colimp (D:=B) _ _ idpath x). }
  intros n m [] x.
  rewrite transport_paths_FlFr.
  rewrite ap_const.
  rewrite ap_idmap.
  destruct n; simpl; hott_simpl.
Qed.

Definition seq_shift_from_zero_by {A : Sequence} (a : A 0) k : A k.
Proof.
  induction k as [ | k q].
  - exact a.
  - exact q^+.
Defined.

Notation "a ^+ k" := (seq_shift_from_zero_by a k).

(** Shiftings; described in the paragraph after Lemma 3.7. *)
Definition seq_pair_shift {A : Sequence} (x : sig A) : sig A.
Proof.
  destruct x as [n a]; exact (n.+1; a^+).
Defined.

Definition seq_pair_shift_by {A : Sequence} (x : sig A) (k : nat) : sig A.
Proof.
  induction k as [ | k y].
  - exact x.
  - exact (seq_pair_shift y).
Defined.

Notation "x ^++" := (seq_pair_shift x).
Notation "x ^++ k" := (seq_pair_shift_by x k).

Definition seq_pair_shift_assoc {A : Sequence} (x : sig A) (k : nat)
  : (x^++)^++k = x^++(k.+1).
Proof.
  induction k as [ | k q].
  - reflexivity.
  - exact (ap seq_pair_shift q).
Defined.

Definition seq_shift_pair_from_zero {A : Sequence} (a : A 0) k : (0;a)^++k = (k;a^+k).
Proof.
  induction k as [ | k q].
  - reflexivity.
  - exact (ap seq_pair_shift q).
Defined.

Notation inj A := (@colim sequence_graph A).
Notation glue A := (fun n => @colimp sequence_graph A n n.+1 1).

(** The uniqueness principle for sequential colimits; Lemma 3.3. *)
Definition seq_colimit_uniq {A : Sequence} E (F G : Colimit A -> E)
  (h : forall n, F o inj A n == G o inj A n)
  (H : forall n a, ap F (glue A n a) @ h n a = h n.+1 a^+ @ ap G (glue A n a))
  : F == G.
Proof.
  srapply (Colimit_ind _ h); intros n m p a; destruct p.
  generalize (H n a); generalize (h n a); destruct (glue A n a).
  intros p q; srefine ((concat_p1 _)^ @ _); srefine (_ @ (concat_1p _)); exact q^.
Defined.

(** The successor sequence from Lemma 3.6. *)
Definition succ_seq (A : Sequence) : Sequence
  := Build_Sequence (fun k => A k.+1) (fun k a => a^+).

(** The shifted sequence from Lemma 3.7. *)
Definition shift_seq (A : Sequence) n : Sequence
  := Build_Sequence (fun k => A (k+n)%nat) (fun k a => a^+).

(** The canonical equivalence between the colimit of the successor sequence and the colimit of the original sequence; Lemma 3.6. *)
Definition colim_succ_seq_to_colim_seq A : Colimit (succ_seq A) -> Colimit A.
Proof.
  srapply Colimit_rec; srapply Build_Cocone.
  + exact (fun n a => inj _ n.+1 a).
  + intros n m p; destruct p; exact (glue A n.+1).
Defined.

Definition colim_succ_seq_to_colim_seq_beta_glue A n a
  : ap (colim_succ_seq_to_colim_seq A) (glue (succ_seq A) n a) = glue A (n.+1) a.
Proof.
  srapply Colimit_rec_beta_colimp.
Defined.

Definition colim_succ_seq_to_colim_seq_ap_inj A n (a1 a2 : succ_seq A n) (p : a1 = a2)
  : ap (colim_succ_seq_to_colim_seq A) (ap (inj _ n) p) = ap (inj _ n.+1) p.
Proof.
  destruct p; reflexivity.
Defined.

Instance isequiv_colim_succ_seq_to_colim_seq A
  : IsEquiv (colim_succ_seq_to_colim_seq A).
Proof.
  srapply isequiv_adjointify.
  + srapply Colimit_rec; srapply Build_Cocone.
    * exact (fun n a => inj (succ_seq A) n a^+).
    * intros n m p a; destruct p; exact (glue (succ_seq A) n a^+).
  + srapply seq_colimit_uniq.
    * exact (fun n a => glue _ n a).
    * intros n a; rewrite ap_idmap, ap_compose, Colimit_rec_beta_colimp.
      rewrite colim_succ_seq_to_colim_seq_beta_glue; reflexivity.
  + srapply seq_colimit_uniq.
    * exact (fun n a => glue _ n a).
    * intros n a; rewrite ap_idmap, ap_compose, Colimit_rec_beta_colimp.
      rewrite (@Colimit_rec_beta_colimp _ A _ _ _ _ 1); reflexivity.
Defined.

Definition equiv_colim_succ_seq_to_colim_seq A : Colimit (succ_seq A) <~> Colimit A
  := Build_Equiv _ _ (colim_succ_seq_to_colim_seq A) _.

(** The canonical equivalence between the colimit of the shifted sequence and the colimit of the original sequence; Lemma 3.6. *)
Definition colim_shift_seq_to_colim_seq A n : Colimit (shift_seq A n) -> Colimit A.
Proof.
  srapply Colimit_rec; srapply Build_Cocone.
  + exact (fun k a => inj A (k+n)%nat a).
  + intros k l p; destruct p; exact (glue A (k+n)%nat).
Defined.

Definition colim_shift_seq_to_colim_seq_beta_glue A n k a
  : ap (colim_shift_seq_to_colim_seq A n) (glue (shift_seq A n) k a) = glue A (k+n)%nat a.
Proof.
  srapply Colimit_rec_beta_colimp.
Defined.

Definition colim_shift_seq_to_colim_seq_ap_inj A n k (a1 a2 : shift_seq A n k) (p : a1 = a2)
  : ap (colim_shift_seq_to_colim_seq A n) (ap (inj _ k) p) = ap (inj _ (k+n)%nat) p.
Proof.
  destruct p; reflexivity.
Defined.

Local Definition J {X Y Z} {x1 x2 : X} {y} {I : forall x, Y x -> Z} (p : x2 = x1)
  : I x2 y = I x1 (coe (ap Y p) y).
Proof.
  destruct p; reflexivity.
Defined.

Local Definition K {X Y} {x1 x2 : X} {y} F G (p : x1 = x2) :
  G x2 (coe (ap Y p) y) = coe (ap Y (ap F p)) (G x1 y).
Proof.
  destruct p; reflexivity.
Defined.

Local Definition L {X Y Z} {x1 x2 : X} {y} {F G} {I : forall x, Y x -> Z} {p : x2 = x1}
  (Q : forall x y, I (F x) (G x y) = I x y)
  : Q x2 y @ J p =
    J (ap F p) @ (ap (I (F x1)) (K F G p)^ @
    Q x1 (coe (ap Y p) y)).
Proof.
  destruct p; cbn.
  apply equiv_p1_1q.
  symmetry; apply concat_1p.
Defined.

Instance isequiv_colim_shift_seq_to_colim_seq `{Funext} A n
  : IsEquiv (colim_shift_seq_to_colim_seq A n).
Proof.
  induction n as [ | n e]; srapply isequiv_homotopic'.
  - srapply equiv_functor_colimit; srapply Build_diagram_equiv.
    + srapply Build_DiagramMap.
      * exact (fun k => coe (ap A (nat_add_zero_r k))).
      * intros k l p a; destruct p. exact (K S (fun n a => a^+) _).
    + exact _.
  - symmetry; srapply seq_colimit_uniq.
    + intros k a; exact (J (nat_add_zero_r k)).
    + intros k a; rewrite !Colimit_rec_beta_colimp; exact (L (glue A)).
  - transitivity (Colimit (succ_seq (shift_seq A n))).
    + srapply equiv_functor_colimit; srapply Build_diagram_equiv.
      * srapply Build_DiagramMap.
        { exact (fun k => coe (ap A (nat_add_succ_r k n))). }
        { intros k l p a; destruct p; rapply (K S (fun n a => a^+) (nat_add_succ_r k n)). }
      * exact _.
    + srefine (transitivity (equiv_colim_succ_seq_to_colim_seq _) (Build_Equiv _ _ _ e)).
  - symmetry; srapply seq_colimit_uniq.
    + intros k a; exact (J (nat_add_succ_r k n)).
    + intros k a; rewrite Colimit_rec_beta_colimp; simpl.
      rewrite 2(ap_compose' _ _ (glue _ k a)), Colimit_rec_beta_colimp, 2ap_pp.
      rewrite colim_succ_seq_to_colim_seq_ap_inj, colim_shift_seq_to_colim_seq_ap_inj.
      rewrite (colim_succ_seq_to_colim_seq_beta_glue (shift_seq A n)).
      rewrite colim_shift_seq_to_colim_seq_beta_glue; exact (L (glue A)).
Defined.

Definition equiv_colim_shift_seq_to_colim_seq `{Funext} A n
  : Colimit (shift_seq A n) <~> Colimit A
  := Build_Equiv _ _ (colim_shift_seq_to_colim_seq A n) _.

(** Corollary 7.7.1 for k := -2; implies Lemma 7.2. *)
Definition contr_colim_contr_seq `{Funext} (A : Sequence)
  : (forall k, Contr (A k)) -> Contr (Colimit A).
Proof.
  intro h_seqcontr; pose (unit_seq := Build_Sequence (fun _ => Unit) (fun _ _ => tt)).
  srapply (contr_equiv' (Colimit unit_seq)).
  - symmetry; srapply equiv_functor_colimit.
    srapply Build_diagram_equiv; srapply Build_DiagramMap.
    * exact (fun _ _ => tt).
    * intros n m p a; destruct p; reflexivity.
  - srapply (Build_Contr _ (inj unit_seq 0 tt)); intro y; symmetry; revert y.
    srapply seq_colimit_uniq.
    * intros n a; destruct a; induction n as [ | n r].
      + reflexivity.
      + exact (glue unit_seq n tt @ r).
    * intro n; destruct a; rewrite ap_idmap, ap_const, concat_p1; reflexivity.
Defined.

(** Fibered sequences; Section 4. *)
Record FibSequence (A : Sequence) := {
  fibSequence : sig A -> Type;
  fibSequenceArr x : fibSequence x -> fibSequence x^++
}.

Coercion fibSequence : FibSequence  >-> Funclass.

Arguments fibSequence {A}.
Arguments fibSequenceArr {A}.

Notation "b ^+f" := (fibSequenceArr _ _ b).

(** The Sigma of a fibered type sequence; Definition 4.3. *)
Definition sig_seq {A} (B : FibSequence A) : Sequence.
Proof.
  srapply Build_Sequence.
  - exact (fun n => {a : A n & B (n;a)}).
  - intros n [a b]; exact (a^+; b^+f).
Defined.

(** The canonical projection from the sequential colimit of Sigmas to the sequential colimit of the first component; Definition 4.3. *)
Definition seq_colim_sum_to_seq_colim_fst {A} (B : FibSequence A)
  : Colimit (sig_seq B) -> Colimit A.
Proof.
  srapply Colimit_rec; srapply Build_Cocone.
  - intros n [a _]; exact (inj _ n a).
  - intros n m p [a b]; destruct p; exact (glue _ n a).
Defined.

(** Given a sequence fibered over [A], each point [x : sig A] induces a new type sequence; Section 4. *)
Definition fib_seq_to_seq {A} (B : FibSequence A) (x : sig A) : Sequence.
Proof.
  srapply Build_Sequence; intro k; revert x; induction k as [ | k h].
  * exact (fun x => B x).
  * exact (fun x => h x^++).
  * exact (fun x b => b^+f).
  * exact (fun x => h x^++).
Defined.

(** The induced sequence can be equivalently described by using shifting; Lemma 7.1. *)
Definition fib_seq_to_seq' {A} (B : FibSequence A) (x : sig A) : Sequence
  := Build_Sequence (fun k => B x^++k) (fun k b => b^+f).

Definition equiv_fib_seq_to_seq {A} (B : FibSequence A) (x : sig A)
  : fib_seq_to_seq B x ~d~ fib_seq_to_seq' B x.
Proof.
  srapply Build_diagram_equiv.
  + srapply Build_DiagramMap.
    * intro n; revert x; induction n as [ | n e].
      - exact (fun _ => idmap).
      - exact (fun x => coe (ap B (seq_pair_shift_assoc x n)) o e x^++).
    * intros n m p; destruct p; revert x; induction n as [ | n p].
      - exact (fun _ _ => idpath).
      - exact (fun x b => K _ _ _ @ (ap _ (p (x^++) b))).
  + intro n; revert x; induction n as [ | n e].
    * exact (fun _ => isequiv_idmap _).
    * intro x; rapply isequiv_compose.
Defined.

(** A fibered type sequence defines a type family; Section 4. *)
Definition fib_seq_to_type_fam `{Univalence} {A} (B : FibSequence A) : Colimit A -> Type.
Proof.
  srapply Colimit_rec; srapply Build_Cocone.
  - exact (fun n a => Colimit (fib_seq_to_seq B (n;a))).
  - intros n m p a; destruct p; apply path_universe_uncurried.
    exact (equiv_colim_succ_seq_to_colim_seq (fib_seq_to_seq B (n;a))).
Defined.

Definition fib_seq_to_type_fam_beta_glue `{Univalence} {A} B n a :
  coe (ap (fib_seq_to_type_fam B) (glue A n a))=
  colim_succ_seq_to_colim_seq (fib_seq_to_seq B (n;a)).
Proof.
  srapply (ap _ (Colimit_rec_beta_colimp _ _ _ _ _ _) @ _).
  exact (transport_idmap_path_universe_uncurried _).
Defined.

Local Definition Delta {X Y} {x1 x2 : X} {F} (p : x1 = x2) (psi : coe (ap Y p) = F) y
  : (x1;y) = (x2;F y).
Proof.
  destruct p; destruct psi; reflexivity.
Defined.

Local Definition Delta_proj {X Y} {x1 x2 : X} {F} (p : x1 = x2) (psi : coe (ap Y p) = F) y
  : ap pr1 (Delta p psi y) = p.
Proof.
  destruct p; destruct psi; reflexivity.
Defined.

(** The canonical map from the sequential colimit of Sigmas to the Sigma of sequential colimits; Definition 5.1. *)
Definition seq_colim_sum_to_sum_seq_colim `{Univalence} {A} (B : FibSequence A)
  : Colimit (sig_seq B) -> sig (fib_seq_to_type_fam B).
Proof.
  srapply Colimit_rec; srapply Build_Cocone.
  - intros n [a b]; exact (inj A n a; inj (fib_seq_to_seq _ _) 0 b).
  - intros n m p [a b]; destruct p; srefine (_ @ ap _ (glue (fib_seq_to_seq _ _) 0 b)).
    srapply (Delta _ (fib_seq_to_type_fam_beta_glue B n a)).
Defined.

Definition seq_colim_sum_to_sum_seq_colim_beta_glue `{Univalence} {A} B n a b :
  ap (seq_colim_sum_to_sum_seq_colim B) (glue (sig_seq B) n (a;b)) =
  Delta _ (fib_seq_to_type_fam_beta_glue B n a) (inj _ _ _) @
  ap (exist _ (inj A n a)) (glue (fib_seq_to_seq _ _) 0 b).
Proof.
  srapply Colimit_rec_beta_colimp.
Defined.

(** An alternative induction principle for the sum of colimits; Lemma 5.2 and Section 6. *)
Section SeqColimitSumInd.

  Context `{Univalence} {A} (B : FibSequence A).
  Context (E : sig (fib_seq_to_type_fam B) -> Type).
  Context (e : forall n a b, E (seq_colim_sum_to_sum_seq_colim B (inj (sig_seq B) n (a;b)))).
  Context (t : forall n a b, ap (seq_colim_sum_to_sum_seq_colim B) (glue (sig_seq B) n (a;b))
    # e n.+1 (a^+) (b^+f) = e n a b).

  (** The point-point case of the nested induction; corresponds to "h" in the paper. *)
  Local Definition Q k : forall n a b, E (inj _ n a; inj _ k b).
  Proof.
    induction k as [ | k h].
    - exact e.
    - intros n a b; exact (Delta _ (fib_seq_to_type_fam_beta_glue B n a) _ # h n.+1 (a^+) b).
  Defined.

  (** The path-point case of the nested induction is just reflexivity; corresponds to "mu" in the paper. *)

  Local Definition Eta {X Y Z} {x : X} {y1 y2 : Y x} {z : sig Y} {p : y1 = y2}
    {q1 : z = (x;y1)} {q2 : z = (x;y2)} (theta : q2 = q1 @ ap _ p)
    : transport (Z o exist Y x) p o transport Z q1 == transport Z q2.
  Proof.
    symmetry in theta; destruct theta; destruct p; simpl; destruct q1. reflexivity.
  Defined.

  Local Definition Epsilon {X Y Z} {x1 x2 : X} {y1 y2} {F} (p : x1 = x2) {q : y1 = y2}
    {psi : coe (ap Y p) = F} {r : F y1 = F y2} (theta : ap F q = r)
    : transport (Z o exist Y x2) r o transport Z (Delta p psi y1) ==
      transport Z (Delta p psi y2) o transport (Z o exist Y x1) q.
  Proof.
    destruct theta; destruct q; reflexivity.
  Defined.

  (** The point-path case of the nested induction; corresponds to "H" in the paper. *)
  Local Definition R k : forall n a b,
    transport (E o exist _ (inj A n a)) (glue _ k b) (Q k.+1 n a (b^+)) = Q k n a b.
  Proof.
    induction k as [ | k h].
    - intros n a b; srapply (_ @ t n a b).
      srapply (Eta (seq_colim_sum_to_sum_seq_colim_beta_glue B n a b)).
    - intros n a b; srefine (_ @ ap _ (h n.+1 (a^+) b)).
      srapply (Epsilon (glue A n a) (colim_succ_seq_to_colim_seq_beta_glue _ _ _)).
  Defined.

  (** The point case of the nested induction; corresponds to "g" in the paper. *)
  Local Definition F n a : forall x, E (inj _ n a; x).
  Proof.
    srapply Colimit_ind.
    - exact (fun k => Q k n a).
    - intros k l p; destruct p; exact (R k n a).
  Defined.

  Local Definition F_beta_glue n a b : apD (F n a) (glue _ 0 b) = R 0 n a b.
  Proof.
    srapply Colimit_ind_beta_colimp.
  Defined.

  Local Definition Phi {X Y Z} {x1 x2 : X} {y1 y2} {F} (p : x1 = x2) {q : y1 = y2}
    {psi : coe (ap Y p) = F} {G1 : forall y, Z (x1;y)} {G2 : forall y, Z (x2;y)}
    {r : F y1 = F y2} (theta : ap F q = r)
    : forall u1 u2,
      apD G2 r @ u2 = ap (transport _ r) u1 @ Epsilon p theta (G1 y1) @
                      ap (transport Z (Delta p psi y2)) (apD G1 q)
      -> transport (fun y => G2 (F y) = Delta p psi y # G1 y) q u1 = u2.
  Proof.
    destruct theta; destruct q; intros u1 u2; rewrite ap_idmap, !concat_p1. simpl.
    intro s; destruct s; exact (concat_1p _).
  Defined.

  (** The path case of the nested induction; corresponds to "omega" in the paper. *)
  Local Definition G n a : forall y,
    F n a _ = Delta _ (fib_seq_to_type_fam_beta_glue B n a) y # F n.+1 (a^+) y.
  Proof.
    srapply Colimit_ind.
    - exact (fun k b => idpath).
    - intros k l p b; destruct p.
      snapply (Phi (glue A n a) (colim_succ_seq_to_colim_seq_beta_glue _ _ _)).
      rewrite (Colimit_ind_beta_colimp _ (fun k => Q k n a) _ _ _ idpath).
      rewrite (Colimit_ind_beta_colimp _ (fun k => Q k n.+1 a^+) _ _ _ idpath).
      rewrite concat_p1, concat_1p; reflexivity.
  Defined.

  Local Definition I {X Y Z} {x1 x2 : X} {p : x1 = x2} {F} (psi : coe (ap Y p) = F) {G1 G2}
    : transport (fun x => forall y, Z (x;y)) p G1 = G2 <~>
      forall y, G2 (F y) = Delta p psi y # G1 y.
  Proof.
    destruct p; destruct psi.
    exact (transitivity (equiv_path_inverse _ _) (equiv_apD10 _ _ _)).
  Defined.

  (** The alternative induction rule in curried form; corresponds to curried "G" in
      the paper. *)
  Definition seq_colim_sum_ind_cur : forall x y, E (x;y).
  Proof.
    srapply (Colimit_ind _ F); intros n m p a; destruct p.
    exact ((I (fib_seq_to_type_fam_beta_glue B n a))^-1 (G n a)).
  Defined.

  (** The computation rule for the alternative induction rule in curried form. *)
  Definition seq_colim_sum_ind_cur_beta_glue n a :
    I (fib_seq_to_type_fam_beta_glue B n a) (apD seq_colim_sum_ind_cur (glue _ n a)) = G n a.
  Proof.
    apply moveR_equiv_M; srapply Colimit_ind_beta_colimp.
  Defined.

  (** The alternative induction rule; corresponds to "G" in the paper. *)
  Definition seq_colim_sum_ind : forall x, E x.
  Proof.
    intros [x y]; apply seq_colim_sum_ind_cur.
  Defined.

  Local Definition Xi {X Y Z} G {x : X} {y1 y2 : Y x} {z : sig Y} {p : y1 = y2}
    {q1 : z = (x;y1)} {q2 : z = (x;y2)} (theta : q2 = q1 @ ap _ p)
    : apD (G o exist Y x) p =
      ap (transport (Z o exist Y x) p) (apD G q1)^ @ Eta theta (G z) @ apD G q2.
  Proof.
    revert theta; srapply (equiv_ind (equiv_path_inverse _ _)). intro s; destruct s.
    revert q1; srapply (equiv_ind (equiv_path_inverse _ _)); intro s; destruct s.
    destruct p; reflexivity.
  Defined.

  Local Definition Mu {X Y Z} {x1 x2 : X} (p : x1 = x2) {F} (G : forall z, Z z)
    {psi : coe (ap Y p) = F} {q} (theta : I psi (apD (fun x y => G (x;y)) p) = q) y
    : apD G (Delta p psi y) = (q y)^.
  Proof.
    destruct p; destruct psi; destruct theta; reflexivity.
  Defined.

  (** The computation rule for the alternative induction rule. *)
  Definition seq_colim_sum_ind_beta_glue : forall n a b,
    apD seq_colim_sum_ind (ap (seq_colim_sum_to_sum_seq_colim B) (glue (sig_seq B) n _)) =
    t n a b.
  Proof.
    intros n a b; pose (h := F_beta_glue n a b).
    rewrite (Xi seq_colim_sum_ind (seq_colim_sum_to_sum_seq_colim_beta_glue B n a b)) in h.
    rewrite (Mu (glue _ n a) seq_colim_sum_ind (seq_colim_sum_ind_cur_beta_glue n a)) in h.
    rewrite concat_1p in h; exact (cancelL _ _ _ h).
  Defined.

End SeqColimitSumInd.

(** An alternative recursion principle for the sum of colimits; Lemma 5.3. *)
Section SeqColimitSumRec.

  Context `{Univalence} {A} (B : FibSequence A).
  Context E (e : forall n a, B (n;a) -> E).
  Context (t : forall n a (b : B (n;a)), e n.+1 (a^+) (b^+f) = e n a b).

  Definition seq_colim_sum_rec : sig (fib_seq_to_type_fam B)-> E.
  Proof.
    exact (seq_colim_sum_ind B _ e (fun n a b => transport_const _ _ @ t n a b)).
  Defined.

  Definition seq_colim_sum_rec_beta_glue : forall n a b,
    ap seq_colim_sum_rec (ap (seq_colim_sum_to_sum_seq_colim B) (glue (sig_seq B) n (a;b))) =
    t n a b.
  Proof.
    intros n a b; srapply (cancelL _ _ _ ((apD_const _ _)^ @ _)).
    srapply seq_colim_sum_ind_beta_glue.
  Defined.

End SeqColimitSumRec.

(** Lemma 5.4. *)
Definition seq_colimit_sum_uniq `{Univalence} {A} (B : FibSequence A) E
  (F G : sig (fib_seq_to_type_fam B) -> E)
  : F o (seq_colim_sum_to_sum_seq_colim B) == G o (seq_colim_sum_to_sum_seq_colim B) ->
    F == G.
Proof.
  intro h; srapply (seq_colim_sum_ind B _ (fun _ _ _ => h _)); intros n a b.
  srapply ((transport_compose _ _ _ _)^ @ _); exact (apD h (glue (sig_seq B) n (a;b))).
Defined.

(** The canonical map from the sequential colimit of Sigmas to the Sigma of sequential colimits is an equivalence; Theorem 5.1. *)
Instance isequiv_seq_colim_sum_to_sum_seq_colim `{Univalence} {A} (B : FibSequence A)
  : IsEquiv (seq_colim_sum_to_sum_seq_colim B).
Proof.
  assert (L : {G : _ & G o seq_colim_sum_to_sum_seq_colim B == idmap}).
  - srapply (_;_).
    + srapply seq_colim_sum_rec.
      * exact (fun n a b => inj (sig_seq B) n (a;b)).
      * exact (fun n a b => glue (sig_seq B) n (a;b)).
    + srapply seq_colimit_uniq.
      * exact (fun n a => idpath).
      * intros n a; rewrite concat_1p, concat_p1, ap_compose, ap_idmap.
        rewrite seq_colim_sum_rec_beta_glue; reflexivity.
  - srapply (isequiv_adjointify _ L.1 _ L.2); srapply seq_colimit_sum_uniq.
    intro x; rewrite L.2; reflexivity.
Defined.

Definition equiv_seq_colim_sum_to_sum_seq_colim `{Univalence} {A} (B : FibSequence A)
  : Colimit (sig_seq B) <~> sig (fib_seq_to_type_fam B)
  := Build_Equiv _ _ _ (isequiv_seq_colim_sum_to_sum_seq_colim B).
  
(** The canonical map from the sequential colimit of Sigmas to the Sigma of sequential colimits commutes with the first projection; Theorem 5.1. *)
Definition seq_colim_sum_to_sum_seq_colim_fst `{Univalence} {A} (B : FibSequence A)
  : pr1 o (seq_colim_sum_to_sum_seq_colim B) == seq_colim_sum_to_seq_colim_fst B.
Proof.
  srapply seq_colimit_uniq.
  - exact (fun n a => idpath).
  - intros n [a b]; rewrite concat_1p, concat_p1, ap_compose, !Colimit_rec_beta_colimp.
    rewrite ap_pp, (Delta_proj _ (fib_seq_to_type_fam_beta_glue B n a)).
    srapply (whiskerL _ _ @ concat_p1 _); rewrite (ap_compose _ _ _)^; simpl.
    rewrite ap_const; reflexivity.
Defined.

(** The characterization of path spaces in sequential colimits; Theorem 7.4, first part. *)
Definition path_seq (A : Sequence) (a1 a2 : A 0)
  := Build_Sequence (fun k => a1^+k = a2^+k) (fun k p => ap (fun a => a^+) p).

Definition equiv_path_colim_zero `{Univalence} {A : Sequence} (a1 a2 : A 0) :
  (inj A 0 a1 = inj A 0 a2) <~> Colimit (path_seq A a1 a2). 
Proof.
  pose (B := Build_FibSequence A (fun x => a1^+(x.1) = x.2) (fun x => ap (fun a => a^+))).
  transitivity (fib_seq_to_type_fam B (inj A 0 a2)).
  + symmetry; srapply equiv_path_from_contr.
    - exact (inj (fib_seq_to_seq B (0;a1)) 0 idpath).
    - srefine (contr_equiv _ (seq_colim_sum_to_sum_seq_colim B)).
      srapply contr_colim_contr_seq; intro k; srapply contr_basedpaths.
  + srapply equiv_functor_colimit; srefine (transitivity (equiv_fib_seq_to_seq B (0;a2)) _).
    srapply Build_diagram_equiv.
    * srapply Build_DiagramMap.
      - exact (fun n => coe (ap B (seq_shift_pair_from_zero a2 n))).
      - intros n m p b; destruct p; srapply (K _ _ (seq_shift_pair_from_zero a2 n)).
    * exact _.
Defined.

(** The characterization of path spaces in sequential colimits; Theorem 7.4, second part. *)
Definition equiv_path_colim `{Univalence} {A : Sequence} n (a1 a2 : A n) :
  (inj A n a1 = inj A n a2) <~> Colimit (path_seq (shift_seq A n) a1 a2).
Proof.
  srefine (transitivity _ (equiv_path_colim_zero _ _)); symmetry.
  srapply (@equiv_ap _ _ (colim_shift_seq_to_colim_seq A n)).
Defined.

Open Scope trunc_scope.

(** Corollary 7.7.1, second part. *)
Instance trunc_seq_colim `{Univalence} {A : Sequence} k :
  (forall n, IsTrunc k (A n)) -> IsTrunc k (Colimit A) | 100.
Proof.
  revert A; induction k as [ | k IHk].
  - exact contr_colim_contr_seq.
  - intros A trH; apply istrunc_S; srapply Colimit_ind.
    + intro n; revert trH; revert A; induction n as [ | n IHn].
      * intros A trH a; srapply Colimit_ind.
        { intros m b; revert b; revert a; revert trH; revert A; induction m as [ | m IHm].
          { intros A trH a b.
            exact (istrunc_equiv_istrunc _ (equiv_inverse (equiv_path_colim _ a b))). }
          { intros A trH a b.
            srefine (istrunc_equiv_istrunc _ (equiv_inverse (equiv_concat_l (glue A _ a) _))).
            srapply (@istrunc_equiv_istrunc _ _ _ k (IHm (succ_seq A) _ (@arr _ A 0%nat _ 1%path a) b)).
            srapply (equiv_ap (colim_succ_seq_to_colim_seq A)). }}
        { intros n m p b; snapply path_ishprop; snapply ishprop_istrunc; exact _. }
      * intros A trH a; srapply (functor_forall_equiv_pb (colim_succ_seq_to_colim_seq A)).
        intro x; srapply (@istrunc_equiv_istrunc _ _ _ k (IHn (succ_seq A) _ a x)); srapply equiv_ap.
    + intros n m p a; snapply path_ishprop; snapply istrunc_forall.
      intro x; srapply ishprop_istrunc.
Defined.
