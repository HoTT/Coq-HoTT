(** We present a proof of the conjecture that sequential colimits in HoTT apropriately
    commute with Σ-types. As a corollary, we characterize the path space of a sequential
    colimit as a sequential colimit of path spaces. For the written account of these results
    see https://www.cs.cornell.edu/~ks858/papers/sequential_colimits_homotopy.pdf. *)

Require Import Basics.
Require Import Types.
Require Import Diagrams.Diagram.
Require Import Diagrams.Sequence.
Require Import Diagrams.Cocone.
Require Import Colimits.Colimit.
Require Import Spaces.Nat.
Require Import HProp.

Local Open Scope path_scope.

Section Sequence.

  Context (A : Sequence).

  Let f n := @arr _ A n _ 1.

  (** Liftings; described in the paragraph after Lemma 3.7. *)
  Definition seqPairLift (x : sig A) : sig A.
  Proof.
    destruct x as [n a]; exact (n.+1; f n a).
  Defined.

  Definition seqPairLiftBy (x : sig A) (k : nat) : sig A.
  Proof.
    induction k as [ | k y].
    - exact x.
    - exact (seqPairLift y).
  Defined.

  Notation "x ^+" := (seqPairLift x) (at level 0).
  Notation "x ^+ k" := (seqPairLiftBy x k) (at level 0).
  
  Definition seqPairLiftAssoc (x : sig A) (k : nat) : (x^+)^+k = x^+(k.+1).
  Proof.
    induction k as [ | k q].
    - reflexivity.
    - exact (ap seqPairLift q).
  Defined.

  Definition seqLiftFromZeroBy (a : A 0) k : A k.
  Proof.
    induction k as [ | k q].
    - exact a.
    - exact (f k q).
  Defined.

  Notation "a ^++ k" := (seqLiftFromZeroBy a k) (at level 0).

  Definition seqLiftPairZero (a : A 0) k : (0;a)^+k = (k;a^++k).
  Proof.
    induction k as [ | k q].
    - reflexivity.
    - exact (ap seqPairLift q).
  Defined.

  Notation inj A := (@colim sequence_graph A).
  Notation glue A := (fun n => @colimp sequence_graph A n n.+1 1).

  (** The uniqueness principle for sequential colimits; Lemma 3.3. *)
  Definition seqColimitUniqueness E (F G : Colimit A -> E)
    (h : forall n, F o inj A n == G o inj A n)
    (H : forall n a, ap F (glue A n a) @ h n a = h n.+1 (f n a) @ ap G (glue A n a))
    : F == G.
  Proof.
    srapply (Colimit_ind _ h); intros n m p a; destruct p.
    generalize (H n a); generalize (h n a); destruct (glue A n a).
    intros p q; srefine ((concat_p1 _)^ @ _); srefine (_ @ (concat_1p _)); exact q^.
  Defined.

  (** The successor sequence from Lemma 3.6. *)
  Definition succSeq : Sequence
    := Build_Sequence (fun k => A k.+1) (fun k => f k.+1).

  (** The shifted sequence from Lemma 3.7. *)
  Definition shiftSeq n : Sequence
    := Build_Sequence (fun k => A (k+n)%nat) (fun k => f (k+n)%nat).

End Sequence.

Arguments seqPairLift {A}.
Arguments seqPairLiftBy {A}.
Arguments seqLiftFromZeroBy {A}.
Arguments seqPairLiftAssoc {A}.

Notation "x ^+" := (seqPairLift x) (at level 0).
Notation "x ^+ k" := (seqPairLiftBy x k) (at level 0).
Notation "a ^++ k" := (seqLiftFromZeroBy a k) (at level 0).

Notation inj A := (@colim sequence_graph A).
Notation glue A := (fun n => @colimp sequence_graph A n n.+1 1).

Notation coe := (transport idmap).

Section ColimitSuccSequence.

  Context `{Funext} (A : Sequence).

  Let f n := @arr _ A n _ 1.

  (** The canonical equivalence between the colimit of the succesor sequence and the colimit
      of the original sequence; Lemma 3.6. *)
  Definition colimitSuccSeqToColimitSeq : Colimit (succSeq A) -> Colimit A.
  Proof.
    srapply Colimit_rec; srapply Build_Cocone.
    + exact (fun n a => inj _ n.+1 a).
    + intros n m p; destruct p; exact (glue A n.+1).
  Defined.

  Definition colimitSuccSeqToColimitSeq_beta_glue n a
    : ap colimitSuccSeqToColimitSeq (glue (succSeq A) n a) = glue A (n.+1) a.
  Proof.
    srapply Colimit_rec_beta_colimp.
  Defined.

  Definition colimitSuccSeqToColimitSeq_ap_inj n (a1 a2 : succSeq A n) (p : a1 = a2)
    : ap colimitSuccSeqToColimitSeq (ap (inj _ n) p) = ap (inj _ n.+1) p.
  Proof.
    destruct p; reflexivity.
  Defined.

  Global Instance isequiv_colimitSuccSeqToColimitSeq
    : IsEquiv colimitSuccSeqToColimitSeq.
  Proof.
    srapply isequiv_adjointify.
    + srapply Colimit_rec; srapply Build_Cocone.
      * exact (fun n a => inj (succSeq A) n (f n a)).
      * intros n m p a; destruct p; exact (glue (succSeq A) n (f n a)).
    + srapply seqColimitUniqueness.
      * exact (fun n a => glue _ n a).
      * intros n a; rewrite ap_idmap, ap_compose, Colimit_rec_beta_colimp.
        rewrite colimitSuccSeqToColimitSeq_beta_glue; reflexivity.
    + srapply seqColimitUniqueness.
      * exact (fun n a => glue _ n a).
      * intros n a; rewrite ap_idmap, ap_compose, Colimit_rec_beta_colimp.
        rewrite (@Colimit_rec_beta_colimp _ A _ _ _ _ 1); reflexivity.
  Defined.

  Definition equiv_colimitSuccSeqToColimitSeq : Colimit (succSeq A) <~> Colimit A
    := Build_Equiv _ _ colimitSuccSeqToColimitSeq _.

End ColimitSuccSequence.

Section ColimitShiftSequence.

  Context `{Funext} (A : Sequence).

  Let f n := @arr _ A n _ 1.

  (** The canonical equivalence between the colimit of the shifted sequence and the colimit
      of the original sequence; Lemma 3.6. *)
  Definition colimitShiftSeqToColimitSeq n : Colimit (shiftSeq A n) -> Colimit A.
  Proof.
    srapply Colimit_rec; srapply Build_Cocone.
    + exact (fun k a => inj A (k+n)%nat a).
    + intros k l p; destruct p; exact (glue A (k+n)%nat).
  Defined.

  Definition colimitShiftSeqToColimitSeq_beta_glue n k a
    : ap (colimitShiftSeqToColimitSeq n) (glue (shiftSeq A n) k a) = glue A (k+n)%nat a.
  Proof.
    srapply Colimit_rec_beta_colimp.
  Defined.

  Definition colimitShiftSeqToColimitSeq_ap_inj n k (a1 a2 : shiftSeq A n k) (p : a1 = a2)
    : ap (colimitShiftSeqToColimitSeq n) (ap (inj _ k) p) = ap (inj _ (k+n)%nat) p.
  Proof.
    destruct p; reflexivity.
  Defined.

  Local Definition nat_plus_n_O n : (n + 0)%nat = n.
  Proof.
  induction n as [ | n p].
    - reflexivity.
    - exact (ap S p).
  Defined.

  Local Definition nat_plus_n_Sm n m : (n + m.+1)%nat = (n + m)%nat.+1.
  Proof.
  induction n as [ | n p].
    - reflexivity.
    - exact (ap S p).
  Defined.

  Local Definition J {X Y Z} {x1 x2 : X} {y} {I : forall x, Y x -> Z} (p : x1 = x2) :
    I x1 y = I x2 (coe (ap Y p) y).
  Proof.
    destruct p; reflexivity.
  Defined.

  Local Definition Kappa {X Y} {x1 x2 : X} {y} F G (p : x1 = x2) :
    G x2 (coe (ap Y p) y) = coe (ap Y (ap F p)) (G x1 y).
  Proof.
    destruct p; reflexivity.
  Defined.

  Local Definition L {X Y Z} {x1 x2 : X} {y} {F G} {I : forall x, Y x -> Z} {p : x1 = x2}
    (Q : forall x y, I (F x) (G x y) = I x y)
    : Q x1 y @ J p = J (ap F p) @ (ap (I (F x2)) (Kappa F G p)^ @ Q x2 (coe (ap Y p) y)).
  Proof.
    destruct p; rewrite !concat_1p, concat_p1; reflexivity.
  Defined.

  Global Instance isequiv_colimitShiftSeqToColimitSeq n
    : IsEquiv (colimitShiftSeqToColimitSeq n).
  Proof.
    induction n as [ | n e]; srapply isequiv_homotopic'.
    - srapply equiv_functor_colimit; srapply Build_diagram_equiv.
      + srapply Build_DiagramMap.
        * exact (fun k => coe (ap A (nat_plus_n_O k))).
        * intros k l p a; destruct p; exact (Kappa _ f _).
      + intro k; srapply isequiv_path.
    - symmetry; srapply seqColimitUniqueness.
      + intros k a; exact (J (nat_plus_n_O k)).
      + intros k a; rewrite !Colimit_rec_beta_colimp; srapply (L (glue A)).
    - transitivity (Colimit (succSeq (shiftSeq A n))).
      + srapply equiv_functor_colimit; srapply Build_diagram_equiv.
        * srapply Build_DiagramMap.
          { exact (fun k => coe (ap A (nat_plus_n_Sm k n))). }
          { intros k l p a; destruct p; exact (Kappa _ f _). }
        * intro k; srapply isequiv_path.
      + srefine (transitivity (equiv_colimitSuccSeqToColimitSeq _) (Build_Equiv _ _ _ e)).
    - symmetry; srapply seqColimitUniqueness.
      + intros k a; exact (J (nat_plus_n_Sm k n)).
      + intros k a; rewrite Colimit_rec_beta_colimp; simpl.
      rewrite 2(ap_compose' _ _ (glue _ k a)), Colimit_rec_beta_colimp, 2ap_pp.
      rewrite colimitSuccSeqToColimitSeq_ap_inj, colimitShiftSeqToColimitSeq_ap_inj.
      rewrite (colimitSuccSeqToColimitSeq_beta_glue (shiftSeq A n)).
      rewrite colimitShiftSeqToColimitSeq_beta_glue; srapply (L (glue A)).
  Defined.

  Definition equiv_colimitShiftSeqToColimitSeq n : Colimit (shiftSeq A n) <~> Colimit A
    := Build_Equiv _ _ (colimitShiftSeqToColimitSeq n) _.

End ColimitShiftSequence.

(** Corollary 7.7.1 for k := -2; implies Lemma 7.2. *)
Definition contr_ColimitContrSeq `{Funext} (A : Sequence) :
  (forall k, Contr (A k)) -> Contr (Colimit A).
Proof.
  intro h_seqcontr; pose (unit_seq := Build_Sequence (fun _ => Unit) (fun _ _ => tt)).
  srapply (contr_equiv' (Colimit unit_seq)).
  - symmetry; srapply equiv_functor_colimit.
    srapply Build_diagram_equiv; srapply Build_DiagramMap.
    * exact (fun _ _ => tt).
    * intros n m p a; destruct p; reflexivity.
  - srapply (Build_Contr _ (inj unit_seq 0 tt)); intro y; symmetry; revert y.
    srapply seqColimitUniqueness.
    * intros n a; destruct a; induction n as [ | n r].
      + reflexivity.
      + exact (glue unit_seq n tt @ r).
    * intro n; destruct a; rewrite ap_idmap, ap_const, concat_p1; reflexivity.
Defined.

(** Fibered sequences; Section 4. *)
Record FibSequence (A : Sequence) := {
  fibSequence : sig A -> Type;
  fibSequenceArr x : fibSequence x -> fibSequence x^+
}.

Coercion fibSequence : FibSequence  >-> Funclass.

Arguments fibSequence {A}.
Arguments fibSequenceArr {A}.

Section FibSequence.

  Context `{Univalence} {A : Sequence} (B : FibSequence A).

  Let f n := @arr _ A n _ 1.
  Let g := fibSequenceArr B.

  (** The Sigma of a fibered type sequence; Definition 4.3. *)
  Definition sigSequence : Sequence.
  Proof.
    srapply Build_Sequence.
    - exact (fun n => {a : A n & B (n;a)}).
    - intros n [a b]; exact (f n a; g (n;a) b).
  Defined.

  (** The canonical projection from the sequential colimit of Sigmas to the sequential colimit
      of the first component; Definition 4.3. *)
  Definition seqColimSumToSeqColim_proj : Colimit sigSequence -> Colimit A.
  Proof.
    srapply Colimit_rec; srapply Build_Cocone.
    - intros n [a _]; exact (inj _ n a).
    - intros n m p [a b]; destruct p; exact (glue _ n a).
  Defined.

  (** Each point x : sig A induces a new type sequence; Section 4. *)
  Definition fibSeqToSeq (x : sig A) : Sequence.
  Proof.
    srapply Build_Sequence; intro k; revert x; induction k as [ | k h].
    * exact (fun x => B x).
    * exact (fun x => h x^+).
    * exact (fun x => g x).
    * exact (fun x => h x^+).
  Defined.

  (** This sequence can be equivalently described by using lifting; Lemma 7.1. *)
  Definition fibSeqToSeq' (x : sig A) : Sequence
    := Build_Sequence (fun k => B x^+k) (fun k => g x^+k).

  Definition equiv_fibSeqToSeq (x : sig A) : fibSeqToSeq x ~d~ fibSeqToSeq' x.
  Proof.
    srapply Build_diagram_equiv.
    + srapply Build_DiagramMap.
      * intro n; revert x; induction n as [ | n e].
        ++ exact (fun _ => idmap).
        ++ exact (fun x => coe (ap B (seqPairLiftAssoc x n)) o e x^+).
      * intros n m p; destruct p; revert x; induction n as [ | n p].
        ++ exact (fun _ _ => 1).
        ++ exact (fun x b => Kappa _ _ _ @ (ap _ (p (x^+) b))).
    + intro n; revert x; induction n as [ | n e].
      * exact (fun _ => isequiv_idmap _).
      * intro x; srapply isequiv_compose.
  Defined.

  (** A fibered type sequence defines a type family; Section 4. *)
  Definition fibSeqToTypeFam : Colimit A -> Type.
  Proof.
    srapply Colimit_rec; srapply Build_Cocone.
    - exact (fun n a => Colimit (fibSeqToSeq (n;a))).
    - intros n m p a; destruct p; apply path_universe_uncurried.
      exact (equiv_colimitSuccSeqToColimitSeq (fibSeqToSeq (n;a))).
  Defined.

  Definition fibSeqToTypeFam_beta_glue n a :
    coe (ap fibSeqToTypeFam (glue A n a)) =
    colimitSuccSeqToColimitSeq (fibSeqToSeq (n;a)).
  Proof.
    srapply (ap _ (Colimit_rec_beta_colimp _ _ _ _ _ _) @ _).
    srapply (transport_idmap_path_universe_uncurried _).
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

  (** The canonical map from the sequential colimit of Sigmas to the Sigma of
      sequential colimits; Definition 5.1. *)
  Definition seqColimSumToSumSeqColim : Colimit sigSequence -> sig fibSeqToTypeFam.
  Proof.
    srapply Colimit_rec; srapply Build_Cocone.
    - intros n [a b]; exact (inj A n a; inj (fibSeqToSeq _) 0 b).
    - intros n m p [a b]; destruct p; exact
        (Delta _ (fibSeqToTypeFam_beta_glue n a) _ @ ap _ (glue (fibSeqToSeq _) 0 b)).
  Defined.

  Definition seqColimSumToSumSeqColim_beta_glue n a b :
    ap seqColimSumToSumSeqColim (glue sigSequence n (a;b)) =
    Delta (glue A n a) (fibSeqToTypeFam_beta_glue n a)
          (inj (fibSeqToSeq (n.+1; f n a)) 0 (g (n;a) b)) @
    ap (exist fibSeqToTypeFam (inj A n a)) (glue (fibSeqToSeq (n;a)) 0 b).
  Proof.
    srapply Colimit_rec_beta_colimp.
  Defined.

  (** An alternative induction principle for the sum of colimits; Lemma 5.2 and Section 6. *)
  Section SeqColimitSumInd.

    Context (E : sig fibSeqToTypeFam -> Type).
    Context (e : forall n a b, E (seqColimSumToSumSeqColim (inj sigSequence n (a;b)))).
    Context (t : forall n a b, ap seqColimSumToSumSeqColim (glue sigSequence n (a;b)) #
      e n.+1 (f n a) (g (n;a) b) = e n a b).

    Local Definition I {X Y Z} {x1 x2 : X} {p : x1 = x2} {F} (psi : coe (ap Y p) = F)
      {G1} {G2} : transport (fun x => forall y, Z (x;y)) p G1 = G2 <~>
                  forall y, G2 (F y) = Delta p psi y # G1 y.
    Proof.
      destruct p; destruct psi.
      srefine (transitivity (equiv_path_inverse _ _) (equiv_apD10 _ _ _)).
    Defined.

    Local Definition Mu {X Y Z} {x1 x2 : X} (p : x1 = x2) {F} (G : forall z, Z z)
      {psi : coe (ap Y p) = F} {q} (theta : I psi (apD (fun x y => G (x;y)) p) = q) y
      : apD G (Delta p psi y) = (q y)^.
    Proof.
      destruct p; destruct psi; destruct theta; reflexivity.
    Defined.

    Local Definition Eta {X Y Z} {x : X} {y1 y2 : Y x} {z : sig Y} {p : y1 = y2}
      {q1 : z = (x;y1)} {q2 : z = (x;y2)} (theta : q2 = q1 @ ap _ p)
      : transport (Z o exist Y x) p o transport Z q1 == transport Z q2.
    Proof.
      symmetry in theta; destruct theta; destruct p; simpl; destruct q1.
      exact (fun _ => 1).
    Defined.

    Local Definition Xi {X Y Z} G {x : X} {y1 y2 : Y x} {z : sig Y} {p : y1 = y2}
      {q1 : z = (x;y1)} {q2 : z = (x;y2)} (theta : q2 = q1 @ ap _ p)
      : apD (G o exist Y x) p = ap (transport (Z o exist Y x) p) (apD G q1)^ @
        Eta theta (G z) @ apD G q2.
    Proof.
      revert theta; srapply (equiv_ind (equiv_path_inverse _ _)); destruct x0.
      revert q1; srapply (equiv_ind (equiv_path_inverse _ _)); destruct x0.
      destruct p; reflexivity.
    Defined.

    Local Definition Epsilon {X Y Z} {x1 x2 : X} {y1 y2} {F} (p : x1 = x2) {q : y1 = y2}
      {psi : coe (ap Y p) = F} {r : F y1 = F y2} (theta : ap F q = r)
      : transport (Z o exist Y x2) r o transport Z (Delta p psi y1) ==
        transport Z (Delta p psi y2) o transport (Z o exist Y x1) q.
    Proof.
      destruct theta; destruct q; intros z; reflexivity.
    Defined.

    Local Definition Phi {X Y Z} {x1 x2 : X} {y1 y2} {F} (p : x1 = x2) {q : y1 = y2}
      {psi : coe (ap Y p) = F} {G1 : forall y, Z (x1;y)} {G2 : forall y, Z (x2;y)}
      {r : F y1 = F y2} (theta : ap F q = r)
      : forall u1 u2,
        apD G2 r @ u2 = ap (transport _ r) u1 @ Epsilon p theta (G1 y1) @
                        ap (transport Z (Delta p psi y2)) (apD G1 q)
        -> transport (fun y => G2 (F y) = Delta p psi y # G1 y) q u1 = u2.
    Proof.
      destruct theta; destruct q; intros u1 u2; rewrite ap_idmap, !concat_p1.
      intro s; destruct s; srefine (concat_1p _).
    Defined.

    (** The point-point case of the nested induction; corresponds to "h" in the paper. *)
    Let Q k : forall n a b, E (inj _ n a; inj _ k b).
    Proof.
      induction k as [ | k h].
      - exact e.
      - intros n a b; exact (Delta _ (fibSeqToTypeFam_beta_glue n a) _ # h n.+1 (f n a) b).
    Defined.

    (** The path-point case of the nested induction is just reflexivity; corresponds to
        "mu" in the paper. *)

    (** The point-path case of the nested induction; corresponds to "H" in the paper. *)
    Let R k : forall n a b,
      transport (E o exist _ (inj A n a)) (glue _ k b) (Q k.+1 n a _) = Q k n a b.
    Proof.
      induction k as [ | k h].
      - intros n a b; srapply (_ @ t n a b).
        srapply (Eta (seqColimSumToSumSeqColim_beta_glue n a b)).
      - intros n a b; srefine (_ @ ap _ (h n.+1 (f n a) b)).
        srapply (Epsilon (glue A n a) (colimitSuccSeqToColimitSeq_beta_glue _ _ _)).
    Defined.

    (** The point case of the nested induction; correcponds to "g" in the paper. *)
    Let F n a : forall x, E (inj _ n a; x).
    Proof.
      srapply Colimit_ind.
      - exact (fun k => Q k n a).
      - intros k l p; destruct p; exact (R k n a).
    Defined.

    (** The path case of the nested induction; corresponds to "omega" in the paper. *)
    Let G n a : forall y,
      F n a _ = Delta _ (fibSeqToTypeFam_beta_glue n a) y # F n.+1 (f n a) y.
    Proof.
      srapply Colimit_ind.
      - exact (fun k b => 1).
      - intros k l p b; destruct p.
        snrapply (Phi (glue A n a) (colimitSuccSeqToColimitSeq_beta_glue _ _ _)).
        rewrite (Colimit_ind_beta_colimp _ (fun k => Q k n a) _ _ _ 1).
        rewrite (Colimit_ind_beta_colimp _ (fun k => Q k n.+1 (f n a)) _ _ _ 1).
        rewrite concat_p1, concat_1p; reflexivity.
    Defined.

    (** The alternative induction rule in curried form; corresponds to curried "G" in
        the paper. *)
    Definition SeqColimitSum_ind_cur : forall x y, E (x;y).
    Proof.
      srapply (Colimit_ind _ F); intros n m p a; destruct p.
      exact ((I (fibSeqToTypeFam_beta_glue n a))^-1 (G n a)).
    Defined.

    (** The computation rule for the alternative induction rule in curried form. *)
    Definition SeqColimitSum_ind_cur_beta_glue n a :
      I (fibSeqToTypeFam_beta_glue n a) (apD SeqColimitSum_ind_cur (glue _ n a)) = G n a.
    Proof.
      apply moveR_equiv_M; srapply Colimit_ind_beta_colimp.
    Defined.

    (** The alternative induction rule; corresponds to "G" in the paper. *)
    Definition SeqColimitSum_ind : forall x, E x.
    Proof.
      intros [x y]; apply SeqColimitSum_ind_cur.
    Defined.

    (** The computation rule for the alternative induction rule. *)
    Definition SeqColimitSum_ind_beta_glue : forall n a b,
      apD SeqColimitSum_ind (ap seqColimSumToSumSeqColim (glue sigSequence n _)) = t n a b.
    Proof.
      intros n a b.
      pose (h := Colimit_ind_beta_colimp _ (fun k => Q k n a)
        (fun k l p => match p with 1 => R k n a end) 0 _ 1 b).
      rewrite (Xi SeqColimitSum_ind (seqColimSumToSumSeqColim_beta_glue n a b)) in h.
      rewrite (Mu (glue _ n a) SeqColimitSum_ind (SeqColimitSum_ind_cur_beta_glue n a)) in h.
      rewrite concat_1p in h; exact (cancelL _ _ _ h).
    Defined.

  End SeqColimitSumInd.

  (** An alternative recursion principle for the sum of colimits; Lemma 5.3. *)
  Section SeqColimitSumRec.

    Context E (e : forall n a, B (n;a) -> E).
    Context (t : forall n a b, e n.+1 (f n a) (g (n;a) b) = e n a b).

    Definition SeqColimitSum_rec : sig fibSeqToTypeFam -> E.
    Proof.
      exact (SeqColimitSum_ind _ e (fun n a b => transport_const _ _ @ t n a b)).
    Defined.

    Definition SeqColimitSum_rec_beta_glue : forall n a b,
      ap SeqColimitSum_rec (ap seqColimSumToSumSeqColim (glue sigSequence n (a;b))) = t n a b.
    Proof.
      intros n a b; srapply (cancelL _ _ _ ((apD_const _ _)^ @ _)).
      apply SeqColimitSum_ind_beta_glue.
    Defined.

  End SeqColimitSumRec.

  (** Lemma 5.4. *)
  Definition seq_colimit_sum_uniqueness E (F G : sig fibSeqToTypeFam -> E)
    : F o seqColimSumToSumSeqColim == G o seqColimSumToSumSeqColim -> F == G.
  Proof.
    intro h; srapply (SeqColimitSum_ind _ (fun _ _ _ => h _)); intros n a b.
    srapply ((transport_compose _ _ _ _)^ @ _); exact (apD h (glue sigSequence n (a;b))).
  Defined.

  (** The canonical map from the sequential colimit of Sigmas to the Sigma of
      sequential colimits is an equivalence; Theorem 5.1. *)
  Global Instance isequiv_seqColimSumToSumSeqColim : IsEquiv seqColimSumToSumSeqColim.
  Proof.
    assert (L : {G : _ & Sect seqColimSumToSumSeqColim G}).
    - srapply (_;_).
      + srapply SeqColimitSum_rec.
        * exact (fun n a b => inj sigSequence n (a;b)).
        * exact (fun n a b => glue sigSequence n (a;b)).
      + srapply seqColimitUniqueness.
        * exact (fun n a => 1).
        * intros n a; rewrite concat_1p, concat_p1, ap_compose, ap_idmap.
          rewrite SeqColimitSum_rec_beta_glue; reflexivity.
    - srapply (isequiv_adjointify _ L.1 _ L.2); srapply seq_colimit_sum_uniqueness.
      intro x; rewrite L.2; reflexivity.
  Defined.

  Definition equiv_seqColimSumToSumSeqColim
    : Colimit sigSequence <~> sig fibSeqToTypeFam
    := Build_Equiv _ _ seqColimSumToSumSeqColim _.
  
  (** The canonical map from the sequential colimit of Sigmas to the Sigma of
      sequential colimits commutes with the first projection; Theorem 5.1. *)
  Definition seqColimSumToSumSeqColim_proj
    : pr1 o seqColimSumToSumSeqColim == seqColimSumToSeqColim_proj.
  Proof.
    srapply seqColimitUniqueness.
    - exact (fun n a => 1).
    - intros n [a b]; rewrite concat_1p, concat_p1, ap_compose, !Colimit_rec_beta_colimp.
      rewrite ap_pp, (Delta_proj _ (fibSeqToTypeFam_beta_glue n a)).
      srapply (whiskerL _ _ @ concat_p1 _); rewrite (ap_compose _ _ _)^; simpl.
      rewrite ap_const; reflexivity.
  Defined.

End FibSequence.

(** Lemma 7.3; this probably belongs to a different file. *)
Definition encode_decode `{Funext} {A} {B : A -> Type} a (b : B a) :
  Contr (sig B) <~> forall x, IsEquiv (fun p : a = x => p # b).
Proof.
  srapply equiv_equiv_iff_hprop; split.
  - intros h_contr x; srapply isequiv_adjointify.
    * exact (fun y => (path_contr (a;b) (x;y))..1).
    * exact (fun y => (path_contr (a;b) (x;y))..2).
    * exact (fun p => ap _ (path2_contr _ _) @ @pr1_path_sigma _ _ (a;b) (x; p#b) _ 1).
  - intro h_eq; srapply (Build_Contr _ (a;b)); intros [x y]; srapply path_sigma.
    * exact ((fun p => p # b)^-1 y).
    * exact (@eisretr _ _ _ (h_eq x) y).
Defined.

(** The characterization of path spaces in sequential colimits; Lemma 7.4. *)
Section SeqColimitPathIndexZero.

  Context `{Univalence} (A : Sequence) (a1 a2 : A 0).

  Let f n := @arr _ A n _ 1.

  Definition pathSeq : Sequence
    := Build_Sequence (fun k => a1^++k = a2^++k) (fun k p => ap (f k) p).

  Let B : FibSequence A.
  Proof.
    srapply Build_FibSequence.
    - intros [k b]; exact (a1^++k = b).
    - intros [k b]; exact (ap (f k)).
  Defined.
 
  Let g := fibSequenceArr B.

  (** Lemma 7.4, first part. *)
  Definition equiv_pathColimitIndexZero :
    (inj A 0 a1 = inj A 0 a2) <~> Colimit pathSeq.
  Proof.
    transitivity (fibSeqToTypeFam B (inj A 0 a2)).
    + srefine (Build_Equiv _ _ _ (encode_decode _ (inj (fibSeqToSeq B (0;a1)) 0 1) _ _)).
      srefine (contr_equiv _ (seqColimSumToSumSeqColim B)).
      srapply contr_ColimitContrSeq; intro k; srapply contr_basedpaths.
    + srapply equiv_functor_colimit; srefine (transitivity (equiv_fibSeqToSeq B (0;a2)) _).
      srapply Build_diagram_equiv.
      * srapply Build_DiagramMap.
        - exact (fun n => coe (ap B (seqLiftPairZero A a2 n))).
        - intros n m p b; destruct p; srapply (Kappa _ _ (seqLiftPairZero A a2 n)).
      * intro n; srapply isequiv_path.
  Defined.

End SeqColimitPathIndexZero.

(** Lemma 7.4, second part. *)
Definition equiv_pathColimitSameIndex `{Univalence} (A : Sequence) n (a1 a2 : A n) :
  (inj A n a1 = inj A n a2) <~> Colimit (pathSeq (shiftSeq A n) a1 a2).
Proof.
  srefine (transitivity _ (equiv_pathColimitIndexZero _ _ _)); symmetry.
  srapply (@equiv_ap _ _ (colimitShiftSeqToColimitSeq A n)).
Defined.
