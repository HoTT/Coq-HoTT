Require Import Basics.
Require Import Types.
Require Import Diagrams.Diagram.
Require Import Diagrams.Sequence.
Require Import Diagrams.Cocone.
Require Import Colimits.Colimit.
Require Import Spaces.Nat.

Local Open Scope path_scope.

Section Lift.

  Context {A : Sequence}.

  Local Definition f n := @arr _ A n _ 1.

  Local Definition pair_lift (x : sig A) : sig A := match x with (n;a) => (n.+1; f n a) end.

  Local Definition pair_lift_by (x : sig A) (k : nat) : sig A.
  Proof.
    induction k as [ | k y].
    - exact x.
    - exact (pair_lift y).
  Defined.

  Notation "x ^+" := (pair_lift x) (at level 0).
  Notation "x ^+ k" := (pair_lift_by x k) (at level 0).

  Local Definition pair_lift_assoc (x : sig A) (k : nat) : (x^+)^+k = x^+(k.+1).
  Proof.
    induction k as [ | k q].
      - exact 1.
      - exact (ap pair_lift q).
  Defined.

End Lift.

Notation "x ^+" := (pair_lift x) (at level 0).
Notation "x ^+ k" := (pair_lift_by x k) (at level 0).

Notation inj A := (@colim sequence_graph A).

Notation glue A := (fun n => @colimp sequence_graph A n n.+1 1).

Definition seq_colimit_uniqueness (A : Sequence) E (F G : Colimit A -> E)
  (h : forall n, F o inj A n == G o inj A n)
  (H : forall n a, ap F (glue A n a) @ h n a = h n.+1 (f n a) @ ap G (glue A n a))
  : F == G.
Proof.
  srapply (Colimit_ind _ h); intros n m p a; destruct p.
  generalize (H n a); generalize (h n a); destruct (glue A n a).
  intros p q; srapply ((concat_p1 _)^ @ _); srapply (_ @ (concat_1p _)); exact q^.
Defined.

Definition succSeq (A : Sequence) : Sequence.
Proof.
  destruct A as [A f]; exact (Build_Sequence (fun n => A n.+1) (fun n => f n.+1 _ 1)).
Defined.

Definition equiv_seq_colimit_succ A : Colimit (succSeq A) <~> Colimit A.
Proof.
  pose (f n := @arr _ A n _ 1); srapply Build_Equiv.
  - srapply Colimit_rec; srapply Build_Cocone.
    + exact (fun n a => inj _ n.+1 a).
    + exact (fun n m p => match p with 1 => glue A n.+1 end).
  - srapply isequiv_adjointify.
    + srapply Colimit_rec; srapply Build_Cocone.
      * exact (fun n a => inj (succSeq A) n (f n a)).
      * exact (fun n m p a => match p with 1 => glue (succSeq A) n (f n a) end).
    + srapply seq_colimit_uniqueness.
      * exact (fun n a => glue _ n a).
      * intros n a; rewrite ap_idmap, ap_compose, Colimit_rec_beta_colimp.
        rewrite (@Colimit_rec_beta_colimp _ (succSeq A) _ _ _ _ 1); exact 1.
    + srapply seq_colimit_uniqueness.
      * exact (fun n a => glue _ n a).
      * intros n a; rewrite ap_idmap, ap_compose, Colimit_rec_beta_colimp.
        rewrite (@Colimit_rec_beta_colimp _ A _ _ _ _ 1); exact 1.
Defined.

Definition equiv_seq_colimit_succ_n A n (a1 a2 : succSeq A n) (p : a1 = a2)
  : ap (equiv_seq_colimit_succ A) (ap (inj (succSeq A) n) p) = ap (inj A n.+1) p
  := match p with 1 => 1 end.

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
  Local Definition g := fibSequenceArr B.

  (** The Sigma of a fibered type sequence. *)
  Definition sigSequence : Sequence.
  Proof.
    srapply Build_Sequence.
    - exact (fun n => {a : A n & B (n;a)}).
    - intros n [a b]; exact (f n a; g (n;a) b).
  Defined.

  (** Each point x : sig A induces a new type sequence. *)
  Definition fibSeqToSequence (x : sig A) : Sequence
    := Build_Sequence (fun k => B x^+k) (fun k => g x^+k).

  Notation coe := (transport idmap).

  Local Definition Beta {X Y F G} {x1 x2 : X} (p : x1 = x2)
    : coe (ap Y (ap F p)) o G x1 == G x2 o coe (ap Y p).
  Proof.
    destruct p; exact (fun _ => 1).
  Defined.

  Definition fib_seq_succ_equiv (x : sig A)
    : (fibSeqToSequence x^+) ~d~ (succSeq (fibSeqToSequence x)).
  Proof.
    srapply Build_diagram_equiv.
    - srapply Build_DiagramMap.
      * exact (fun k => coe (ap _ (pair_lift_assoc x k))).
      * exact (fun k l p b => match p with 1 => (Beta (pair_lift_assoc x k) b)^ end).
    - intro k; srapply isequiv_path.
  Defined.

  Definition equiv_fib_seq_lift_colim (x : sig A)
    : Colimit (fibSeqToSequence x^+) <~> Colimit (fibSeqToSequence x).
  Proof.
    srapply (equiv_compose' (equiv_seq_colimit_succ _)).
    srapply equiv_functor_colimit; srapply fib_seq_succ_equiv.
  Defined.

  Definition equiv_fib_seq_lift_colim_beta (x : sig A) k b
    : ap (equiv_fib_seq_lift_colim _) (glue (fibSeqToSequence x^+) k b) =
      ap (inj (fibSeqToSequence x) k.+2) (Beta (pair_lift_assoc x k) b) @
      glue (fibSeqToSequence x) k.+1 (coe (ap _ (pair_lift_assoc x k)) b).
  Proof.
    srapply (ap_compose (equiv_functor_colimit _ _ _) (equiv_seq_colimit_succ _) _ @ _).
    srapply (ap _ (Colimit_rec_beta_colimp _ _ _ _ _ _) @ _); simpl.
    srapply (ap_pp _ _ _ @ _); srapply (whiskerL _ (Colimit_rec_beta_colimp _ _ _ _ _ _) @ _).
    apply whiskerR; srapply (ap _ (ap _ (inv_V _)) @ _); srapply equiv_seq_colimit_succ_n.
  Defined.
 
  (** A fibered type sequence defines a type family. *)
  Definition fibSequenceToTypeFam : Colimit A -> Type.
  Proof.
    srapply Colimit_rec; srapply Build_Cocone.
    - exact (fun n a => Colimit (fibSeqToSequence (n;a))).
    - intros n m p a; destruct p; apply path_universe_uncurried.
      exact (equiv_fib_seq_lift_colim (n;a)).
  Defined.

  Definition fibSequenceToTypeFam_beta n a :
    coe (ap fibSequenceToTypeFam (glue A n a)) = equiv_fib_seq_lift_colim (n;a).
  Proof.
    srapply (ap _ (Colimit_rec_beta_colimp _ _ _ _ _ _) @ _).
    srapply (transport_idmap_path_universe_uncurried _).
  Defined.

  Local Definition Delta {X Y} {x1 x2 : X} {F} (p : x1 = x2) (psi : coe (ap Y p) = F) y
     : (x1;y) = (x2;F y).
  Proof.
    destruct p; destruct psi; exact 1.
  Defined.

  Local Definition Delta_proj {X Y} {x1 x2 : X} {F} (p : x1 = x2) (psi : coe (ap Y p) = F) y
    : ap pr1 (Delta p psi y) = p.
  Proof.
    destruct p; destruct psi; exact 1.
  Defined.

  (** The canonical map from the sequential colimit of Sigmas to the sequential colimit
      of the first component. *)
  Definition seqColimSumToSeqColim_proj : Colimit sigSequence -> Colimit A.
  Proof.
    srapply Colimit_rec; srapply Build_Cocone.
    - exact (fun n x => inj _ n x.1).
    - intros n m p x; destruct p; exact (glue _ n x.1).
  Defined.

  (** The canonical map from the sequential colimit of Sigmas to the Sigma of
      sequential colimits. *)
  Definition seqColimSumToSumSeqColim : Colimit sigSequence -> sig fibSequenceToTypeFam.
  Proof.
    srapply Colimit_rec; srapply Build_Cocone.
    - intros n [a b]; exact (inj A n a; inj (fibSeqToSequence _) 0 b).
    - intros n m p [a b]; destruct p; exact
        (Delta _ (fibSequenceToTypeFam_beta n a) _ @ ap _ (glue (fibSeqToSequence _) 0 b)).
  Defined.

  Definition seqColimSumToSumSeqColim_beta_glue n a b :
    ap seqColimSumToSumSeqColim (glue sigSequence n (a; b)) =
    Delta _ (fibSequenceToTypeFam_beta n a) _ @ ap _ (glue (fibSeqToSequence _) 0 b).
  Proof.
    srapply Colimit_rec_beta_colimp.
  Defined.

  (** An alternative induction principle for the sum of colimits. *)
  Section SeqColimitSumInd.

    Context (E : sig fibSequenceToTypeFam -> Type).
    Context (e : forall n a b, E (seqColimSumToSumSeqColim (inj sigSequence n (a;b)))).
    Context (t : forall n a b, ap seqColimSumToSumSeqColim (glue sigSequence n (a;b)) #
      e n.+1 (f n a) (g (n;a) b) = e n a b).

    Local Definition Eta {X Y Z} {x : X} {y1 y2 : Y x} {z : sig Y} {p : y1 = y2}
      {q1 : z = (x;y1)} {q2 : z = (x;y2)} (theta : q2 = q1 @ ap _ p)
      : transport (Z o exist Y x) p o transport Z q1 == transport Z q2.
    Proof.
      apply inverse in theta; destruct theta; destruct p; simpl; destruct q1.
      exact (fun _ => 1).
    Defined.

    Local Definition Xi {X Y Z} G {x : X} {y1 y2 : Y x} {z : sig Y} {p : y1 = y2}
      {q1 : z = (x;y1)} {q2 : z = (x;y2)} (theta : q2 = q1 @ ap _ p)
      : apD (G o exist Y x) p = ap (transport (Z o exist Y x) p) (apD G q1)^ @
        Eta theta (G z) @ apD G q2.
    Proof.
      revert theta; srapply (equiv_ind (equiv_path_inverse _ _)); destruct x0.
      revert q1; srapply (equiv_ind (equiv_path_inverse _ _)); destruct x0.
      destruct p; exact 1.
    Defined.

    Local Definition I {X Y Z} {x1 x2 : X} {p : x1 = x2} {F} (psi : coe (ap Y p) = F)
      {G1} {G2} : transport (fun x => forall y, Z (x;y)) p G1 = G2 <~>
                  forall y, G2 (F y) = Delta p psi y # G1 y.
    Proof.
      destruct p; destruct psi.
      srapply (equiv_compose' (equiv_apD10 _ _ _) (equiv_path_inverse _ _)).
    Defined.

    Local Definition Epsilon {X Y Z} {x1 x2 : X} {y1 y2 w z} {F} (p : x1 = x2) {q : y1 = y2}
      {psi : coe (ap Y p) = F} {r1 : F y1 = w} {r2 : w = F y2} (theta : ap F q = r1 @ r2)
      : r2 # transport (Z o exist Y x2) r1 (Delta p psi y1 # z) =
        Delta p psi y2 # transport (Z o exist Y x1) q z.
    Proof.
      revert theta; srapply (equiv_ind (equiv_moveR_Vp _ _ _)^-1); destruct x.
      destruct q; destruct r1; exact 1.
    Defined.

    Local Definition Phi {X Y Z} {x1 x2 : X} {y1 y2 w} {F} (p : x1 = x2) {q : y1 = y2}
      {psi : coe (ap Y p) = F} {G1 : forall y, Z (x1;y)} {G2 : forall y, Z (x2;y)}
      {r1 : F y1 = w} {r2 : w = F y2} (theta : ap F q = r1 @ r2)
      : forall u1 u2, 
        apD G2 r2 = ap (transport _ r2) (apD G2 r1)^ @
                    ap (transport _ r2) (ap (transport _ r1) u1) @ Epsilon p theta @
                    ap (transport Z (Delta p psi y2)) (apD G1 q) @ u2^
        -> transport (fun y => G2 (F y) = Delta p psi y # G1 y) q u1 = u2.
    Proof.
      revert theta; srapply (equiv_ind (equiv_moveR_Vp _ _ _)^-1); destruct x.
      destruct q; destruct r1; intros u1 u2; simpl; rewrite concat_1p, !concat_p1, !ap_idmap.
      intro s; apply inverse in s; revert s; apply moveL_1M.
    Defined.

    Local Definition Mu {X Y Z} {x1 x2 : X} (p : x1 = x2) {F} (G : forall z, Z z)
      {psi : coe (ap Y p) = F} {q} (theta : I psi (apD (fun x y => G (x;y)) p) = q) y
      : apD G (Delta p psi y) = (q y)^.
    Proof.
      destruct p; destruct psi; destruct theta; exact 1.
    Defined. 

    (** The point-point case of the nested induction. *)
    Local Definition Q k : forall n a b, E (inj _ n a; inj _ k b).
    Proof.
      induction k as [ | k h].
      - exact e.
      - intros n a; apply (functor_forall_equiv_pb (coe (ap B (pair_lift_assoc _ k)))).
        intros b; exact (Delta _ (fibSequenceToTypeFam_beta n a) _ # h n.+1 (f n a) b).
    Defined.

    (** The path-point case of the nested induction. *)
    Local Definition Q_beta k n a b
      : Q k.+1 n a _ = Delta _ (fibSequenceToTypeFam_beta n a) _ # Q k n.+1 (f n a) b.
    Proof.
      srapply (functor_forall_equiv_pb_beta _).
    Defined.

    (** The point-path case of the nested induction. *)
    Local Definition R k : forall n a b,
      transport (E o exist _ (inj A n a)) (glue _ k b) (Q k.+1 n a _) = Q k n a b.
    Proof.
      induction k as [ | k h].
      - intros n a b; srapply (_ @ t n a b).
        srapply (Eta (seqColimSumToSumSeqColim_beta_glue n a b)).
      - intros n a; apply (functor_forall_equiv_pb (coe (ap B (pair_lift_assoc _ k)))).
        intro b; srapply (_ @ (Q_beta k n a b)^).
        srefine (_ @ ap _ (h n.+1 (f n a) b)).
        srefine (_ @ (Epsilon (glue A n a) (equiv_fib_seq_lift_colim_beta _ _ _))).
        srefine (_ @ ap _ (ap _ (Q_beta _ n a _))).
        srefine (ap _ ((transport_compose _ _ _ _)^ @ _)^).
        exact (apD _ (Beta _ b)).
    Defined.

    (** The point case of the nested induction. *)
    Local Definition F n a : forall x, E (inj _ n a; x).
    Proof.
      srapply Colimit_ind.
      - exact (fun k => Q k n a).
      - exact (fun k l p => match p with 1 => R k n a end).
    Defined.

    (** The path case of the nested induction. *)
    Local Definition G n a : forall y,
      F n a _ = Delta _ (fibSequenceToTypeFam_beta n a) y # F n.+1 (f n a) y.
    Proof.
      srapply Colimit_ind.
      - exact (fun k => Q_beta k n a).
      - intros k l p b; destruct p.
        snrapply (Phi (glue A n a) (equiv_fib_seq_lift_colim_beta _ _ _)).
        rewrite (Colimit_ind_beta_colimp _ (fun k => Q k n a) _ _ _ 1).
        rewrite (Colimit_ind_beta_colimp _ (fun k => Q k n.+1 (f n a)) _ _ _ 1).
        rewrite (apD_compose' _ _ (Beta (pair_lift_assoc (n;a) k) b)).
        snrapply functor_forall_equiv_pb_beta.
    Defined.

    (** The alternative induction rule in curried form. *)
    Definition SeqColimitSum_ind_cur : forall x y, E (x;y).
    Proof.
      srapply (Colimit_ind _ F); intros n m p a; destruct p.
      exact ((I (fibSequenceToTypeFam_beta n a))^-1 (G n a)).
    Defined.

    (** The computation rule for the alternative induction rule in curried form. *)
    Definition SeqColimitSum_ind_cur_beta_glue n a :
      I (fibSequenceToTypeFam_beta n a) (apD SeqColimitSum_ind_cur (glue _ n a)) = G n a.
    Proof.
      apply moveR_equiv_M; srapply Colimit_ind_beta_colimp.
    Defined.

    (** The alternative induction rule. *)
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

  (** An alternative recursion principle for the sum of colimits. *)
  Section SeqColimitSumRec.

    Context E (e : forall n a, B (n;a) -> E).
    Context (t : forall n a b, e n.+1 (f n a) (g (n;a) b) = e n a b).

    Definition SeqColimitSum_rec : sig fibSequenceToTypeFam -> E.
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

  Definition seq_colimit_sum_uniqueness E (F G : sig fibSequenceToTypeFam -> E)
    : F o seqColimSumToSumSeqColim == G o seqColimSumToSumSeqColim -> F == G.
  Proof.
    intro h; srapply (SeqColimitSum_ind _ (fun _ _ _ => h _)); intros n a b.
    srapply ((transport_compose _ _ _ _)^ @ _); exact (apD h (glue sigSequence n (a;b))).
  Defined.

  (** The canonical map from the sequential colimit of Sigmas to the Sigma of
      sequential colimits is an equivalence. *)
  Global Instance isequiv_seqColimSumToSumSeqColim : IsEquiv seqColimSumToSumSeqColim.
  Proof.
    assert (L : {G : _ & Sect seqColimSumToSumSeqColim G}).
    - srapply (_;_).
      + srapply SeqColimitSum_rec.
        * exact (fun n a b => inj sigSequence n (a;b)).
        * exact (fun n a b => glue sigSequence n (a;b)).
      + srapply seq_colimit_uniqueness.
        * exact (fun n a => 1).
        * intros n a; rewrite concat_1p, concat_p1, ap_compose, ap_idmap.
          rewrite SeqColimitSum_rec_beta_glue; exact 1.
    - srapply (isequiv_adjointify _ L.1 _ L.2); srapply seq_colimit_sum_uniqueness.
      intro x; rewrite L.2; exact 1.
  Defined.

  Definition equiv_seqColimSumToSumSeqColim
    : Colimit sigSequence <~> sig fibSequenceToTypeFam
    := Build_Equiv _ _ seqColimSumToSumSeqColim _.
  
  (** The canonical map from the sequential colimit of Sigmas to the Sigma of
      sequential colimits commutes with the first projection. *)
  Definition seqColimSumToSumSeqColim_proj
    : pr1 o seqColimSumToSumSeqColim == seqColimSumToSeqColim_proj.
  Proof.
    srapply seq_colimit_uniqueness.
    - exact (fun n a => 1).
    - intros n [a b]; rewrite concat_1p, concat_p1, ap_compose, !Colimit_rec_beta_colimp.
      rewrite ap_pp, (Delta_proj _ (fibSequenceToTypeFam_beta n a)).
      srapply (whiskerL _ _ @ concat_p1 _); rewrite (ap_compose _ _ _)^; simpl.
      rewrite ap_const; exact 1.
  Defined.

End FibSequence.
