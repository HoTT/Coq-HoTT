Require Import Basics.
Require Import Types.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.
Require Import Diagrams.Sequence.
Require Import Diagrams.DDiagram.
Require Import Diagrams.Cocone.
Require Import Colimits.Colimit.
Require Import Spaces.Nat.

Local Open Scope nat_scope.
Local Open Scope path_scope.

Definition functor_forall_equiv_pb {A B : Type} {P : B -> Type} (f : A -> B) `{IsEquiv _ _ f}
  : (forall a, P (f a)) -> (forall b, P b)
  := fun h b => eisretr f b # h (f^-1 b).

Definition functor_forall_equiv_pb_beta {A B : Type} {P : B -> Type} (f : A -> B)
  `{IsEquiv _ _ f} (h : forall a, P (f a))
  : forall a, functor_forall_equiv_pb f h (f a) = h a.
Proof.
  intro a; srapply (_ @ apD h (eissect f a)); srapply (_ @ (transport_compose _ _ _ _)^).
  srapply ap10; apply ap; apply eisadj.
Defined.

Record TypeSeq := {
  typeSeq : nat -> Type;
  typeSeqArr n : typeSeq n -> typeSeq n.+1
}.

Coercion typeSeq : TypeSeq >-> Funclass.

Definition TypeSeqToDiagram : TypeSeq -> Diagram sequence_graph.
Proof.
  intros [A f]; srapply Build_Diagram.
  - exact A.
  - intros n m p; destruct p; exact (f n).
Defined.

Definition succTypeSeq (A : TypeSeq) : TypeSeq
  := Build_TypeSeq (fun n => A n.+1) (fun n => typeSeqArr A n.+1).

Record TypeSeqMap (A B : TypeSeq) := {
  typeSeqMap n : A n -> B n;
  typeSeqHom n : typeSeqMap n.+1 o typeSeqArr A n == typeSeqArr B n o typeSeqMap n
}.

Arguments typeSeqMap {A B}.
Arguments typeSeqHom {A B}.

Coercion typeSeqMap : TypeSeqMap >-> Funclass.

Definition TypeSeqMapToDiagramMap {A B}
  : TypeSeqMap A B -> DiagramMap (TypeSeqToDiagram A) (TypeSeqToDiagram B).
Proof.
  intros [h H]; srapply Build_DiagramMap.
  - exact h.
  - intros n m p a; destruct p; exact (H n a)^.
Defined.

Record TypeSeqEquiv (A B : TypeSeq) := {
  typeSeqEquivMap : TypeSeqMap A B;
  typeSeqEquiv n : IsEquiv (typeSeqEquivMap n)
}.

Arguments typeSeqEquiv {A B}.
Arguments typeSeqEquivMap {A B}.

Definition TypeSeqEquivToDiagramEquiv {A B}
  : TypeSeqEquiv A B -> diagram_equiv (TypeSeqToDiagram A) (TypeSeqToDiagram B).
Proof.
  intros [M e]; srapply Build_diagram_equiv.
  - exact (TypeSeqMapToDiagramMap M).
  - exact e.
Defined.

Section TypeSeq.

  Context {A : TypeSeq}.

  Local Definition f := typeSeqArr A.

  Definition pair_lift (x : sig A) : sig A := match x with (n;a) => (n.+1; f n a) end.

  Definition pair_lift_by (x : sig A) (k : nat) : sig A.
  Proof.
    induction k as [ | k y].
    - exact x.
    - exact (pair_lift y).
  Defined.

  Notation "x ^+" := (pair_lift x) (at level 0).
  Notation "x ^+ k" := (pair_lift_by x k) (at level 0).

  Definition pair_lift_assoc (x : sig A) (k : nat) : (x^+)^+k = x^+(k.+1).
  Proof.
    induction k as [ | k q].
      - exact 1.
      - exact (ap pair_lift q).
  Defined.

End TypeSeq.

Notation "x ^+" := (pair_lift x) (at level 0).
Notation "x ^+ k" := (pair_lift_by x k) (at level 0).

Section SeqColimitDef.

  Context (A : TypeSeq).

  Let f := typeSeqArr A.
  Let S' := TypeSeqToDiagram A.

  Definition SeqColimit : Type := Colimit S'.

  Definition inj n (a : A n) : SeqColimit := @colim _ S' n a.

  Definition glue n (a : A n) : inj n.+1 (f n a) = inj n a := @colimp _ S' n n.+1 1 a.

  Definition SeqColimit_ind (E : SeqColimit -> Type) (e : forall n a, E (inj n a))
    (p : forall n a, glue n a # e n.+1 (f n a) = e n a)
    : forall x, E x.
  Proof.
    srapply (Colimit_ind E e); destruct g; exact (p i).
  Defined.

  Definition SeqColimit_ind_beta_glue (E : SeqColimit -> Type) (e : forall n a, E (inj n a))
    (p : forall n a, glue n a # e n.+1 (f n a) = e n a) n (a : A n) :
    apD (SeqColimit_ind E e p) (glue n a) = p n a.
  Proof.
    srapply Colimit_ind_beta_colimp.
  Defined.
 
  Definition SeqColimit_rec (E : Type) (e : forall n, A n -> E)
    (p : forall n a, e n.+1 (f n a) = e n a)
    : SeqColimit -> E.
  Proof.
    apply Colimit_rec; apply (@Build_Cocone _ S' E e); destruct g; exact (p i).
  Defined.

  Definition SeqColimit_rec_beta_glue (E : Type) (e : forall n, A n -> E)
    (p : forall n a, e n.+1 (f n a) = e n a) n (a : A n) :
    ap (SeqColimit_rec E e p) (glue n a) = p n a.
  Proof.
    srapply (@Colimit_rec_beta_colimp _ S' _ _ _ _ 1).
  Defined.

  Definition seq_colimit_uniqueness E (F G : SeqColimit -> E)
    (h : forall n, F o inj n == G o inj n)
    (H : forall n a, ap F (glue n a) @ h n a = h n.+1 (f n a) @ ap G (glue n a)) : F == G.
  Proof.
    srapply SeqColimit_ind.
    - exact h.
    - intros n a; generalize (H n a); generalize (h n a); destruct (glue n a).
      intros p q; srapply ((concat_p1 _)^ @ _); srapply (_ @ (concat_1p _)); exact q^.
  Defined.

End SeqColimitDef.

Definition seq_colimit_succ_equiv A : SeqColimit (succTypeSeq A) <~> SeqColimit A.
Proof.
  pose (f := typeSeqArr A); srapply Build_Equiv.
  - srapply SeqColimit_rec.
    + exact (fun n a => inj A n.+1 a).
    + exact (fun n a => glue A n.+1 a).
  - srapply isequiv_adjointify.
    + srapply SeqColimit_rec.
      * exact (fun n a => inj (succTypeSeq A) n (f n a)).
      * exact (fun n a => glue (succTypeSeq A) n (f n a)).
    + srapply seq_colimit_uniqueness.
      * exact (fun n a => glue _ n a).
      * intros n a; rewrite ap_idmap, ap_compose, SeqColimit_rec_beta_glue.
        rewrite (SeqColimit_rec_beta_glue (succTypeSeq A)); exact 1.
    + srapply seq_colimit_uniqueness.
      * exact (fun n a => glue _ n a).
      * intros n a; rewrite ap_idmap, ap_compose, SeqColimit_rec_beta_glue.
        rewrite (SeqColimit_rec_beta_glue A); exact 1.
Defined.

Lemma seq_colimit_succ_equiv_n A n (a1 a2 : succTypeSeq A n) (p : a1 = a2)
  : ap (seq_colimit_succ_equiv A) (ap (inj (succTypeSeq A) n) p) = ap (inj A n.+1) p.
Proof.
  destruct p; exact 1.
Defined.

Definition functor_seq_colimit {A} {B} (M : TypeSeqMap A B) : SeqColimit A -> SeqColimit B.
Proof.
  destruct M as [h H]; srapply SeqColimit_rec.
  - exact (fun n a => inj _ n (h n a)).
  - exact (fun n a => ap (inj _ n.+1) (H n a) @ glue _ n (h n a)).
Defined.

Global Instance functor_seq_colimit_equiv `{Funext} {A} {B} (M : TypeSeqEquiv A B) :
  IsEquiv (functor_seq_colimit (typeSeqEquivMap M)).
Proof.
  srapply isequiv_homotopic.
  - srapply (functor_colimit (TypeSeqMapToDiagramMap (typeSeqEquivMap M))).
  - srapply (isequiv_functor_colimit (TypeSeqEquivToDiagramEquiv M)).
  - srapply seq_colimit_uniqueness.
    + exact (fun n a => 1).
    + intros n a; rewrite concat_1p, concat_p1, SeqColimit_rec_beta_glue.
      rewrite (Colimit_rec_beta_colimp _
        (cocone_precompose (TypeSeqMapToDiagramMap _)_) _ _ 1 _).
      simpl; rewrite inv_V; exact 1.
Defined.

Record FibTypeSeq (A : TypeSeq) := {
  fibTypeSeq : sig A -> Type;
  fibTypeSeqArr x : fibTypeSeq x -> fibTypeSeq x^+
}.

Coercion fibTypeSeq : FibTypeSeq  >-> Funclass.

Arguments fibTypeSeq {A}.
Arguments fibTypeSeqArr {A}.

Section FibTypeSeq.

  Context `{Univalence} {A : TypeSeq} (B : FibTypeSeq A).

  Let f := typeSeqArr A.
  Let g := fibTypeSeqArr B.

  (** The Sigma of a fibered type sequence. *)
  Definition sigTypeSeq := Build_TypeSeq (fun n => {a : A n & B (n;a)})
    (fun n x => match x with (a;b) => (f n a; g (n;a) b) end).

  (** Each point x : sig A induces a new type sequence. *)
  Definition fibSeqToTypeSeq (x : sig A) : TypeSeq
    := Build_TypeSeq (fun k => B x^+k) (fun k => g x^+k).

  Notation coe := (transport idmap).

  Local Definition Beta {X Y F G} {x1 x2 : X} (p : x1 = x2)
    : coe (ap Y (ap F p)) o G x1 == G x2 o coe (ap Y p).
  Proof.
    destruct p; exact (fun _ => 1).
  Defined.

  Definition fib_seq_succ_equiv (x : sig A)
    : TypeSeqEquiv (fibSeqToTypeSeq x^+) (succTypeSeq (fibSeqToTypeSeq x)).
  Proof.
    srapply Build_TypeSeqEquiv.
    - srapply Build_TypeSeqMap.
      * exact (fun k => coe (ap _ (pair_lift_assoc x k))).
      * exact (fun k b => Beta (pair_lift_assoc x k) b). 
    - intro k; srapply isequiv_path.
  Defined.

  Definition fib_seq_lift_colim_equiv (x : sig A)
    : SeqColimit (fibSeqToTypeSeq x^+) <~> SeqColimit (fibSeqToTypeSeq x)
    := @equiv_compose _ _ _ (seq_colimit_succ_equiv _) _ _
       (functor_seq_colimit_equiv (fib_seq_succ_equiv x)).

  Definition fib_seq_lift_colim_equiv_beta (x : sig A) k b
    : ap (fib_seq_lift_colim_equiv _) (glue (fibSeqToTypeSeq x^+) k b) =
      ap (inj (fibSeqToTypeSeq x) k.+2) (Beta (pair_lift_assoc x k) b) @
      glue (fibSeqToTypeSeq x) k.+1 (coe (ap _ (pair_lift_assoc x k)) b).
  Proof.
    srapply (ap_compose' (functor_seq_colimit _) (seq_colimit_succ_equiv _) _ @ _).
    srapply (ap _ (SeqColimit_rec_beta_glue _ _ _ _ _ _) @ _).
    srapply (ap_pp (seq_colimit_succ_equiv _) _ _ @ _ ).
    srapply (whiskerL _ (SeqColimit_rec_beta_glue _ _ _ _ _ _) @ _).
    apply whiskerR; apply seq_colimit_succ_equiv_n.
  Defined.

  (** A fibered type sequence defines a type family. *)
  Definition fibTypeSeqToTypeFam : SeqColimit A -> Type.
  Proof.
    srapply SeqColimit_rec.
    - exact (fun n a => SeqColimit (fibSeqToTypeSeq (n;a))).
    - exact (fun n a => path_universe_uncurried (fib_seq_lift_colim_equiv (n;a))).
  Defined.

  Definition fibTypeSeqToTypeFam_beta n a :
    coe (ap fibTypeSeqToTypeFam (glue A n a)) = fib_seq_lift_colim_equiv (n;a).
  Proof.
    srapply (ap _ (SeqColimit_rec_beta_glue _ _ _ _ _ _) @ _).
    srapply (transport_idmap_path_universe_uncurried _).
  Defined.

  Local Definition Delta {X Y} {x1 x2 : X} {F} (p : x1 = x2) (psi : coe (ap Y p) = F) (y : Y x1)
    : (x1;y) = (x2;F y).
  Proof.
    destruct p; destruct psi; exact 1.
  Defined.

  Local Definition Delta_proj {X Y} {x1 x2 : X} {F} (p : x1 = x2) (psi : coe (ap Y p) = F) (y : Y x1)
    : ap pr1 (Delta p psi y) = p.
  Proof.
    destruct p; destruct psi; exact 1.
  Defined.

  (** The canonical map from the sequential colimit of Sigmas to the sequential colimit
      of the first component. *)
  Definition seqColimSumToSeqColim_proj : SeqColimit sigTypeSeq -> SeqColimit A
    := SeqColimit_rec sigTypeSeq _ (fun n x => inj _ n x.1) (fun n x => glue _ n x.1).

  (** The canonical map from the sequential colimit of Sigmas to the Sigma of
      sequential colimits. *)
  Definition seqColimSumToSumSeqColim : SeqColimit sigTypeSeq -> sig fibTypeSeqToTypeFam.
  Proof.
    srapply SeqColimit_rec.
    - exact (fun n x => match x with (a;b) => (inj A n a; inj (fibSeqToTypeSeq _) 0 b) end).
    - exact (fun n x => match x with (a;b) =>
        Delta _ (fibTypeSeqToTypeFam_beta n a) _ @ ap _ (glue (fibSeqToTypeSeq _) 0 b) end).
  Defined.

  Definition seqColimSumToSumSeqColim_beta_glue n a b :
    ap seqColimSumToSumSeqColim (glue sigTypeSeq n (a; b)) =
    Delta _ (fibTypeSeqToTypeFam_beta n a) _ @ ap _ (glue (fibSeqToTypeSeq _) 0 b).
  Proof.
    srapply SeqColimit_rec_beta_glue.
  Defined.

  (** An alternative induction principle for the sum of colimits. *)
  Section SeqColimitSumInd.

    Context (E : sig fibTypeSeqToTypeFam -> Type).
    Context (e : forall n a b, E (seqColimSumToSumSeqColim (inj sigTypeSeq n (a;b)))).
    Context (t : forall n a b, ap seqColimSumToSumSeqColim (glue sigTypeSeq n (a;b)) #
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

    Local Definition I {X Y Z} {x1 x2 : X} {p : x1 = x2} {F} {G1} {G2} (psi : coe (ap Y p) = F)
      : transport (fun x => forall y, Z (x;y)) p G1 = G2 <~>
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

    Local Definition Mu {X Y Z} {x1 x2 : X} (p : x1 = x2) {F} (G : forall z, Z z) {psi : coe (ap Y p) = F}
      {q} (theta : I psi (apD (fun x y => G (x;y)) p) = q) y
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
        intros b; exact (Delta _ (fibTypeSeqToTypeFam_beta n a) _ # h n.+1 (f n a) b).
    Defined.

    (** The path-point case of the nested induction. *)
    Local Definition Q_beta k n a b
      : Q k.+1 n a _ = Delta _ (fibTypeSeqToTypeFam_beta n a) _ # Q k n.+1 (f n a) b.
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
        srapply (_ @ ap _ (h n.+1 (f n a) b)).
        srapply (_ @ (Epsilon (glue A n a) (fib_seq_lift_colim_equiv_beta _ _ _))).
        srapply (_ @ ap _ (ap _ (Q_beta _ n a _))).
        srapply (ap _ ((transport_compose _ _ _ _)^ @ _)^).
        exact (apD _ (Beta _ b)).
    Defined.

    (** The point case of the nested induction. *)
    Local Definition F n a : forall x, E (inj _ n a; x)
      := SeqColimit_ind _ _ (fun k => Q k n a) (fun k => R k n a).

    (** The path case of the nested induction. *)
    Local Definition G n a y : F n a _ = Delta _ (fibTypeSeqToTypeFam_beta n a) y # F n.+1 (f n a) y.
    Proof.
      revert y; srapply (SeqColimit_ind _ _ (fun k => Q_beta k n a)); intros k b.
      srapply (Phi (glue A n a) (fib_seq_lift_colim_equiv_beta _ _ _)).
      rewrite (SeqColimit_ind_beta_glue _ _ _ (fun k : nat => R k n.+1 (f n a)) k _).
      rewrite (SeqColimit_ind_beta_glue _ _ _ (fun k : nat => R k n a) k.+1 _).
      rewrite (apD_compose' _ _ (Beta (pair_lift_assoc (n; a) k) b)).
      srapply functor_forall_equiv_pb_beta.
    Defined.

    (** The alternative induction rule in curried form. *)
    Definition SeqColimitSum_ind_cur : forall x y, E (x;y).
    Proof.
      srapply (SeqColimit_ind _ _ F).
      exact (fun n a => (I (fibTypeSeqToTypeFam_beta n a))^-1 (G n a)).
    Defined.

    (** The computation rule for the alternative induction rule in curried form. *)
    Definition SeqColimitSum_ind_cur_beta_glue n a :
      I (fibTypeSeqToTypeFam_beta n a) (apD SeqColimitSum_ind_cur (glue _ n a)) = G n a.
    Proof.
      apply moveR_equiv_M; srapply SeqColimit_ind_beta_glue.
    Defined.

    (** The alternative induction rule. *)
    Definition SeqColimitSum_ind : forall x, E x.
    Proof.
      intros [x y]; apply SeqColimitSum_ind_cur.
    Defined.

    (** The computation rule for the alternative induction rule. *)
    Definition SeqColimitSum_ind_beta_glue : forall n a b,
      apD SeqColimitSum_ind (ap seqColimSumToSumSeqColim (glue sigTypeSeq n _)) = t n a b.
    Proof.
      intros n a b.
      pose (h := SeqColimit_ind_beta_glue _ _ (fun k => Q k n a) (fun k => R k n a) 0 b).
      rewrite (Xi SeqColimitSum_ind (seqColimSumToSumSeqColim_beta_glue n a b)) in h.
      rewrite (Mu (glue _ n a) SeqColimitSum_ind (SeqColimitSum_ind_cur_beta_glue n a)) in h.
      rewrite concat_1p in h; exact (cancelL _ _ _ h).
    Defined.

  End SeqColimitSumInd.

  (** An alternative recursion principle for the sum of colimits. *)
  Section SeqColimitSumRec.

    Context E (e : forall n a, B (n;a) -> E).
    Context (t : forall n a b, e n.+1 (f n a) (g (n;a) b) = e n a b).

    Definition SeqColimitSum_rec : sig fibTypeSeqToTypeFam -> E.
    Proof.
      exact (SeqColimitSum_ind _ e (fun n a b => transport_const _ _ @ t n a b)).
    Defined.

    Definition SeqColimitSum_rec_beta_glue : forall n a b,
      ap SeqColimitSum_rec (ap seqColimSumToSumSeqColim (glue sigTypeSeq n (a;b))) = t n a b.
    Proof.
      intros n a b; srapply (cancelL _ _ _ ((apD_const _ _)^ @ _)).
      apply SeqColimitSum_ind_beta_glue.
    Defined.

  End SeqColimitSumRec.

  Definition seq_colimit_sum_uniqueness E (F G : sig fibTypeSeqToTypeFam -> E)
    : F o seqColimSumToSumSeqColim == G o seqColimSumToSumSeqColim -> F == G.
  Proof.
    intro h; srapply (SeqColimitSum_ind _ (fun _ _ _ => h _)); intros n a b.
    srapply ((transport_compose _ _ _ _)^ @ _); exact (apD h (glue sigTypeSeq n (a;b))).
  Defined.

  (** The canonical map from the sequential colimit of Sigmas to the Sigma of
      sequential colimits is an equivalence. *)
  Definition seqColimSumToSumSeqColim_equiv : IsEquiv seqColimSumToSumSeqColim.
  Proof.
    assert (L : {G : _ & Sect seqColimSumToSumSeqColim G}).
    - srapply (_;_).
      + srapply SeqColimitSum_rec.
        * exact (fun n a b => inj sigTypeSeq n (a;b)).
        * exact (fun n a b => glue sigTypeSeq n (a;b)).
      + srapply seq_colimit_uniqueness.
        * exact (fun n a => 1).
        * intros n a; rewrite concat_1p, concat_p1, ap_compose, ap_idmap.
          rewrite SeqColimitSum_rec_beta_glue; exact 1.
    - srapply (isequiv_adjointify _ L.1 _ L.2); srapply seq_colimit_sum_uniqueness.
      intro x; rewrite L.2; exact 1.
  Defined.

  (** The canonical map from the sequential colimit of Sigmas to the Sigma of
      sequential colimits commutes with the first projection. *)
  Definition seqColimSumToSumSeqColim_proj
    : pr1 o seqColimSumToSumSeqColim == seqColimSumToSeqColim_proj.
  Proof.
    srapply seq_colimit_uniqueness.
    - exact (fun n a => 1).
    - intros n [a b]; rewrite concat_1p, concat_p1, ap_compose, !SeqColimit_rec_beta_glue.
      rewrite ap_pp, (Delta_proj _ (fibTypeSeqToTypeFam_beta n a)).
      srapply (whiskerL _ _ @ concat_p1 _); rewrite (ap_compose _ _ _)^; simpl.
      rewrite ap_const; exact 1.
  Defined.

End FibTypeSeq.