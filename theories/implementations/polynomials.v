Require Import HoTT.hit.quotient
  HoTT.Basics.PathGroupoids
  HoTT.Types.Universe
  HoTT.Basics.Trunc.
Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.implementations.list.

Import ListNotations.

Section contents.
  Context {univalence : Univalence} {funext : Funext}.
  Context R `{SemiRing R} `{IsHSet R}.

  Definition all_zero : list R -> Type := for_all ((=) 0).

  Lemma all_zero_ind : forall (Pr : list R -> Type),
  Pr [] -> (forall ps, all_zero ps -> Pr ps -> Pr (0 :: ps)) ->
  forall ps, all_zero ps -> Pr ps.
  Proof.
  intros Pr Pr0 PrS.
  intros ps;induction ps as [|p ps IH];auto.
  intros [[] H1];auto.
  Qed.

  (* Polynomials are equal if one is a prefix of the other *)
  Definition same_poly : relation (list R) :=
    fix F p q :=
    match p, q with
    | [], _ => all_zero q
    | _, [] => all_zero p
    | h :: t, h' :: t' => h = h' ∧ F t t'
    end.

  Instance : forall l, IsHProp (all_zero l).
  Proof.
  unfold all_zero. intros l.
  unfold compose. apply for_all_trunc.
  apply for_all_trivial. apply _.
  Qed.

  Global Instance same_poly_hprop : forall P Q, IsHProp (same_poly P Q).
  Proof.
  intros P;induction P as [|x P IHP].
  - simpl. apply _.
  - intros Q;destruct Q as [|y Q];simpl;apply _.
  Qed.

  Global Instance : Reflexive same_poly.
  Proof.
  intros x;induction x as [|p ps IH];simpl;auto.
  split.
  Qed.

  Global Instance : Symmetric same_poly.
  Proof.
  intros ps;induction ps as [|p ps IH];intros [|q qs];simpl;auto.
  intros [pq Hps]. split;auto. apply symmetry;auto.
  Qed.

  Lemma all_zero_trans : forall ps, all_zero ps ->
    forall qs, same_poly ps qs -> all_zero qs.
  Proof.
  intros ps;induction ps as [|p ps IHp];[intros _|intros [Hp Hps]];
  intros [|q qs];simpl;auto.
  - split.
  - intros [Hpq Hs]. split.
    + path_via p.
    + apply IHp;auto.
  Qed.

  Lemma all_zero_same : forall ps, all_zero ps ->
    forall qs, all_zero qs -> same_poly ps qs.
  Proof.
  intros ps;induction ps as [|p ps IHp];simpl;auto.
  intros [Hp Hps] [|q qs];simpl.
  - intros _;split;auto.
  - intros [Hq Hqs];split;auto.
    path_via 0.
  Qed.

  Lemma all_zero_same_nil : forall ps, all_zero ps -> same_poly ps [].
  Proof.
  intros. apply all_zero_same;auto. split.
  Qed.

  Global Instance : Transitive same_poly.
  Proof.
  intros ps;induction ps as [|p ps IHps].
  - simpl. intros ?? Hy Hs;eapply all_zero_trans;eauto.
  - intros [|q qs] [|r rs];simpl;auto.
    + intros [Hp Hps] [Hr Hrs];split.
      * path_via 0.
      * apply all_zero_same;auto.
    + intros [Hpq Hs] [Hq Hqs];split.
      * path_via q.
      * apply all_zero_trans with qs;trivial.
        apply symmetry. assumption.
    + intros [Hpq Hpqs] [Hqr Hqrs];eauto.
  Qed.

  Definition poly := quotient same_poly.

  Definition of_list : list R -> poly := class_of _.

  Definition poly_path {P Q} : same_poly P Q -> of_list P = of_list Q
    := related_classes_eq _.

(*   Global Instance poly_set : IsHSet poly := _. *)

  Definition poly_rect : forall (T : poly -> Type) {sT : forall P, IsHSet (T P)}
    (dclass : forall ps, T (of_list ps))
    (dequiv : forall ps qs (Hs: same_poly ps qs),
       (poly_path Hs) # (dclass ps) = (dclass qs))
    P, T P
    := quotient_ind same_poly.

  Definition poly_compute {T sT} dclass dequiv x
    : @poly_rect T sT dclass dequiv (of_list x) = dclass x := idpath.

  Definition poly_compute_path {T sT} dclass dequiv : forall ps qs (Hs : same_poly ps qs),
    apD (@poly_rect T sT dclass dequiv) (poly_path Hs) = dequiv ps qs Hs.
  Proof.
  apply quotient_ind_compute_path.
  Qed.

  Coercion poly_constant (c : R) : poly := of_list [c].

  Global Instance poly_zero: Zero poly := of_list [].
  Global Instance poly_one: One poly := poly_constant 1.

  Lemma all_zero_eq_zero : forall ps, all_zero ps -> of_list ps = 0.
  Proof.
  intros ps Hps.
  apply poly_path.
  destruct ps;auto.
  Qed.

  Definition poly_ind (Pr : poly -> Type) {hPr : forall P, IsHProp (Pr P)} :
    (forall ps, Pr (of_list ps)) -> forall P, Pr P.
  Proof.
  intros dclass.
  apply (poly_rect Pr dclass).
  intros;apply path_ishprop.
  Qed.

  Definition poly_rec {T : Type} {sT : IsHSet T}: forall (dclass : list R -> T)
    (dequiv : forall ps qs, same_poly ps qs -> dclass ps = dclass qs),
    poly -> T := quotient_rec _.

  Definition poly_rec2 {T : Type} {sT : IsHSet T}
   : forall (dclass : list R -> list R -> T)
    (dequiv : forall ps1 qs1, same_poly ps1 qs1 -> forall ps2 qs2, same_poly ps2 qs2 ->
      dclass ps1 ps2 = dclass qs1 qs2),
    poly -> poly -> T := @quotient_rec2 _ _ _ _ _ (BuildhSet _).

  Lemma same_poly_map (f : R -> R) (Hf : f 0 = 0)
   : forall ps qs, same_poly ps qs -> same_poly (map f ps) (map f qs).
  Proof.
  intros ps;induction ps as [|p ps IHps].
  - simpl. unfold all_zero.
    intros qs Hqs. apply for_all_map with (paths 0);[|assumption].
    intros x []. apply symmetry;assumption.
  - intros [|q qs].
    + apply (for_all_map _ _ f).
      intros x []. apply symmetry;assumption.
    + simpl. intros [Hpq Hs];auto.
  Qed.

  Definition poly_map (f : R -> R) (Hf : f 0 = 0) : poly -> poly.
  Proof.
  apply (poly_rec (compose of_list (map f))).
  intros ps qs Hs.
  apply poly_path. apply same_poly_map ;assumption.
  Defined.

  Lemma map2_nil_l (f : R -> R -> R) : forall ps, map2 f id id [] ps = ps.
  Proof.
  intros [|p ps];reflexivity.
  Qed.

  Lemma map2_nil_r (f : R -> R -> R) : forall ps, map2 f id id ps [] = ps.
  Proof.
  intros [|p ps];reflexivity.
  Qed.

  Lemma same_poly_map2 (f : R -> R -> R)
    (Hfl : forall x, f 0 x = x) (Hfr : forall x, f x 0 = x)
    : forall ps1 ps2 qs1 qs2,
      same_poly ps1 qs1 -> same_poly ps2 qs2 ->
      same_poly (map2 f id id ps1 ps2) (map2 f id id qs1 qs2).
  Proof.
  intros ps1;induction ps1 as [|p1 ps1 IH1].
  - intros ps2; rewrite map2_nil_l; induction ps2 as [|p2 ps2 IH2];intros qs1 qs2 H1 H2.
    + apply for_all_map2 with (paths 0) (paths 0);auto.
      intros ?? [] [];apply symmetry;trivial.
    + destruct qs2 as [|q2 qs2].
      * apply all_zero_same;trivial.
        rewrite map2_nil_r. trivial.
      * destruct H2 as [[] H2];clear q2.
        destruct qs1 as [|q1 qs1];simpl;split;trivial.
        ** destruct H1 as [H1 _]. rewrite <-H1.
           apply symmetry;apply Hfl.
        ** destruct H1;auto.
  - intros [|p2 ps2] [|q1 qs1] [|q2 qs2];simpl;auto.
    + intros [[] H1] [[] H2];clear p1 q2;split;trivial.
      apply all_zero_same;trivial.
    + intros [[] H1] [[] H2];clear q1 q2;split.
      * apply symmetry;apply Hfr.
      * pose proof (IH1 [] qs1 qs2 H1 H2) as H3.
        rewrite map2_nil_r in H3. trivial.
    + intros [[] H1] [[] H2];clear p1 p2.
      split.
      * apply symmetry;trivial.
      * apply all_zero_trans with (map2 f id id [] []);[split|].
        apply symmetry.
        apply IH1;apply all_zero_same;auto;split.
    + intros [[] H1] [[] H2];clear p1 q2.
      split;[apply Hfl|].
      pose proof (fun X => IH1 ps2 [] qs2 X H2) as H3.
      rewrite map2_nil_l in H3. apply H3.
      apply all_zero_same;auto;split.
    + intros [[] H1] [[] H2];clear q1 p2.
      split;[apply Hfr|].
      pose proof (IH1 ps2 qs1 [] H1) as H3.
      rewrite map2_nil_r in H3. apply H3.
      apply all_zero_same;auto;split.
    + intros [[] H1] [[] H2];clear q1 q2.
      auto.
  Qed.

  Definition poly_map2 (f : R -> R -> R)
    (Hfl : forall x, f 0 x = x) (Hfr : forall x, f x 0 = x): poly -> poly -> poly.
  Proof.
  apply (poly_rec2 (fun ps qs => of_list (map2 f id id ps qs))).
  intros ps1 qs1 H1 ps2 qs2 H2. apply poly_path.
  apply same_poly_map2;assumption.
  Defined.

  Lemma poly_map2_compute f Hfl Hfr ps qs :
    poly_map2 f Hfl Hfr (of_list ps) (of_list qs) = of_list (map2 f id id ps qs).
  Proof.
  reflexivity.
  Qed.

  Global Instance : Plus poly.
  Proof.
  red. apply (poly_map2 (+)).
  - exact left_identity.
  - exact right_identity.
  Defined.

  (* TODO *)
(*   Global Instance neg : Negate poly.
  Proof.
  red. apply (poly_map (-)).
  Abort. *)

  Definition mult_cl : R -> poly -> poly.
  Proof.
  intros c.
  apply (poly_map (c *.)).
  rewrite (@commutativity _ _ (.*.) _). apply left_absorb.
  Defined.

  (* mlX P[X] = X * P *)
  Definition mlX : poly -> poly.
  Proof.
  apply (poly_rec (fun qs => of_list (0 :: qs))).
  intros. apply poly_path. split;auto.
  Defined.

  Fixpoint ml ps Q :=
    match ps with
    | [] => of_list []
    | c :: ps => mult_cl c Q + mlX (ml ps Q)
    end.

  Lemma mlX_zero : mlX 0 = 0.
  Proof.
  simpl. apply poly_path.
  split;split.
  Qed.

  Lemma mult_cl_zero : forall Q, mult_cl 0 Q = 0.
  Proof.
  apply poly_ind;[apply _|].
  simpl. intros. apply poly_path.
  apply all_zero_same_nil.
  red. apply for_all_map with (fun _ => True).
  - intros x _;apply symmetry. apply left_absorb.
  - apply for_all_trivial. auto.
  Qed.

  Lemma ml_zero_l : forall ps, all_zero ps -> forall Q, ml ps Q = 0.
  Proof.
  apply (all_zero_ind (fun ps => forall Q, ml ps Q = 0)).
  - reflexivity.
  - intros ps Hps IH Q.
    simpl.
    rewrite IH. rewrite mlX_zero.
    rewrite mult_cl_zero. reflexivity.
  Qed.

  Lemma mult_pr : ∀ ps1 ps2, same_poly ps1 ps2 ->
    forall Q, ml ps1 Q = ml ps2 Q.
  Proof.
  intros ps1;induction ps1 as [|p1 ps1 IH1].
  - simpl. intros. apply symmetry, ml_zero_l. assumption.
  - intros [|p2 ps2].
    + intros; apply ml_zero_l; assumption.
    + intros [[] H1] Q;clear p2.
      simpl; apply ap, ap, IH1, H1.
  Defined.

  Lemma mult_respectful : ∀ ps qs : list R, same_poly ps qs → ml ps = ml qs.
  Proof.
  intros ps1 ps2 Hps. apply path_forall.
  red; apply poly_ind.
  - apply _.
  - intro;apply mult_pr. assumption.
  Qed.

  Global Instance: Mult poly.
  Proof.
  red. apply (poly_rec ml). exact mult_respectful.
  Defined.

  Lemma pl_comm : forall ps qs : list R, map2 (+) id id ps qs = map2 (+) id id qs ps.
  Proof.
  intros ps;induction ps as [|p ps IHps].
  - intros. rewrite map2_nil_r. apply map2_nil_l.
  - intros [|q qs].
    + rewrite map2_nil_l. apply map2_nil_r.
    + simpl. rewrite (@commutativity R _ _ _ p q). apply ap;trivial.
  Qed.

  Instance: @Commutative poly poly (+).
  Proof.
  red. apply (poly_ind (fun x => forall y, _)).
  intros ps. apply (poly_ind _).
  intros;simpl;apply poly_path. rewrite pl_comm. apply reflexivity.
  Qed.

  Instance: @Associative poly (+).
  Proof.
  hnf. apply (poly_ind (fun x => forall y z, _)).
  intros ps. apply (poly_ind (fun y => forall z, _)).
  intros qs. apply (poly_ind _).
  intros rs. apply poly_path.
  revert qs rs;
  induction ps as [|p ps IHps];[|intros [|q qs] [|r rs]];
  try apply reflexivity.
  - intros;rewrite map2_nil_l,map2_nil_l. apply reflexivity.
  - simpl. split;trivial.
    apply associativity.
  Qed.

  Instance: LeftIdentity (+) (0:poly).
  Proof.
  hnf. apply (poly_ind _).
  intros ps. apply poly_path. rewrite map2_nil_l. apply reflexivity.
  Qed.

  Instance: CommutativeMonoid poly (Aop:=(+)) (Aunit:=0).
  Proof.
  repeat (split; try apply _).
  intros x. path_via (0 + x).
  - apply commutativity.
  - apply left_identity.
  Qed.

  Lemma ml_zero_r : forall ps, ml ps 0 = 0.
  Proof.
  intros ps;induction ps as [|p ps IHps].
  - reflexivity.
  - simpl. rewrite IHps.
    rewrite mlX_zero. reflexivity.
  Qed.

  Lemma cons_plus_mlX : forall ps p, of_list (p :: ps) = of_list [p] + mlX (of_list ps).
  Proof.
  intros. simpl. apply (ap of_list).
  rewrite map2_cons. rewrite map2_nil_l. rewrite right_identity. reflexivity.
  Qed.

  Lemma plus_cons : forall p ps q qs,
    of_list (p::ps) + of_list (q::qs) = of_list ((p+q) :: map2 plus id id ps qs).
  Proof.
  intros. reflexivity.
  Qed.

  Lemma plus_consX : forall p ps q qs,
    of_list (p::ps) + of_list (q::qs) = of_list [p+q] + mlX (of_list ps + of_list qs).
  Proof.
  intros. rewrite plus_cons,plus_cons.
  rewrite map2_nil_l. rewrite (@right_identity R R plus 0 _).
  reflexivity.
  Qed.

  Lemma mlX_plus : forall P Q, mlX P + mlX Q = mlX (P + Q).
  Proof.
  apply (poly_ind (fun x => forall y, _)).
  intros ps;apply (poly_ind _);intros qs.
  simpl. rewrite plus_cons. rewrite (@left_identity R R plus _ _).
  reflexivity.
  Qed.

  Lemma mult_cl_plus : forall c P Q, mult_cl c (P + Q) = mult_cl c P + mult_cl c Q.
  Proof.
  intros c P Q;revert P Q c.
  apply (poly_ind (fun x => forall y z, _)).
  intros ps;apply (poly_ind (fun x => forall y, _));intros qs.
  simpl. unfold compose;simpl.
  revert qs. induction ps as [|p ps IHps].
  - intros. rewrite map2_nil_l. simpl. rewrite (@left_identity poly poly plus _ _).
    reflexivity.
  - intros [|q qs] c.
    + rewrite map2_nil_r. apply symmetry;apply right_identity.
    + rewrite map2_cons.
      simpl. rewrite plus_consX.
      rewrite <-IHps. rewrite <-cons_plus_mlX. rewrite simple_distribute_l.
      reflexivity.
  Qed.

  Lemma ml_plus : forall ps P Q, ml ps (P + Q) = ml ps P + ml ps Q.
  Proof.
  induction ps as [|p ps IHps];trivial.
  intros P Q; simpl. rewrite IHps. rewrite <-mlX_plus.
  rewrite mult_cl_plus.
  set (A := mult_cl p P);set (B := mult_cl p Q);
  set (C := mlX (ml ps P));set (D := mlX (ml ps Q)).
  clearbody A B C D.
  rewrite <-simple_associativity,<-simple_associativity. apply ap.
  rewrite (@commutativity poly _ _ _). rewrite <-simple_associativity. apply ap.
  apply commutativity.
  Qed.

  Definition X := of_list [0; 1].

  Lemma mult_singleton : forall p P, of_list [p] * P = mult_cl p P.
  Proof.
  intros p. apply (poly_ind _).
  simpl. unfold compose.
  intros ps. destruct ps as [|p' ps].
  - simpl. apply ml_zero_r.
  - simpl. apply (ap (of_list)). simpl.
    rewrite map2_nil_r. apply (ap (fun x => x :: _)).
    apply right_identity.
  Defined.

  Lemma mult_cons : forall p ps P,
    of_list (p::ps) * P = of_list [p] * P + mlX (of_list ps * P).
  Proof.
  intros p ps. apply (poly_ind _). intros qs.
  rewrite mult_singleton.
  reflexivity.
  Defined.

  Lemma zero_singleton : of_list [0] = 0.
  Proof.
  apply mlX_zero.
  Qed.

  Instance: LeftAbsorb (.*.) (0:poly).
  Proof.
  red. reflexivity.
  Qed.

  Instance: LeftIdentity (.*.) (1:poly).
  Proof.
  intros P. rewrite mult_singleton.
  revert P. apply (poly_ind _).
  intros. simpl. unfold compose.
  apply ap. apply map_id. apply left_identity.
  Qed.

  Lemma mlX_ml_X : forall P, mlX P = X * P.
  Proof.
  apply (poly_ind _).
  unfold X;simpl. intros ps.
  rewrite mult_cons.
  rewrite zero_singleton. rewrite (@left_absorb _ _ _ 0 _).
  change (of_list [1]) with 1. rewrite (@left_identity poly poly mult _ _).
  reflexivity.
  Defined.

  Lemma ml_X_r : forall (ps : list R) q qs,
    ml ps (of_list (q :: qs)) = mult_cl q (of_list ps) + mlX (ml ps (of_list qs)).
  Proof.
  intros ps q qs;revert qs q;
  induction ps as [|p ps IHps].
  - simpl. intros _ q. change (of_list [0]) with (mlX 0). rewrite mlX_zero.
    reflexivity.
  - intros [|q qs] q'.
    + simpl. unfold compose;simpl. rewrite ml_zero_r. repeat rewrite mlX_zero.
      rewrite (commutativity (f:=(.*.)) p q').
      rewrite IHps. rewrite ml_zero_r,mlX_zero.
      rewrite (cons_plus_mlX (map (mult q') ps) (q' * p)).
      repeat rewrite (@right_identity poly poly (+) 0 _).
      reflexivity.
    + simpl. unfold compose.
      simpl. repeat rewrite (cons_plus_mlX (_::_)).
      repeat rewrite (cons_plus_mlX (map _ _)).
      repeat rewrite <-simple_associativity.
      apply ap2;[apply ap,(ap (fun x => [x])),commutativity|].
      rewrite mlX_plus,mlX_plus. apply ap.
      simpl. repeat rewrite plus_cons.
      repeat rewrite (@right_identity R R plus 0 _).
      rewrite map2_nil_l,map2_nil_l.
      repeat rewrite IHps.
      set (P := of_list ps). set (Q := of_list qs).
      rewrite (simple_associativity (of_list [p * q])). rewrite plus_cons.
      rewrite (@right_identity R R plus _ _).
      rewrite map2_nil_l.
      set (P' := of_list (p*q :: map (mult p) qs)).
      set (qP := mult_cl q P);set (qP' := mult_cl q' P).
      set (XqP := mlX (qP + mlX (ml ps Q))).
      change (P' + (qP' + XqP) = qP' + (P' + XqP)).
      repeat rewrite simple_associativity.
      rewrite (commutativity P' qP'). reflexivity.
  Qed.

  Instance: @Commutative poly poly (.*.).
  Proof.
  hnf. apply (poly_ind (fun x => forall y, _)).
  intros ps. apply (poly_ind _).
  change (∀ qs, ml ps (of_list qs) = ml qs (of_list ps)).
  induction ps as [|p ps IHps].
  - intros qs;simpl. apply symmetry, ml_zero_r.
  - intros qs;simpl.
    induction qs as [|q qs IHqs].
    + simpl. rewrite ml_zero_r,mlX_zero. reflexivity.
    + rewrite IHps. simpl.
      unfold compose;simpl.
      rewrite (commutativity (f:=(.*.)) p q).
      rewrite ml_X_r.
      set (QP := mlX (ml qs (of_list ps))).
      clearbody QP.
      set (qp := q * p);clearbody qp.
      rewrite cons_plus_mlX. rewrite (cons_plus_mlX (map _ _)).
      repeat rewrite <-mlX_plus. simpl.
      set (pqs := map (mult p) qs).
      set (qps := map (mult q) ps).
      clearbody pqs qps.
      repeat rewrite <-simple_associativity. apply ap.
      repeat rewrite simple_associativity.
      rewrite (commutativity (f:=plus) (of_list _)). reflexivity.
  Qed.

  (* Doesn't work for rect because we need to verify some nutty identity *)
  Lemma ind (Pr : poly -> Type) `{forall P, IsHProp (Pr P)} :
    Pr 0 -> (forall (c:R) P, Pr P -> Pr ((c : poly) + mlX P)) ->
    forall P, Pr P.
  Proof.
  intros init next.
  apply (poly_ind Pr).
  induction ps as [|p ps IHps].
  - exact init.
  - rewrite cons_plus_mlX. apply next. assumption.
  Qed.

  Fixpoint rec_aux {T : Type} (val0 : T) (val_c_X : R -> poly -> T -> T) ps :=
    match ps with
    | [] => val0
    | p :: ps => val_c_X p (of_list ps) (rec_aux val0 val_c_X ps)
    end.

  Lemma rec_aux_zero {T : Type}
    (val0 : T) (val_c_X : R -> poly -> T -> T)
    (pr0 : val_c_X 0 0 val0 = val0)
    : forall ps, all_zero ps -> rec_aux val0 val_c_X ps = val0.
  Proof.
  induction ps as [|p ps IHps].
  - reflexivity.
  - intros [[] Hps];clear p.
    simpl.
    rewrite (all_zero_eq_zero ps Hps).
    rewrite (IHps Hps).
    exact pr0.
  Qed.

  Lemma rec_aux_same {T : Type}
    (val0 : T) (val_c_X : R -> poly -> T -> T)
    (pr0 : val_c_X 0 0 val0 = val0)
    : forall ps qs, same_poly ps qs ->
      rec_aux val0 val_c_X ps = rec_aux val0 val_c_X qs.
  Proof.
  intros ps;induction ps as [|p ps IHps];intros [|q qs] Hsame.
  - reflexivity.
  - simpl.
    apply symmetry.
    destruct Hsame as [[] Hsame];clear q.
    rewrite rec_aux_zero by assumption.
    rewrite (all_zero_eq_zero _ Hsame). assumption.
  - apply rec_aux_zero;auto.
  - simpl;destruct Hsame as [[] Hsame];clear q.
    rewrite (poly_path Hsame).
    apply ap.
    auto.
  Qed.

  Lemma rec {T : Type} {sT : IsHSet T}
    (val0 : T) (val_c_X : R -> poly -> T -> T)
    (pr0 : val_c_X 0 0 val0 = val0)
    : poly -> T.
  Proof.
  apply (poly_rec (rec_aux val0 val_c_X)).
  apply rec_aux_same. assumption.
  Defined.

  Lemma rec_compute_zero {T : Type} {sT : IsHSet T}
    (val0 : T) (val_c_X : R -> poly -> T -> T)
    (pr0 : val_c_X 0 0 val0 = val0)
    : rec val0 val_c_X pr0 0 = val0.
  Proof.
  reflexivity.
  Qed.

  Lemma rec_compute_X {T : Type} {sT : IsHSet T}
    (val0 : T) (val_c_X : R -> poly -> T -> T)
    (pr0 : val_c_X 0 0 val0 = val0)
    : forall (c:R) P,
      rec val0 val_c_X pr0 ((c:poly) + mlX P) =
       val_c_X c P (rec val0 val_c_X pr0 P).
  Proof.
  intros c. apply (poly_ind _).
  intros [|p ps].
  - simpl. rewrite right_identity. reflexivity.
  - simpl. rewrite right_identity. reflexivity.
  Qed.

  Instance: @LeftDistribute poly mult plus.
  Proof.
  hnf.
  apply (poly_ind (fun a => forall b c, _)).
  apply ml_plus.
  Qed.

  Instance: @RightDistribute poly mult plus.
  Proof.
  hnf;intros A B C.
  rewrite (commutativity (f:=mult)).
  rewrite simple_distribute_l.
  rewrite (commutativity (f:=mult) C A).
  rewrite (commutativity (f:=mult) C B).
  reflexivity.
  Qed.
(* 
  Instance: @Associative poly (.*.).
  Proof.
  hnf. apply (ind (fun x => forall y z, _)).
  - intros. rewrite left_absorb,left_absorb,left_absorb. reflexivity.
  - intros c A IHP.
    intros B C.
    rewrite simple_distribute_r.
    
  Qed.

  Instance: CommutativeMonoid poly (Aop:=(.*.)) (Aunit:=1).
  Proof.
  repeat (split; try apply _).
  Qed.

  Global Instance: SemiRing poly.
  Proof.
  constructor.
  - apply _.
  - 
  Admitted.
 *)
End contents.

(*

Section test.

  Context `{Ring R} (x y: poly (poly (poly (poly R)))).

  Goal x + y == x * y.
    set (d := Plus_instance_0 ).
    set (u := Mult_instance_0).
    set (t := poly (poly R)).
    unfold poly_zero.

*)
