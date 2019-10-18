Require Import HoTT.HIT.quotient
  HoTT.Basics.PathGroupoids
  HoTT.Types.Universe
  HoTT.Basics.Trunc
  HoTT.Basics.Decidable.
Require Import 
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.theory.rings
  HoTT.Classes.theory.dec_fields.

Module Frac.

Section contents.
Universe UR.
Context `{Funext} `{Univalence} (R:Type@{UR})
  `{IntegralDomain R} `{DecidablePaths R}.

Record Frac@{} : Type
  := frac { num: R; den: R; den_ne_0: PropHolds (den <> 0) }.
  (* We used to have [den] and [den_nonzero] bundled,
     which did work relatively nicely with Program, but the
     extra messyness in proofs etc turned out not to be worth it. *)

Lemma Frac_ishset' : IsHSet Frac.
Proof.
assert (E : sigT (fun n : R => sigT (fun d : R => ~ d = 0 )) <~> Frac).
- issig.
- apply (trunc_equiv' _ E).
Qed.

Global Instance Frac_ishset@{} : IsHSet Frac
  := ltac:(first [exact Frac_ishset'@{UR Ularge Set}|
                  exact Frac_ishset'@{}]).

Local Existing Instance den_ne_0.

Global Instance Frac_inject@{} : Cast R Frac.
Proof.
intros x. apply (frac x 1 _).
Defined.

Global Instance Frac_0@{} : Zero Frac := ('0 : Frac).
Global Instance Frac_1@{} : One Frac := ('1 : Frac).

Instance pl@{} : Plus Frac.
Proof.
intros q r; refine (frac (num q * den r + num r * den q) (den q * den r) _).
Defined.

Definition equiv@{} := fun x y => num x * den y = num y * den x.

Global Instance equiv_equiv_rel@{} : EquivRel equiv.
Proof.
split.
- intros x. hnf. reflexivity.
- intros x y. unfold equiv.
  apply symmetry.
- intros x y z. unfold equiv.
  intros E1 E2.
  apply (mult_left_cancel (den y)).
  + solve_propholds.
  + rewrite !mult_assoc, !(mult_comm (den y)).
    rewrite E1, <-E2.
    rewrite <-!mult_assoc. rewrite (mult_comm (den x)).
    reflexivity.
Qed.

Global Instance equiv_dec@{} : forall x y: Frac, Decidable (equiv x y)
  := fun x y => decide_rel (=) (num x * den y) (num y * den x).

Lemma pl_respect@{} : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  equiv (q1 + r1) (q2 + r2).
Proof.
unfold equiv;intros q1 q2 Eq r1 r2 Er.
simpl.
rewrite plus_mult_distr_r.
rewrite <-(associativity (num q1) (den r1)).
rewrite (associativity (den r1)), (mult_comm (den r1)), <-(associativity (den q2)).
rewrite (associativity (num q1)), Eq.
rewrite (mult_comm (den q2)), <-(associativity (num r1)), (associativity (den q1)).
rewrite (mult_comm (den q1)), <-(associativity (den r2)), (associativity (num r1)).
rewrite Er.
rewrite (mult_comm (den r1)), <-(associativity (num q2)), (associativity (den q1)).
rewrite (mult_comm (den q1)), <-(associativity (den r2)), (associativity (num q2)).
rewrite <-(associativity (num r2)), (associativity (den r1)),
  (mult_comm _ (den q2)).
rewrite (mult_comm (den r1)), (associativity (num r2)).
apply symmetry;apply plus_mult_distr_r.
Qed.

Lemma pl_comm@{} : forall q r, equiv (pl q r) (pl r q).
Proof.
intros q r;unfold equiv;simpl.
rewrite (mult_comm (den r)), plus_comm. reflexivity.
Qed.

Lemma pl_assoc@{} : forall q r t, equiv (pl q (pl r t)) (pl (pl q r) t).
Proof.
intros;unfold equiv;simpl.
apply ap2;[|apply symmetry,associativity].
rewrite plus_mult_distr_r.
rewrite (plus_mult_distr_r _ _ (den t)).
rewrite plus_assoc. apply ap2;[apply ap2|].
- apply associativity.
- rewrite <-(associativity (num r)), <-(associativity (num r) (den q)).
  rewrite (mult_comm (den t)). reflexivity.
- rewrite (mult_comm (den q));apply symmetry,associativity.
Qed.

Instance ml@{} : Mult Frac.
Proof.
intros q r; refine (frac (num q * num r) (den q * den r) _).
Defined.

Lemma ml_respect@{} : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  equiv (q1 * r1) (q2 * r2).
Proof.
unfold equiv;intros q1 q2 Eq r1 r2 Er.
simpl.
rewrite <-(associativity (num q1)), (associativity (num r1)).
rewrite (mult_comm (num r1)), <-(associativity (den q2)), (associativity (num q1)).
rewrite Eq, Er.
rewrite <-(associativity (num q2)), (associativity (den q1)), (mult_comm (den q1)).
rewrite <-(simple_associativity (num r2)), <-(simple_associativity (num q2)).
reflexivity.
Qed.

Instance neg@{} : Negate Frac.
Proof.
intros q;refine (frac (- num q) (den q) _).
Defined.

Lemma neg_respect@{} : forall q r, equiv q r -> equiv (- q) (- r).
Proof.
unfold equiv;simpl;intros q r E.
rewrite <-2!negate_mult_distr_l. rewrite E;reflexivity.
Qed.

Lemma nonzero_num@{} x : ~ equiv x 0 <-> num x <> 0.
Proof.
split; intros E F; apply E.
- red. rewrite F. simpl. rewrite 2!mult_0_l. reflexivity.
- red in F;simpl in F. rewrite mult_1_r, mult_0_l in F. trivial.
Qed.

Lemma pl_0_l@{} x : equiv (0 + x) x.
Proof.
red;simpl. rewrite mult_1_r, mult_0_l, mult_1_l, plus_0_l. reflexivity.
Qed.

Lemma pl_0_r@{} x : equiv (x + 0) x.
Proof.
red;simpl. rewrite 2!mult_1_r, mult_0_l, plus_0_r. reflexivity.
Qed.

Lemma pl_neg_l@{} x : equiv (- x + x) 0.
Proof.
red;simpl.
rewrite mult_1_r, mult_0_l.
rewrite <-plus_mult_distr_r.
rewrite plus_negate_l.
apply mult_0_l.
Qed.

Lemma ml_assoc@{} q r t : equiv (ml q (ml r t)) (ml (ml q r) t).
Proof.
red;simpl.
rewrite (associativity (num q)), (associativity (den q)).
reflexivity.
Qed.

Instance dec_rec@{} : DecRecip Frac := fun x =>
  match decide_rel (=) (num x) 0 with
  | inl _ => 0
  | inr P => frac (den x) (num x) P
  end.

Lemma dec_recip_respect@{} : forall q r, equiv q r -> equiv (/ q) (/ r).
Proof.
unfold equiv,dec_recip,dec_rec;intros q r E;simpl.
destruct (decide_rel paths (num q) 0) as [E1|E1],
(decide_rel paths (num r) 0) as [E2|E2];simpl.
- trivial.
- rewrite E1 in E;rewrite mult_0_l in E.
  destruct E2.
  apply (right_cancellation_ne_0 mult (den q));try solve_propholds.
  rewrite mult_0_l;apply symmetry,E.
- rewrite E2 in E;rewrite mult_0_l in E.
  destruct E1.
  apply (right_cancellation_ne_0 mult (den r));try solve_propholds.
  rewrite mult_0_l;trivial.
- rewrite (mult_comm (den q)), (mult_comm (den r)).
  apply symmetry, E.
Qed.

End contents.

Arguments Frac R {Rzero} : rename.
Arguments frac {R Rzero} _ _ _ : rename.
Arguments num {R Rzero} _ : rename.
Arguments den {R Rzero} _ : rename.
Arguments den_ne_0 {R Rzero} _ _ : rename.
Arguments equiv {R _ _} _ _.


Section morphisms.
Context `{IntegralDomain R1} `{DecidablePaths R1}.
Context `{IntegralDomain R2} `{DecidablePaths R2}.
Context `(f : R1 -> R2) `{!SemiRingPreserving f} `{!Injective f}.

Definition lift (x : Frac R1) : Frac R2.
Proof.
apply (frac (f (num x)) (f (den x))).
apply injective_ne_0.
apply (den_ne_0 x).
Defined.

Lemma lift_respects : forall q r, equiv q r -> equiv (lift q) (lift r).
Proof.
unfold equiv;simpl;intros q r E.
rewrite <-2!preserves_mult.
apply ap,E.
Qed.

End morphisms.

End Frac.
Import Frac.

Module FracField.

Section contents.
(* NB: we need a separate IsHSet instance
   so we don't need to depend on everything to define F. *)
Universe UR.
Context `{Funext} `{Univalence} {R:Type@{UR} } `{IsHSet R} `{IntegralDomain R}
  `{DecidablePaths R}.

Local Existing Instance den_ne_0.

(* Add Ring R: (stdlib_ring_theory R). *)

Definition F@{} := quotient equiv.

Global Instance class@{} : Cast (Frac R) F := class_of _.

(* injection from R *)

Global Instance inject@{} : Cast R F := Compose class (Frac_inject _).

Definition path@{} {x y} : equiv x y -> ' x = ' y := related_classes_eq _.

Definition F_rect@{i} (P : F -> Type@{i}) {sP : forall x, IsHSet (P x)}
  (dclass : forall x : Frac R, P (' x))
  (dequiv : forall x y E, (path E) # (dclass x) = (dclass y))
  : forall q, P q
  := quotient_ind equiv P dclass dequiv.

Definition F_compute P {sP} dclass dequiv x
 : @F_rect P sP dclass dequiv (' x) = dclass x := 1.

Definition F_compute_path P {sP} dclass dequiv q r (E : equiv q r)
  : apD (@F_rect P sP dclass dequiv) (path E) = dequiv q r E
  := quotient_ind_compute_path _ _ _ _ _ _ _ _.

Definition F_ind@{i} (P : F -> Type@{i}) {sP : forall x, IsHProp (P x)}
  (dclass : forall x : Frac R, P (' x)) : forall x, P x.
Proof.
apply (@F_rect P (fun _ => trunc_hprop) dclass).
intros;apply path_ishprop.
Qed.

Definition F_ind2@{i j} (P : F -> F -> Type@{i}) {sP : forall x y, IsHProp (P x y)}
  (dclass : forall x y : Frac R, P (' x) (' y)) : forall x y, P x y.
Proof.
apply (@F_ind (fun x => forall y, _)).
- intros;apply Forall.trunc_forall@{UR i j}.
- intros x.
  apply (F_ind _);intros y.
  apply dclass.
Qed.

Definition F_ind3@{i j} (P : F -> F -> F -> Type@{i})
  {sP : forall x y z, IsHProp (P x y z)}
  (dclass : forall x y z : Frac R, P (' x) (' y) (' z))
  : forall x y z, P x y z.
Proof.
apply (@F_ind (fun x => forall y z, _)).
- intros;apply Forall.trunc_forall@{UR j j}.
- intros x.
  apply (F_ind2@{i j} _). auto.
Qed.

Definition F_rec@{i} {T : Type@{i} } {sT : IsHSet T}
  : forall (dclass : Frac R -> T)
  (dequiv : forall x y, equiv x y -> dclass x = dclass y),
  F -> T
  := quotient_rec equiv.

Definition F_rec_compute T sT dclass dequiv x
  : @F_rec T sT dclass dequiv (' x) = dclass x
  := 1.

Definition F_rec2@{i j} {T:Type@{i} } {sT : IsHSet T}
  : forall (dclass : Frac R -> Frac R -> T)
  (dequiv : forall x1 x2, equiv x1 x2 -> forall y1 y2, equiv y1 y2 ->
    dclass x1 y1 = dclass x2 y2),
  F -> F -> T
  := @quotient_rec2@{UR UR j i} _ _ _ _ _ (BuildhSet _).

Definition F_rec2_compute {T sT} dclass dequiv x y
  : @F_rec2 T sT dclass dequiv (' x) (' y) = dclass x y
  := 1.

(* Relations, operations and constants *)

Global Instance F0@{} : Zero F := ('0 : F).
Global Instance F1@{} : One F := ('1 : F).

Global Instance Fplus@{} : Plus F.
Proof.
refine (F_rec2 (fun x y => ' (Frac.pl _ x y)) _).
intros. apply path. apply Frac.pl_respect;trivial.
Defined.

Definition Fplus_compute@{} q r : (' q) + (' r) = ' (Frac.pl _ q r)
  := 1.

Global Instance Fneg@{} : Negate F.
Proof.
refine (F_rec (fun x => ' (Frac.neg _ x)) _).
intros;apply path; eapply Frac.neg_respect;try apply _. trivial.
Defined.

Definition Fneg_compute@{} q : - (' q) = ' (Frac.neg _ q) := 1.

Global Instance Fmult@{} : Mult F.
Proof.
refine (F_rec2 (fun x y => ' (Frac.ml _ x y)) _).
intros. apply path. apply Frac.ml_respect;trivial.
Defined.

Definition Fmult_compute@{} q r : (' q) * (' r) = ' (Frac.ml _ q r)
  := 1.

Instance Fmult_comm@{} : Commutative Fplus.
Proof.
hnf. apply (F_ind2 _).
intros;apply path, Frac.pl_comm.
Qed.

Instance F_ring@{} : Ring F.
Proof.
repeat split;
first [change sg_op with mult; change mon_unit with 1|
       change sg_op with plus; change mon_unit with 0].
- apply _.
- hnf. apply (F_ind3 _).
  intros;apply path. apply Frac.pl_assoc.
- hnf. apply (F_ind _).
  intros;apply path, Frac.pl_0_l.
- hnf. apply (F_ind _).
  intros;apply path, Frac.pl_0_r.
- hnf. apply (F_ind _).
  intros;apply path, Frac.pl_neg_l.
- hnf;intros.
  rewrite (commutativity (f:=plus)).
  revert x;apply (F_ind _).
  intros;apply path, Frac.pl_neg_l.
- apply _.
- apply _.
- hnf; apply (F_ind3 _).
  intros;apply path, Frac.ml_assoc.
- hnf. apply (F_ind _).
  intros;apply path. red;simpl.
  rewrite 2!mult_1_l. reflexivity.
- hnf. apply (F_ind _).
  intros;apply path. red;simpl.
  rewrite 2!mult_1_r. reflexivity.
- hnf; apply (F_ind2 _).
  intros;apply path.
  red;simpl.
  rewrite (mult_comm (num y)), (mult_comm (den y)).
  reflexivity.
- hnf. apply (F_ind3 _).
  intros a b c;apply path.
  red;simpl.
  rewrite <-!(mult_assoc (num a)).
  rewrite <-plus_mult_distr_l.
  rewrite <-(mult_assoc (num a)). apply ap.
  rewrite (mult_comm (den a) (den c)), (mult_comm (den a) (den b)).
  rewrite (mult_assoc (num b)), (mult_assoc (num c)).
  rewrite <-plus_mult_distr_r.
  rewrite <-(mult_assoc _ (den a) (den a * _)).
  apply ap.
  rewrite (mult_comm (den b)), <-mult_assoc. apply ap.
  rewrite (mult_comm (den a)). apply associativity.
Qed.

Global Instance Fdec_rec@{} : DecRecip F.
Proof.
refine (F_rec (fun x => ' (Frac.dec_rec _ x)) _).
intros. apply path. apply Frac.dec_recip_respect;trivial.
Defined.

Lemma classes_eq_related@{} : forall q r, ' q = ' r -> equiv q r.
Proof.
apply classes_eq_related@{UR UR Ularge Ularge Uhuge};apply _.
Qed.

Lemma class_neq@{} : forall q r, ~ equiv q r -> ~ ' q = ' r.
Proof.
intros q r E1 E2;apply E1;apply classes_eq_related, E2.
Qed.

Lemma classes_neq_related@{} : forall q r, ~ ' q = ' r -> ~ equiv q r.
Proof.
intros q r E1 E2;apply E1,path,E2.
Qed.

Lemma dec_recip_0@{} : / 0 = 0.
Proof.
unfold dec_recip. simpl.
unfold Frac.dec_rec;simpl.
destruct (decide_rel paths 0 0) as [_|E].
- reflexivity.
- destruct E;reflexivity.
Qed.

Lemma dec_recip_nonzero_aux@{} : forall q, ~ ' q = 0 -> ~ num q = 0.
Proof.
intros q E;apply classes_neq_related in E.
apply Frac.nonzero_num in E. trivial.
Qed.

Lemma dec_recip_nonzero@{} : forall q (E : ~ ' q = 0),
  / (' q) = ' (frac (den q) (num q) (dec_recip_nonzero_aux q E)).
Proof.
intros. apply path.
red;simpl. unfold Frac.dec_rec.
apply classes_neq_related, Frac.nonzero_num in E.
destruct (decide_rel paths (num q) 0) as [E'|?];[destruct E;apply E'|].
simpl. reflexivity.
Qed.

Global Instance F_field@{} : DecField F.
Proof.
split;try apply _.
- red. apply class_neq.
  unfold equiv;simpl. rewrite 2!mult_1_r. solve_propholds.
- apply dec_recip_0.
- apply (F_ind (fun x => _ -> _)).
  intros x E.
  rewrite (dec_recip_nonzero _ E).
  apply path;red;simpl. rewrite mult_1_r,mult_1_l.
  apply mult_comm.
Qed.

Lemma dec_class@{} : forall q r, Decidable (class q = class r).
Proof.
intros q r.
destruct (dec (equiv q r)) as [E|E].
- left. apply path,E.
- right. intros E'.
  apply E. apply (classes_eq_related _ _ E').
Defined.

Global Instance F_dec@{} : DecidablePaths F.
Proof.
hnf. apply (F_ind2 _).
apply dec_class.
Qed.

Lemma mult_num_den@{} q :
  ' q = (' num q) / ' den q.
Proof.
apply path. red. simpl.
rewrite mult_1_l. unfold Frac.dec_rec.
simpl. destruct (decide_rel paths (den q) 0) as [E|E];simpl.
- destruct (den_ne_0 q E).
- rewrite mult_1_r. reflexivity.
Qed.

Lemma recip_den_num@{} q :
  / ' q = (' den q) / 'num q.
Proof.
apply path;red;simpl.
unfold Frac.dec_rec;simpl.
destruct (decide_rel paths (num q) 0) as [E|E];simpl.
- rewrite (mult_0_r (Azero:=Azero)), 2!mult_0_l. reflexivity.
- rewrite mult_1_l,mult_1_r. reflexivity.
Qed.

(* A final word about inject *)
Global Instance inject_sr_morphism@{} : SemiRingPreserving (cast R F).
Proof.
repeat (split; try apply _).
- intros x y. apply path. change ((x + y) * (1 * 1) = (x * 1 + y * 1) * 1).
  rewrite !mult_1_r. reflexivity.
- intros x y. apply path. change ((x * y) * (1 * 1) = x * y * 1).
  rewrite !mult_1_r. reflexivity.
Qed.

Global Instance inject_injective@{} : Injective (cast R F).
Proof.
repeat (split; try apply _).
intros x y E. apply classes_eq_related in E.
red in E. simpl in E. rewrite 2!mult_1_r in E;trivial.
Qed.

End contents.

Arguments F R {_ _ _}.

Module Lift.

Section morphisms.
Universe UR1 UR2.
Context `{Funext} `{Univalence}.
Context {R1:Type@{UR1} } `{IntegralDomain R1} `{DecidablePaths R1}.
Context {R2:Type@{UR2} } `{IntegralDomain R2} `{DecidablePaths R2}.
Context `(f : R1 -> R2) `{!SemiRingPreserving f} `{!Injective f}.

Definition lift@{} : F R1 -> F R2.
Proof.
apply (F_rec (fun x => class (Frac.lift f x))).
intros;apply path,Frac.lift_respects;trivial.
Defined.

Global Instance lift_sr_morphism@{i} : SemiRingPreserving lift.
Proof.
(* This takes a few seconds. *)
split;split;red.
- apply (F_ind2@{UR1 UR2 i} _).
  intros;simpl.
  apply @path. (* very slow or doesn't terminate without the @ but fast with it *)
  red;simpl.
  repeat (rewrite <-(preserves_mult (f:=f)) || rewrite <-(preserves_plus (f:=f))).
  reflexivity.
- simpl. apply path.
  red;simpl. rewrite (preserves_0 (f:=f)). rewrite 2!mult_0_l. reflexivity.
- apply (F_ind2@{UR1 UR2 i} _).
  intros;simpl. apply @path.
  red;simpl.
  rewrite <-!(preserves_mult (f:=f)). reflexivity.
- simpl. apply path.
  red;simpl. apply commutativity.
Qed.

Global Instance lift_injective@{i} : Injective lift.
Proof.
red.
apply (F_ind2@{UR1 i i} (fun _ _ => _ -> _)).
intros x y E.
simpl in E.
apply classes_eq_related in E. red in E;simpl in E.
apply path. red.
apply (injective f). rewrite 2!(preserves_mult (f:=f)).
apply E.
Qed.
End morphisms.

End Lift.

End FracField.
