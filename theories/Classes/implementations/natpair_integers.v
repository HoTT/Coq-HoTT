Require Import HoTT.HIT.quotient
  HoTT.Basics.PathGroupoids
  HoTT.Types.Universe
  HoTT.Basics.Trunc
  HoTT.Basics.Decidable
  HoTT.Types.Prod
  HoTT.Types.Arrow
  HoTT.Types.Sum
  HoTT.TruncType.
Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.interfaces.naturals
  HoTT.Classes.interfaces.integers
  HoTT.Classes.theory.rings
  HoTT.Classes.orders.rings
  HoTT.Classes.tactics.ring_tac
  HoTT.Classes.interfaces.naturals
  HoTT.Classes.theory.naturals.

Local Set Universe Minimization ToSet.

Module NatPair.

Module PairT.

Record T (N : Type) := C { pos : N ; neg : N }.
Arguments C {N} _ _.
Arguments pos {N} _.
Arguments neg {N} _.

Section contents.
Universe UN UNalt.
Context (N : Type@{UN}) `{Naturals@{UN UN UN UN UN UN UN UNalt} N}.

Global Instance T_set : IsHSet (T N).
Proof.
assert (E : sigT (fun _ : N => N) <~> (T N)).
- issig.
- apply (trunc_equiv' _ E).
Qed.

Global Instance inject : Cast N (T N) := fun x => C x 0.

Definition equiv := fun x y => pos x + neg y = pos y + neg x.

Global Instance equiv_is_equiv_rel@{} : EquivRel equiv.
Proof.
split.
- hnf. reflexivity.
- hnf. unfold equiv.
  intros ??;apply symmetry.
- hnf. unfold equiv.
  intros a b c E1 E2.
  apply (left_cancellation (+) (neg b)).
  rewrite (plus_assoc (neg b) (pos a)).
  rewrite (plus_comm (neg b) (pos a)), E1.
  rewrite (plus_comm (pos b)). rewrite <-plus_assoc.
  rewrite E2. rewrite (plus_comm (pos c) (neg b)).
  rewrite plus_assoc. rewrite (plus_comm (neg a)).
  rewrite <-plus_assoc. rewrite (plus_comm (neg a)).
  reflexivity.
Qed.

Instance pl : Plus (T N) := fun x y => C (pos x + pos y) (neg x + neg y).

Instance ml : Mult (T N) := fun x y =>
  C (pos x * pos y + neg x * neg y) (pos x * neg y + neg x * pos y).

Instance opp : Negate (T N) := fun x => C (neg x) (pos x).

Instance SR0 : Zero (T N) := C 0 0.

Instance SR1 : One (T N) := C 1 0.

Lemma pl_respects : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  equiv (q1 + r1) (q2 + r2).
Proof.
unfold equiv;simpl.
intros q1 q2 Eq r1 r2 Er.
rewrite (plus_assoc _ (neg q2)).
rewrite <-(plus_assoc (pos q1)).
rewrite (plus_comm (pos r1)).
rewrite (plus_assoc (pos q1)). rewrite Eq.
rewrite <-(plus_assoc _ (pos r1)). rewrite Er.
rewrite plus_assoc. rewrite <-(plus_assoc (pos q2)).
rewrite (plus_comm (neg q1)). rewrite !plus_assoc.
reflexivity.
Qed.

Lemma ml_respects : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  equiv (q1 * r1) (q2 * r2).
Proof.
intros q1 q2 Eq r1 r2 Er. transitivity (q1 * r2);unfold equiv in *;simpl.
- transitivity (pos q1 * (pos r1 + neg r2) + neg q1 * (neg r1 + pos r2)).
  + rewrite 2!plus_mult_distr_l.
    rewrite <-2!plus_assoc.
    apply ap.
    rewrite 2!plus_assoc. rewrite (plus_comm (neg q1 * neg r1)).
    reflexivity.
  + rewrite Er. rewrite plus_mult_distr_l.
    rewrite (plus_comm (neg r1)).
    rewrite <-Er. rewrite plus_mult_distr_l.
    rewrite <-2!plus_assoc. apply ap.
    rewrite (plus_comm (neg q1 * pos r1)).
    rewrite 2!plus_assoc.
    rewrite (plus_comm (pos q1 * neg r1)). reflexivity.
- transitivity ((pos q1 + neg q2) * pos r2 + (neg q1 + pos q2) * neg r2).
  + rewrite 2!plus_mult_distr_r.
    rewrite <-2!plus_assoc;apply ap.
    rewrite (plus_comm (pos q2 * neg r2)).
    rewrite 2!plus_assoc. rewrite (plus_comm (neg q1 * neg r2)).
    reflexivity.
  + rewrite Eq,plus_mult_distr_r.
    rewrite (plus_comm (neg q1)),<-Eq,plus_mult_distr_r.
    rewrite <-2!plus_assoc. apply ap.
    rewrite plus_assoc,(plus_comm (neg q1 * pos r2)).
    apply plus_comm.
Qed.

Lemma opp_respects : forall q1 q2, equiv q1 q2 -> equiv (opp q1) (opp q2).
Proof.
unfold equiv;simpl.
intros q1 q2 E.
rewrite !(plus_comm (neg _)). symmetry. apply E.
Qed.

Definition Tle : Le (T N)
  := fun a b => pos a + neg b <= pos b + neg a.
Definition Tlt : Lt (T N)
  := fun a b => pos a + neg b < pos b + neg a.
Definition Tapart : Apart (T N)
  := fun a b => apart (pos a + neg b) (pos b + neg a).

Global Instance Tle_hprop@{}
  : is_mere_relation (T N) Tle.
Proof.
intros;unfold Tle.
apply full_pseudo_srorder_le_hprop.
Qed.

Global Instance Tlt_hprop@{}
  : is_mere_relation (T N) Tlt.
Proof.
intros;unfold Tlt;apply _.
Qed.

Local Existing Instance pseudo_order_apart.
Global Instance Tapart_hprop@{} : is_mere_relation (T N) Tapart.
Proof.
intros;unfold Tapart;apply _.
Qed.

Lemma le_respects_aux@{} : forall q1 q2, equiv q1 q2 ->
  forall r1 r2, equiv r1 r2 ->
  Tle q1 r1 -> Tle q2 r2.
Proof.
unfold equiv,Tle;intros [pa na] [pb nb] Eq [pc nc] [pd nd] Er E;simpl in *.
apply (order_reflecting (+ (pc + na))).
assert (Erw : pb + nd + (pc + na)
  = (pb + na) + (pc + nd)) by ring_with_nat.
rewrite Erw,<-Eq,Er;clear Erw.
assert (Erw : pa + nb + (pd + nc) = pd + nb + (pa + nc)) by ring_with_nat.
rewrite Erw.
apply (order_preserving _), E.
Qed.

Lemma le_respects@{} : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  Tle q1 r1 <~> Tle q2 r2.
Proof.
intros. apply equiv_iff_hprop_uncurried.
split;apply le_respects_aux;
trivial;apply symmetry;trivial.
Qed.

Lemma lt_respects_aux@{} : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  Tlt q1 r1 -> Tlt q2 r2.
Proof.
unfold equiv,Tlt;intros [pa na] [pb nb] Eq [pc nc] [pd nd] Er E;simpl in *.
apply (strictly_order_reflecting (+ (pc + na))).
assert (Erw : pb + nd + (pc + na)
  = (pb + na) + (pc + nd)) by ring_with_nat.
rewrite Erw,<-Eq,Er;clear Erw.
assert (Erw : pa + nb + (pd + nc) = pd + nb + (pa + nc)) by ring_with_nat.
rewrite Erw.
apply (strictly_order_preserving _), E.
Qed.

Lemma lt_respects@{} : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  Tlt q1 r1 <~> Tlt q2 r2.
Proof.
intros. apply equiv_iff_hprop_uncurried.
split;apply lt_respects_aux;
trivial;apply symmetry;trivial.
Qed.

Lemma apart_cotrans@{} : CoTransitive Tapart.
Proof.
hnf.
unfold Tapart. intros q1 q2 Eq r.
apply (strong_left_cancellation (+) (neg r)) in Eq.
apply (merely_destruct (cotransitive Eq (pos r + neg q1 + neg q2)));
intros [E|E];apply tr.
- left. apply (strong_extensionality (+ (neg q2))).
  assert (Hrw : pos q1 + neg r + neg q2
    = neg r + (pos q1 + neg q2)) by ring_with_nat.
  rewrite Hrw;clear Hrw.
  trivial.
- right. apply (strong_extensionality (+ (neg q1))).
  assert (Hrw : pos r + neg q2 + neg q1 = pos r + neg q1 + neg q2)
  by ring_with_nat.
  rewrite Hrw;clear Hrw.
  assert (Hrw : pos q2 + neg r + neg q1 = neg r + (pos q2 + neg q1))
  by ring_with_nat.
  rewrite Hrw;clear Hrw.
  trivial.
Qed.
Existing Instance apart_cotrans.

Instance : Symmetric Tapart.
Proof.
hnf.
unfold Tapart.
intros ??;apply symmetry.
Qed.

Lemma apart_respects_aux@{}
  : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  Tapart q1 r1 -> Tapart q2 r2.
Proof.
assert (forall q1 q2, equiv q1 q2 -> forall r, Tapart q1 r -> Tapart q2 r)
  as E.
- intros q1 q2 Eq r Er.
  unfold Tapart,equiv in *.
  apply (strong_extensionality (+ (neg q1))).
  assert (Hrw : pos q2 + neg r + neg q1 = (pos q2 + neg q1) + neg r)
  by ring_with_nat.
  rewrite Hrw;clear Hrw.
  rewrite <-Eq.
  assert (Hrw : pos q1 + neg q2 + neg r = neg q2 + (pos q1 + neg r))
  by ring_with_nat.
  rewrite Hrw;clear Hrw.
  assert (Hrw : pos r + neg q2 + neg q1 = neg q2 + (pos r + neg q1))
  by ring_with_nat;rewrite Hrw;clear Hrw.
  apply (strong_left_cancellation _ _),Er.
- intros ?? Eq ?? Er E'.
  apply E with q1;trivial.
  apply symmetry;apply E with r1;apply symmetry;trivial.
  apply symmetry;trivial.
Qed.

Lemma apart_respects : forall q1 q2, equiv q1 q2 -> forall r1 r2, equiv r1 r2 ->
  Tapart q1 r1 <~> Tapart q2 r2.
Proof.
intros ?? Eq ?? Er.
apply equiv_iff_hprop_uncurried.
split;apply apart_respects_aux;
trivial;apply symmetry;trivial.
Qed.

Section to_ring.
Context {B : Type@{UNalt} } `{Ring@{UNalt} B}.

Definition to_ring@{} : T N -> B.
Proof.
intros p.
exact (naturals_to_semiring N B (pos p) - naturals_to_semiring N B (neg p)).
Defined.

Lemma to_ring_respects@{} : forall a b, equiv a b ->
  to_ring a = to_ring b.
Proof.
unfold equiv;intros [pa na] [pb nb] E.
unfold to_ring;simpl in *.
apply (left_cancellation (+)
  (naturals_to_semiring N B na + naturals_to_semiring N B nb)).
path_via (naturals_to_semiring N B pa + naturals_to_semiring N B nb + 0);
[rewrite <-(plus_negate_r (naturals_to_semiring N B na));ring_with_nat
|rewrite plus_0_r].
path_via (naturals_to_semiring N B pb + naturals_to_semiring N B na + 0);
[rewrite plus_0_r|
rewrite <-(plus_negate_r (naturals_to_semiring N B nb));ring_with_nat].
rewrite <-2!preserves_plus. apply ap,E.
Qed.

End to_ring.

End contents.

Arguments equiv {_ _} _ _.
Arguments Tle {_ _ _} _ _.
Arguments Tlt {_ _ _} _ _.
Arguments Tapart {_ _ _} _ _.
Arguments to_ring N {_} B {_ _ _ _ _ _} / _.

End PairT.

Section contents.
Universe UN UNalt.
Context `{Funext} `{Univalence} (N : Type@{UN})
  `{Naturals@{UN UN UN UN UN UN UN UNalt} N}.

(* Add Ring SR : (rings.stdlib_semiring_theory SR). *)
Instance N_fullpartial : FullPartialOrder Ale Alt
  := fullpseudo_fullpartial@{UN UN UN UN UN UN UN Ularge}.

Definition Z@{} : Type@{UN} := @quotient _ PairT.equiv@{UN UNalt} _.

Global Instance Z_of_pair : Cast (PairT.T N) Z := class_of _.

Global Instance Z_of_N : Cast N Z := Compose Z_of_pair (PairT.inject@{UN UNalt} _).

Definition Z_path {x y} : PairT.equiv x y -> Z_of_pair x = Z_of_pair y
  := related_classes_eq _.

Definition related_path {x y} : Z_of_pair x = Z_of_pair y -> PairT.equiv x y
  := classes_eq_related@{UN UN Ularge Ularge Uhuge} _ _ _.

Definition Z_rect@{i} (P : Z -> Type@{i}) {sP : forall x, IsHSet (P x)}
  (dclass : forall x : PairT.T N, P (' x))
  (dequiv : forall x y E, (Z_path E) # (dclass x) = (dclass y))
  : forall q, P q
  := quotient_ind PairT.equiv P dclass dequiv.

Definition Z_compute P {sP} dclass dequiv x
 : @Z_rect P sP dclass dequiv (Z_of_pair x) = dclass x := 1.

Definition Z_compute_path P {sP} dclass dequiv q r (E : PairT.equiv q r)
  : apD (@Z_rect P sP dclass dequiv) (Z_path E) = dequiv q r E
  := quotient_ind_compute_path _ _ _ _ _ _ _ _.

Definition Z_ind@{i} (P : Z -> Type@{i}) {sP : forall x : Z, IsHProp (P x)}
  (dclass : forall x : PairT.T N, P (cast (PairT.T N) Z x)) : forall x : Z, P x.
Proof.
apply (Z_rect@{i} P dclass).
intros;apply path_ishprop@{i}.
Defined.

Definition Z_ind2 (P : Z -> Z -> Type) {sP : forall x y, IsHProp (P x y)}
  (dclass : forall x y : PairT.T N, P (' x) (' y)) : forall x y, P x y.
Proof.
apply (Z_ind (fun x => forall y, _));intros x.
apply (Z_ind _);intros y.
apply dclass.
Defined.

Definition Z_ind3@{i j} (P : Z -> Z -> Z -> Type@{i})
  {sP : forall x y z : Z, IsHProp (P x y z)}
  (dclass : forall x y z : PairT.T N, P (' x) (' y) (' z))
  : forall x y z : Z, P x y z.
Proof.
apply (@Z_ind (fun x => forall y z, _));intros x.
2:apply (Z_ind2@{i j} _);auto.
apply (@Forall.trunc_forall@{UN j j} _).
intros. apply Forall.trunc_forall@{UN i j}.
Defined.

Definition Z_rec@{i} {T : Type@{i} } {sT : IsHSet T}
  : forall (dclass : PairT.T N -> T)
  (dequiv : forall x y, PairT.equiv x y -> dclass x = dclass y),
  Z -> T
  := quotient_rec _.

Definition Z_rec_compute T sT dclass dequiv x
  : @Z_rec T sT dclass dequiv (' x) = dclass x
  := 1.

Definition Z_rec2@{i j} {T:Type@{i} } {sT : IsHSet T}
  : forall (dclass : PairT.T N -> PairT.T N -> T)
  (dequiv : forall x1 x2, PairT.equiv x1 x2 -> forall y1 y2, PairT.equiv y1 y2 ->
    dclass x1 y1 = dclass x2 y2),
  Z -> Z -> T
  := @quotient_rec2@{UN UN j i} _ _ _ _ _ (BuildhSet _).

Definition Z_rec2_compute {T sT} dclass dequiv x y
  : @Z_rec2 T sT dclass dequiv (' x) (' y) = dclass x y
  := 1.

Lemma dec_Z_of_pair `{DecidablePaths N} : forall q r : PairT.T N,
  Decidable (' q = ' r).
Proof.
intros q r.
destruct (dec (PairT.equiv q r)) as [E|E].
- left. apply Z_path,E.
- right. intros E'.
  apply E. apply (related_path E').
Defined.

Global Instance R_dec `{DecidablePaths N}
  : DecidablePaths Z.
Proof.
hnf. apply (Z_ind2 _).
apply dec_Z_of_pair.
Defined.

(* Relations, operations and constants *)

Global Instance Z0 : Zero Z := ' 0.
Global Instance Z1 : One Z := ' 1.

Global Instance Z_plus@{} : Plus Z.
Proof.
refine (Z_rec2 (fun x y => ' (PairT.pl@{UN UNalt} _ x y)) _).
intros;apply Z_path;eapply PairT.pl_respects;trivial.
Defined.

Definition Z_plus_compute q r : (' q) + (' r) = ' (PairT.pl _ q r)
  := 1.

Global Instance Z_mult@{} : Mult Z.
Proof.
refine (Z_rec2 (fun x y => ' (PairT.ml@{UN UNalt} _ x y)) _).
intros;apply Z_path;eapply PairT.ml_respects;trivial.
Defined.

Definition Z_mult_compute q r : (' q) * (' r) = ' (PairT.ml _ q r)
  := 1.

Global Instance Z_negate@{} : Negate Z.
Proof.
red. apply (Z_rec (fun x => ' (PairT.opp@{UN UNalt} _ x))).
intros;apply Z_path;eapply PairT.opp_respects;trivial.
Defined.

Definition Z_negate_compute q : - (' q) = ' (PairT.opp _ q)
  := 1.

Lemma Z_ring@{} : Ring Z.
Proof.
repeat split;try apply _;
first [change sg_op with mult; change mon_unit with 1|
       change sg_op with plus; change mon_unit with 0];hnf.
- apply (Z_ind3 _).
  intros a b c;apply Z_path;red;simpl.
  rewrite !plus_assoc. reflexivity.
- apply (Z_ind _).
  intros a;apply Z_path;red;simpl.
  rewrite !plus_0_l. reflexivity.
- apply (Z_ind _).
  intros a;apply Z_path;red;simpl.
  rewrite !plus_0_r. reflexivity.
- apply (Z_ind _).
  intros a;apply Z_path;red;simpl.
  rewrite plus_0_l,plus_0_r. apply plus_comm.
- apply (Z_ind _).
  intros a;apply Z_path;red;simpl.
  rewrite plus_0_l,plus_0_r. apply plus_comm.
- apply (Z_ind2 _).
  intros a b;apply Z_path;red;simpl.
  apply ap2;apply plus_comm.
- apply (Z_ind3 _).
  intros [pa na] [pb nb] [pc nc];apply Z_path;red;simpl.
  ring_with_nat.
- apply (Z_ind _).
  intros;apply Z_path;red;simpl.
  ring_with_nat.
- apply (Z_ind _).
  intros;apply Z_path;red;simpl.
  ring_with_nat.
- apply (Z_ind2 _).
  intros;apply Z_path;red;simpl.
  ring_with_nat.
- apply (Z_ind3 _).
  intros [pa na] [pb nb] [pc nc];apply Z_path;red;simpl.
  ring_with_nat.
Qed.

(* A final word about inject *)
Lemma Z_of_N_morphism@{} : SemiRingPreserving (cast N Z).
Proof.
repeat (constructor; try apply _).
- intros x y.
  apply Z_path. red. simpl. ring_with_nat.
- intros x y. apply Z_path. red;simpl.
  ring_with_nat.
Qed.
Global Existing Instance Z_of_N_morphism.

Global Instance Z_of_N_injective@{} : Injective (cast N Z).
Proof.
intros x y E. apply related_path in E.
red in E. simpl in E. rewrite 2!plus_0_r in E. trivial.
Qed.

Lemma Npair_splits@{} : forall n m : N, ' (PairT.C n m) = ' n + - ' m.
Proof.
intros.
apply Z_path;red;simpl.
ring_with_nat.
Qed.

Definition Zle_hProp@{} : Z -> Z -> TruncType@{UN} -1.
Proof.
apply (@Z_rec2@{Ularge Ularge} _ (@istrunc_trunctype@{UN Ularge Uhuge} _ _)
  (fun q r => BuildhProp (PairT.Tle q r))).
intros. apply path_hprop@{UN Ularge Uhuge}. simpl.
apply (PairT.le_respects _);trivial.
Defined.

Global Instance Zle@{} : Le Z := fun x y => Zle_hProp x y.

Global Instance ishprop_Zle : is_mere_relation _ Zle.
Proof. unfold Zle;exact _. Qed.

Lemma Zle_def@{} : forall a b : PairT.T N,
  @paths@{Uhuge} Type@{UN} (' a <= ' b) (PairT.Tle@{UN UNalt} a b).
Proof. intros; exact idpath. Qed.

Lemma Z_partial_order' : PartialOrder Zle.
Proof.
split;[apply _|apply _|split|].
- hnf. apply (Z_ind _).
  intros. change (PairT.Tle x x). red. reflexivity.
- hnf. apply (Z_ind3 (fun _ _ _ => _ -> _ -> _)).
  intros [pa na] [pb nb] [pc nc]. rewrite !Zle_def;unfold PairT.Tle;simpl.
  intros E1 E2.
  apply (order_reflecting (+ (nb + pb))).
  assert (Hrw : pa + nc + (nb + pb) = (pa + nb) + (pb + nc))
    by abstract ring_with_nat.
  rewrite Hrw;clear Hrw.
  assert (Hrw : pc + na + (nb + pb) = (pb + na) + (pc + nb))
    by abstract ring_with_nat.
  rewrite Hrw;clear Hrw.
  apply plus_le_compat;trivial.
- hnf. apply (Z_ind2 (fun _ _ => _ -> _ -> _)).
  intros [pa na] [pb nb];rewrite !Zle_def;unfold PairT.Tle;simpl.
  intros E1 E2;apply Z_path;red;simpl.
  apply (antisymmetry le);trivial.
Qed.

(* Coq pre 8.8 produces phantom universes, see GitHub Coq/Coq#1033. *)
Instance Z_partial_order@{} : PartialOrder Zle
  := ltac:(first [exact Z_partial_order'@{Ularge Ularge Ularge Ularge Ularge}|
                  exact Z_partial_order']).

Lemma Zle_cast_embedding' : OrderEmbedding (cast N Z).
Proof.
split;red.
- intros. rewrite Zle_def. unfold PairT.Tle. simpl.
  rewrite 2!plus_0_r;trivial.
- intros ??. rewrite Zle_def. unfold PairT.Tle. simpl.
  rewrite 2!plus_0_r;trivial.
Qed.

(* Coq pre 8.8 produces phantom universes, see GitHub Coq/Coq#1033. *)
Global Instance Zle_cast_embedding@{} : OrderEmbedding (cast N Z)
  := ltac:(first [exact Zle_cast_embedding'@{Ularge Ularge}|
                  exact Zle_cast_embedding']).

Lemma Zle_plus_preserving_l' : forall z : Z, OrderPreserving ((+) z).
Proof.
red.
apply (Z_ind3 (fun _ _ _ => _ -> _)).
intros [pc nc] [pa na] [pb nb]. rewrite !Zle_def;unfold PairT.Tle;simpl.
intros E.
assert (Hrw : pc + pa + (nc + nb) = (pc + nc) + (pa + nb)) by ring_with_nat.
rewrite Hrw;clear Hrw.
assert (Hrw : pc + pb + (nc + na) = (pc + nc) + (pb + na)) by ring_with_nat.
rewrite Hrw;clear Hrw.
apply (order_preserving _),E.
Qed.

(* Coq pre 8.8 produces phantom universes, see GitHub Coq/Coq#1033. *)
Instance Zle_plus_preserving_l@{} : forall z : Z, OrderPreserving ((+) z)
  := ltac:(first [exact Zle_plus_preserving_l'@{Ularge Ularge}|
                  exact Zle_plus_preserving_l']).

Lemma Zmult_nonneg' : forall x y : Z, PropHolds (0 ≤ x) -> PropHolds (0 ≤ y) ->
  PropHolds (0 ≤ x * y).
Proof.
unfold PropHolds.
apply (Z_ind2 (fun _ _ => _ -> _ -> _)).
intros [pa na] [pb nb]. rewrite !Zle_def;unfold PairT.Tle;simpl.
rewrite !plus_0_l,!plus_0_r.
intros E1 E2.
destruct (decompose_le E1) as [a [Ea1 Ea2]], (decompose_le E2) as [b [Eb1 Eb2]].
rewrite Ea2, Eb2.
apply compose_le with (a * b).
- apply nonneg_mult_compat;trivial.
- ring_with_nat.
Qed.

(* Coq pre 8.8 produces phantom universes, see GitHub Coq/Coq#1033. *)
Instance Zmult_nonneg@{} : forall x y : Z, PropHolds (0 ≤ x) -> PropHolds (0 ≤ y) ->
  PropHolds (0 ≤ x * y)
  := ltac:(first [exact Zmult_nonneg'@{Ularge Ularge Ularge}|
                  exact Zmult_nonneg']).

Global Instance Z_order@{} : SemiRingOrder Zle.
Proof. pose proof Z_ring; apply rings.from_ring_order; apply _. Qed.

(* Make this computable? Would need to compute through Z_ind2. *)
Global Instance Zle_dec `{forall x y : N, Decidable (x <= y)}
  : forall x y : Z, Decidable (x <= y).
Proof.
apply (Z_ind2 _).
intros a b. change (Decidable (PairT.Tle a b)).
unfold PairT.Tle. apply _.
Qed.

Definition Zlt_hProp@{} : Z -> Z -> TruncType@{UN} -1.
Proof.
apply (@Z_rec2@{Ularge Ularge} _ (@istrunc_trunctype@{UN Ularge Uhuge} _ _)
  (fun q r => BuildhProp (PairT.Tlt q r))).
intros. apply path_hprop@{UN Ularge Uhuge}. simpl.
apply (PairT.lt_respects _);trivial.
Defined.

Global Instance Zlt@{} : Lt Z := fun x y => Zlt_hProp x y.

Global Instance ishprop_Zlt : is_mere_relation _ Zlt.
Proof. unfold Zlt;exact _. Qed.

Lemma Zlt_def' : forall a b, ' a < ' b = PairT.Tlt a b.
Proof. reflexivity. Qed.

(* Coq pre 8.8 produces phantom universes, see GitHub Coq/Coq#1033. *)
Definition Zlt_def@{i} := ltac:(first [exact Zlt_def'@{Uhuge i}|exact Zlt_def'@{i}]).

Lemma Zlt_strict' : StrictOrder Zlt.
Proof.
split.
- apply _.
- (* we need to change so that it sees Empty,
     needed to figure out IsHProp (using Funext) *)
  change (forall x, x < x -> Empty). apply (Z_ind (fun _ => _ -> _)).
  intros [pa na];rewrite Zlt_def;unfold PairT.Tlt;simpl.
  apply irreflexivity,_.
- hnf. apply (Z_ind3 (fun _ _ _ => _ -> _ -> _)).
  intros [pa na] [pb nb] [pc nc];rewrite !Zlt_def;unfold PairT.Tlt;simpl.
  intros E1 E2.
  apply (strictly_order_reflecting (+ (nb + pb))).
  assert (Hrw : pa + nc + (nb + pb) = (pa + nb) + (pb + nc)) by ring_with_nat.
  rewrite Hrw;clear Hrw.
  assert (Hrw : pc + na + (nb + pb) = (pb + na) + (pc + nb)) by ring_with_nat.
  rewrite Hrw;clear Hrw.
  apply plus_lt_compat;trivial.
Qed.

Instance Zlt_strict@{} : StrictOrder Zlt
  := ltac:(first [exact Zlt_strict'@{Ularge Ularge Ularge Ularge Ularge}|
                  exact Zlt_strict'@{}]).

Lemma plus_strict_order_preserving_l'
  : forall z : Z, StrictlyOrderPreserving ((+) z).
Proof.
red; apply (Z_ind3 (fun _ _ _ => _ -> _)).
intros [pa na] [pb nb] [pc nc].
rewrite !Zlt_def;unfold PairT.Tlt;simpl.
intros E.
assert (Hrw : pa + pb + (na + nc) = (pa + na) + (pb + nc)) by ring_with_nat.
rewrite Hrw;clear Hrw.
assert (Hrw : pa + pc + (na + nb) = (pa + na) + (pc + nb)) by ring_with_nat.
rewrite Hrw;clear Hrw.
apply (strictly_order_preserving _),E.
Qed.

Instance Zplus_strict_order_preserving_l@{}
  : forall z : Z, StrictlyOrderPreserving ((+) z)
  := ltac:(first [exact plus_strict_order_preserving_l'@{Ularge Ularge}|
                  exact plus_strict_order_preserving_l'@{}]).

Lemma Zmult_pos' : forall x y : Z, PropHolds (0 < x) -> PropHolds (0 < y) ->
  PropHolds (0 < x * y).
Proof.
unfold PropHolds.
apply (Z_ind2 (fun _ _ => _ -> _ -> _)).
intros [pa na] [pb nb]. rewrite !Zlt_def;unfold PairT.Tlt;simpl.
rewrite !plus_0_l,!plus_0_r.
intros E1 E2.
destruct (decompose_lt E1) as [a [Ea1 Ea2]], (decompose_lt E2) as [b [Eb1 Eb2]].
rewrite Ea2, Eb2.
apply compose_lt with (a * b).
- apply pos_mult_compat;trivial.
- ring_with_nat.
Qed.

Instance Zmult_pos@{} : forall x y : Z, PropHolds (0 < x) -> PropHolds (0 < y) ->
  PropHolds (0 < x * y)
  := ltac:(first [exact Zmult_pos'@{Ularge Ularge Ularge}|
                  exact Zmult_pos'@{}]).

Global Instance Z_strict_srorder : StrictSemiRingOrder Zlt.
Proof. pose proof Z_ring; apply from_strict_ring_order; apply _. Qed.

Global Instance Zlt_dec `{forall x y : N, Decidable (x < y)}
  : forall x y : Z, Decidable (x < y).
Proof.
apply (Z_ind2 _).
intros a b. change (Decidable (PairT.Tlt a b)).
unfold PairT.Tlt.
apply _.
Qed.

Local Existing Instance pseudo_order_apart.

Definition Zapart_hProp@{} : Z -> Z -> TruncType@{UN} -1.
Proof.
apply (@Z_rec2@{Ularge Ularge} _ (@istrunc_trunctype@{UN Ularge Uhuge} _ _)
  (fun q r => BuildhProp (PairT.Tapart q r))).
intros. apply path_hprop@{UN Ularge Uhuge}. simpl.
apply (PairT.apart_respects _);trivial.
Defined.

Global Instance Zapart@{} : Apart Z := fun x y => Zapart_hProp x y.

Lemma Zapart_def' : forall a b, apart (' a) (' b) = PairT.Tapart a b.
Proof. reflexivity. Qed.

(* Coq pre 8.8 produces phantom universes, see GitHub Coq/Coq#1033. *)
Definition Zapart_def@{i} := ltac:(first [exact Zapart_def'@{Uhuge i}|
                                          exact Zapart_def'@{i}]).

Global Instance ishprop_Zapart : is_mere_relation _ Zapart.
Proof. unfold Zapart;exact _. Qed.

Lemma Z_trivial_apart' `{!TrivialApart N}
  : TrivialApart Z.
Proof.
split;[exact _|idtac].
apply (Z_ind2 _).
intros [pa na] [pb nb];rewrite Zapart_def;unfold PairT.Tapart;simpl.
split;intros E1.
- intros E2. apply related_path in E2.
  red in E2;simpl in E2.
  apply trivial_apart in E1. auto.
- apply trivial_apart. intros E2.
  apply E1,Z_path. red;simpl. trivial.
Qed.

Global Instance Z_trivial_apart@{} `{!TrivialApart N}
  : TrivialApart Z
  := ltac:(first [exact Z_trivial_apart'@{Ularge}|
                  exact Z_trivial_apart'@{}]).

Lemma Z_is_apart' : IsApart Z.
Proof.
split.
- apply _.
- apply _.
- hnf. apply (Z_ind2 (fun _ _ => _ -> _)).
  intros [pa na] [pb nb];rewrite !Zapart_def;unfold PairT.Tapart;simpl.
  apply symmetry.
- hnf. intros x y E z;revert x y z E.
  apply (Z_ind3 (fun _ _ _ => _ -> _)).
  intros a b c;rewrite !Zapart_def;unfold PairT.Tapart;simpl.
  intros E1.
  apply (strong_left_cancellation (+) (PairT.neg c)) in E1.
  eapply (merely_destruct (cotransitive E1 _));intros [E2|E2];apply tr.
  + left. apply (strong_extensionality (+ (PairT.neg b))).
    assert (Hrw : PairT.pos a + PairT.neg c + PairT.neg b =
      PairT.neg c + (PairT.pos a + PairT.neg b))
    by ring_with_nat;rewrite Hrw;exact E2.
  + right. apply (strong_extensionality (+ (PairT.neg a))).
    assert (Hrw : PairT.pos c + PairT.neg b + PairT.neg a =
      PairT.pos c + PairT.neg a + PairT.neg b)
    by ring_with_nat;rewrite Hrw;clear Hrw.
    assert (Hrw : PairT.pos b + PairT.neg c + PairT.neg a =
      PairT.neg c + (PairT.pos b + PairT.neg a))
    by ring_with_nat;rewrite Hrw;clear Hrw.
    trivial.
- apply (Z_ind2 _).
  intros a b;rewrite Zapart_def;unfold PairT.Tapart.
  split;intros E.
  + apply Z_path;red.
    apply tight_apart,E.
  + apply related_path in E. apply tight_apart,E.
Qed.

Instance Z_is_apart@{} : IsApart Z
  := ltac:(first [exact Z_is_apart'@{Ularge Ularge Ularge Ularge Ularge
                                     Ularge}|
                  exact Z_is_apart'@{}]).

Lemma Z_full_psorder' : FullPseudoOrder Zle Zlt.
Proof.
split;[apply _|split;try apply _|].
- apply (Z_ind2 _).
  intros a b;rewrite !Zlt_def;unfold PairT.Tlt.
  apply pseudo_order_antisym.
- hnf. intros a b E c;revert a b c E.
  apply (Z_ind3 (fun _ _ _ => _ -> _)).
  intros [pa na] [pb nb] [pc nc];rewrite !Zlt_def;unfold PairT.Tlt.
  intros E1.
  apply (strictly_order_preserving (+ nc)) in E1.
  eapply (merely_destruct (cotransitive E1 _));intros [E2|E2];apply tr.
  + left. apply (strictly_order_reflecting ((nb) +)).
    assert (Hrw : nb + (pa + nc) = pa + nb + nc)
    by ring_with_nat;rewrite Hrw;exact E2.
  + right. apply (strictly_order_reflecting ((na) +)).
    assert (Hrw : na + (pc + nb) = nb + (pc + na))
    by ring_with_nat;rewrite Hrw;clear Hrw.
    assert (Hrw : na + (pb + nc) = pb + na + nc)
    by ring_with_nat;rewrite Hrw;clear Hrw.
    trivial.
- apply @Z_ind2.
  + intros a b.
    apply @trunc_prod;[|apply _].
    apply (@trunc_arrow _).
    apply ishprop_sum;try apply _.
    intros E1 E2;apply (irreflexivity lt a).
    transitivity b;trivial.
  + intros a b;rewrite Zapart_def,!Zlt_def;unfold PairT.Tapart,PairT.Tlt.
    apply apart_iff_total_lt.
- apply (Z_ind2 _).
  intros a b;rewrite Zle_def,Zlt_def;unfold PairT.Tlt,PairT.Tle.
  apply le_iff_not_lt_flip.
Qed.

(* Coq pre 8.8 produces phantom universes, see GitHub Coq/Coq#1033. *)
Instance Z_full_psorder@{} : FullPseudoOrder Zle Zlt
  := ltac:(first [exact Z_full_psorder'@{Ularge Ularge Ularge Ularge Ularge
                                                Ularge Ularge Ularge Ularge}|
                  exact Z_full_psorder'@{Ularge Ularge Ularge Ularge Ularge
                                         Ularge Ularge Ularge Ularge Ularge}|
                  exact Z_full_psorder'@{}]).

Lemma Zmult_strong_ext_l' : forall z : Z, StrongExtensionality (z *.).
Proof.
red;apply (Z_ind3 (fun _ _ _ => _ -> _)).
intros [zp zn] [xp xn] [yp yn];rewrite !Zapart_def;unfold PairT.Tapart;simpl.
intros E1.
refine (merely_destruct (strong_binary_extensionality (+)
     (zp * (xp + yn)) (zn * (yp + xn)) (zp * (yp + xn)) (zn * (xp + yn)) _) _).
- assert (Hrw : zp * (xp + yn) + zn * (yp + xn)
  = zp * xp + zn * xn + (zp * yn + zn * yp))
  by ring_with_nat;rewrite Hrw;clear Hrw.
  assert (Hrw : zp * (yp + xn) + zn * (xp + yn)
  = zp * yp + zn * yn + (zp * xn + zn * xp))
  by ring_with_nat;rewrite Hrw;exact E1.
- intros [E2|E2].
  + apply (strong_extensionality (zp *.)).
    trivial.
  + apply symmetry;apply (strong_extensionality (zn *.)).
    trivial.
Qed.

Instance Zmult_strong_ext_l@{} : forall z : Z, StrongExtensionality (z *.)
  := ltac:(first [exact Zmult_strong_ext_l'@{Ularge Ularge}|
                  exact Zmult_strong_ext_l'@{}]).

Instance Z_full_pseudo_srorder@{}
  : FullPseudoSemiRingOrder Zle Zlt.
Proof.
pose proof Z_ring.
first [apply from_full_pseudo_ring_order@{UN UN UN UN UN UN UN Ularge}|
       apply from_full_pseudo_ring_order]; try apply _.
apply apartness.strong_binary_setoid_morphism_commutative.
Qed.

Goal FullPseudoSemiRingOrder Zle Zlt.
Proof.
Fail exact Z_full_pseudo_srorder@{i}.
Abort.

Global Instance Z_to_ring@{} : IntegersToRing@{UN UNalt} Z.
Proof.
red. intros R ??????.
eapply Z_rec.
apply (PairT.to_ring_respects N).
Defined.

Lemma Z_to_ring_morphism' `{Ring B} : SemiRingPreserving (integers_to_ring Z B).
Proof.
split;split;red.
- change (@sg_op B _) with (@plus B _);
  change (@sg_op Z _) with (@plus Z _).
  apply (Z_ind2 _).
  intros [pa na] [pb nb].
  unfold integers_to_ring;simpl.
  rewrite !(preserves_plus (f:=naturals_to_semiring N B)).
  rewrite negate_plus_distr. ring_with_nat.
- change (@mon_unit B _) with (@zero B _);
  change (@mon_unit Z _) with (@zero Z _).
  unfold integers_to_ring;simpl.
  rewrite (preserves_0 (f:=naturals_to_semiring N B)).
  rewrite negate_0,plus_0_r;trivial.
- change (@sg_op B _) with (@mult B _);
  change (@sg_op Z _) with (@mult Z _).
  apply (Z_ind2 _).
  intros [pa na] [pb nb].
  unfold integers_to_ring;simpl.
  rewrite !(preserves_plus (f:=naturals_to_semiring N B)).
  rewrite !(preserves_mult (f:=naturals_to_semiring N B)).
  rewrite (preserves_plus (f:=naturals_to_semiring N B)).
  rewrite !(preserves_mult (f:=naturals_to_semiring N B)).
  rewrite negate_plus_distr.
  rewrite negate_mult_distr_r,negate_mult_distr_l.
  rewrite <-(negate_mult_negate (naturals_to_semiring N B na)
    (naturals_to_semiring N B nb)).
  ring_with_nat.
- change (@mon_unit B _) with (@one B _);
  change (@mon_unit Z _) with (@one Z _).
  unfold integers_to_ring;simpl.
  rewrite (preserves_1 (f:=naturals_to_semiring N B)).
  rewrite (preserves_0 (f:=naturals_to_semiring N B)).
  rewrite negate_0,plus_0_r;trivial.
Qed.

Instance Z_to_ring_morphism@{} `{Ring B} : SemiRingPreserving (integers_to_ring Z B)
  := ltac:(first [exact Z_to_ring_morphism'@{Ularge}|
                  exact Z_to_ring_morphism'@{}]).

Lemma Z_to_ring_unique@{} `{Ring B} (h : Z -> B) `{!SemiRingPreserving h}
  : forall x : Z, integers_to_ring Z B x = h x.
Proof.
pose proof Z_ring.
apply (Z_ind _).
intros [pa na];unfold integers_to_ring;simpl.
rewrite Npair_splits.
rewrite (preserves_plus (f:=h)),(preserves_negate (f:=h)).
change (h (' pa)) with (Compose h (cast N Z) pa).
change (h (' na)) with (Compose h (cast N Z) na).
rewrite 2!(naturals_initial (h:=Compose h (cast N Z))).
trivial.
Qed.

Global Instance Z_integers@{} : Integers Z.
Proof.
split;try apply _.
- apply Z_ring.
- apply @Z_to_ring_unique.
Qed.

Context `{!NatDistance N}.

Lemma Z_abs_aux_0@{} : forall a b z : N, a + z = b -> z = 0 ->
  naturals_to_semiring N Z 0 = ' {| PairT.pos := a; PairT.neg := b |}.
Proof.
intros a b z E E'.
rewrite (preserves_0 (A:=N)).
rewrite E',plus_0_r in E. rewrite E.
apply Z_path. red;simpl. apply plus_comm.
Qed.

Lemma Z_abs_aux_neg@{} : forall a b z : N, a + z = b ->
  naturals_to_semiring N Z z = - ' {| PairT.pos := a; PairT.neg := b |}.
Proof.
intros a b z E.
rewrite <-(naturals.to_semiring_unique (cast N Z)).
apply Z_path. red;simpl. rewrite plus_0_r,plus_comm;trivial.
Qed.

Lemma Z_abs_aux_pos@{} : forall a b z : N, b + z = a ->
  naturals_to_semiring N Z z = ' {| PairT.pos := a; PairT.neg := b |}.
Proof.
intros a b z E.
rewrite <-(naturals.to_semiring_unique (cast N Z)).
apply Z_path;red;simpl. rewrite plus_0_r,plus_comm;trivial.
Qed.

(* We use decidability of equality on N
   to make sure we always go left when the inputs are equal.
   Otherwise we would have to truncate IntAbs. *)
Definition Z_abs_def@{} : forall x : PairT.T N,
  (exists n : N, naturals_to_semiring N Z n = ' x)
  |_| (exists n : N, naturals_to_semiring N Z n = - ' x).
Proof.
intros [a b].
destruct (nat_distance_sig a b) as [[z E]|[z E]].
- destruct (dec (z = 0)) as [E'|_].
  + left. exists 0. apply Z_abs_aux_0 with z;trivial.
  + right. exists z. apply Z_abs_aux_neg;trivial.
- left. exists z. apply Z_abs_aux_pos;trivial.
Defined.

Lemma Z_abs_respects' : forall (x y : PairT.T N) (E : PairT.equiv x y),
  transport
    (fun q : Z =>
     (exists n : N, naturals_to_semiring N Z n = q)
     |_| (exists n : N, naturals_to_semiring N Z n = - q)) (Z_path E) (Z_abs_def x)
  = Z_abs_def y.
Proof.
intros [pa pb] [na nb] E.
red in E; simpl in E.
unfold Z_abs_def.
destruct (nat_distance_sig pa pb) as [[z1 E1] | [z1 E1]];simpl.
- destruct (dec (z1 = 0)) as [E2 | E2].
  + rewrite Sum.transport_sum. rewrite Sigma.transport_sigma.
    destruct (nat_distance_sig na nb) as [[z2 E3] | [z2 E3]];
    [destruct (dec (z2 = 0)) as [E4 | E4]|];simpl.
    * apply ap.
      apply Sigma.path_sigma_hprop;simpl.
      apply PathGroupoids.transport_const.
    * destruct E4.
      rewrite <-E1,<-E3,E2,plus_0_r,<-(plus_0_r (na+pa)) in E.
      rewrite plus_assoc,(plus_comm pa) in E.
      apply (left_cancellation plus _) in E. trivial.
    * apply ap. apply Sigma.path_sigma_hprop. simpl.
      rewrite PathGroupoids.transport_const.
      rewrite E2,plus_0_r in E1.
      rewrite <-E3,E1 in E.
      apply (left_cancellation plus (pb + nb)).
      rewrite plus_0_r. etransitivity;[apply E|].
      ring_with_nat.
  + rewrite Sum.transport_sum,Sigma.transport_sigma.
    destruct (nat_distance_sig na nb) as [[z2 E3] | [z2 E3]];
    [destruct (dec (z2 = 0)) as [E4 | E4]|];simpl.
    * destruct E2.
      rewrite E4,plus_0_r in E3;rewrite <-E1,<-E3 in E.
      apply (left_cancellation plus (pa+na)).
      rewrite (plus_comm pa na),plus_0_r,<-plus_assoc.
      rewrite (plus_comm na pa). symmetry;trivial.
    * apply ap. apply Sigma.path_sigma_hprop.
      simpl. rewrite PathGroupoids.transport_const.
      rewrite <-E1,<-E3 in E.
      apply (left_cancellation plus (pa + na)).
      rewrite <-(plus_assoc pa na z2),(plus_comm pa na),<-plus_assoc.
      symmetry;trivial.
    * destruct E2.
      rewrite <-E1,<-E3 in E.
      assert (Erw : nb + z2 + (pa + z1) = (pa + nb) + (z2 + z1))
      by ring_with_nat.
      rewrite <-(plus_0_r (pa+nb)),Erw in E.
      apply (left_cancellation plus _),symmetry,naturals.zero_sum in E.
      apply E.
- rewrite Sum.transport_sum,Sigma.transport_sigma. simpl.
  destruct (nat_distance_sig na nb) as [[z2 E3] | [z2 E3]];
  [destruct (dec (z2 = 0)) as [E4 | E4]|];simpl.
  + apply ap. apply Sigma.path_sigma_hprop. simpl.
    rewrite PathGroupoids.transport_const.
    rewrite <-E1,<-E3,E4,plus_0_r in E.
    apply (left_cancellation plus (na+pb)).
    rewrite plus_0_r.
    path_via (pb + z1 + na). ring_with_nat.
  + destruct E4.
    rewrite <-E1,<-E3 in E.
    assert (Hrw : pb + z1 + (na + z2) = (na + pb) + (z1 + z2))
    by ring_with_nat.
    rewrite <-(plus_0_r (na+pb)),Hrw in E.
    apply (left_cancellation _ _),naturals.zero_sum in E.
    apply E.
  + apply ap,Sigma.path_sigma_hprop. simpl.
    rewrite PathGroupoids.transport_const.
    rewrite <-E1,<-E3 in E.
    apply (left_cancellation plus (pb+nb)).
    path_via (pb + z1 + nb);[|path_via (nb + z2 + pb)];ring_with_nat.
Qed.

Lemma Z_abs' : IntAbs Z N.
Proof.
red. apply (Z_rect _ Z_abs_def).
exact Z_abs_respects'.
Qed.

Global Instance Z_abs@{} : IntAbs@{UN UN UN UN UN
  UN UN UN UN UN
  UN UN UN UN UN
  UN UN} Z N
  := ltac:(first [exact Z_abs'@{Ularge Ularge Ularge Ularge Ularge
                                Ularge Ularge}|
                  exact Z_abs'@{Ularge Ularge Ularge Ularge Ularge
                                Ularge}]).

Notation n_to_z := (naturals_to_semiring N Z).

Definition zero_product_aux a b :
  n_to_z a * n_to_z b = 0 -> n_to_z a = 0 |_| n_to_z b = 0.
Proof.
rewrite <-rings.preserves_mult.
rewrite <-!(naturals.to_semiring_unique (cast N Z)).
intros E.
change 0 with (' 0) in E. apply (injective _) in E.
apply zero_product in E.
destruct E as [E|E];rewrite E;[left|right];apply preserves_0.
Qed.

Lemma Z_zero_product' : ZeroProduct Z.
Proof.
intros x y E.
destruct (int_abs_sig Z N x) as [[a Ea]|[a Ea]],
  (int_abs_sig Z N y) as [[b Eb]|[b Eb]].
- rewrite <-Ea,<-Eb in E.
  apply zero_product_aux in E.
  rewrite <-Ea,<-Eb.
  trivial.
- apply (ap negate) in E. rewrite negate_mult_distr_r in E.
  rewrite <-Ea,<-Eb in E.
  rewrite negate_0 in E.
  apply zero_product_aux in E.
  destruct E as [E|E].
  + left;rewrite <-Ea;trivial.
  + right.
    apply (injective negate).
    rewrite negate_0,<-Eb;trivial.
- apply (ap negate) in E. rewrite negate_mult_distr_l in E.
  rewrite <-Ea,<-Eb in E.
  rewrite negate_0 in E.
  apply zero_product_aux in E.
  destruct E as [E|E].
  + left.
    apply (injective negate).
    rewrite negate_0,<-Ea;trivial.
  + right;rewrite <-Eb;trivial.
- rewrite <-negate_mult_negate,<-Ea,<-Eb in E.
  apply zero_product_aux in E.
  destruct E as [E|E].
  + left.
    apply (injective negate).
    rewrite negate_0,<-Ea;trivial.
  + right.
    apply (injective negate).
    rewrite negate_0,<-Eb;trivial.
Qed.

Global Instance Z_zero_product@{} : ZeroProduct Z
  := ltac:(first [exact Z_zero_product'@{Ularge Ularge}|
                  exact Z_zero_product'@{}]).

End contents.

End NatPair.
