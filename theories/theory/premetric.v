Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.integers
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.rationals
  HoTTClasses.interfaces.orders
  HoTTClasses.implementations.natpair_integers
  HoTTClasses.theory.rings
  HoTTClasses.theory.integers
  HoTTClasses.theory.dec_fields
  HoTTClasses.orders.dec_fields
  HoTTClasses.theory.rationals
  HoTTClasses.orders.lattices
  HoTTClasses.theory.additional_operations.

Local Set Universe Minimization ToSet.

Section contents.
Context {funext : Funext} {univalence : Univalence}.

Class Closeness@{i} (A : Type@{i}) := close : Q+ -> relation@{i i} A.

Global Instance Q_close@{} : Closeness Q := fun e q r => - ' e < q - r < ' e.

Lemma Qclose_alt : forall e (q r : Q), close e q r <-> abs (q - r) < ' e.
Proof.
intros e q r;split.
- intros [E1 E2].
  destruct (total le 0 (q - r)) as [E|E].
  + rewrite (Qabs_of_nonneg _ E).
    trivial.
  + rewrite (Qabs_of_nonpos _ E).
    apply flip_lt_negate. rewrite involutive. trivial.
- intros E. split;[apply flip_lt_negate;rewrite involutive|];
  apply le_lt_trans with (abs (q - r));trivial.
  + apply Qabs_le_neg_raw.
  + apply Qabs_le_raw.
Qed.

Lemma Qclose_neg@{} : forall e (x y : Q), close e x y <-> close e (- x) (- y).
Proof.
intros e x y;split;intros E;apply Qclose_alt in E;apply Qclose_alt.
- rewrite <-(negate_plus_distr),Qabs_neg. trivial.
- rewrite <-(negate_plus_distr),Qabs_neg in E. trivial.
Qed.

Class Separated A `{Closeness A}
  := separated : forall x y, (forall e, close e x y) -> x = y :> A.

Class Triangular A `{Closeness A}
  := triangular : forall u v w e d, close e u v -> close d v w ->
  close (e+d) u w.

Class Rounded@{i j} (A:Type@{i}) `{Closeness A}
  := rounded : forall e u v, iff@{i j j} (close e u v)
    (merely@{j} (sigT@{UQ j} (fun d => sigT@{UQ j} (fun d' =>
      e = d + d' /\ close d u v)))).

Class PreMetric@{i j} (A:Type@{i}) {Aclose : Closeness A} :=
  { premetric_refl :> forall e, Reflexive (close (A:=A) e)
  ; premetric_symm :> forall e, Symmetric (close (A:=A) e)
  ; premetric_separated :> Separated A
  ; premetric_triangular :> Triangular A
  ; premetric_rounded :> Rounded@{i j} A }.

Lemma rounded_plus `{Rounded A} : forall d d' u v, close d u v ->
  close (d+d') u v.
Proof.
intros d d' u v xi;apply rounded.
apply tr;exists d,d';auto.
Qed.

Lemma rounded_le' `{Rounded A}
  : forall e u v, close e u v ->
  forall d, ' e <= ' d -> close d u v.
Proof.
intros e u v xi d E.
apply le_equiv_lt in E. destruct E as [E|E].
- apply pos_eq in E. rewrite <-E;trivial.
- pose proof (pos_eq _ (_ + _) (Qpos_diff_pr _ _ E)) as E'.
  rewrite E'. apply rounded_plus. trivial.
Qed.

Definition rounded_le@{i j} := @rounded_le'@{j i Ularge j}.
Arguments rounded_le {A _ _} e u v _ d _.

Section close_prod.
Universe UA UB i.
Context (A:Type@{UA}) (B:Type@{UB}) `{Closeness A} `{Closeness B}
  `{forall e, is_mere_relation A (close e)}
  `{forall e, is_mere_relation B (close e)}.

Global Instance close_prod@{} : Closeness@{i} (A /\ B)
  := fun e x y => close e (fst x) (fst y) /\ close e (snd x) (snd y).

Global Instance close_prod_refl@{}
  `{forall e, Reflexive (close (A:=A) e)}
  `{forall e, Reflexive (close (A:=B) e)}
  : forall e, Reflexive (close (A:=A /\ B) e).
Proof.
intros e;split;reflexivity.
Qed.

Global Instance close_prod_symm@{}
  `{forall e, Symmetric (close (A:=A) e)}
  `{forall e, Symmetric (close (A:=B) e)}
  : forall e, Symmetric (close (A:=A /\ B) e).
Proof.
intros e u v xi;split;Symmetry;apply xi.
Qed.

Global Instance close_prod_separated@{}
  `{!Separated A}
  `{!Separated B}
  : Separated (A /\ B).
Proof.
intros x y E.
apply Prod.path_prod;apply separated;intros;apply E.
Qed.

Global Instance close_prod_triangular@{}
  `{!Triangular A}
  `{!Triangular B}
  : Triangular (A /\ B).
Proof.
intros u v w e d E1 E2;split;(eapply triangular;[apply E1|apply E2]).
Qed.

Lemma close_prod_rounded'
  `{!Rounded A} 
  `{!Rounded B}
  : Rounded (A /\ B).
Proof.
intros e u v. split.
- intros [E0 E0'];apply rounded in E0;apply rounded in E0'.
  revert E0;apply (Trunc_ind _);intros [d1 [d1' [E1 E2]]].
  revert E0';apply (Trunc_ind _);intros [d2 [d2' [E3 E4]]].
  apply tr;exists (join d1 d2), (meet d1' d2');split.
  + rewrite E1. apply Qpos_sum_eq_join_meet. rewrite <-E1;trivial.
  + split.
    * apply rounded_le with d1;trivial.
      apply join_ub_l.
    * apply rounded_le with d2;trivial.
      apply join_ub_r.
- apply (Trunc_ind _);intros [d [d' [E1 E2]]].
  rewrite E1;split;apply rounded_plus,E2.
Qed.

Definition close_prod_rounded@{j} := @close_prod_rounded'@{j j j j j j}.
Arguments close_prod_rounded {_ _} _ _ _.
Global Existing Instance close_prod_rounded.

Lemma prod_premetric@{j} `{!PreMetric@{UA j} A} `{!PreMetric@{UB j} B}
  : PreMetric@{i j} (A /\ B).
Proof.
split;try apply _.
Qed.
Global Existing Instance prod_premetric.

End close_prod.

Class NonExpanding `{Closeness A} `{Closeness B} (f : A -> B)
  := non_expanding : forall e x y, close e x y -> close e (f x) (f y).
Arguments non_expanding {A _ B _} f {_ e x y} _.

Class Lipschitz `{Closeness A} `{Closeness B} (f : A -> B) (L : Q+)
  := lipschitz : forall e x y, close e x y -> close (L * e) (f x) (f y).
Arguments lipschitz {A _ B _} f L {_ e x y} _.

Class Uniform `{Closeness A} `{Closeness B} (f : A -> B) (mu : Q+ -> Q+)
  := uniform : forall e x y, close (mu e) x y -> close e (f x) (f y).
Arguments uniform {A _ B _} f mu {_} _ _ _ _.

Class Continuous@{UA UB}
  {A:Type@{UA} } `{Closeness A}
  {B:Type@{UB} } `{Closeness B} (f : A -> B)
  := continuous : forall u e, merely@{Ularge} (sigT@{UQ Ularge}
    (fun d => forall v, close d u v ->
    close e (f u) (f v))).
Arguments continuous {A _ B _} f {_} _ _.

Definition BinaryDup@{i} {A : Type@{i} } : A -> A /\ A := fun x => (x, x).
Definition uncurry {A B C} (f : A -> B -> C) : A /\ B -> C
  := fun x => f (fst x) (snd x).
Definition map2 {A B C D} (f : A -> C) (g : B -> D) : A /\ B -> C /\ D
  := fun x => (f (fst x), g (snd x)).

Section closeness.
Universe UA.
Context {A:Type@{UA} } `{Closeness A}.

Global Instance id_nonexpanding : NonExpanding (@id A).
Proof.
hnf;trivial.
Qed.

Global Instance BinaryDup_nonexpanding@{} : NonExpanding (@BinaryDup A).
Proof.
intros e x y E;split;exact E.
Qed.

Universe UB.
Context {B:Type@{UB} } `{Closeness B} (f : A -> B).

Lemma nonexpanding_lipschitz' `{!NonExpanding f}
  : Lipschitz f 1.
Proof.
red. intro;rewrite left_identity;apply non_expanding,_.
Qed.

Definition nonexpanding_lipschitz@{} `{!NonExpanding f}
  : Lipschitz f 1
  := nonexpanding_lipschitz'@{Ularge}.
Global Existing Instance nonexpanding_lipschitz.


Lemma lipschitz_nonexpanding@{} `{!Lipschitz f 1} : NonExpanding f.
Proof.
red. intros e x y E;rewrite <-(left_identity e). apply (lipschitz f 1 E).
Qed.

Global Instance const_nonexpanding@{} `{forall e, Reflexive (close (A:=B) e)}
  (b : B) : NonExpanding (fun _ : A => b).
Proof.
hnf. intros;reflexivity.
Qed.

Global Instance lipschitz_uniform@{} (L:Q+) `{!Lipschitz f L}
  : Uniform f (fun e => e / L).
Proof.
intros e u v xi.
rewrite <-(pos_unconjugate L e),<-Qpos_mult_assoc.
apply (lipschitz f L),xi.
Qed.

Lemma uniform_continuous@{} mu `{!Uniform@{UA UB} f mu} : Continuous f.
Proof.
hnf.
intros u e;apply tr;exists (mu e).
apply (uniform f mu).
Qed.
Global Existing Instance uniform_continuous.

Definition lipschitz_continuous@{} (L:Q+) `{!Lipschitz f L} : Continuous f
  := _.

Definition nonexpanding_continuous@{} `{!NonExpanding f} : Continuous f
  := _.

End closeness.

Section compositions.
Universe UA.
Context {A:Type@{UA} } `{Closeness A}.
Universe UB.
Context {B:Type@{UB} } `{Closeness B}.
Universe UC.
Context {C:Type@{UC} } `{Closeness C} (g : B -> C) (f : A -> B).

Global Instance nonexpanding_compose@{}
  {Eg : NonExpanding g} {Ef : NonExpanding f}
  : NonExpanding (compose g f).
Proof.
hnf. intros e x y xi;exact (non_expanding g (non_expanding f xi)).
Qed.

Global Instance lipschitz_compose@{}
  Lg {Eg : Lipschitz g Lg} Lf {Ef : Lipschitz f Lf}
  : Lipschitz (compose g f) (Lg * Lf).
Proof.
intros ??? He.
unfold compose;apply Ef,Eg in He.
pattern (Lg * Lf * e).
eapply transport;[|exact He].
apply associativity.
Qed.

Lemma lipschitz_compose_nonexpanding_r'
  L {Eg : Lipschitz g L} {Ef : NonExpanding f}
  : Lipschitz (compose g f) L.
Proof.
rewrite <-(left_identity L),commutativity. apply _.
Qed.

Global Instance lipschitz_compose_nonexpanding_r@{}
  L {Eg : Lipschitz g L} {Ef : NonExpanding f}
  : Lipschitz (compose g f) L
  := lipschitz_compose_nonexpanding_r'@{Ularge} L.

Lemma lipschitz_compose_nonexpanding_l'
  L {Eg : NonExpanding g} {Ef : Lipschitz f L}
  : Lipschitz (compose g f) L.
Proof.
rewrite <-(left_identity L). apply _.
Qed.

Global Instance lipschitz_compose_nonexpanding_l@{}
  L {Eg : NonExpanding g} {Ef : Lipschitz f L}
  : Lipschitz (compose g f) L
  := lipschitz_compose_nonexpanding_l'@{Ularge} L.

Lemma uniform_compose@{} mu {Eg : Uniform g mu} mu' {Ef : Uniform f mu'}
  : Uniform (compose g f) (compose mu' mu).
Proof.
intros e u v xi. unfold compose.
apply (uniform g _),(uniform f _),xi.
Qed.
Global Existing Instance uniform_compose.

Global Instance continuous_compose@{} {Eg : Continuous g} {Ef : Continuous f}
  : Continuous (compose g f).
Proof.
intros u e.
apply (merely_destruct (continuous g (f u) e)).
intros [d E].
apply (merely_destruct (continuous f u d)).
intros [d' E'].
apply tr;exists d';intros v xi.
apply E,E',xi.
Qed.

End compositions.

Section currying.
Universe UA.
Context {A:Type@{UA} } `{Closeness A}.
Universe UB.
Context {B:Type@{UB} } `{Closeness B}.
Universe UC.
Context {C:Type@{UC} } `{Closeness C} `{!Triangular C}.

Global Instance uncurry_lipschitz (f : A -> B -> C) L1 L2
  `{!forall x, Lipschitz (f x) L1}
  `{!forall y, Lipschitz (fun x => f x y) L2}
  : Lipschitz (uncurry f) (L1 + L2).
Proof.
intros e [u1 u2] [v1 v2] [xi1 xi2]. simpl in xi1,xi2.
unfold uncurry;simpl.
assert (Hrw : (L1 + L2) * e = L1 * e + L2 * e)
by abstract (apply pos_eq;ring_tac.ring_with_nat);
rewrite Hrw;clear Hrw.
apply (triangular _ (f u1 v2)).
- apply (lipschitz _ L1). trivial.
- apply (lipschitz (fun u => f u v2) L2). trivial.
Qed.

Global Instance uncurry_uniform
  `{!Rounded A} `{!Rounded B} (f : A -> B -> C) mu mu'
  `{!forall x, Uniform (f x) mu}
  `{!forall y, Uniform (fun x => f x y) mu'}
  : Uniform (uncurry f) (fun e => meet (mu (e/2)) (mu' (e/2))).
Proof.
intros e [u1 u2] [v1 v2] [xi1 xi2].
simpl in *.
rewrite (pos_split2 e).
apply (triangular _ (f u1 v2)).
- apply (uniform (f u1) _).
  eapply rounded_le.
  + exact xi2.
  + apply meet_lb_l.
- apply (uniform (fun v => f v v2) _).
  eapply rounded_le.
  + exact xi1.
  + apply meet_lb_r.
Qed.

End currying.

Section pair.
Universe UA.
Context {A:Type@{UA} } `{Closeness A} `{forall e, Reflexive (close (A:=A) e)}.
Universe UB.
Context {B:Type@{UB} } `{Closeness B} `{forall e, Reflexive (close (A:=B) e)}.

Global Instance pair_nonexpanding_l : forall x, NonExpanding (@pair A B x).
Proof.
intros x e u v xi;split;simpl.
- reflexivity.
- exact xi.
Qed.

Global Instance pair_nonexpanding_r : forall y,
  NonExpanding (fun x => @pair A B x y).
Proof.
intros x e u v xi;split;simpl.
- exact xi.
- reflexivity.
Qed.

Global Instance fst_nonexpanding : NonExpanding (@fst A B).
Proof.
intros e u v xi;apply xi.
Qed.

Global Instance snd_nonexpanding : NonExpanding (@snd A B).
Proof.
intros e u v xi;apply xi.
Qed.

End pair.

Section prod_equiv.
Universe UA.
Context {A:Type@{UA} } `{Closeness A}.
Universe UB.
Context {B:Type@{UB} } `{Closeness B}.

Global Instance equiv_prod_symm_nonexpanding
  : NonExpanding (@Prod.equiv_prod_symm A B).
Proof.
intros e u v xi;split;apply xi.
Qed.

Global Instance equiv_prod_symm_inv_nonexpanding
  : NonExpanding ((@Prod.equiv_prod_symm A B)^-1).
Proof.
intros e u v xi;split;apply xi.
Qed.

Universe UC.
Context {C:Type@{UC} } `{Closeness C}.

Global Instance equiv_prod_assoc_nonexpanding
  : NonExpanding (@Prod.equiv_prod_assoc A B C).
Proof.
intros e u v xi;repeat split;apply xi.
Qed.

Global Instance equiv_prod_assoc_inc_nonexpanding
  : NonExpanding ((@Prod.equiv_prod_assoc A B C)^-1).
Proof.
intros e u v xi;repeat split;apply xi.
Qed.

End prod_equiv.

Section map2.
Universe UA.
Context {A:Type@{UA} } `{Closeness A}.
Universe UB.
Context {B:Type@{UB} } `{Closeness B}.
Universe UC.
Context {C:Type@{UC} } `{Closeness C}.
Universe UD.
Context {D:Type@{UD} } `{Closeness D}.
Variables (f : A -> C) (g : B -> D).

Lemma map2_nonexpanding'
  `{!NonExpanding f} `{!NonExpanding g}
  : NonExpanding (map2 f g).
Proof.
intros e u v xi;split;simpl; apply (non_expanding _),xi.
Qed.

Definition map2_nonexpanding@{i} := @map2_nonexpanding'@{i i}.
Arguments map2_nonexpanding {_ _} e x y xi.
Global Existing Instance map2_nonexpanding.

Lemma map2_lipschitz' `{!Rounded C} `{!Rounded D} Lf Lg
  `{!Lipschitz f Lf} `{!Lipschitz g Lg}
  : Lipschitz (map2 f g) (join Lf Lg).
Proof.
intros e u v xi. split;simpl.
- apply rounded_le with (Lf * e).
  + apply (lipschitz _ _),xi.
  + apply (order_preserving (.* ' e)).
    apply join_ub_l.
- apply rounded_le with (Lg * e).
  + apply (lipschitz _ _),xi.
  + apply (order_preserving (.* ' e)).
    apply join_ub_r.
Qed.

Definition map2_lipschitz@{i} := @map2_lipschitz'@{i i i i}.
Arguments map2_lipschitz {_ _} Lf Lg {_ _} e x y xi.
Global Existing Instance map2_lipschitz.

Lemma map2_continuous' `{!Rounded A} `{!Rounded B}
  `{!Continuous f} `{!Continuous g}
  : Continuous (map2 f g).
Proof.
intros u e.
apply (merely_destruct (continuous f (fst u) e));intros [d1 E1].
apply (merely_destruct (continuous g (snd u) e));intros [d2 E2].
apply tr;exists (meet d1 d2). intros v xi.
split;simpl.
- apply E1. apply rounded_le with (meet d1 d2).
  + apply xi.
  + apply meet_lb_l.
- apply E2. apply rounded_le with (meet d1 d2).
  + apply xi.
  + apply meet_lb_r.
Qed.

Definition map2_continuous@{i} := @map2_continuous'@{i i i i}.
Arguments map2_continuous {_ _ _ _} u e.
Global Existing Instance map2_continuous.

End map2.

Section interval.
Universe UA UALE.
Context {A:Type@{UA} } {Ale : Le@{UA UALE} A}.

Definition Interval a b := sigT (fun x : A => a <= x /\ x <= b).

Definition interval_proj a b : Interval a b -> A := pr1.

Context {Ameet : Meet A} {Ajoin : Join A}
  `{!LatticeOrder@{UA UALE} Ale}.

Definition Interval_restrict@{} (a b : A) (E : a <= b) : A -> Interval a b.
Proof.
intros x.
exists (join a (meet x b)).
split.
- apply join_ub_l.
- apply join_le.
  + exact E.
  + apply meet_lb_r.
Defined.

Lemma Interval_restrict_pr : forall a b E x (E': a <= x /\ x <= b),
  Interval_restrict a b E x = existT _ x E'.
Proof.
intros a b E x E'.
unfold Interval_restrict.
apply Sigma.path_sigma_hprop.
simpl. rewrite meet_l;[apply join_r|];apply E'.
Qed.

Context `{Closeness A}.

Global Instance Interval_close (a b : A) : Closeness (Interval a b)
  := fun e x y => close e (interval_proj a b x) (interval_proj a b y).
Arguments Interval_close _ _ _ _ _ /.

(* NB: for some reason this forces UALE <= UA *)
Lemma Interval_premetric@{i} `{!PreMetric@{UA i} A} a b
  : PreMetric@{UA i} (Interval a b).
Proof.
split.
- intros e u. red;red. reflexivity.
- intros e u v xi;red;red;Symmetry;apply xi.
- intros u v E.
  apply Sigma.path_sigma_hprop. apply separated,E.
- intros u v w e d xi1 xi2.
  red;red. apply (triangular _ (interval_proj a b v)).
  + exact xi1.
  + exact xi2.
- intros e u v. split.
  + intros xi. do 2 red in xi. apply (fst (rounded _ _ _)) in xi.
    exact xi.
  + intros E. unfold close,Interval_close in E. apply (snd (rounded _ _ _)) in E.
    exact E.
Qed.
Global Existing Instance Interval_premetric.

Global Instance interval_proj_nonexpanding (a b : A)
  : NonExpanding (interval_proj a b)
  := fun _ _ _ xi => xi.

End interval.

End contents.

Arguments rounded_le {_ _ A _ _} e u v _ d _.
Arguments non_expanding {A _ B _} f {_ e x y} _.
Arguments lipschitz {A _ B _} f L {_ e x y} _.
Arguments uniform {A _ B _} f mu {_} _ _ _ _.
Arguments continuous {A _ B _} f {_} _ _.

Arguments map2_nonexpanding {A _ B _ C _ D _} f g {_ _} e x y xi.
Arguments map2_lipschitz {_ _ A _ B _ C _ D _} f g {_ _} Lf Lg {_ _} e x y xi.
Arguments map2_continuous {_ _ A _ B _ C _ D _} f g {_ _ _ _} u e.

Arguments Interval_close {_ _ _} _ _ _ _ _ /.
