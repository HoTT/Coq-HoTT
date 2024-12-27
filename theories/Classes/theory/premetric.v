Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.rationals
  HoTT.Classes.interfaces.orders
  HoTT.Classes.implementations.peano_naturals
  HoTT.Classes.implementations.natpair_integers
  HoTT.Classes.theory.groups
  HoTT.Classes.theory.integers
  HoTT.Classes.theory.dec_fields
  HoTT.Classes.orders.dec_fields
  HoTT.Classes.orders.sum
  HoTT.Classes.theory.rationals
  HoTT.Classes.orders.lattices
  HoTT.Classes.implementations.assume_rationals
  HoTT.Classes.tactics.ring_quote
  HoTT.Classes.tactics.ring_tac.

Import NatPair.Instances.
Import Quoting.Instances.
Generalizable Variables A B.

Local Set Universe Minimization ToSet.

Class Closeness@{i} (A : Type@{i}) := close : Q+ -> Relation@{i i} A.

Global Instance Q_close@{} : Closeness Q := fun e q r => - ' e < q - r < ' e.

Class Separated A `{Closeness A}
  := separated : forall x y, (forall e, close e x y) -> x = y :> A.

Class Triangular A `{Closeness A}
  := triangular : forall u v w e d, close e u v -> close d v w ->
  close (e+d) u w.

Class Rounded@{i j} (A:Type@{i}) `{Closeness A}
  := rounded : forall e u v, iff@{i j j} (close e u v)
    (merely@{j} (sig@{UQ j} (fun d => sig@{UQ j} (fun d' =>
      e = d + d' /\ close d u v)))).

Class PreMetric@{i j} (A:Type@{i}) {Aclose : Closeness A} :=
  { premetric_prop : forall e, is_mere_relation A (close e)
  ; premetric_refl : forall e, Reflexive (close (A:=A) e)
  ; premetric_symm : forall e, Symmetric (close (A:=A) e)
  ; premetric_separated : Separated A
  ; premetric_triangular : Triangular A
  ; premetric_rounded : Rounded@{i j} A }.
#[export] Existing Instances
  premetric_prop
  premetric_refl
  premetric_symm
  premetric_separated
  premetric_triangular
  premetric_rounded.

Global Instance premetric_hset@{i j} `{Funext}
  {A:Type@{i} } `{PreMetric@{i j} A} : IsHSet A.
Proof.
apply (@HSet.ishset_hrel_subpaths@{j i j} _ (fun x y => forall e, close e x y)).
- intros x;reflexivity.
- apply _.
- apply separated.
Qed.

Record Approximation@{i} (A:Type@{i}) {Aclose : Closeness A} :=
  { approximate :> Q+ -> A
  ; approx_equiv : forall d e, close (d+e) (approximate d) (approximate e) }.

Lemma approx_eq `{Funext} `{Closeness A} `{forall e x y, IsHProp (close e x y)}
  : forall x y : Approximation A,
  approximate _ x = approximate _ y -> x = y.
Proof.
intros [x Ex] [y Ey];simpl;intros E.
destruct E. apply ap. apply path_ishprop.
Qed.


Definition IsLimit@{i} {A:Type@{i} } {Aclose : Closeness A}
  (x : Approximation A) (l : A)
  := forall e d : Q+, close (e+d) (x d) l.

Class Lim@{i} (A:Type@{i}) {Aclose : Closeness A} := lim : Approximation A -> A.

Class CauchyComplete@{i} (A:Type@{i}) {Aclose : Closeness A} {Alim : Lim A}
  := cauchy_complete : forall x : Approximation A, IsLimit x (lim x).

Section contents.
Context {funext : Funext} {univalence : Univalence}.

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

(* Coq pre 8.8 produces phantom universes, see coq/coq#6483 **)
Definition rounded_le@{i j} := ltac:(first [exact @rounded_le'@{j i Ularge}|
                                            exact @rounded_le'@{j i Ularge j}|
                                            exact @rounded_le'@{i j}]).
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
intros e u v xi;split;symmetry;apply xi.
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

(* Coq pre 8.8 produces phantom universes, see coq/coq#6483 **)
Definition close_prod_rounded@{j} := ltac:(first [exact @close_prod_rounded'@{j j j j j}|
                                                  exact @close_prod_rounded'@{j j}|
                                                  exact @close_prod_rounded'@{j j j}]).
Arguments close_prod_rounded {_ _} _ _ _.
Global Existing Instance close_prod_rounded.

Lemma prod_premetric@{j} `{!PreMetric@{UA j} A} `{!PreMetric@{UB j} B}
  : PreMetric@{i j} (A /\ B).
Proof.
split;try apply _.
Qed.
Global Existing Instance prod_premetric.

Context {Alim : Lim A} {Blim : Lim B}.

Global Instance prod_lim@{} : Lim (A /\ B).
Proof.
intros xy. split;apply lim;
[exists (fun e => fst (xy e))|exists (fun e => snd (xy e))];intros;apply xy.
Defined.

Global Instance prod_cauchy_complete `{!CauchyComplete A} `{!CauchyComplete B}
  : CauchyComplete (A /\ B).
Proof.
intros xy e d;split.
- apply (cauchy_complete
    {| approximate := fun e0 : Q+ => fst (xy e0); approx_equiv := _ |}).
- apply (cauchy_complete
    {| approximate := fun e0 : Q+ => snd (xy e0); approx_equiv := _ |}).
Qed.

End close_prod.

Section close_arrow.
Context {A:Type} `{Bclose : Closeness B} `{!PreMetric B}.

(* Using [forall x, close e (f x) (g x)] works for closed balls, not open ones. *)
Global Instance close_arrow : Closeness (A -> B)
  := fun e f g => merely (exists d d', e = d + d' /\ forall x, close d (f x) (g x)).

Lemma close_arrow_apply : forall e (f g : A -> B), close e f g ->
  forall x, close e (f x) (g x).
Proof.
intros e f g E x;revert E;apply (Trunc_ind _);intros [d [d' [E1 E2]]].
rewrite E1;apply rounded_plus;trivial.
Qed.

Global Instance close_arrow_premetric : PreMetric (A -> B).
Proof.
split.
- apply _.
- intros e f;apply tr; exists (e/2), (e/2);split.
  + apply (pos_split2 e).
  + intros x;reflexivity.
- intros e f g;apply (Trunc_ind _);intros [d [d' [E1 E2]]].
  apply tr;exists d, d';split;trivial.
  intros x;symmetry;trivial.
- intros f g E. apply path_forall;intros x.
  apply separated. intros e.
  apply (merely_destruct (E e)). intros [d [d' [E1 E2]]].
  rewrite E1. apply rounded_plus. trivial.
- intros f g h e d E1 E2.
  apply (merely_destruct E1);intros [d1 [d1' [E3 E4]]].
  apply (merely_destruct E2);intros [d2 [d2' [E5 E6]]].
  apply tr;exists (d1+d2),(d1'+d2'). split.
  + rewrite E3,E5.
   abstract (apply pos_eq; ring_tac.ring_with_nat).
  + intros x. apply triangular with (g x);trivial.
- intros e f g. split.
  + apply (Trunc_ind _). intros [d [d' [E1 E2]]].
    apply tr;exists (d+d'/2),(d'/2). split.
    * rewrite <-Qpos_plus_assoc,<-pos_split2. exact E1.
    * apply tr. exists d, (d'/2);split;trivial.
  + apply (Trunc_ind _);intros [d [d' [E1 E2]]].
    apply tr;exists d,d';split;trivial.
    apply close_arrow_apply. trivial.
Qed.

Context {Blim : Lim B}.

Global Instance arrow_lim : Lim (A -> B).
Proof.
intros f x. apply lim. exists (fun e => f e x).
intros. apply close_arrow_apply. apply approx_equiv.
Defined.
Arguments arrow_lim _ / _.

Context `{!CauchyComplete B}.
Global Instance arrow_cauchy_complete : CauchyComplete (A -> B).
Proof.
intros f e d.
unfold lim;simpl.
apply tr. exists (e/2 + d), (e/2). split.
+ abstract (set (e' := e/2);rewrite (pos_split2 e);unfold e';
  apply pos_eq;ring_tac.ring_with_nat).
+ intros x.
  set (S := {| approximate := fun e0 : Q+ => (f e0) x
            ;  approx_equiv := _ |}).
  pose proof (cauchy_complete S) as E;red in E.
  apply E.
Qed.

End close_arrow.

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
  := continuous : forall u e, merely@{Ularge} (sig@{UQ Ularge}
    (fun d => forall v, close d u v ->
    close e (f u) (f v))).
Arguments continuous {A _ B _} f {_} _ _.

Definition BinaryDup@{i} {A : Type@{i} } : A -> A /\ A := fun x => (x, x).

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
  := ltac:(first [exact nonexpanding_lipschitz'@{Ularge}|
                  exact nonexpanding_lipschitz'@{}]).
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

Global Instance lipschitz_const@{} `{forall e, Reflexive (close (A:=B) e)}
  : forall (b:B) (L:Q+), Lipschitz (fun _ : A => b) L.
Proof.
intros;hnf.
intros e _ _ _. reflexivity.
Qed.

Global Instance lipschitz_uniform@{} (L:Q+) `{!Lipschitz f L}
  : Uniform f (fun e => e / L) | 5.
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
Global Existing Instance uniform_continuous | 5.

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
  : NonExpanding (Compose g f).
Proof.
hnf. intros e x y xi;exact (non_expanding g (non_expanding f xi)).
Qed.

Global Instance lipschitz_compose@{}
  Lg {Eg : Lipschitz g Lg} Lf {Ef : Lipschitz f Lf}
  : Lipschitz (Compose g f) (Lg * Lf).
Proof.
intros ??? He.
unfold Compose;apply Ef,Eg in He.
pattern (Lg * Lf * e).
eapply transport;[|exact He].
apply associativity.
Qed.

Lemma lipschitz_compose_nonexpanding_r'
  L {Eg : Lipschitz g L} {Ef : NonExpanding f}
  : Lipschitz (Compose g f) L.
Proof.
rewrite <-(left_identity L),commutativity. apply _.
Qed.

Global Instance lipschitz_compose_nonexpanding_r@{}
  L {Eg : Lipschitz g L} {Ef : NonExpanding f}
  : Lipschitz (Compose g f) L
  := ltac:(first [exact (lipschitz_compose_nonexpanding_r'@{Ularge} L)|
                  exact (lipschitz_compose_nonexpanding_r'@{} L)]).

Lemma lipschitz_compose_nonexpanding_l'
  L {Eg : NonExpanding g} {Ef : Lipschitz f L}
  : Lipschitz (Compose g f) L.
Proof.
rewrite <-(left_identity L). apply _.
Qed.

Global Instance lipschitz_compose_nonexpanding_l@{}
  L {Eg : NonExpanding g} {Ef : Lipschitz f L}
  : Lipschitz (Compose g f) L
  := ltac:(first [exact (lipschitz_compose_nonexpanding_l'@{Ularge} L)|
                  exact (lipschitz_compose_nonexpanding_l'@{} L)]).

Lemma uniform_compose@{} mu {Eg : Uniform g mu} mu' {Ef : Uniform f mu'}
  : Uniform (Compose g f) (Compose mu' mu).
Proof.
intros e u v xi. unfold Compose.
apply (uniform g _),(uniform f _),xi.
Qed.
Global Existing Instance uniform_compose.

Global Instance continuous_compose@{} {Eg : Continuous g} {Ef : Continuous f}
  : Continuous (Compose g f).
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
simpl.
assert (Hrw : (L1 + L2) * e = L1 * e + L2 * e)
by abstract (apply pos_eq;ring_tac.ring_with_nat);
rewrite Hrw;clear Hrw.
apply (triangular _ (f u1 v2)).
- apply (lipschitz _ L1). trivial.
- apply (lipschitz (fun u => f u v2) L2). trivial.
Qed.

Lemma uncurry_uniform
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

(* Coq pre 8.8 produces phantom universes, see coq/coq#6483 **)
Definition map2_lipschitz@{i} := ltac:(first [exact @map2_lipschitz'@{i i i}|exact @map2_lipschitz'@{i i i i}]).
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

(* Coq pre 8.8 produces phantom universes, see coq/coq#6483 **)
Definition map2_continuous@{i} := ltac:(first [exact @map2_continuous'@{i i i}|exact @map2_continuous'@{i i i i}]).
Arguments map2_continuous {_ _ _ _} u e.
Global Existing Instance map2_continuous.

End map2.

Section interval.
Universe UA UALE.
Context {A:Type@{UA} } {Ale : Le@{UA UALE} A}.

Definition Interval a b := sig (fun x : A => a <= x /\ x <= b).

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
  Interval_restrict a b E x = exist _ x E'.
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
- unfold close;simpl. apply _.
- intros e u. red;red. reflexivity.
- intros e u v xi;red;red;symmetry;apply xi.
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

Section rationals.

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

Instance Q_close_symm@{} : forall e, Symmetric (@close Q _ e).
Proof.
red;unfold close;simpl.
intros e x y [E1 E2];split.
- apply flip_lt_negate. rewrite <-negate_swap_r,involutive.
  trivial.
- apply flip_lt_negate.
  rewrite negate_swap_r,involutive. trivial.
Qed.

Lemma Q_triangular_one@{} : forall (q r : Q)
(e : Q+) (Hqr : close e q r)
(q0 : Q) (n : Q+),
  (close n q q0 -> close (e + n) r q0).
Proof.
unfold close;simpl.
intros q r e [E1 E1'] s n [E2 E2'].
split.
- apply flip_lt_negate. rewrite negate_swap_r,!involutive.
  apply flip_lt_negate in E2.
  rewrite negate_swap_r,!involutive in E2.
  pose proof (plus_lt_compat _ _ _ _ E1' E2) as E.
  assert (Hrw : s - r = q - r + (s - q))
    by abstract ring_tac.ring_with_integers (NatPair.Z nat).
  rewrite Hrw;trivial.
- apply flip_lt_negate in E1.
  rewrite negate_swap_r,!involutive in E1.
  pose proof (plus_lt_compat _ _ _ _ E1 E2') as E.
  assert (Hrw : r - s = r - q + (q - s))
    by abstract ring_tac.ring_with_integers (NatPair.Z nat).
  rewrite Hrw;trivial.
Qed.

Instance Q_triangular@{} : Triangular Q.
Proof.
hnf. intros u v w e d E1 E2.
apply Q_triangular_one with v.
- symmetry;trivial.
- trivial.
Qed.

Lemma Qclose_separating_not_lt : forall q r : Q, (forall e, close e q r) ->
  ~ (q < r).
Proof.
intros q r E1 E2.
pose proof (E1 (Qpos_diff _ _ E2)) as E3.
apply symmetry in E3;apply Qclose_alt in E3.
unfold cast in E3;simpl in E3.
apply (irreflexivity lt (r - q)).
apply le_lt_trans with (abs (r - q));trivial.
apply Qabs_le_raw.
Qed.

Instance Qclose_separating : Separated Q.
Proof.
hnf. intros q r E1.
apply tight_apart. intros E2.
apply apart_iff_total_lt in E2. destruct E2 as [E2|E2].
- exact (Qclose_separating_not_lt _ _ E1 E2).
- refine (Qclose_separating_not_lt _ _ _ E2).
  intros;symmetry;trivial.
Qed.

Instance Qclose_rounded@{} : Rounded Q.
Proof.
intros e q r;split.
- intros E;apply Qclose_alt in E.
  pose proof (Q_average_between _ _ E) as [E1 E2].
  apply tr;simple refine (exist _ (mkQpos ((abs (q - r) + ' e) / 2) _) _).
  { apply pos_mult_compat;[|solve_propholds].
    red. apply pos_plus_le_lt_compat_r;[solve_propholds|apply Qabs_nonneg].
  }
  simpl. exists (Qpos_diff _ _ E2).
  split.
  + apply pos_eq. exact (Qpos_diff_pr _ _ E2).
  + apply Qclose_alt. exact E1.
- apply (Trunc_ind _). intros [d [d' [He xi]]].
  apply Qclose_alt;rewrite He.
  apply Qclose_alt in xi.
  apply lt_le_trans with (' d);trivial.
  apply nonneg_plus_le_compat_r. solve_propholds.
Qed.

Global Instance Q_premetric@{} : PreMetric Q.
Proof.
split;try apply _.
intros e u;apply Qclose_alt. rewrite plus_negate_r.
unfold abs. rewrite (fst (abs_sig 0).2).
- solve_propholds.
- reflexivity.
Qed.

Global Instance Qneg_nonexpanding@{} : NonExpanding ((-) : Negate Q).
Proof.
intros e x y.
apply Qclose_neg.
Defined.


Global Instance Qplus_nonexpanding_l@{} : forall s : Q, NonExpanding (+ s).
Proof.
red. unfold close,Q_close;simpl. intros s e q r E.
assert (Hrw : q + s - (r + s) = q - r)
  by abstract ring_tac.ring_with_integers (NatPair.Z nat).
rewrite Hrw;trivial.
Qed.

Global Instance Qplus_nonexpanding_r@{} : forall s : Q, NonExpanding (s +).
Proof.
red;unfold close,Q_close;simpl. intros s e q r E.
assert (Hrw : s + q - (s + r) = q - r)
  by abstract ring_tac.ring_with_integers (NatPair.Z nat).
rewrite Hrw;trivial.
Qed.

Global Instance Qabs_nonexpanding : NonExpanding (abs (A:=Q)).
Proof.
intros e q r xi.
apply Qclose_alt in xi;apply Qclose_alt.
apply le_lt_trans with (abs (q - r));trivial.
apply Qabs_triangle_alt.
Qed.

Global Instance Qmeet_nonexpanding_l : forall s : Q, NonExpanding (⊓ s).
Proof.
intros s e q r xi.
apply Qclose_alt;apply Qclose_alt in xi.
apply le_lt_trans with (abs (q - r));trivial. clear xi.
destruct (total le q s) as [E1|E1], (total le r s) as [E2|E2];
rewrite ?(meet_l _ _ E1), ?(meet_r _ _ E1), ?(meet_l _ _ E2), ?(meet_r _ _ E2).
- reflexivity.
- rewrite (Qabs_of_nonpos (q - r))
  by (apply (snd (flip_nonpos_minus _ _)); transitivity s;trivial).
  rewrite <-negate_swap_r.
  rewrite (Qabs_of_nonpos _ (snd (flip_nonpos_minus _ _) E1)).
  rewrite <-negate_swap_r.
  apply (order_preserving (+ (- q))).
  trivial.
- rewrite (Qabs_of_nonneg (q - r))
  by (apply (snd (flip_nonneg_minus _ _)); transitivity s;trivial).
  rewrite (Qabs_of_nonneg _ (snd (flip_nonneg_minus _ _) E2)).
  apply (order_preserving (+ (- r))). trivial.
- rewrite plus_negate_r,Qabs_of_nonneg by reflexivity.
  apply Qabs_nonneg.
Qed.

Global Instance Qmeet_nonexpanding_r : forall s : Q, NonExpanding (s ⊓).
Proof.
intros s e q r xi.
pose proof meet_sl_order_meet_sl.
rewrite !(commutativity s).
apply (non_expanding (fun x => meet x s)). trivial.
Qed.

Global Instance Qjoin_nonexpanding_l : forall s : Q, NonExpanding (⊔ s).
Proof.
intros s e q r xi.
apply Qclose_alt;apply Qclose_alt in xi.
apply le_lt_trans with (abs (q - r));trivial. clear xi.
destruct (total le q s) as [E1|E1], (total le r s) as [E2|E2];
rewrite ?(join_l _ _ E1), ?(join_r _ _ E1), ?(join_l _ _ E2), ?(join_r _ _ E2).
- rewrite plus_negate_r,Qabs_of_nonneg by reflexivity.
  apply Qabs_nonneg.
- rewrite (Qabs_of_nonpos (q - r))
  by (apply (snd (flip_nonpos_minus _ _)); transitivity s;trivial).
  rewrite <-negate_swap_r.
  rewrite (Qabs_of_nonpos _ (snd (flip_nonpos_minus _ _) E2)).
  rewrite <-negate_swap_r.
  apply (order_preserving (r +)).
  apply (snd (flip_le_negate _ _)). trivial.
- rewrite (Qabs_of_nonneg (q - r))
  by (apply (snd (flip_nonneg_minus _ _)); transitivity s;trivial).
  rewrite (Qabs_of_nonneg _ (snd (flip_nonneg_minus _ _) E1)).
  apply (order_preserving (q +)).
  apply (snd (flip_le_negate _ _)). trivial.
- reflexivity.
Qed.

Global Instance Qjoin_nonexpanding_r : forall s : Q, NonExpanding (s ⊔).
Proof.
intros s e q r xi.
pose proof join_sl_order_join_sl.
rewrite !(commutativity s).
apply (non_expanding (fun x => join x s)). trivial.
Qed.

Global Instance Qmult_lipschitz@{} : forall q : Q, Lipschitz (q *.) (pos_of_Q q).
Proof.
intros q e x y xi.
apply Qclose_alt.
rewrite negate_mult_distr_r,<-plus_mult_distr_l,Qabs_mult.
apply pos_mult_le_lt_compat;try split.
- apply Qabs_nonneg.
- rewrite Qabs_is_join. apply join_le.
  + apply flip_le_negate;rewrite involutive; apply Q_abs_plus_1_bounds.
  + apply Q_abs_plus_1_bounds.
- solve_propholds.
- apply Qabs_nonneg.
- apply Qclose_alt,xi.
Qed.

Global Instance Qpos_upper_close e : Closeness (Qpos_upper e)
  := fun n x y => close n x.1 y.1.
Arguments Qpos_upper_close _ _ _ _ /.

Global Instance Q_recip_lipschitz (e : Q+)
  : Lipschitz ((/) ∘ pr1 ∘ (Qpos_upper_inject e)) (/ (e * e)).
Proof.
intros n q r xi.
unfold Compose;simpl. apply Qclose_alt.
assert (PropHolds (0 < join q (' e))) as E
  by (apply lt_le_trans with (' e);[solve_propholds|apply join_ub_r]).
apply (strictly_order_reflecting ((join q (' e)) *.)).
assert (PropHolds (0 < join r (' e))) as E'
  by (apply lt_le_trans with (' e);[solve_propholds|apply join_ub_r]).
apply (strictly_order_reflecting ((join r (' e)) *.)).
set (X := join r (' e)) at 2 3.
rewrite <-(Qabs_of_nonneg (join r _)) by solve_propholds.
set (Y := join q (' e)) at 2 3.
rewrite <-(Qabs_of_nonneg (join q _)) by solve_propholds.
rewrite <-!Qabs_mult.
rewrite !(plus_mult_distr_l (Aplus:=Qplus)).
rewrite dec_recip_inverse by (apply irrefl_neq,symmetric_neq in E;trivial).
rewrite mult_1_r.
assert (Hrw :  (r ⊔ ' e) * ((q ⊔ ' e) * - / (r ⊔ ' e)) = - Y * (X / X))
  by ring_tac.ring_with_integers (NatPair.Z nat).
rewrite Hrw;clear Hrw.
rewrite dec_recip_inverse by (apply irrefl_neq,symmetric_neq in E';trivial).
rewrite mult_1_r. unfold X, Y.
eapply lt_le_trans.
- apply Qclose_alt. eapply (non_expanding (⊔ ' e)). symmetry. apply xi.
- transitivity (' (((e * e) / (e * e)) * n)).
  + rewrite pos_recip_r,Qpos_mult_1_l;reflexivity.
  + rewrite <-!Qpos_mult_assoc.
    change (' (e * (e * (/ (e * e) * n)))) with (' e * (' e * ' (/ (e * e) * n))).
    apply mult_le_compat;try solve_propholds;[apply join_ub_r|].
    apply mult_le_compat;try solve_propholds;[apply join_ub_r|].
    reflexivity.
Qed.

End rationals.

Section cauchy.
Universe UA.
Context {A : Type@{UA} } {Aclose : Closeness A}.
Context `{!PreMetric A}.

Lemma limit_unique : forall x l1 l2, IsLimit x l1 -> IsLimit x l2 -> l1 = l2.
Proof.
intros x l1 l2 E1 E2.
apply separated.
intros e. rewrite (pos_split2 e),(pos_split2 (e/2)).
apply triangular with (x (e / 2 / 2));[symmetry;apply E1|apply E2].
Qed.

Lemma equiv_through_approx0 : forall (y : Approximation A) ly, IsLimit y ly ->
  forall u e d, close e u (y d) -> close (e+d) u ly.
Proof.
intros y ly E1 u e d xi.
apply (merely_destruct ((fst (rounded _ _ _) xi))).
intros [d0 [d' [He E2]]].
pose proof (triangular _ _ _ _ _ E2 (E1 d' _)) as E3.
assert (Hrw : e + d = d0 + (d' + d));[|rewrite Hrw;trivial].
rewrite He. symmetry. apply Qpos_plus_assoc.
Qed.

Context {Alim : Lim A} `{!CauchyComplete A}.

Lemma equiv_through_approx : forall u (y : Approximation A) e d,
  close e u (y d) -> close (e+d) u (lim y).
Proof.
intros u y;apply equiv_through_approx0. apply cauchy_complete.
Qed.

Lemma equiv_lim_lim (x y : Approximation A) (e d n e' : Q+)
  : e = d + n + e' -> close e' (x d) (y n) -> close e (lim x) (lim y).
Proof.
intros He xi.
rewrite He.
assert (Hrw : d + n + e' = e' + d + n) by (apply pos_eq;ring_tac.ring_with_nat);
rewrite Hrw;clear Hrw.
apply equiv_through_approx.
symmetry. apply equiv_through_approx. symmetry;trivial.
Qed.

Lemma lim_same_distance@{} : forall (x y : Approximation A) e,
  (forall d n, close (e+d) (x n) (y n)) ->
  forall d, close (e+d) (lim x) (lim y).
Proof.
intros x y e E d.
apply equiv_lim_lim with (d/3) (d/3) (e + d/3);[|apply E].
path_via (e + 3 / 3 * d).
- rewrite pos_recip_r,Qpos_mult_1_l;trivial.
- apply pos_eq;ring_tac.ring_with_nat.
Qed.

End cauchy.

Section lipschitz_lim.
Context {A:Type} {Aclose : Closeness A} `{!PreMetric A}
  `{Bclose : Closeness B} `{!PreMetric B} {Blim : Lim B}
   `{!CauchyComplete B}.

Global Instance lipschitz_lim_lipschitz (s : Approximation (A -> B)) L
  `{!forall e, Lipschitz (s e) L} : Lipschitz (lim s) L.
Proof.
intros e x y xi.
apply rounded in xi;revert xi;apply (Trunc_ind _);intros [d [d' [E xi]]].
rewrite E,Qpos_plus_mult_distr_l.
apply lim_same_distance.
clear e d' E.
intros d' n. simpl.
apply rounded_plus.
apply (lipschitz (s n) L). trivial.
Qed.

End lipschitz_lim.

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

Arguments Lim A {_}.
Arguments lim {A _ _} _.

Arguments Approximation A {_}.
Arguments Build_Approximation {A _} _ _.
Arguments approximate {A _} _ _.
Arguments approx_equiv {A _} _ _ _.

Arguments CauchyComplete A {_ _}.

Arguments arrow_lim {A B _ _ _} _ / _.
