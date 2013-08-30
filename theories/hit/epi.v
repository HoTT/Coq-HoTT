Require Import HoTT minus1Trunc HProp Misc TruncType.

Open Scope path_scope.
Open Scope equiv_scope.

Section AssumingUA.
(** The univalence axiom for HProp *)
(** We need fs to be able to find hprop_trunc *)
Context `{fs:Funext} `{ua:Univalence}.
Lemma uahp' : forall P P': sigT IsHProp, (P.1<->P'.1) -> P = P'.
intros ? ? X. apply (equiv_path_sigma_hprop P P'). apply ua. 
destruct P, P'. destruct X.
by apply equiv_iff_hprop.
Defined.

Lemma uahp'' : forall P P': sigT IsHProp, P = P' -> (P.1<->P'.1).
intros ?? p. by destruct p.
Defined.

Lemma uahp_biimp :
 forall P P': sigT IsHProp, (P.1<->P'.1) <~> (P = P').
intros.
apply equiv_adjointify with (uahp' P P') (uahp'' P P').
- intro x. destruct x. eapply allpath_hprop.
- intros x. cut (IsHProp (P .1 <-> P' .1)). intro H. apply allpath_hprop.
  cut (Contr(P .1 <-> P' .1)). intro. apply trunc_succ.
  exists x. intro y. destruct y as [y1 y2]. destruct x as [x1 x2].
f_ap; apply fs; intro x; [apply P'.2| apply P.2].
Defined.

(** The variant of [uahp] for record types. *)
Lemma uahp_rec {P P':hProp}: (P->P') -> (P'->P) -> P = P'.
set (p:=issig_hProp^-1 P).
set (p':=issig_hProp^-1 P').
intros X X0.
assert (p=p') by (by apply uahp_biimp). 
clear X X0. 
path_via (issig_hProp (issig_hProp ^-1 P)); destruct P. reflexivity.
path_via (issig_hProp (issig_hProp ^-1 P')); destruct P';[f_ap|reflexivity].
Defined.

(** We will now prove that for sets epis and surjections are biequivalent.*)
Definition epi {X Y} `(f:X->Y) := forall Z: hSet,
  forall g h: Y -> Z, g o f = h o f -> g = h.

Definition surj {X Y} (f:X->Y) := forall y:Y , hexists (fun x => (f x) = y).

Lemma surj_epi {X Y} (f:X->Y): surj f -> epi f.
intros sur ? ? ? ep. apply fs. intro y.
specialize (sur y).
apply (minus1Trunc_rect_nondep (A:=(sigT (fun x : X => f x = y))));
  try assumption.
 intros [x p]. set (p0:=apD10 ep x).
 path_via (g (f x)). by apply ap.
 path_via (h (f x)). by apply ap.
intros. by apply @set_path2.
Qed.

Require Import FunextAxiom.
Lemma epi_surj {X Y} (f:X->Y): epi f -> surj f.
intros epif y.
set (g:=fun _:Y => (default_HProp (Unit:Type) _)).
set (h:=(fun y:Y => (default_HProp
  (hexists (fun _ : Unit => {x:X & y = (f x)})) _ ))).
specialize (epif _ g h).
assert (X1: g o f = h o f ).
 apply funext_axiom; intro x. apply uahp_rec;[|done].
 intros _ . apply min1. exists tt. by exists x.
specialize (epif X1). clear X1.
set (p:=apD10 epif y).
apply (@minus1Trunc_map (sigT (fun _ : Unit => sigT (fun x : X => y = f x)))).
 intros [ _ [x eq]].
  assert (X2: sigT (fun x : X => f x = y)) by (exists x; by symmetry).
 apply X2.
apply (transport hProp2Type p tt).
Defined.

End AssumingUA.