Require Import HoTT minus1Trunc Bool.

Record hProp := BuildhProp {propT:> Type; isp :> IsHProp propT}.
Canonical Structure default_HProp:= fun T P => (@BuildhProp T P).
(* the eta-expansion seems needed *)

Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.
Canonical Structure default_HSet:= fun T P => (@BuildhSet T P).
Hint Resolve isp iss.

Instance hProp_is_hSet : (IsHSet hProp).
intros [p p1] [q q1].
Admitted. (* We need some lemmas about records *)

Lemma uahp `{ua:Univalence}:
  forall P P': hProp, (P->P') -> (P' -> P) -> P = P'.
intros.
destruct P, P'. (* TruncType *)
(* Need Equality on Records
apply (@path_universe_uncurried _ ). eapply ua. apply equiv_iff_hprop
*)
Admitted.

Definition epi {X Y} `(f:X->Y) := forall Z: hSet,
  forall g h: Y -> Z, g o f = h o f -> g = h.

Definition hexists {X} (P:X->Type):Type:= minus1Trunc (sigT  P).
Definition surj {X Y} (f:X->Y) := forall y:Y , hexists (fun x => (f x) = y).

Existing Instances minus1Trunc_is_prop contr_unit.

Lemma epi_surj `{fs:Funext} `{Univalence} {X Y} (f:X->Y): epi f -> surj f.
intros epif y.
set (g:=fun _:Y => (default_HProp Unit _)).
set (h:=(fun y:Y => (default_HProp
  (hexists (fun _ : Unit => {x:X & y = (f x)})) _ ))).
specialize (epif _ g h).
assert (X1: g o f = h o f ).
 apply fs; intro x. apply uahp;[|done].
 intros _ . apply min1. exists tt. by exists x.
specialize (epif X1). clear X1.
set (apD10 epif y).
apply (@minus1Trunc_map (sigT (fun _ : Unit => sigT (fun x : X => y = f x)))).
 intro X1.
  assert (X2:(sigT (fun _ : Unit => sigT (fun x : X => y = f x)) -> sigT (fun x : X => f x = y))).
  intros [ _ [x eq]]. exists x. by symmetry.
 apply (X2 X1).
apply (transport propT p tt).
Qed.

Lemma surj_epi  `{fs:Funext} {X Y} (f:X->Y): surj f -> epi f.
intros sur ? ? ? ep. apply fs. intro y.
specialize (sur y).
apply (minus1Trunc_rect_nondep (A:=(sigT (fun x : X => f x = y))));
  try assumption.
 intros [x p]. set (p0:=apD10 ep x).
 path_via (g (f x)). by apply ap.
 path_via (h (f x)). by apply ap.
intros. by apply @set_path2.
Qed.
