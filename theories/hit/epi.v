Require Import HoTT FunextAxiom minus1Trunc UnivalenceAxiom.

(* This is an experiment, if it works we should 
  apply this technique generally *)
Class hProp :={propT:> Type; isp :> IsHProp propT}.
Coercion propT:hProp >-> Sortclass.
Class hSet :={setT:>Type; iss :> IsHSet setT}.
Coercion setT:hSet >-> Sortclass.

Instance hProp_is_hSet : (IsHSet hProp).
intros [p p1] [q q1].
Admitted. (* We need some lemmas about records *)

Instance hProp_as_hSet : hSet:=  (Build_hSet _ hProp_is_hSet).

Definition epi {X Y} `(f:X->Y) := forall Z: hSet, 
  forall g h: Y -> Z, g o f = h o f -> g = h.

(* min1 will automatically create an hProp *)
Instance min1P (A:Type):hProp:=
 {| propT := minus1Trunc A; isp := minus1Trunc_is_prop |}.

Definition hexists {X} (P:X->Type):hProp:= min1P (sigT  P).

Definition surj {X Y} (f:X->Y) := forall y:Y , hexists (fun x => (f x) = y).

Instance htrue: hProp.
apply (Build_hProp Unit). apply _.
Defined.

Definition htt:htrue:=tt.

Lemma uahp `{ua:Univalence}: 
  forall P P':hProp,(P->P') -> (P' -> P) -> P = P'.
intros. 
destruct P, P'.
(* Need Equality on Records 
apply (@path_universe_uncurried _ ). eapply ua. apply equiv_iff_hprop
*)
Admitted.

Lemma epi_surj `{fs:Funext} {X Y} (f:X->Y): epi f -> surj f.
intros epif y.
set (g:=fun _:Y => htrue).
set (h:=fun y:Y => (hexists (fun _ : Unit => {x:X & y = (f x)}))).
specialize (epif _ g h).
assert (X1: g o f = h o f ).
 apply fs; intro x. apply uahp;[|done]. 
 intros _ . apply min1. exists tt. by exists x. 
specialize (epif X1). clear X1.
set (apD10 epif y).
apply (@minus1Trunc_map (sigT (fun _ : htrue => sigT (fun x : X => y = f x)))).
 intro X1.
  assert (X2:(sigT (fun _ : htrue => sigT (fun x : X => y = f x)) -> sigT (fun x : X => f x = y))).
  intros [ _ [x eq]]. exists x. by symmetry.
 apply (X2 X1).
Let tmp {A B:hProp} : A -> (A = B)->B.
intros a p. induction p. exact a.
Defined.
apply (tmp htt p).
Qed.

Lemma surj_epi  `{fs:Funext} {X Y} (f:X->Y): surj f -> epi f.
intros sur ? ? ? ep. apply fs. intro y.
specialize (sur y).
apply (minus1Trunc_rect_nondep (A:=(sigT (fun x : X => f x = y)))); try assumption.
 intros [x p]. set (p0:=apD10 ep x).
 path_via (g (f x)). by apply ap. 
 path_via (h (f x)). by apply ap.
intros. apply set_path2.
Qed.
