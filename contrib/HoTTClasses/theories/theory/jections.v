Require Import
  HoTT.Types.Arrow
  HoTT.Types.Universe
  HoTT.Basics.Trunc
  HoTT.HIT.Truncations.
Require Import
  HoTTClasses.interfaces.abstract_algebra.

Lemma injective_ne `(f : A -> B) `{!Injective f} x y :
  x <> y -> f x <> f y.
Proof.
intros E1 E2. apply E1.
apply (injective f).
assumption.
Qed.

Section surjective_factor.
Context `{Funext}.
Context `{IsHSet C} `(f : A -> C) `(g : A -> B) {Esurj : IsSurjection g}.
Variable (Eg : forall x y, g x = g y -> f x = f y).

Definition is_img (x : B) (y : C) := merely (exists z : A, x = g z /\ y = f z).

Definition surjective_factor_auxT x := sigT (fun y => is_img x y).

Instance surjective_factor_aux_ishprop
  : forall x, IsHProp (surjective_factor_auxT x).
Proof.
intros. apply Sigma.ishprop_sigma_disjoint.
unfold is_img;intros y1 y2 E1;apply (Trunc_ind _);intros [z2 [E3 E4]].
revert E1;apply (Trunc_ind _);intros [z1 [E1 E2]].
path_via (f z1);path_via (f z2).
apply Eg. path_via x.
Qed.

Definition surjective_factor_aux : forall x, surjective_factor_auxT x.
Proof.
intros x. generalize (center _ (Esurj x)). apply (Trunc_ind _).
intros z. exists (f z.1).
apply tr. exists z.1;split;trivial. symmetry;exact z.2.
Defined.

Definition surjective_factor : B -> C :=
  fun x => (surjective_factor_aux x).1.

Lemma surjective_factor_pr : f = compose surjective_factor g.
Proof.
apply path_forall. intros x.
unfold surjective_factor,surjective_factor_aux,Compose. simpl.
set (Y := (center
           (TrM.Os_ReflectiveSubuniverses.O_reflector
              (modality_to_reflective_subuniverse (trunc_S minus_two))
              (hfiber g (g x))))).
generalize Y. clear Y.
apply (Trunc_ind _).
intros Y. simpl.
apply Eg. symmetry;apply Y.2.
Qed.

End surjective_factor.
