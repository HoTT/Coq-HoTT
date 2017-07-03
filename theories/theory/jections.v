Require Import
  HoTT.Types.Arrow
  HoTT.Types.Universe
  HoTT.Basics.Trunc
  HoTT.HIT.Truncations.
Require Import
  HoTTClasses.interfaces.abstract_algebra.

Lemma injective_compose_cancel `{Funext} {A B C : Type} (f : B → C)
    `{!Injective f} {g : A → B} {h : A → B} :
  f ∘ g = f ∘ h → g = h.
Proof.
  intros E. apply path_arrow;intros x.
  apply (injective f).
  apply (ap (fun F => F x) E).
Qed.

Lemma surjective_applied {A B : Type} (f : A → B) `{!Inverse f} `{!Surjective f} x
 : f (f⁻¹ x) = x.
Proof.
change ((f ∘ (f ⁻¹)) x = id x).
apply (ap (fun F => F x)).
apply (surjective f).
Qed.

Lemma bijective_cancel_left {A B : Type} (f : A → B) `{!Inverse f}
  `{!Bijective f} x y
 : f x = y → x = f⁻¹ y.
Proof.
  intros E.
  apply (injective f).
  rewrite (surjective_applied f).
  assumption.
Qed.

Lemma bijective_cancel_inverse_left {A B : Type} (f : A → B)
  `{!Inverse f} `{!Bijective f} x y
  : f⁻¹ x = y → x = f y.
Proof.
  intros E.
  rewrite <-E, (surjective_applied f).
  reflexivity.
Qed.

Lemma bijective_applied `(f : A → B) `{!Inverse f} `{!Bijective f} x: f⁻¹ (f x) = x.
Proof.
  symmetry. apply (bijective_cancel_left f). reflexivity.
Qed.

Lemma bijective `{Funext} `(f : A → B) `{!Inverse f} `{!Bijective f} : f⁻¹ ∘ f = id.
(* a.k.a. "split-mono" *)
Proof.
  apply path_forall. intros x.
  apply (bijective_applied f).
Qed.

Lemma injective_ne `(f : A → B) `{!Injective f} x y :
  x ≠ y → f x ≠ f y.
Proof.
intros E1 E2. apply E1.
apply (injective f).
assumption.
Qed.

Instance id_inverse {A} : Inverse (@id A) := (@id A).

Instance id_injective {A : Type} : Injective (@id A).
Proof. red;trivial. Qed.
Instance id_surjective {A : Type} : Surjective (@id A).
Proof. red;trivial. Qed.
Instance id_bijective {A : Type} : Bijective (@id A).
Proof. split; try apply _. Qed.

Section compositions.
  Context {A B C : Type} (g: A → B) (f: B → C) `{!Inverse f} `{!Inverse g}.

  Instance compose_inverse: Inverse (f ∘ g) := g⁻¹ ∘ f⁻¹.

  Instance compose_injective: Injective f → Injective g → Injective (f ∘ g).
  Proof.
  red;intros.
  apply (injective g).
  apply (injective f).
  assumption.
  Qed.

  Instance compose_surjective : Surjective f → Surjective g →
    Surjective (f ∘ g).
  Proof.
  red;intros.
  change (compose f (compose (compose g (inverse g)) (inverse f)) = id).
  rewrite (surjective g).
  apply (surjective f).
  Qed.

  Instance compose_bijective : Bijective f → Bijective g → Bijective (f ∘ g)
    := {}.
End compositions.

Hint Extern 4 (Inverse (_ ∘ _)) =>
  class_apply @compose_inverse : typeclass_instances.
Hint Extern 4 (Injective (_ ∘ _)) =>
  class_apply @compose_injective : typeclass_instances.
Hint Extern 4 (Surjective (_ ∘ _)) =>
  class_apply @compose_surjective : typeclass_instances.
Hint Extern 4 (Bijective (_ ∘ _)) =>
  class_apply @compose_bijective : typeclass_instances.

Lemma alt_Build_Injective `(f : A → B) `{!Inverse f} : f⁻¹ ∘ f = id → Injective f.
Proof.
intros E x y F.
path_via (id x).
rewrite <- (ap (fun F => F x) E).
path_via (id y); rewrite <- (ap (fun F => F y) E).
unfold compose. rewrite F. reflexivity.
Qed.

Lemma alt_Build_Bijective `(f : A → B) `{!Inverse f} :
  f⁻¹ ∘ f = id → f ∘ f⁻¹ = id → Bijective f.
Proof.
intros. split.
- apply (alt_Build_Injective f). assumption.
- red; assumption.
Qed.

Definition inverse_inverse `{Inverse A B f} : Inverse (f⁻¹) := f.
Hint Extern 4 (Inverse (_ ⁻¹)) =>
  class_apply @inverse_inverse : typeclass_instances.

Lemma flip_bijection `{Funext} `{Bijective A B f} : Bijective (f⁻¹).
Proof.
apply alt_Build_Bijective.
- apply (surjective f).
- apply path_forall. intros x.
  apply (bijective_applied f).
Qed.

(* We use this instead of making flip_bijection a real instance, because
   otherwise it gets applied too eagerly, resulting in cycles. *)
Hint Extern 4 (Bijective (_ ⁻¹)) => apply flip_bijection : typeclass_instances.

Lemma inverse_involutive `(f : A → B) `{!Inverse f} : (f⁻¹)⁻¹ = f.
Proof. reflexivity. Qed.

(* This second version is strictly for manual application. *)
Lemma flip_bijection_back `{Funext} `(f: A → B) `{!Inverse f}
 : Bijective (f⁻¹) → Bijective f.
Proof. intro. apply (_: Bijective (f⁻¹⁻¹)). Qed.

Ltac setoid_inject :=
  match goal with
  | E : _ = ?f _ |- _ => apply (injective f) in E
  | E : ?f _ = _ |- _ => apply (injective f) in E
  | E : _ = _ |-  ?G => change (id G); injection E; clear E; intros;
    unfold id at 1 
  end.


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
unfold surjective_factor,surjective_factor_aux,compose. simpl.
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
