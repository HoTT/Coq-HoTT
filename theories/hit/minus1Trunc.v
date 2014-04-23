(** * (-1)-truncation *)

Require Import Overture HProp EquivalenceVarieties Contractible Equivalences types.Unit.
Open Local Scope path_scope.
(** The definition of [minus1Trunc], the (-1)-truncation.  Here is what
   it would look like if Coq supported higher inductive types natively:

<<
   Inductive minus1Trunc (A : Type) : Type :=
   | min1 : A -> minus1Trunc A
   | min1_path : forall (x y: minus1Trunc A), x = y
>>
*)

Module Export minus1Trunc.

Local Inductive minus1Trunc (A :Type) : Type :=
  min1 : A -> minus1Trunc A.
Axiom min1_path : forall {A : Type} (x y : minus1Trunc A),  x = y.
Arguments min1 {A} a.

Definition minus1Trunc_rect :
  forall {A : Type} {P : minus1Trunc A -> Type}
    (dmin1 : forall a : A, P (min1 a))
    (dpath : forall {x y : minus1Trunc A} (z : P x) (w : P y), transport _ (min1_path x y) z = w)
    (x : minus1Trunc A), P x.
intros ???? [x]. apply dmin1.
Defined.

Definition minus1Trunc_compute_min1 : forall {A : Type} {P : minus1Trunc A -> Type}
  (dmin1 : forall (a : A), P (min1 a))
  (dpath : forall (x y : minus1Trunc A) (z : P x) (w : P y), transport _ (min1_path x y) z = w),
  forall (a : A), minus1Trunc_rect dmin1 dpath (min1 a) = dmin1 a.
reflexivity.
Defined.

Axiom minus1Trunc_compute_path : forall {A : Type} {P : minus1Trunc A -> Type}
  (dmin1 : forall (a : A), P (min1 a))
  (dpath : forall (x y : minus1Trunc A) (z : P x) (w : P y), transport _ (min1_path x y) z = w),
  forall (x y : minus1Trunc A),
    apD (minus1Trunc_rect dmin1 dpath) (min1_path x y)
    = dpath x y (minus1Trunc_rect dmin1 dpath x) (minus1Trunc_rect dmin1 dpath y).
End minus1Trunc.

(** By adding the following [Hint Resolve] we can simply use the [auto] tactic
   to resolve any path involving [is_inhab]. *)

Hint Resolve @min1_path @minus1Trunc_compute_min1 @minus1Trunc_compute_path.

(** ** The non-dependent version of the eliminator. *)

Definition minus1Trunc_rect_nondep {A B : Type} :
  (A -> B) -> (forall (z w : B), z = w) -> (minus1Trunc A -> B).
Proof.
  intros dmin1' dpath'.
  by apply minus1Trunc_rect.
Defined.

Definition minus1Trunc_compute_min1_nondep {A B : Type}
  (dmin1' : A -> B) (dpath' : forall (z w : B), z = w) (a : A) :
  minus1Trunc_rect_nondep dmin1' dpath' (min1 a) = (dmin1' a).
Proof.
  apply @minus1Trunc_compute_min1 with (P := fun a => B).
Defined.

Definition minus1Trunc_compute_path_nondep {A B : Type}
  (dmin1' : A -> B) (path' : forall (z w : B), z = w)
  (x y : minus1Trunc A) :
  ap (minus1Trunc_rect_nondep dmin1' path') (min1_path x y)
  = path' (minus1Trunc_rect_nondep dmin1' path' x) (minus1Trunc_rect_nondep dmin1' path' y).
Proof.
 apply (@path_contr ).
 by apply hprop_allpath.
Defined.
(** ** [minus1Trunc A] is always a proposition. *)

Instance minus1Trunc_is_prop {A : Type} : IsHProp (minus1Trunc A) | 0.
Proof.
  apply hprop_allpath, min1_path.
Defined.

Definition minus1Trunc_ind {A B : Type} `{IsHProp B} :
  (A -> B) -> minus1Trunc A -> B.
Proof.
intros ?. apply minus1Trunc_rect_nondep. assumption.
apply allpath_hprop.
Defined.

(** And if [A] was already a proposition, then [minus1Trunc A] is equivalent to [A]. *)
Instance IsEquivmin1 {A} `{IsHProp A} : IsEquiv (@min1 A) | 1000.
Proof.
  apply (@isequiv_adjointify _ _ (@min1 A) (minus1Trunc_rect_nondep (fun x:A => x) allpath_hprop )).
   intro x. apply hprop_allpath, min1_path.
  intro a. apply allpath_hprop.
Defined.

Section AssumeFunext.
(** ** Inhabited propositions are contractible. *)
Open Scope fibration_scope.
Context `{Funext}.

Lemma inhab_prop_contr {A} : (IsHProp A) -> minus1Trunc A -> Contr A.
Proof.
  intros prp.
  apply minus1Trunc_rect_nondep.
    by apply contr_inhabited_hprop.
  intros. eapply allpath_hprop.
Defined.

Require Import HProp Fibrations.

(** ** "Epi" and "mono" implies equivalence. *)

Definition is_epi {X Y : Type} (f : X -> Y) :=
  forall y:Y, minus1Trunc (hfiber f y).

Definition is_mono {X Y : Type} (f : X -> Y) :=
  forall y:Y, IsHProp (hfiber f y).

Lemma epi_mono_equiv {X Y : Type} (f : X -> Y) :
  is_epi f -> is_mono f -> IsEquiv f.
Proof.
  intros epi mono.
  apply contr_inhabited_hprop.
   apply hprop_isequiv.
  apply  isequiv_fcontr. intro b.
  apply (inhab_prop_contr (mono b) (epi b)).
Defined.
End AssumeFunext.

Section minus1TruncMonad.

(** ** The monadic structure of [minus1Trunc].

    This is pretty easy to check since any diagram involving propositions commutes. *)

(** We first need the action of [minus1Trunc] on morphisms. *)
Definition minus1Trunc_map_dep {A B}
: (forall x : A, B (min1 x)) -> (forall x : minus1Trunc A, minus1Trunc (B x)).
Proof.
  intros f.
  apply (@minus1Trunc_rect A (fun x => minus1Trunc (B x))
                           (fun x => min1 (f x))); auto.
Defined.

Definition minus1Trunc_map {A B : Type} : (A -> B) -> (minus1Trunc A -> minus1Trunc B)
  := @minus1Trunc_map_dep A (fun _ => B).

(** *** Functoriality of [minus1Trunc_map]. *)
Lemma minus1Trunc_map_id {A : Type} :
  forall (p : minus1Trunc A), minus1Trunc_map (fun x => x) p = p.
Proof.
  auto.
Defined.

Lemma minus1Trunc_map_compose {A B C : Type} (f : A -> B) (g : B -> C):
  forall (p : minus1Trunc A), minus1Trunc_map (compose g f) p = minus1Trunc_map g (minus1Trunc_map f p).
Proof.
  auto.
Defined.

(** *** The unit. *)
Definition eta := @min1.

(** *** Naturality of unit. *)
Lemma eta_natural {A B : Type} (f : A -> B) :
  forall a : A, eta B (f a) = minus1Trunc_map f (eta A a).
Proof.
  auto.
Defined.

(** *** The multiplication. *)
Definition mu (A : Type) : minus1Trunc (minus1Trunc A) -> minus1Trunc A.
Proof.
  intros p. apply @minus1Trunc_rect_nondep with (A := minus1Trunc A); auto.
Defined.

(** *** Naturality of multiplication. *)
Lemma mu_natural {A B : Type} (f : A -> B) :
  forall p : minus1Trunc (minus1Trunc A),
    mu B (minus1Trunc_map (minus1Trunc_map f) p) = minus1Trunc_map f (mu A p).
Proof.
  auto.
Qed.

(** *** Unit laws. *)
Lemma eta_1 (A : Type) :
  forall p : minus1Trunc A, mu A (eta (minus1Trunc A) p) = p.
Proof.
  auto.
Qed.

Lemma eta_2 (A : Type) :
  forall p : minus1Trunc A, mu A (minus1Trunc_map (eta A) p) = p.
Proof.
  auto.
Qed.

Lemma mu_1 (A : Type) :
  forall p : minus1Trunc (minus1Trunc (minus1Trunc A)),
    mu A (minus1Trunc_map (mu A) p) = mu A (mu (minus1Trunc A) p).
Proof.
  auto.
Qed.

(** *** The strength. *)
Lemma t (A B : Type) : A * minus1Trunc B -> minus1Trunc (A * B).
Proof.
  intros [a q].
  apply (minus1Trunc_rect_nondep (A := B)); auto.
  intro b. apply min1; auto.
Defined.

(** *** Naturality of strength. *)
Lemma t_natural (A A' B B' : Type) (f : A -> A') (g : B -> B') :
  forall (a : A) (q : minus1Trunc B),
    minus1Trunc_map (fun xy => (f (fst xy), g (snd xy))) (t A B (a,q)) = t A' B' (f a, minus1Trunc_map g q).
Proof.
  auto.
Qed.

(* The diagrams for strength, see http://en.wikipedia.org/wiki/Strong_monad *)

Lemma strength_unit (A : Type) :
  forall p : Unit * minus1Trunc A,
    minus1Trunc_map (@snd Unit A) (t Unit A p) = snd p.
Proof.
  auto.
Qed.

Lemma strength_eta (A B : Type) :
  forall (a : A) (b : B),
    t A B (a, eta B b) = eta (A * B) (a,b).
Proof.
  auto.
Qed.

Definition alpha A B C (u : (A * B) * C) := (fst (fst u), (snd (fst u), snd u)).

Lemma strength_pentagon_1 (A B C : Type) :
  forall (a : A) (b : B) (r : minus1Trunc C),
    minus1Trunc_map (alpha A B C) (t (A * B) C ((a,b),r)) =
    t A (B * C) (a, t B C (b, r)).
Proof.
  auto.
Qed.

Lemma strength_pentagon_2 (A B : Type) :
  forall (a : A) (p : minus1Trunc (minus1Trunc B)),
    mu (A * B) (minus1Trunc_map (t A B) (t A (minus1Trunc B) (a, p))) = t A B (a, mu B p).
Proof.
  auto.
Qed.

End minus1TruncMonad.

(** We may want to define the other connectives to at some point. *)
Definition hexists {X} (P:X->Type):Type:= minus1Trunc (sigT  P).

(** If the goal is an hProp, we may remove [minus1Trunc] in hypotheses. *)
Ltac strip_truncations :=
  (** get the type of the goal *)
  let G := match goal with |- ?G => constr:(G) end in
  (** prove that the goal is an hProp *)
  let H := fresh in
  assert (H : forall z w : G, z = w) by apply allpath_hprop;
    (** search for truncated hypotheses *)
    progress repeat match goal with
                      | [ T : _ |- _ ]
                        => revert T;
                          refine (@minus1Trunc_rect_nondep _ _ _ H);
                          intro T
                    end;
    (** clear the IsHProp hypothesis *)
    clear H.

(** Define a lengthy pun for the above tactic. *)
Ltac since_the_goal_is_a_mere_proposition_we_may_strip_truncations
  := strip_truncations.
