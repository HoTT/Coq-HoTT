Require Import Basics.
Require Import Types.Universe.
Require Import Types.Sigma.
Require Import HIT.Circle.
Require Import HIT.Pushout.
Require Import HIT.Flattening.


Section FibrationOverPushout.
  Context `{Univalence}.

  Notation ua := path_universe_uncurried.

  Context {X Y Z : Type}.

  Context {j : X -> Y}.
  Context {k : X -> Z}.

  Context {E_Y : Y -> Type}.
  Context {E_Z : Z -> Type}.

  Context {e_X : forall x, E_Y (j x) <~> E_Z (k x)}.

  (* Lemma 8.5.3 of HoTT book *)
  Lemma fibration_pushout : pushout j k -> Type.
  Proof.
    srapply (pushout_ind j k).
    + refine E_Y.
    + refine E_Z.
    + intro x; compute; induction (cp x).
      refine (ua (e_X x)).
  Defined.

  Let E_Y_total := {y : Y & E_Y y}.
  Let E_Z_total := {z : Z & E_Z z}.
  Let E_push_total := {p : pushout j k & fibration_pushout p}.

  Let E_X_total  := {x : X & E_Y (j x)}.
  Let E_X_total' := {x : X & E_Z (k x)}.

  Lemma E_X_total_equiv_E_X_total' : E_X_total <~> E_X_total'.
  Proof.
    apply (@equiv_functor_sigma _ _ _ _ idmap _ e_X _).
  Qed.

  Let j_x_id : E_X_total -> E_Y_total 
    := @functor_sigma _ (E_Y o j) _ _ j (fun a => idmap).
  Let k_x_id : E_X_total' -> E_Z_total
    := @functor_sigma _ (E_Z o k) _ _ k (fun a => idmap).
  Let k_x_id' := k_x_id o E_X_total_equiv_E_X_total'.

  Let A := Y + Z.
  Let B := X.
  Let f : B -> A := inl o j.
  Let g : B -> A := inr o k.
  Let C : A -> Type := fun a => 
    match a with
      | inl y => E_Y y
      | inr z => E_Z z
    end.

  Lemma fibration_pushout_equiv_pushout_fibrations :
    E_push_total <~> pushout j_x_id k_x_id'.
  Proof.
    srapply (@equiv_compose').
    + apply (Wtil A B f g C e_X).
    + admit.
    + unfold E_push_total.
      unfold pushout.
      unfold fibration_pushout.
(*       srapply (equiv_inverse (@equiv_flattening _ B A f g C e_X)). *)
  Admitted.

End FibrationOverPushout.

Section HSpace.
  Context `{Funext}.


  Record HSpace := {
    space :> Type;
    base : space;
    mu : space -> space -> space;
    left_id : forall a, mu base a = a;
    right_id : forall a, mu a base = a
  }.

  Require Import Types.Equiv.
  Require Import HIT.Truncations.
  Import TrM.
  

  Context (A : HSpace).
  Context `{IsConnected 0 A}.

(*

Lean code

definition fiber_const_equiv [constructor] (A : Type) (a₀ : A) (a : A)
    : fiber (λz : unit, a₀) a ≃ a₀ = a :=
  calc
    fiber (λz : unit, a₀) a
      ≃ Σz : unit, a₀ = a : fiber.sigma_char
... ≃ a₀ = a : sigma_unit_left

definition is_equiv_mul_left [instance] : Π(a : A), is_equiv (λx, a * x) :=
  begin
    apply is_conn_fun.elim -1 (is_conn_fun_from_unit -1 A 1)
                           (λa, trunctype.mk' -1 (is_equiv (λx, a * x))),
    intro z, change is_equiv (λx : A, 1 * x), refine is_equiv.homotopy_closed id _ _,
    intro x, apply inverse, apply one_mul
end

protected definition elim : (Πa : A, P (h a)) → (Πb : B, P b) :=
@is_equiv.inv _ _ (λs a, s (h a)) rec

definition is_conn_fun_from_unit (a₀ : A) [H : is_conn n .+1 A]
      : is_conn_fun n (const unit a₀) :=
    begin
      intro a,
      apply is_conn_equiv_closed n (equiv.symm (fiber_const_equiv A a₀ a)),
      apply is_contr_equiv_closed (tr_eq_tr_equiv n a₀ a) _,
end

*)




  Lemma mu_l_equiv : forall (a : A), IsEquiv (A.(mu) a).
  Proof.
    erapply (conn_map_elim -1 _ _).
  Admitted.

  Lemma mu_r_equiv : forall (a : A), IsEquiv (fun x => mu _ x a).
  Proof.
    apply (conn_map_elim -1 _ _).
(*     isconnected_equiv *)
  Admitted.

End HSpace.








(** Hopf fibrations **)

(* Real hopf fibration *)