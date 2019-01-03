Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Equivalences.
Require Import Basics.Trunc.

Require Import Types.Universe.
Require Import Types.Sigma.
Require Import Types.Equiv.
Require Import Types.Bool.
Require Import Types.Paths.
Require Import Types.Arrow.

Require Import HIT.Circle.
Require Import HIT.Pushout.
Require Import HIT.Truncations.
Require Import HIT.Flattening.
Require Import HIT.Suspension.
Require Import HIT.Join.
Require Import HIT.Spheres.

Require Import Modalities.ReflectiveSubuniverse.

Require Import NullHomotopy.
Require Import UnivalenceAxiom.
Require Import UnivalenceImpliesFunext.

Import TrM.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.


Notation ua := path_universe_uncurried.

Section FibrationOverPushout.

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
    + intro x; destruct (pp x); simpl.
      apply (ua (e_X x)).
  Defined.

  Let E_Y_total := {y : Y & E_Y y}.
  Let E_Z_total := {z : Z & E_Z z}.
  Let E_push_total := {p : pushout j k & fibration_pushout p}.

  Let E_X_total  := {x : X & E_Y (j x)}.
  Let E_X_total' := {x : X & E_Z (k x)}.

  Lemma E_X_total_equiv_E_X_total' : E_X_total <~> E_X_total'.
  Proof.
    apply (@equiv_functor_sigma _ _ _ _ idmap _ e_X _).
  Defined.

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

  (* Needs flattening lemma *)
  Lemma fibration_pushout_equiv_pushout_fibrations :
    E_push_total <~> pushout j_x_id k_x_id'.
  Proof.
    srapply (@equiv_compose').
    + apply (Wtil A B f g C e_X).
    + admit.
    + unfold E_push_total.
      unfold pushout.
      unfold fibration_pushout.
      apply (equiv_inverse).
      (*serapply (@equiv_flattening).
      refine (@equiv_flattening _ B A f g C e_X).*)
      admit.
  Admitted.

End FibrationOverPushout.

Section ConnLemma. 

  Lemma hfiber_const_equiv (A : Type) (ab a : A) : 
    hfiber (@const Unit _ ab) a <~> ab = a.
  Proof.
    compute.
    serapply (equiv_adjointify).
    + intro; destruct X as [_ x]; apply x.
    + intro p; apply (tt; p).
    + compute; reflexivity.
    + intro; destruct x; destruct proj1_sig.
      reflexivity.
  Defined.

(* Small lemma about connectivity of constant map 
   should probably be in ReflectiveSubuniverse.v 
   but this isn't a lemma about a single universe. *)

  Lemma conn_map_from_unit_isconnected {A : Type} (b : A)
          `{IsConnected n.+1 A}
  : IsConnMap n (@const Unit A b).
  Proof.
    intro a.
    apply (isconnected_equiv' n _ (hfiber_const_equiv b a)^-1). 
    apply (contr_equiv' ((Trunc n) (b = a))).
    + reflexivity.
    + apply (contr_trunc_conn n).
  Defined.

End ConnLemma.

Section HSpace.
  Context `{Funext}.

  Class IsHSpace (space : Type) := {
    id : space;
    mu : space -> space -> space;
    left_id : forall a, mu id a = a;
    right_id : forall a, mu a id = a
  }.

  Context {A : Type}.
  Context `{IsHSpace A}.
  Context `{IsConnected 0 A}.

  Lemma mu_l_equiv' : forall (a : A), IsEquiv (mu a).
  Proof.
    intro.
  Admitted.

    (* srefine (@conn_map_elim -1 _ _ _ (conn_map_from_unit_isconnected -1 id) (fun a => IsEquiv (mu a))).

     srefine (@conn_map_elim -1 _ _ _ _ _ _).
     intro. refine (IsEquiv (mu x)).
     + srefine (fun x => Tr -1 (IsEquiv (fun y => mu x y))).
  Admitted.  *)
(* Lean:
apply is_conn_fun.elim -1 (is_conn_fun_from_unit -1 A 1)
(λa, trunctype.mk' -1 (is_equiv (λx, a * x))) *)

  Lemma mu_r_equiv' : forall (a : A), IsEquiv (fun x => mu x a).
  Proof.
    serapply (conn_map_elim -1).
  Admitted.

  Lemma mu_l_equiv : forall (a : A), A <~> A.
  Proof.
    intro; apply (BuildEquiv _ _ _ (mu_l_equiv' a)).
  Defined.

  Lemma mu_r_equiv : forall (a : A), A <~> A.
  Proof.
    intro; apply (BuildEquiv _ _ _ (mu_r_equiv' a)).
  Defined.

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

End HSpace.


Section Suspension.
  Context {X : Type}.

  (** The suspension ΣX can be written as a pushout: 1 ⊔_X 1 **)
  Lemma susp_equiv_pushout : Susp X <~> pushout (@const X _ tt) (const tt).
  Proof.
    serapply (equiv_adjointify).
      + refine (Susp_rec (pushl tt) (pushr tt) pp).
      + refine (pushout_rec _ (const North) (const South) merid).
      + unfold Sect.
        srapply (pushout_ind (@const X _ tt) (const tt)).
        * intro b; destruct b; reflexivity.
        * intro c; destruct c; reflexivity.
        * intro a. simpl.
          rewrite transport_paths_FlFr.
          rewrite_moveR_Mp_p.
          hott_simpl.
          admit.
      + admit.
  Admitted.
End Suspension.

Section HopfConstruction.

  Context {X : Type}.
  Context `{IsHSpace X}.
  Context `{IsConnected 0 X}.

  (** Hopf construction **)
  Definition susp_fibration : Susp X -> Type.
  Proof.
    rewrite (ua (susp_equiv_pushout)).
    serapply (@fibration_pushout _ _ _ _ _).
      apply (fun _ => X).
      apply (fun _ => X).
      intro x; refine (mu_l_equiv x).
  Defined.

  (** Fiber of hopf construction **)
  Lemma susp_fibration_fiber : forall x, susp_fibration x <~> X.
  Proof.
    intro x.
    serapply (equiv_adjointify).
    + intro.
  Admitted.

  (** Total space of hopf construction **)
  Lemma susp_fibration_total : {x : Susp X & susp_fibration x} <~> join X X.
  Proof.
    serapply (equiv_adjointify).
    + intro x. destruct x as [x fib].
      rewrite (ua (susp_fibration_fiber x)) in fib.
      apply (pushl fib).
    + serapply (pushout_ind).
      * intro; srefine (North;_); simpl.
        rewrite (ua (susp_fibration_fiber _)). 
        refine b.
      * intro; srefine (South;_); simpl.
        rewrite (ua (susp_fibration_fiber _)). 
        refine c.
      * simpl.
      
        refine (North; _).
    
    intro x. destruct x as [x fib].
      rewrite (ua (susp_fibration_fiber x)) in fib.
      apply (pushr fib).
      revert fib; revert SX.
      serapply (Susp_ind).
      * simpl. intro. apply susp_fibration_fiber.
      
  Admitted.

End HopfConstruction.

(** Now in order to get the hopf fibrations we "simply" need to give
    a H-space structure to various spheres:

    Real: A = S0                Easy to do without lemmas. (Junior Hopf)
      S0 --> S0 * S0 --> S1     However note that S0 isn't connected.
      S0 --> S1 --> S1          So it doesn't follow from lemmas anyway.

    Complex: A = S1             See HoTT book. (Hopf fibration)
      S1 --> S1 * S1 --> S2
      S1 --> S3 --> S2

    Quaternionic: A = S3        See https://arxiv.org/abs/1610.01134 for
      S3 --> S3 * S3 --> S4     a description. A formalisation in lean
      S3 --> S7 --> S4          exists!

    Octonionic: A = S7          ????
      S7 --> S7 * S7 --> S8
      S7 --> S15 --> S8 
**)

(***
      Hopf fibrations 
 ***)


(* Real hopf fibration *)

Section RealHopf.

  (** Since S0 isn't connected the junior hopf fibration,
      doesn't follow from our lemmas. However it is easy
      enough to define by induction on the circle.

      Notice how it twists.
   **)

  Definition junior_hopf_fibration : S1 -> Type. 
  Proof.
    srapply (S1_ind).
    + refine Bool.
    + destruct loop. refine (ua (equiv_negb)).
  Defined.

End RealHopf.

Section ComplexHopf.

  Definition h : forall (x : S1), x = x.
  Proof.
    srapply (S1_ind).
    + apply loop.
    + rewrite (transport_paths_lr loop loop).
      rewrite (concat_Vp).
      rewrite (concat_1p).
      reflexivity.
  Defined.

  Global Instance S1_IsHSpace : IsHSpace S1.
  Proof.
    srapply Build_IsHSpace.
    + apply base.
    + srapply (S1_rec).
      * refine idmap.
      * refine (path_forall _ _ h).
    + reflexivity.
    + srapply (S1_ind).
      * reflexivity. 
      * rewrite transport_paths_FlFr.
        rewrite ap_idmap.
        rewrite_moveR_Mp_p.
        rewrite ap_apply_Fl.
        rewrite S1_rec_beta_loop.
        rewrite ap10_path_forall.
        rewrite concat_1p.
        rewrite concat_p1.
        rewrite inv_V.
        reflexivity.
  Defined.

  Global Instance Sphere_1_IsHSpace : IsHSpace (Sphere 1).
  Proof.
    rewrite  (ua (BuildEquiv _ _ _ isequiv_Sph1_to_S1)).
    apply S1_IsHSpace.
  Defined.

  (* This may be a useful lemma to have *)
  Lemma Susp_Sphere {n} : Susp (Sphere n.+1) = Sphere n.+2.
  Proof.
    induction n.
    reflexivity.
    reflexivity.
  Defined.

  (** Need connected sphere lemma to make this proof shorter **)
  Definition hopf_fibration : Sphere 2 -> Type.
  Proof.
    serapply susp_fibration.
    rewrite (@Susp_Sphere -1).
    rewrite (ua (BuildEquiv _ _ _ isequiv_Sph1_to_S1)).
    apply isconnected_S1.
  Defined.

End ComplexHopf.

Section QuaternionicHopf.

  (**

    In https://arxiv.org/abs/1610.01134 the authors conjecture that
    there is H-space structure on S3 and give a description of it.

    In https://github.com/leanprover/lean2/blob/master/hott/homotopy/quaternionic_hopf.hlean we have a formalisation in lean. I am therefore
    inclined to believe that this can be done.

  **)


  (* Global Instance S3_IsHSpace : IsHSpace S3.
  Admitted. *)


End QuaternionicHopf.





