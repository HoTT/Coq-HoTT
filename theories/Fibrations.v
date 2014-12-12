(** * Basic facts about fibrations *)

Require Import HoTT.Basics Types.Sigma Types.Paths.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(* ** Homotopy fibers *)

(** Paths in homotopy fibers can be constructed using [path_sigma] and [transport_paths_Fl]. *)

Definition path_hfiber {A B : Type} {f : A -> B} {y : B}
  {x1 x2 : hfiber f y} (q : x1.1 = x2.1) (r : x1.2 = ap f q @ x2.2)
: x1 = x2.
Proof.
  refine (path_sigma _ _ _ q _).
  refine (transport_paths_Fl _ _ @ _).
  apply moveR_Vp, r.
Defined.

(** Homotopic maps have equivalent fibers. *)

Definition equiv_hfiber_homotopic
           {A B : Type} (f g : A -> B) (h : f == g) (b : B)
: hfiber f b <~> hfiber g b.
Proof.
  refine (BuildEquiv _ _ (fun fx => (fx.1 ; (h fx.1)^ @ fx.2)) _).
  refine (isequiv_adjointify _ (fun gx => (gx.1 ; (h gx.1) @ gx.2)) _ _);
    intros [a p]; simpl.
  - apply ap, concat_V_pp.
  - apply ap, concat_p_Vp.
Defined.

(** ** Replacing a map with a fibration *)

Definition equiv_fibration_replacement  {B C} (f:C ->B):
  C <~> {y:B & hfiber f y}.
Proof.
  refine (BuildEquiv _ _ _ (BuildIsEquiv
               C {y:B & {x:C & f x = y}}
               (fun c => (f c; (c; idpath)))
               (fun c => c.2.1)
               _
               (fun c => idpath)
               _)).
  - repeat (intros [] || intro); reflexivity.
  - reflexivity.
Defined.

Definition hfiber_fibration {X} (x : X) (P:X->Type):
    P x <~> @hfiber (sigT P) X pr1 x.
Proof.
  refine (BuildEquiv _ _ _ (BuildIsEquiv
               (P x) { z : sigT P & z.1 = x }
               (fun Px => ((x; Px); idpath))
               (fun Px => transport P Px.2 Px.1.2)
               _
               (fun Px => idpath)
               _)).
  - repeat (intros [] || intro); reflexivity.
  - reflexivity.
Defined.

(** ** Exercise 4.4: The unstable octahedral axiom. *)

Section UnstableOctahedral.

  Context {A B C} (f : A -> B) (g : B -> C).

  Definition hfiber_compose_map (b : B)
  : hfiber (g o f) (g b) -> hfiber g (g b)
    := fun x => (f x.1 ; x.2).

  Definition hfiber_hfiber_compose_map (b : B)
  : hfiber (hfiber_compose_map b) (b;1) <~> hfiber f b.
  Proof.
    unfold hfiber, hfiber_compose_map.
    refine (equiv_compose' _ (equiv_inverse (equiv_sigma_assoc _ _))).
    refine (equiv_functor_sigma' (equiv_idmap _) _); intros a; simpl.
    transitivity ({p : g (f a) = g b & {q : f a = b & transport (fun y => g y = g b) q p = 1}}).
    - refine (equiv_functor_sigma' (equiv_idmap _)
                (fun p => equiv_inverse (equiv_path_sigma _ _ _))).
    - refine (equiv_compose' _ (equiv_sigma_symm _)).
      apply equiv_sigma_contr; intros p.
      destruct p; simpl; exact _.
  Defined.

  Definition hfiber_compose (c : C)
  : hfiber (g o f) c <~> { w : hfiber g c & hfiber f w.1 }.
  Proof.
    unfold hfiber.
    refine (equiv_compose' (equiv_sigma_assoc
              (fun x => g x = c) (fun w => {x : A & f x = w.1})) _).
    refine (equiv_compose' (equiv_functor_sigma' (equiv_idmap B)
             (fun b => equiv_sigma_symm (fun a p => f a = b))) _).
    refine (equiv_compose' (equiv_sigma_symm _) _).
    refine (equiv_functor_sigma' (equiv_idmap A) _); intros a.
    refine (equiv_compose' (equiv_functor_sigma' (equiv_idmap B)
              (fun b => equiv_sigma_symm0 _ _)) _); simpl.
    refine (equiv_compose' (equiv_inverse (equiv_sigma_assoc (fun b => f a = b) (fun w => g w.1 = c))) _).
    symmetry.
    exact (equiv_contr_sigma (fun (w:{b:B & f a = b}) => g w.1 = c)).
  Defined.

End UnstableOctahedral.

(** ** Fibers of [functor_sigma] *)

Definition hfiber_functor_sigma {A B} (P : A -> Type) (Q : B -> Type)
           (f : A -> B) (g : forall a, P a -> Q (f a))
           (b : B) (v : Q b)
: (hfiber (functor_sigma f g) (b; v)) <~>
  {w : hfiber f b & hfiber (g w.1) ((w.2)^ # v)}.
Proof.
  unfold hfiber, functor_sigma.
  equiv_via ({x : sigT P & {p : f x.1 = b & p # (g x.1 x.2) = v}}).
  { refine (equiv_functor_sigma' (equiv_idmap _)
             (fun x => equiv_inverse (equiv_path_sigma Q _ _))). }
  refine (equiv_compose' _ (equiv_inverse (equiv_sigma_assoc P _))).
  equiv_via ({a:A & {q:f a = b & {p : P a & q # (g a p) = v}}}).
  { refine (equiv_functor_sigma' (equiv_idmap _) (fun a => _)); simpl.
    refine (equiv_sigma_symm _). }
  refine (equiv_compose' _
           (equiv_sigma_assoc (fun a => f a = b)
             (fun w => {p : P w.1 & w.2 # (g w.1 p) = v}))).
  refine (equiv_functor_sigma' (equiv_idmap _) _);
    intros [a p]; simpl.
  refine (equiv_functor_sigma' (equiv_idmap _) _);
    intros u; simpl.
  apply equiv_moveL_transport_V.
Defined.

(** Theorem 4.7.6 *)
Definition hfiber_functor_sigma_idmap {A} (P Q : A -> Type)
           (g : forall a, P a -> Q a)
           (b : A) (v : Q b)
: (hfiber (functor_sigma idmap g) (b; v)) <~>
   hfiber (g b) v.
Proof.
  refine (equiv_compose' _ (hfiber_functor_sigma P Q idmap g b v)).
  exact (equiv_contr_sigma
           (fun (w:hfiber idmap b) => hfiber (g w.1) (transport Q (w.2)^ v))).
Defined.
