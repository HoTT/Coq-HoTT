(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics.
Require Import types.Universe types.Bool types.Sigma types.Arrow types.Sum.
Require Import ReflectiveSubuniverse Modality HProp UnivalenceImpliesFunext.
Require Import hit.Truncations.
Require Import Logic.Generic Logic.Notations.
Require Import HoTT.Tactics.

Local Open Scope trunc_scope.
Local Open Scope path_scope.

(** * Excluded middle *)

Section LEM.
Context {fs : Funext}.

(** If we end up needing this universe-polymorphically, we could change it to an axiom depending on a dummy typeclass like [Funext] and [Univalence].  Its name ends with an underscore to indicate that it is parametrized by the logic (as a "subscript").*)
Class LEM_ (log : Logic) :=
  lem : forall P, (P \/ (~ P)).

(** If proving LEM, we may as well assume that [P] is a generic proposition. *)
Definition easyLEM (log : Logic)
: (forall P, IsGenericProp P -> (P \/ (~ P))) -> LEM_ log.
Proof.
  intros H P.
  refine (hor_elim  _ _ (H (@O log P) _)).
  - apply O_rect; try exact _.
    apply hor_inl.
  - intros nop.
    apply hor_inr.
    intros p.
    exact (nop (O_unit P p)).
Defined.

(** The double negation of LEM always holds. *)
Theorem notnot_LEM (log : Logic) (P : Type)
: ~ ~ (P \/ (~ P)).
Proof.
  intros K.
  refine (K _).
  apply hor_inr.
  intros p.
  refine (K _).
  exact (hor_inl p).
Defined.

(** As a corollary, LEM itself holds in double-negation logic.  This proof would be substantially more complicated if our definition of [notnot_logic] didn't record the fact that [Empty] is modal, since in that case [LEM_ notnot_logic] would involve a [~~Empty] where [notnot_LEM PAT_logic] has an [Empty]. *)
Definition LEM_notnot : LEM_ notnot_logic :=
  fun P => notnot_LEM PAT_logic P.

(** LEM is equivalent to the law of double negation, in any logic.  Note that in the law of double negation, we *do* have to assume that [P] is a generic proposition. *)
Theorem double_negation {log : Logic} {lem : @LEM_ log} P `{IsGenericProp P}
: (~ ~ P) -> P.
Proof.
  pose (pnp := lem P).
  intros nnp.
  refine (hor_elim _ _ pnp).
  - exact idmap.
  - intros np.
    refine (hfalse_elim _ _).
    exact (nnp np).
Defined.

Theorem lem_from_double_negation {log : Logic}
 : (forall P, IsGenericProp P -> (~ ~ P) -> P) -> LEM_ log.
Proof.
  intros H; apply easyLEM; intros P ?.
  apply H; try exact _.
  apply notnot_LEM.
Defined.

End LEM.

(** If LEM holds in some logic, then every generic proposition in that logic must be an hprop. *)
Section LEMisprop.

  Context {ua : Univalence} (log : Logic) {lem : LEM_ log}.
  Local Existing Instance logic_modality.

  Local Definition DN P {P_inO : inO P}
  : ~~P -> P
  := @double_negation log _ P _.

  Local Definition nnobool : ~~(O Bool)
    := (fun nb => nb (O_unit Bool true)).

  Local Definition b : O Bool
    := DN (O Bool) nnobool.

  Local Definition allob_is_true_or_false (x : O Bool)
  : (x = O_unit Bool true) \/ (x = O_unit Bool false).
  Proof.
    revert x; apply O_rect; try exact _.
    intros [|].
    - apply hor_inl; reflexivity.
    - apply hor_inr; reflexivity.
  Defined.

  Local Definition Onegb_b : O_functor negb b = b.
    pose (p := ap10 (apD DN (path_universe (O_functor negb))) _).
    rewrite transport_arrow in p.
    refine (_ @ ap10 p nnobool).
    rewrite transport_arrow, transport_path_universe.
    apply ap; unfold b.
    apply ap011; apply allpath_hprop.
  Qed.

  Local Definition Otrue_is_Ofalse :
    O_unit Bool true = O_unit Bool false.
  Proof.
    refine (hor_elim _ _ (allob_is_true_or_false b)); intros p.
    - transitivity (O_functor negb (O_unit Bool true)).
      + rewrite <- p.
        symmetry; apply Onegb_b.
      + refine (_ @ (O_unit_natural negb true)).
        reflexivity.
    - transitivity (O_functor negb (O_unit Bool false)).
      + refine (_ @ (O_unit_natural negb false)^).
        reflexivity.
      + rewrite <- p.
        apply Onegb_b.
  Qed.
    
  Theorem allO_hprop_lem P `{IsGenericProp P} : IsHProp P.
  Proof.
    apply hprop_allpath; intros x y.
    pose (f := O_rect (fun _ => P) (fun b:Bool => if b then x else y)).
    transitivity (f (O_unit Bool true)).
    - unfold f; rewrite O_rect_beta; reflexivity.
    - transitivity (f (O_unit Bool false)).
      + exact (ap f (Otrue_is_Ofalse)).
      + unfold f; rewrite O_rect_beta; reflexivity.
  Qed.
  
End LEMisprop.

(** In particular, LEM is false in oo-logic.
This is Corollary 3.2.7. *)
Theorem not_LEMoo {ua : Univalence} : ~ LEM_ oo.
Proof.
  intros ?.
  pose (H := allO_hprop_lem oo Bool).
  apply true_ne_false, allpath_hprop.
Defined.

(** Thus, nearly always, when we say "LEM" we mean the version in (-1)-logic.  *)
Notation LEM := (LEM_(-1)).

(** In this case, since [P] and [~P] are disjoint, we have a simpler phrasing of LEM. *)
Definition lem' `{LEM} `{Funext} P `{IsHProp P} : P + ~P.
Proof.
  refine ((@O_unit (-1) (P + ~P))^-1 _).
  - apply isequiv_O_unit_inO. simpl.
    refine (hprop_sum _).
    intros p np; exact (np p).
  - exact (lem P).
Defined.
