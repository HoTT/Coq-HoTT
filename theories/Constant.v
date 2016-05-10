(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics HoTT.Types.
Require Import Extensions Factorization Modalities.Modality.
Require Import hit.Truncations hit.Connectedness.
Import TrM.

Local Open Scope path_scope.
Local Open Scope trunc_scope.

(** * Varieties of constant function *)

(** Recall that a function [f : X -> Y] is *weakly constant*, [WeaklyConstant f], if [forall x y, f x = f y].  We show, following Kraus, Escardo, Coquand, and Altenkirch, that the type of fixed points of a weakly constant endofunction is an hprop.  However, to avoid potential confusion with [Coq.Init.Wf.Fix], instead of their notation [Fix], we denote this type by [FixedBy]. *)

Definition FixedBy {X : Type} (f : X -> X) := {x : X & f x = x}.

Global Instance ishprop_fix_wconst {X : Type} (f : X -> X)
       `{WeaklyConstant _ _ f}
: IsHProp (FixedBy f).
Proof.
  apply hprop_inhabited_contr; intros [x0 p0].
  refine (contr_equiv' {x:X & f x0 = x} _); unfold FixedBy.
  refine (equiv_functor_sigma' (equiv_idmap X)
           (fun x => equiv_concat_l (wconst x x0) x)).
Defined.

(** It follows that if a type [X] admits a weakly constant endofunction [f], then [FixedBy f] is equivalent to [merely X]. *)
Definition equiv_fix_merely {X : Type} (f : X -> X)
           `{WeaklyConstant _ _ f}
: FixedBy f <~> merely X.
Proof.
  apply equiv_iff_hprop.
  - intros [x p]; exact (tr x).
  - apply Trunc_rec; intros x.
    exists (f x).
    apply wconst.
Defined.

(** Therefore, a type is collapsible (admits a weakly constant endomap) if and only if [merely X -> X] (it has "split support"). *)
Definition splitsupp_collapsible {X} `{Collapsible X}
: merely X -> X.
Proof.
  refine (_ o (equiv_fix_merely collapse)^-1).
  apply pr1.
Defined.

Definition collapsible_splitsupp {X} (s : merely X -> X)
: Collapsible X.
Proof.
  refine (Build_Collapsible _ (s o tr) _); intros x y.
  apply (ap s), path_ishprop.
Defined.

(**  We say that [f] is *conditionally constant* if it factors through the propositional truncation [merely X], and *constant* if it factors through [Unit]. *)

Definition ConditionallyConstant {X Y : Type} (f : X -> Y)
  := ExtensionAlong (@tr -1 X) (fun _ => Y) f.

(** We don't yet have a need for a predicate [Constant] on functions; we do already have the operation [const] which constructs the constant function at a given point.  Every such constant function is, of course, conditionally constant. *)
Definition cconst_const {X Y} (y : Y)
: ConditionallyConstant (@const X Y y).
Proof.
  exists (const y); intros x; reflexivity.
Defined.

(** The type of conditionally constant functions is equivalent to [merely X -> Y]. *)
Definition equiv_cconst_from_merely `{Funext} (X Y : Type)
: { f : X -> Y & ConditionallyConstant f } <~> (merely X -> Y).
Proof.
  refine (_ oE (equiv_sigma_symm _)).
  refine (equiv_sigma_contr _).
Defined.

(** If a function factors through any hprop, it is conditionally constant. *)
Definition cconst_factors_hprop {X Y : Type} (f : X -> Y)
           (P : Type) `{IsHProp P}
           (g : X -> P) (h : P -> Y) (p : h o g == f)
: ConditionallyConstant f.
Proof.
  pose (g' := Trunc_rec g : merely X -> P).
  exists (h o g'); intros x.
  apply p.
Defined.

(** Thus, if it factors through a type that [X] implies is contractible, then it is also conditionally constant. *)
Definition cconst_factors_contr `{Funext}  {X Y : Type} (f : X -> Y)
           (P : Type) `{Pc : X -> Contr P}
           (g : X -> P) (h : P -> Y) (p : h o g == f)
: ConditionallyConstant f.
Proof.
  assert (merely X -> IsHProp P).
  { apply Trunc_rec.            (** Uses funext *)
    intros x; pose (Pc x); apply trunc_succ. }
  pose (g' := Trunc_ind (fun _ => P) g : merely X -> P).
  exists (h o g'); intros x.
  apply p.
Defined.

(** Any weakly constant function with collapsible domain is conditionally constant. *)
Definition cconst_wconst_collapsible {X Y : Type} (f : X -> Y)
           `{Collapsible X} `{WeaklyConstant _ _ f}
: ConditionallyConstant f.
Proof.
  exists (f o splitsupp_collapsible); intros x.
  unfold splitsupp_collapsible; simpl.
  apply wconst.
Defined.

(** Any weakly constant function with hset codomain is conditionally constant. *)
Definition cconst_wconst_hset `{Funext} {X Y : Type} (f : X -> Y)
           `{Ys : X -> IsHSet Y} `{WeaklyConstant _ _ f}
: ConditionallyConstant f.
Proof.
  assert (Ys' : merely X -> IsHSet Y).
  { apply Trunc_rec. intros x; exact (Ys x). }
  simple refine (cconst_factors_hprop f (image -1 f) _ _ _).
  - apply hprop_allpath; intros [y1 p1] [y2 p2].
    apply path_sigma_hprop; simpl.
    pose proof (Ys' (Trunc_functor -1 pr1 p1)).
    strip_truncations.
    destruct p1 as [x1 q1], p2 as [x2 q2].
    exact (q1^ @ wconst x1 x2 @ q2).
  - apply factor1.
  - apply factor2.
  - apply fact_factors.
Defined.

(** We can decompose this into an "induction principle" and its computation rule. *)
Definition merely_rec_hset `{Funext} {X Y : Type} (f : X -> Y)
           `{Ys : X -> IsHSet Y} `{WeaklyConstant _ _ f}
: merely X -> Y
  := (cconst_wconst_hset f).1.

Definition merely_rec_hset_beta `{Funext} {X Y : Type} (f : X -> Y)
           `{Ys : X -> IsHSet Y} `{WeaklyConstant _ _ f}
           (x : X)
: merely_rec_hset f (tr x) = f x
  := (cconst_wconst_hset f).2 x.

(** More generally, the type of weakly constant functions [X -> Y], when [Y] is a set, is equivalent to [merely X -> Y]. *)
Definition equiv_merely_rec_hset `{Funext} (X Y : Type)
           `{Ys : X -> IsHSet Y}
: { f : X -> Y & WeaklyConstant f } <~> (merely X -> Y).
Proof.
  assert (Ys' : merely X -> IsHSet Y).
  { apply Trunc_rec. intros x; exact (Ys x). }
  simple refine (equiv_adjointify
            (fun fc => @merely_rec_hset _ _ _ fc.1 _ fc.2)
            (fun g => (g o tr ; _)) _ _); try exact _.
  - intros x y; apply (ap g), path_ishprop.
  - intros g; apply path_arrow; intros mx.
    pose proof (Ys' mx).
    strip_truncations; reflexivity.
  - intros [f ?].
    refine (path_sigma_hprop _ _ _).
    + intros f'; apply hprop_allpath; intros w1 w2.
      apply path_forall; intros x; apply path_forall; intros y.
      pose (Ys x); apply path_ishprop.
    + apply path_arrow; intros x; reflexivity.
Defined.
