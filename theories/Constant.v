Require Import HoTT.Basics HoTT.Types.
Require Import Extensions Factorization.
Require Import Truncations.Core Modalities.Modality.

Local Open Scope path_scope.
Local Open Scope trunc_scope.

(** * Varieties of constant function *)

(** Recall that a function [f : X -> Y] is *weakly constant*, [WeaklyConstant f], if [forall x y, f x = f y].  We show, following Kraus, Escardo, Coquand, and Altenkirch, that the type of fixed points of a weakly constant endofunction is an hprop.  However, to avoid potential confusion with [Coq.Init.Wf.Fix], instead of their notation [Fix], we denote this type by [FixedBy]. *)

Definition FixedBy {X : Type} (f : X -> X) := {x : X & f x = x}.

Global Instance ishprop_fix_wconst {X : Type} (f : X -> X)
  {wc : WeaklyConstant f}
  : IsHProp (FixedBy f).
Proof.
  apply hprop_inhabited_contr; intros [x0 p0].
  refine (contr_equiv' {x:X & f x0 = x} _); unfold FixedBy.
  apply equiv_functor_sigma_id. intros x.
  apply equiv_concat_l.
  apply wconst.
Defined.

(** It follows that if a type [X] admits a weakly constant endofunction [f], then [FixedBy f] is equivalent to [merely X]. *)
Definition equiv_fix_merely {X : Type} (f : X -> X)
  {wc : WeaklyConstant f}
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
  := ExtensionAlong (@tr (-1) X) (fun _ => Y) f.

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
  (P : Type) {Pc : X -> Contr P}
  (g : X -> P) (h : P -> Y) (p : h o g == f)
  : ConditionallyConstant f.
Proof.
  assert (merely X -> IsHProp P).
  { apply Trunc_rec.            (** Uses funext *)
    intros x; pose (Pc x); apply istrunc_succ. }
  pose (g' := Trunc_ind (fun _ => P) g : merely X -> P).
  exists (h o g'); intros x.
  apply p.
Defined.

(** Any weakly constant function with collapsible domain is conditionally constant. *)
Definition cconst_wconst_collapsible {X Y : Type} `{Collapsible X}
  (f : X -> Y) {wc : WeaklyConstant f}
  : ConditionallyConstant f.
Proof.
  exists (f o splitsupp_collapsible); intros x.
  unfold splitsupp_collapsible; simpl.
  apply wconst.
Defined.

(** The image of a weakly constant function with hset codomain is an hprop. In fact, we just need to assume that [merely X -> IsHSet Y]. *)
Local Instance hprop_image_wconst_hset_if_merely_domain {X Y : Type} (f : X -> Y)
  {Ys : merely X -> IsHSet Y} {wc: WeaklyConstant f}
  : IsHProp (image (-1) f).
Proof.
  apply hprop_allpath.
  intros [b m] [b' m'].
  apply path_sigma_hprop; cbn.
  assert (Ys' : IsHSet Y).
  { apply Ys. strip_truncations. exact (tr m.1). }
  strip_truncations.
  destruct m as [x p], m' as [x' p'].
  exact (p^ @ wc x x' @ p').
Defined.

(** When [merely X -> IsHSet Y], any weakly constant function [X -> Y] is conditionally constant. *)
Definition cconst_wconst_hset_if_merely_domain {X Y : Type} (f : X -> Y)
  {Ys : merely X -> IsHSet Y} {wc: WeaklyConstant f}
  : ConditionallyConstant f.
Proof.
  srapply (cconst_factors_hprop f (image (-1) f)).
  - apply factor1.
  - apply factor2.
  - apply fact_factors.
Defined.

(** The previous result will be most often used when we know [Y] is an hset, so we specialize to this case. *)
Definition cconst_wconst_hset {X Y : Type} (f : X -> Y)
  {Ys : IsHSet Y} {wc : WeaklyConstant f}
  : ConditionallyConstant f
  := cconst_wconst_hset_if_merely_domain f (Ys:=fun _ => Ys).

(** We can decompose this into an "induction principle" and its computation rule. *)
Definition merely_rec_hset {X Y : Type} (f : X -> Y)
  {Ys : IsHSet Y} {wc : WeaklyConstant f}
  : merely X -> Y
  := (cconst_wconst_hset f).1.

(** The computation rule is [(cconst_wconst_hset f).2 x], but that's reflexivity. *)
Definition merely_rec_hset_beta {X Y : Type} (f : X -> Y)
  {Ys : IsHSet Y} {wc : WeaklyConstant f}
  (x : X)
  : merely_rec_hset f (tr x) = f x
  := idpath.

(** If we assume [Funext], then we can weaken the hypothesis from [merely X -> IsHSet Y] to [X -> IsHSet Y], since with [Funext], we know that [IsHSet Y] is an hprop. *)
Definition cconst_wconst_hset_if_domain `{Funext} {X Y : Type} (f : X -> Y)
  {Ys : X -> IsHSet Y} {wc : WeaklyConstant f}
  : ConditionallyConstant f
  := cconst_wconst_hset_if_merely_domain f (Ys:=Trunc_rec Ys).

(** We record the corresponding induction principle, but not the computation principle, since it is again definitional. *)
Definition merely_rec_hset_if_domain `{Funext} {X Y : Type} (f : X -> Y)
  {Ys : X -> IsHSet Y} {wc : WeaklyConstant f}
  : merely X -> Y
  := (cconst_wconst_hset_if_domain f).1.

(** The type of weakly constant functions [X -> Y], when [Y] is a set, is equivalent to [merely X -> Y]. This uses [Funext] for the main argument, so we may as well state it with the more general assumption [X -> IsHSet Y]. *)
Definition equiv_merely_rec_hset_if_domain `{Funext} (X Y : Type)
  {Ys : X -> IsHSet Y}
  : { f : X -> Y & WeaklyConstant f } <~> (merely X -> Y).
Proof.
  pose proof (Ys' := Trunc_rec Ys : merely X -> IsHSet Y).
  snrapply equiv_adjointify.
  - intros [f wc].  exact (merely_rec_hset_if_domain f (wc:=wc)).
  - intro g.  exists (g o tr).
    intros x y; apply (ap g), path_ishprop.
  - intros g; apply path_arrow; intros mx.
    pose proof (Ys' mx).
    strip_truncations; reflexivity.
  - intros [f wc].
    snrapply path_sigma; cbn.
    + reflexivity.
    + cbn. funext x y.
      pose (Ys x); apply path_ishprop.
Defined.
