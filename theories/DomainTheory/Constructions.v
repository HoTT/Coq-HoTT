(** * Constructions of dcpos *)

From HoTT Require Import Basics Types TruncType Truncations.Core Universes.Smallness.
From HoTT.Classes.interfaces Require Import canonical_names orders.
From HoTT.DomainTheory Require Import Dcpo.

Local Open Scope type_scope.

(** We construct the dcpo of elements of a subdcpo, the dcpo of all maps into a dcpo and, assuming propositional resizing, the dcpo of propositions. In each case the index universe [v] is unchanged. *)

(** ** The dcpo of elements of a subdcpo *)

Definition le_sig {A : Type} {Ale : Le A} (B : A -> Type) : Le (sig B)
  := fun a b => a.1 ≤ b.1.

#[export] Instance partialorder_sig {A : Type} {Ale : Le A} `{!PartialOrder Ale}
  (B : A -> HProp)
  : PartialOrder (le_sig B).
Proof.
  split.
  - exact _.
  - intros a b; unfold le, le_sig; exact _.
  - split.
    + intros a; unfold le, le_sig; reflexivity.
    + intros a b c; unfold le, le_sig; apply transitivity.
  - intros a b p q.
    apply path_sigma_hprop.
    apply (antisymmetry Ale); [exact p|exact q].
Defined.

Section Subdcpo.
  Context {A : Type} {Ale : Le A} `{!IsDcpo Ale} (B : A -> HProp) `{!IsSubdcpo Ale B}.

  Local Existing Instance le_sig.

  Local Instance orderpreserving_pr1_sig : OrderPreserving (@pr1 A B)
    := fun _ _ => idmap.

  #[export] Instance isdcpo_sig : IsDcpo (le_sig B).
  Proof.
    split.
    1: exact _.
    intros I x d.
    pose (d' := isdirected_compose pr1 x d).
    exists (dcpo_sup (pr1 o x) d'; issubdcpo B I (pr1 o x) d' (fun i => (x i).2)).
    split.
    - exact (dcpo_sup_upper (pr1 o x) d').
    - intros b ub.
      exact (dcpo_sup_least (pr1 o x) d' b.1 ub).
  Defined.

End Subdcpo.

(** ** Function spaces *)

Section Pointwise.
  Context `{Funext} {A B : Type} (Ble : Le B).

  Local Notation le_pointwise := (relation_pointwise (fun _ : A => Ble)).

  #[export] Instance partialorder_pointwise `{!PartialOrder Ble}
    : PartialOrder le_pointwise.
  Proof.
    split.
    - exact _.
    - intros f g; unfold relation_pointwise; exact _.
    - split.
      + intros f a; exact (reflexivity (R:=Ble) (f a)).
      + intros f g h p q a; exact (transitivity (R:=Ble) (p a) (q a)).
    - intros f g p q.
      apply path_forall; intro a.
      apply (antisymmetry Ble); [exact (p a)|exact (q a)].
  Defined.

  #[export] Instance orderpreserving_ev (a : A)
    : OrderPreserving (Ale:=le_pointwise) (fun f : A -> B => f a)
    := fun f g p => p a.

  #[export] Instance isdcpo_pointwise `{!IsDcpo Ble} : IsDcpo le_pointwise.
  Proof.
    split.
    1: exact _.
    intros I x d.
    pose (da := fun a => isdirected_compose (fun f : A -> B => f a) x d).
    exists (fun a => dcpo_sup (fun i => x i a) (da a)).
    split.
    - intros i a.
      exact (dcpo_sup_upper (fun i => x i a) (da a) i).
    - intros g ub a.
      exact (dcpo_sup_least (fun i => x i a) (da a) (g a) (fun i => ub i a)).
  Defined.

  Definition dcpo_sup_pointwise `{!IsDcpo Ble} {I : Type} (x : I -> A -> B)
    (d : IsDirected (Ale:=le_pointwise) x) (a : A)
    : IsSup (fun i => x i a) (dcpo_sup x d a)
    := (dcpo_hassup I (fun i => x i a) (isdirected_compose (fun f : A -> B => f a) x d)).2.

End Pointwise.

Hint Extern 2 (IsDcpo (relation_pointwise _)) =>
  exact (isdcpo_pointwise _) : typeclass_instances.

(** ** Joins and meets of propositions *)

(** With propositional resizing, every family of propositions has a join and a meet in [HProp], in any universe. *)
Section HPropLattice.
  Universes w i j.
  Constraint w <= j, i <= j.
  Context `{PropResizing} {I : Type@{w}}.

  Definition hprop_join (P : I -> HProp@{i}) : HProp@{i}
    := Build_HProp (smalltype@{i j} (merely@{j} {k : I & P k})).

  Definition hprop_join_in (P : I -> HProp@{i}) (k : I)
    : P k -> hprop_join P
    := fun p => (equiv_smalltype _)^-1 (tr@{j} (k; p)).

  Definition hprop_join_rec (P : I -> HProp@{i}) (Q : HProp@{i})
    (f : forall k, P k -> Q)
    : hprop_join P -> Q.
  Proof.
    intro p.
    pose proof (equiv_smalltype _ p) as p'.
    strip_truncations.
    exact (f p'.1 p'.2).
  Defined.

  Context `{Funext}.

  Definition hprop_meet (P : I -> HProp@{i}) : HProp@{i}
    := Build_HProp (smalltype@{i j} (forall k, P k)).

  Definition hprop_meet_in (P : I -> HProp@{i})
    : (forall k, P k) -> hprop_meet P
    := (equiv_smalltype _)^-1.

  Definition hprop_meet_out (P : I -> HProp@{i}) (k : I)
    : hprop_meet P -> P k
    := fun p => equiv_smalltype _ p k.

End HPropLattice.

(** ** The dcpo of propositions *)

Definition le_hprop@{i u | i < u} : Le@{u i} HProp@{i}
  := fun P Q => P -> Q.

#[export] Instance partialorder_hprop `{Univalence} : PartialOrder le_hprop.
Proof.
  split.
  - exact _.
  - intros P Q; unfold le_hprop; exact _.
  - split.
    + intros P; exact idmap.
    + intros P Q R p q; exact (q o p).
  - intros P Q p q.
    exact (path_iff_hprop p q).
Defined.

(** By [isdcpo_pointwise], the same holds for the subsets [A -> HProp@{i}] of a type [A], ordered by inclusion. *)
#[export] Instance isdcpo_hprop@{v i u s} `{PropResizing} `{Univalence} : IsDcpo@{v u i s} le_hprop@{i u}.
Proof.
  split.
  1: exact _.
  intros I P _.
  exists (hprop_join@{v i s} P).
  split.
  - exact (hprop_join_in@{v i s} P).
  - exact (hprop_join_rec@{v i s} P).
Defined.

(** Without propositional resizing, [HProp@{i}] is still a [v]-dcpo when [v <= i], with suprema given by existential quantification. *)
Definition isdcpo_hprop_without_resizing@{v i u s | v <= i, i < u, u <= s}
  `{Univalence}
  : IsDcpo@{v u i s} le_hprop@{i u}.
Proof.
  split.
  1: exact _.
  intros I P _.
  exists (merely@{i} {k : I & P k}).
  split.
  - intros k p; exact (tr (k; p)).
  - intros Q ub.
    exact (Trunc_rec (fun kp => ub kp.1 kp.2)).
Defined.
