(** * Constructions of dcpos *)

From HoTT Require Import Basics Types TruncType Truncations.Core Universes.Smallness.
From HoTT.Classes.interfaces Require Import canonical_names orders.
From HoTT.DomainTheory Require Import Dcpo.

Local Open Scope type_scope.

(** We construct the dcpo of elements of a subdcpo, products of dcpos, the dcpo of all maps into a dcpo, the dcpo of Scott continuous maps between dcpos and, assuming propositional resizing, the dcpo of propositions. In each case the index universe [v] is unchanged. *)

(** ** The dcpo of elements of a subdcpo *)

(** The order on [A] restricts to the elements of a subtype of [A]. *)
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
    exact (antisymmetry Ale _ _ p q).
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
    exists (dcpo_sup _ d'; issubdcpo B I _ d' (fun i => (x i).2)).
    split.
    - exact (dcpo_sup_upper _ d').
    - intros b ub.
      exact (dcpo_sup_least _ d' b.1 ub).
  Defined.

  (** The inclusion of a subdcpo is Scott continuous. *)
  #[export] Instance isscottcontinuous_pr1_sig : IsScottContinuous (@pr1 A B)
    := fun I x d => issup_dcpo_sup _ (isdirected_compose pr1 x d).

End Subdcpo.

(** ** Products *)

Definition le_prod {A B : Type} (Ale : Le A) (Ble : Le B) : Le (A * B)
  := fun a b => (fst a ≤ fst b) * (snd a ≤ snd b).

Section Product.
  Context {A B : Type} {Ale : Le A} {Ble : Le B}.

  Local Existing Instance le_prod.

  #[export] Instance partialorder_prod `{!PartialOrder Ale} `{!PartialOrder Ble}
    : PartialOrder (le_prod Ale Ble).
  Proof.
    split.
    - exact _.
    - intros a b; unfold le, le_prod; exact _.
    - split.
      + intros a; exact (reflexivity _, reflexivity _).
      + intros a b c p q.
        exact (transitivity (fst p) (fst q), transitivity (snd p) (snd q)).
    - intros a b p q.
      apply path_prod.
      + exact (antisymmetry Ale _ _ (fst p) (fst q)).
      + exact (antisymmetry Ble _ _ (snd p) (snd q)).
  Defined.

  #[export] Instance orderpreserving_fst : OrderPreserving (@fst A B)
    := fun _ _ => fst.

  #[export] Instance orderpreserving_snd : OrderPreserving (@snd A B)
    := fun _ _ => snd.

  (** Suprema in a product are computed componentwise. *)
  #[export] Instance isdcpo_prod `{!IsDcpo Ale} `{!IsDcpo Ble}
    : IsDcpo (le_prod Ale Ble).
  Proof.
    split.
    1: exact _.
    intros I x d.
    pose (d1 := isdirected_compose fst x d).
    pose (d2 := isdirected_compose snd x d).
    exists (dcpo_sup _ d1, dcpo_sup _ d2).
    split.
    - intro i.
      exact (dcpo_sup_upper _ d1 i, dcpo_sup_upper _ d2 i).
    - intros a ub.
      exact (dcpo_sup_least _ d1 _ (fun i => fst (ub i)),
             dcpo_sup_least _ d2 _ (fun i => snd (ub i))).
  Defined.

  #[export] Instance bottom_prod `{Bottom A} `{Bottom B} : Bottom (A * B)
    := (⊥, ⊥).

  #[export] Instance ispointeddcpo_prod `{Bottom A} `{Bottom B}
    `{!IsPointedDcpo Ale} `{!IsPointedDcpo Ble}
    : IsPointedDcpo (le_prod Ale Ble).
  Proof.
    split.
    - exact _.
    - intro a; exact (bottom_least _, bottom_least _).
  Defined.

  #[export] Instance isscottcontinuous_fst `{!IsDcpo Ale} `{!IsDcpo Ble}
    : IsScottContinuous (@fst A B)
    := fun I x d => issup_dcpo_sup _ (isdirected_compose fst x d).

  #[export] Instance isscottcontinuous_snd `{!IsDcpo Ale} `{!IsDcpo Ble}
    : IsScottContinuous (@snd A B)
    := fun I x d => issup_dcpo_sup _ (isdirected_compose snd x d).

End Product.

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
      + intros f a; exact (reflexivity (R:=Ble) _).
      + intros f g h p q a; exact (transitivity (R:=Ble) (p a) (q a)).
    - intros f g p q.
      apply path_forall; intro a.
      exact (antisymmetry Ble _ _ (p a) (q a)).
  Defined.

  (** Evaluation at a point is monotone. *)
  #[export] Instance orderpreserving_ev (a : A)
    : OrderPreserving (Ale:=le_pointwise) (fun f : A -> B => f a)
    := fun f g p => p a.

  (** Suprema in [A -> B] are computed pointwise. *)
  #[export] Instance isdcpo_pointwise `{!IsDcpo Ble} : IsDcpo le_pointwise.
  Proof.
    split.
    1: exact _.
    intros I x d.
    pose (da := fun a => isdirected_compose (fun f : A -> B => f a) x d).
    exists (fun a => dcpo_sup _ (da a)).
    split.
    - intros i a.
      exact (dcpo_sup_upper _ (da a) i).
    - intros g ub a.
      exact (dcpo_sup_least _ (da a) _ (fun i => ub i a)).
  Defined.

  Definition dcpo_sup_pointwise `{!IsDcpo Ble} {I : Type} (x : I -> A -> B)
    (d : IsDirected (Ale:=le_pointwise) x) (a : A)
    : IsSup (fun i => x i a) (dcpo_sup x d a)
    := (dcpo_hassup _ _ (isdirected_compose (fun f : A -> B => f a) x d)).2.

  #[export] Instance bottom_pointwise `{Bottom B} : Bottom (A -> B)
    := fun _ => ⊥.

  #[export] Instance ispointeddcpo_pointwise `{Bottom B} `{!IsPointedDcpo Ble}
    : IsPointedDcpo le_pointwise.
  Proof.
    split.
    - exact _.
    - intros f a; exact (bottom_least _).
  Defined.

End Pointwise.

Hint Extern 2 (IsDcpo (relation_pointwise _)) =>
  exact (isdcpo_pointwise _) : typeclass_instances.

(** ** Scott continuous maps *)

Section ScottContinuousMaps.
  Universes v u t s u' t' s'.
  Context `{Funext} {A : Type@{u}} {B : Type@{u'}} {Ale : Le@{u t} A} {Ble : Le@{u' t'} B}
    `{!IsDcpo@{v u t s} Ale} `{!IsDcpo@{v u' t' s'} Ble}.

  Local Notation le_pointwise := (relation_pointwise (fun _ : A => Ble)).

  (** The Scott continuous maps form a subdcpo of all maps. *)
  Definition subset_isscottcontinuous : (A -> B) -> HProp
    := fun f => Build_HProp (IsScottContinuous f).

  #[export] Instance issubdcpo_isscottcontinuous
    : IsSubdcpo le_pointwise subset_isscottcontinuous.
  Proof.
    intros I f d cf J x dx.
    pose (gs := dcpo_sup_pointwise Ble f d).
    split.
    - intro j.
      apply (issup_least (gs (x j))); intro i.
      pose proof (cf i : IsScottContinuous (f i)).
      exact (transitivity (order_preserving (f i) _ _ (dcpo_sup_upper x dx j))
               (issup_upper (gs _) i)).
    - intros b ub.
      apply (issup_least (gs _)); intro i.
      pose proof (cf i : IsScottContinuous (f i)).
      apply (issup_least (scott_continuous (f i) J x dx)); intro j.
      exact (transitivity (issup_upper (gs (x j)) i) (ub j)).
  Defined.

End ScottContinuousMaps.

(** By [isdcpo_sig], the Scott continuous maps form a dcpo under the pointwise order. *)

(** ** Joins and meets of propositions *)

(** With propositional resizing, every family of propositions has a join and a meet in [HProp], in any universe. *)
Section HPropLattice.
  Universes w i j.
  Constraint w <= j, i <= j.
  Context `{PropResizing} {I : Type@{w}}.

  (** The join of a family of propositions in [HProp@{i}], indexed by a type in [Type@{w}]; the universe [j] contains both. *)
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

(** Propositions are ordered by implication. *)
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

(** With propositional resizing, [HProp@{i}] is a [v]-dcpo for every universe [v]. By [isdcpo_pointwise], the same holds for the subsets [A -> HProp@{i}] of a type [A], ordered by inclusion. *)
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
