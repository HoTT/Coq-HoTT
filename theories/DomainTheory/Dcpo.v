(** * Directed-complete partial orders *)

From HoTT Require Import Basics Types TruncType Truncations.Core.
From HoTT.Classes.interfaces Require Import canonical_names orders.
From HoTT.Spaces Require Import Nat.Core.

Local Open Scope type_scope.

(** We develop domain theory following de Jong and Escardó, "Domain theory in constructive and predicative univalent foundations" (CSL 2021), and its formalization in the [DomainTheory] directory of the TypeTopology library. Suprema are taken of families [x : I -> A] rather than of subsets of [A]. Without propositional resizing it matters which universe the index types [I] live in: for a universe [v], a _[v]-dcpo_ is a partial order in which every directed family indexed by a type in [Type@{v}] has a supremum. The carrier and the order may live in other universes. The universe parameters of [IsDcpo@{v u t s}] are the index universe [v], the universe [u] of the carrier, the universe [t] of the order, and a universe [s] containing the other three, in which the statements about directed families live.

The constructions of dcpos are in [DomainTheory.Constructions] and the fixed point theorems in [DomainTheory.FixedPoints]. *)

(** ** Suprema and directed families *)

(** The universe parameters are [u] for the carrier, [t] for the order, [w] for the index type of a family, and [s], containing the other three, for the statements that a family is directed or has a given supremum. *)

Definition IsUpperBound@{u t w} {A : Type@{u}} {Ale : Le@{u t} A} {I : Type@{w}}
  (x : I -> A) (a : A)
  := forall i, x i ≤ a.

Section Sup.
  Universes u t w s.
  Constraint u <= s, t <= s, w <= s.
  Context {A : Type@{u}} {Ale : Le@{u t} A}.

  Definition IsSup {I : Type@{w}} (x : I -> A) (a : A)
    := prod@{s s} (IsUpperBound x a) (forall b, IsUpperBound x b -> a ≤ b).

  Definition IsSemidirected {I : Type@{w}} (x : I -> A)
    := forall i j, merely@{s} (sig@{w t} (fun k => prod@{t t} (x i ≤ x k) (x j ≤ x k))).

  Definition IsDirected {I : Type@{w}} (x : I -> A)
    := prod@{w s} (merely@{w} I) (IsSemidirected x).

End Sup.

Section SupTheory.
  Context {A : Type} {Ale : Le A}.

  Definition issup_upper {I : Type} {x : I -> A} {a : A} (p : IsSup x a) (i : I)
    : x i ≤ a
    := fst p i.

  Definition issup_least {I : Type} {x : I -> A} {a : A} (p : IsSup x a) (b : A)
    : IsUpperBound x b -> a ≤ b
    := snd p b.

  Context `{Funext}.

  #[export] Instance ishprop_issemidirected {I : Type} (x : I -> A)
    : IsHProp (IsSemidirected x)
    := _.

  #[export] Instance ishprop_isdirected {I : Type} (x : I -> A)
    : IsHProp (IsDirected x)
    := _.

  Context `{!is_mere_relation A Ale}.

  #[export] Instance ishprop_isupperbound {I : Type} (x : I -> A) (a : A)
    : IsHProp (IsUpperBound x a)
    := _.

  #[export] Instance ishprop_issup {I : Type} (x : I -> A) (a : A)
    : IsHProp (IsSup x a)
    := _.

  Context `{!AntiSymmetric Ale}.

  Definition path_issup {I : Type} (x : I -> A) {a b : A}
    (p : IsSup x a) (q : IsSup x b)
    : a = b
    := antisymmetry Ale a b (issup_least p b (fst q)) (issup_least q a (fst p)).

  #[export] Instance ishprop_hassup {I : Type} (x : I -> A)
    : IsHProp {a : A & IsSup x a}.
  Proof.
    apply hprop_allpath.
    intros [a p] [b q].
    apply path_sigma_hprop.
    exact (path_issup x p q).
  Defined.

End SupTheory.

(** ** Dcpos *)

(** The suprema are given as structure, but by [ishprop_hassup] this is a property. *)
Class IsDcpo@{v u t s} {A : Type@{u}} (Ale : Le@{u t} A) := {
  isdcpo_partialorder :: PartialOrder Ale ;
  dcpo_hassup : forall (I : Type@{v}) (x : I -> A),
    IsDirected@{u t v s} x -> sig@{u s} (fun a => IsSup@{u t v s} x a)
}.

Arguments dcpo_hassup {A Ale _} I x _.

Section DcpoSup.
  Universes v u t s.
  Context {A : Type@{u}} {Ale : Le@{u t} A} `{!IsDcpo@{v u t s} Ale}.

  Definition dcpo_sup {I : Type@{v}} (x : I -> A) (d : IsDirected x) : A
    := (dcpo_hassup I x d).1.

  Definition issup_dcpo_sup {I : Type@{v}} (x : I -> A) (d : IsDirected x)
    : IsSup x (dcpo_sup x d)
    := (dcpo_hassup I x d).2.

  Definition dcpo_sup_upper {I : Type@{v}} (x : I -> A) (d : IsDirected x) (i : I)
    : x i ≤ dcpo_sup x d
    := issup_upper (issup_dcpo_sup x d) i.

  Definition dcpo_sup_least {I : Type@{v}} (x : I -> A) (d : IsDirected x) (t : A)
    : IsUpperBound x t -> dcpo_sup x d ≤ t
    := issup_least (issup_dcpo_sup x d) t.

  Definition path_dcpo_sup {I : Type@{v}} (x : I -> A) (d : IsDirected x) {s : A}
    (p : IsSup x s)
    : dcpo_sup x d = s
    := path_issup x (issup_dcpo_sup x d) p.

End DcpoSup.

(** ** Directed families *)

Section Directed.
  Context {A : Type} {Ale : Le A}.

  Definition isdirected_compose {B : Type} {Ble : Le B} (f : A -> B)
    `{!OrderPreserving f} {I : Type} (x : I -> A) (d : IsDirected x)
    : IsDirected (f o x).
  Proof.
    split.
    - exact (fst d).
    - intros i j.
      specialize (snd d i j); apply Trunc_functor.
      intros [k [p q]].
      exists k; split; apply (order_preserving f); assumption.
  Defined.

  Context `{!PreOrder Ale}.

  Local Definition increasing_sequence_le (x : nat -> A) (c : forall n, x n ≤ x n.+1%nat)
    (n m : nat)
    : x n ≤ x (m + n)%nat.
  Proof.
    induction m as [|m IHm].
    - reflexivity.
    - exact (transitivity IHm (c (m + n)%nat)).
  Defined.

  Definition isdirected_increasing_sequence (x : nat -> A)
    (c : forall n, x n ≤ x n.+1%nat)
    : IsDirected x.
  Proof.
    split.
    - exact (tr 0%nat).
    - intros n m.
      apply tr; exists (m + n)%nat.
      split.
      + exact (increasing_sequence_le x c n m).
      + rewrite nat_add_comm.
        exact (increasing_sequence_le x c m n).
  Defined.

End Directed.

(** ** Monotone and Scott continuous maps *)

(** Monotone maps are the [OrderPreserving] maps of [Classes.interfaces.orders]. *)
#[export] Instance ishprop_orderpreserving `{Funext} {A B : Type} {Ale : Le A}
  {Ble : Le B} `{!is_mere_relation B Ble} (f : A -> B)
  : IsHProp (OrderPreserving f).
Proof.
  unfold OrderPreserving; exact _.
Defined.

#[export] Instance orderpreserving_idmap {A : Type} {Ale : Le A}
  : OrderPreserving (idmap : A -> A)
  := fun _ _ => idmap.

#[export] Instance orderpreserving_compose {A B C : Type} {Ale : Le A} {Ble : Le B}
  {Cle : Le C} (g : B -> C) (f : A -> B) `{!OrderPreserving f} `{!OrderPreserving g}
  : OrderPreserving (g o f)
  := fun x y p => order_preserving g (f x) (f y) (order_preserving f x y p).

Class IsScottContinuous@{v u t s u' t' s'} {A : Type@{u}} {B : Type@{u'}}
  {Ale : Le@{u t} A} {Ble : Le@{u' t'} B} `{!IsDcpo@{v u t s} Ale} (f : A -> B)
  := scott_continuous : forall (I : Type@{v}) (x : I -> A) (d : IsDirected x),
      IsSup@{u' t' v s'} (f o x) (f (dcpo_sup x d)).

Arguments scott_continuous {A B Ale Ble _} f {_} I x d.

Section ScottContinuous.
  Universes v u t s u' t' s'.
  Context {A : Type@{u}} {B : Type@{u'}} {Ale : Le@{u t} A} {Ble : Le@{u' t'} B}
    `{!IsDcpo@{v u t s} Ale}.

  #[export] Instance ishprop_isscottcontinuous `{Funext} `{!PartialOrder Ble}
    (f : A -> B)
    : IsHProp (IsScottContinuous@{v u t s u' t' s'} f).
  Proof.
    unfold IsScottContinuous; exact _.
  Defined.

  Local Definition bool_family (x y : A) : Bool -> A
    := fun b => if b then y else x.

  Local Definition isdirected_bool_family (x y : A) (p : x ≤ y)
    : IsDirected (bool_family x y).
  Proof.
    split.
    - exact (tr true).
    - intros i j.
      apply tr; exists true.
      split; destruct i, j; first [exact p | reflexivity].
  Defined.

  Local Definition issup_bool_family (x y : A) (p : x ≤ y)
    : IsSup (bool_family x y) y.
  Proof.
    split.
    - intros [|]; [reflexivity | exact p].
    - intros t ub.
      exact (ub true).
  Defined.

  (** For [x ≤ y], [y] is the supremum of the directed family [bool_family x y], so [f y] is the supremum of [f x] and [f y]. *)
  #[export] Instance orderpreserving_isscottcontinuous (f : A -> B)
    `{!IsScottContinuous@{v u t s u' t' s'} f}
    : OrderPreserving f.
  Proof.
    intros x y p.
    pose (d := isdirected_bool_family x y p).
    rewrite <- (path_dcpo_sup (bool_family x y) d (issup_bool_family x y p)).
    exact (issup_upper (scott_continuous f Bool (bool_family x y) d) false).
  Defined.

End ScottContinuous.

(** ** Pointed dcpos *)

Class IsPointedDcpo@{v u t s} {A : Type@{u}} (Ale : Le@{u t} A) `{Bottom A} := {
  ispointeddcpo_isdcpo :: IsDcpo@{v u t s} Ale ;
  bottom_least : forall x, ⊥ ≤ x
}.

Arguments bottom_least {A Ale _ _} x.

(** ** Subdcpos *)

Section Subdcpo.
  Universes v u t s.
  Context {A : Type@{u}} {Ale : Le@{u t} A} `{!IsDcpo@{v u t s} Ale}.

  Class IsSubdcpo (B : A -> HProp) :=
    issubdcpo : forall (I : Type@{v}) (x : I -> A) (d : IsDirected x),
      (forall i, B (x i)) -> B (dcpo_sup x d).

End Subdcpo.

Arguments IsSubdcpo {A} Ale {_} B.
Arguments issubdcpo {A Ale _} B {_} I x d _.

(** ** Directed subsets *)

(** A subset [D : A -> HProp] is directed if the family [pr1 : sig D -> A] is directed, so the suprema of directed subsets are a special case of the suprema of directed families. Conversely, a partial order in which every directed subset has a supremum is a dcpo, since the image of a family is a subset with the same upper bounds. For a [v]-dcpo this needs the subsets to be valued in [HProp@{v}] and the carrier to live in [Type@{v}]. When all three universes are equal, this shows that [v]-dcpos are the dcpos defined using subsets. *)

Section Subsets.
  Universes v u t s.
  Constraint u <= v.
  Context {A : Type@{u}} {Ale : Le@{u t} A} `{!PartialOrder Ale}.

  Local Definition image_subset {I : Type@{v}} (x : I -> A) : A -> HProp@{v}
    := fun a => merely (hfiber x a).

  Local Definition isupperbound_image_subset {I : Type@{v}} (x : I -> A) (s : A)
    : IsUpperBound x s <-> IsUpperBound (@pr1 A (image_subset x)) s.
  Proof.
    split.
    - intros ub [a p].
      strip_truncations.
      destruct p as [i []].
      exact (ub i).
    - intros ub i.
      exact (ub (x i; tr (i; idpath))).
  Defined.

  Local Definition isdirected_image_subset {I : Type@{v}} (x : I -> A)
    (d : IsDirected x)
    : IsDirected (@pr1 A (image_subset x)).
  Proof.
    split.
    - pose proof (fst d) as i; strip_truncations.
      exact (tr ((x i; tr (i; idpath)))).
    - intros [a p] [b q].
      strip_truncations.
      destruct p as [i []], q as [j []].
      specialize (snd d i j); apply Trunc_functor.
      intros [k r].
      exact ((x k; tr (k; idpath)); r).
  Defined.

  Definition isdcpo_from_subsets
    (sups : forall D : A -> HProp@{v}, IsDirected (@pr1 A D)
      -> {s : A & IsSup (@pr1 A D) s})
    : IsDcpo@{v u t s} Ale.
  Proof.
    split.
    1: exact _.
    intros I x d.
    destruct (sups (image_subset x) (isdirected_image_subset x d)) as [s [ub least]].
    exists s.
    split.
    - exact (snd (isupperbound_image_subset x s) ub).
    - intros t ubt.
      exact (least t (fst (isupperbound_image_subset x t) ubt)).
  Defined.

End Subsets.
