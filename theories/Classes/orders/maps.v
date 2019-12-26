Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.orders.orders
  HoTT.Classes.theory.apartness.

Generalizable Variables A B C R S f g z.

(* If a function between strict partial orders is order preserving (back), we can
  derive that it is strictly order preserving (back) *)
Section strictly_order_preserving.
  Context `{FullPartialOrder A} `{FullPartialOrder B}.

  Global Instance strictly_order_preserving_inj  `{!OrderPreserving (f : A -> B)}
    `{!IsStrongInjective f} :
    StrictlyOrderPreserving f | 20.
  Proof.
  intros x y E.
  apply lt_iff_le_apart in E. apply lt_iff_le_apart.
  destruct E as [E1 E2]. split.
  - apply (order_preserving f);trivial.
  - apply (strong_injective f);trivial.
  Qed.

  Global Instance strictly_order_reflecting_mor `{!OrderReflecting (f : A -> B)}
    `{!StrongExtensionality f} :
    StrictlyOrderReflecting f | 20.
  Proof.
  intros x y E.
  apply lt_iff_le_apart in E. apply lt_iff_le_apart.
  destruct E as [E1 E2]. split.
  - apply (order_reflecting f);trivial.
  - apply (strong_extensionality f);trivial.
  Qed.
End strictly_order_preserving.

(* For structures with a trivial apartness relation
   we have a stronger result of the above *)
Section strictly_order_preserving_dec.
  Context `{FullPartialOrder A} `{!TrivialApart A}
          `{FullPartialOrder B} `{!TrivialApart B}.

  Local Existing Instance strict_po_apart.

  Global Instance dec_strictly_order_preserving_inj
    `{!OrderPreserving (f : A -> B)}
    `{!IsInjective f} :
    StrictlyOrderPreserving f | 19.
  Proof.
  pose proof (dec_strong_injective f).
  apply _.
  Qed.

  Global Instance dec_strictly_order_reflecting_mor
    `{!OrderReflecting (f : A -> B)}
    : StrictlyOrderReflecting f | 19.
  Proof.
  pose proof (dec_strong_morphism f). apply _.
  Qed.
End strictly_order_preserving_dec.

Section pseudo_injective.
  Context `{PseudoOrder A} `{PseudoOrder B}.

  Local Existing Instance pseudo_order_apart.

  Instance pseudo_order_embedding_ext `{!StrictOrderEmbedding (f : A -> B)} :
    StrongExtensionality f.
  Proof.
  intros x y E.
  apply apart_iff_total_lt;apply apart_iff_total_lt in E.
  destruct E; [left | right]; apply (strictly_order_reflecting f);trivial.
  Qed.

  Lemma pseudo_order_embedding_inj `{!StrictOrderEmbedding (f : A -> B)} :
    IsStrongInjective f.
  Proof.
  split;try apply _.
  intros x y E.
  apply apart_iff_total_lt;apply apart_iff_total_lt in E.
  destruct E; [left | right]; apply (strictly_order_preserving f);trivial.
  Qed.
End pseudo_injective.

(* If a function between pseudo partial orders is strictly order preserving (back),
   we can derive that it is order preserving (back) *)
Section full_pseudo_strictly_preserving.
  Context `{FullPseudoOrder A} `{FullPseudoOrder B}.

  Local Existing Instance pseudo_order_apart.

  Lemma full_pseudo_order_preserving `{!StrictlyOrderReflecting (f : A -> B)}
    : OrderPreserving f.
  Proof.
  intros x y E1.
  apply le_iff_not_lt_flip;apply le_iff_not_lt_flip in E1.
  intros E2. apply E1.
  apply (strictly_order_reflecting f).
  trivial.
  Qed.

  Lemma full_pseudo_order_reflecting `{!StrictlyOrderPreserving (f : A -> B)}
    : OrderReflecting f.
  Proof.
  intros x y E1.
  apply le_iff_not_lt_flip;apply le_iff_not_lt_flip in E1.
  intros E2. apply E1.
  apply (strictly_order_preserving f).
  trivial.
  Qed.
End full_pseudo_strictly_preserving.

(* Some helper lemmas to easily transform order preserving instances. *)
Section order_preserving_ops.
  Context `{Le R}.

  Lemma order_preserving_flip {op} `{!Commutative op} `{!OrderPreserving (op z)}
    : OrderPreserving (fun y => op y z).
  Proof.
  intros x y E.
  rewrite 2!(commutativity _ z).
  apply order_preserving;trivial.
  Qed.

  Lemma order_reflecting_flip {op} `{!Commutative op}
    `{!OrderReflecting (op z) }
    : OrderReflecting (fun y => op y z).
  Proof.
  intros x y E.
  apply (order_reflecting (op z)).
  rewrite 2!(commutativity (f:=op) z).
  trivial.
  Qed.

  Lemma order_preserving_nonneg (op : R -> R -> R) `{!Zero R}
    `{forall z, PropHolds (0 ≤ z) -> OrderPreserving (op z)} z
    : 0 ≤ z -> forall x y, x ≤ y -> op z x ≤ op z y.
  Proof.
  auto.
  Qed.

  Lemma order_preserving_flip_nonneg (op : R -> R -> R) `{!Zero R}
    {E:forall z, PropHolds (0 ≤ z) -> OrderPreserving (fun y => op y z)} z
    : 0 ≤ z -> forall x y, x ≤ y -> op x z ≤ op y z.
  Proof.
  apply E.
  Qed.

  Context `{Lt R}.

  Lemma order_reflecting_pos (op : R -> R -> R) `{!Zero R}
    {E:forall z, PropHolds (0 < z) -> OrderReflecting (op z)} z
    : 0 < z -> forall x y, op z x ≤ op z y -> x ≤ y.
  Proof.
  apply E.
  Qed.

  Lemma order_reflecting_flip_pos (op : R -> R -> R) `{!Zero R}
    {E:forall z, PropHolds (0 < z) -> OrderReflecting (fun y => op y z)} z
    : 0 < z -> forall x y, op x z ≤ op y z -> x ≤ y.
  Proof.
  apply E.
  Qed.

End order_preserving_ops.

Section strict_order_preserving_ops.
  Context `{Lt R}.

  Lemma strictly_order_preserving_flip {op} `{!Commutative op}
    `{!StrictlyOrderPreserving (op z)}
    : StrictlyOrderPreserving (fun y => op y z).
  Proof.
  intros x y E.
  rewrite 2!(commutativity _ z).
  apply strictly_order_preserving;trivial.
  Qed.

  Lemma strictly_order_reflecting_flip {op} `{!Commutative op}
    `{!StrictlyOrderReflecting (op z) }
    : StrictlyOrderReflecting (fun y => op y z).
  Proof.
  intros x y E.
  apply (strictly_order_reflecting (op z)).
  rewrite 2!(commutativity (f:=op) z).
  trivial.
  Qed.

  Lemma strictly_order_preserving_pos (op : R -> R -> R) `{!Zero R}
    {E:forall z, PropHolds (0 < z) -> StrictlyOrderPreserving (op z)} z
    : 0 < z -> forall x y, x < y -> op z x < op z y.
  Proof.
  apply E.
  Qed.

  Lemma strictly_order_preserving_flip_pos (op : R -> R -> R) `{!Zero R}
    {E:forall z, PropHolds (0 < z) -> StrictlyOrderPreserving (fun y => op y z)} z
    : 0 < z -> forall x y, x < y -> op x z < op y z.
  Proof.
  apply E.
  Qed.

End strict_order_preserving_ops.

Lemma projected_partial_order `{IsHSet A} {Ale : Le A}
  `{is_mere_relation A Ale} `{Ble : Le B}
  (f : A -> B) `{!IsInjective f} `{!PartialOrder Ble}
  : (forall x y, x ≤ y <-> f x ≤ f y) -> PartialOrder Ale.
Proof.
intros P. repeat split.
- apply _.
- apply _.
- intros x. apply P. apply reflexivity.
- intros x y z E1 E2. apply P.
  transitivity (f y); apply P;trivial.
- intros x y E1 E2. apply (injective f).
  apply (antisymmetry (≤)); apply P;trivial.
Qed.

Lemma projected_total_order `{Ale : Le A} `{Ble : Le B}
  (f : A -> B) `{!TotalRelation Ble}
  : (forall x y, x ≤ y <-> f x ≤ f y) -> TotalRelation Ale.
Proof.
intros P x y.
destruct (total (≤) (f x) (f y)); [left | right]; apply P;trivial.
Qed.

Lemma projected_strict_order `{Alt : Lt A} `{is_mere_relation A lt} `{Blt : Lt B}
  (f : A -> B) `{!StrictOrder Blt}
  : (forall x y, x < y <-> f x < f y) -> StrictOrder Alt.
Proof.
intros P. split.
- apply _.
- intros x E. destruct (irreflexivity (<) (f x)). apply P. trivial.
- intros x y z E1 E2. apply P. transitivity (f y); apply P;trivial.
Qed.

Lemma projected_pseudo_order `{IsApart A} `{Alt : Lt A} `{is_mere_relation A lt}
  `{Apart B} `{Blt : Lt B}
  (f : A -> B) `{!IsStrongInjective f} `{!PseudoOrder Blt}
  : (forall x y, x < y <-> f x < f y) -> PseudoOrder Alt.
Proof.
pose proof (strong_injective_mor f).
intros P. split; try apply _.
- intros x y E. apply (pseudo_order_antisym (f x) (f y)).
  split; apply P,E.
- intros x y E z. apply P in E.
  apply (merely_destruct (cotransitive E (f z)));
  intros [?|?];apply tr; [left | right]; apply P;trivial.
- intros x y; split; intros E.
  + apply (strong_injective f) in E.
    apply apart_iff_total_lt in E.
    destruct E; [left | right]; apply P;trivial.
  + apply (strong_extensionality f).
    apply apart_iff_total_lt.
    destruct E; [left | right]; apply P;trivial.
Qed.

Lemma projected_full_pseudo_order `{IsApart A} `{Ale : Le A} `{Alt : Lt A}
  `{is_mere_relation A le} `{is_mere_relation A lt}
  `{Apart B} `{Ble : Le B} `{Blt : Lt B}
  (f : A -> B) `{!IsStrongInjective f} `{!FullPseudoOrder Ble Blt}
  : (forall x y, x ≤ y <-> f x ≤ f y) -> (forall x y, x < y <-> f x < f y) ->
    FullPseudoOrder Ale Alt.
Proof.
intros P1 P2. split.
- apply _.
- apply (projected_pseudo_order f);assumption.
- intros x y; split; intros E.
  + intros F. destruct (le_not_lt_flip (f y) (f x));[apply P1|apply P2];trivial.
  + apply P1. apply not_lt_le_flip.
    intros F. apply E,P2. trivial.
Qed.

Instance id_order_preserving `{PartialOrder A} : OrderPreserving (@id A).
Proof.
red;trivial.
Qed.

Instance id_order_reflecting `{PartialOrder A} : OrderReflecting (@id A).
Proof.
red;trivial.
Qed.

Section composition.
  Context {A B C} `{Le A} `{Le B} `{Le C} (f : A -> B) (g : B -> C).

  Instance compose_order_preserving:
    OrderPreserving f -> OrderPreserving g -> OrderPreserving (g ∘ f).
  Proof.
  red;intros. unfold Compose.
  do 2 apply (order_preserving _).
  trivial.
  Qed.

  Instance compose_order_reflecting:
    OrderReflecting f -> OrderReflecting g -> OrderReflecting (g ∘ f).
  Proof.
  intros ?? x y E. unfold Compose in E.
  do 2 apply (order_reflecting _) in E.
  trivial.
  Qed.

  Instance compose_order_embedding:
    OrderEmbedding f -> OrderEmbedding g -> OrderEmbedding (g ∘ f) := {}.
End composition.

Hint Extern 4 (OrderPreserving (_ ∘ _)) =>
  class_apply @compose_order_preserving : typeclass_instances.
Hint Extern 4 (OrderReflecting (_ ∘ _)) =>
  class_apply @compose_order_reflecting : typeclass_instances.
Hint Extern 4 (OrderEmbedding (_ ∘ _)) =>
  class_apply @compose_order_embedding : typeclass_instances.

