Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.orders
  HoTTClasses.orders.orders
  HoTTClasses.theory.apartness.

Local Existing Instance order_morphism_po_a.
Local Existing Instance order_morphism_po_b.
Local Existing Instance strict_order_morphism_so_a.
Local Existing Instance strict_order_morphism_so_b.

(* If a function between strict partial orders is order preserving (back), we can
  derive that it is strictly order preserving (back) *)
Section strictly_order_preserving.
  Context `{FullPartialOrder A} `{FullPartialOrder B}.

  Global Instance strictly_order_preserving_inj  `{!OrderPreserving (f : A → B)}
    `{!StrongInjective f} :
    StrictlyOrderPreserving f | 20.
  Proof.
  repeat (split; try apply _).
  intros x y E.
  apply lt_iff_le_apart in E. apply lt_iff_le_apart.
  destruct E as [E1 E2]. split.
  - apply (order_preserving f);trivial.
  - apply (strong_injective f);trivial.
  Qed.

  Global Instance strictly_order_reflecting_mor `{!OrderReflecting (f : A → B)}
    `{!StrongMorphism f} :
    StrictlyOrderReflecting f | 20.
  Proof.
  repeat (split; try apply _).
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

  Global Instance dec_strictly_order_preserving_inj  `{!OrderPreserving (f : A → B)}
    `{!Injective f} :
    StrictlyOrderPreserving f | 19.
  Proof.
  pose proof (dec_strong_injective f).
  apply _.
  Qed.

  Global Instance dec_strictly_order_reflecting_mor `{!OrderReflecting (f : A → B)} :
    StrictlyOrderReflecting f | 19.
  Proof.
  pose proof (dec_strong_morphism f). apply _.
  Qed.
End strictly_order_preserving_dec.

Section pseudo_injective.
  Context `{PseudoOrder A} `{PseudoOrder B}.

  Local Existing Instance pseudo_order_apart.

  Instance pseudo_order_embedding_ext `{!StrictOrderEmbedding (f : A → B)} :
    StrongMorphism f.
  Proof.
  split; try apply _.
  intros x y E.
  apply apart_iff_total_lt;apply apart_iff_total_lt in E.
  destruct E; [left | right]; apply (strictly_order_reflecting f);trivial.
  Qed.

  Lemma pseudo_order_embedding_inj `{!StrictOrderEmbedding (f : A → B)} :
    StrongInjective f.
  Proof.
  split; try apply _.
  intros x y E.
  apply apart_iff_total_lt;apply apart_iff_total_lt in E.
  destruct E; [left | right]; apply (strictly_order_preserving f);trivial.
  Qed.
End pseudo_injective.

(* If a function between pseudo partial orders is strictly order preserving (back), we can
  derive that it is order preserving (back) *)
Section full_pseudo_strictly_preserving.
  Context `{FullPseudoOrder A} `{FullPseudoOrder B}.

  Local Existing Instance pseudo_order_apart.

  Lemma full_pseudo_order_preserving `{!StrictlyOrderReflecting (f : A → B)}
    : OrderPreserving f.
  Proof.
  repeat (split; try apply _).
  intros x y E1.
  apply le_iff_not_lt_flip;apply le_iff_not_lt_flip in E1.
  intros E2. apply E1.
  apply (strictly_order_reflecting f).
  trivial.
  Qed.

  Lemma full_pseudo_order_reflecting `{!StrictlyOrderPreserving (f : A → B)}
    : OrderReflecting f.
  Proof.
  repeat (split; try apply _).
  intros x y E1.
  apply le_iff_not_lt_flip;apply le_iff_not_lt_flip in E1.
  intros E2. apply E1.
  apply (strictly_order_preserving f).
  trivial.
  Qed.
End full_pseudo_strictly_preserving.

(* Some helper lemmas to easily transform order preserving instances. *)
Section order_preserving_ops.
  Context `{Le R} `{Lt R}.

  Lemma order_preserving_flip {op} `{!Commutative op} `{!OrderPreserving (op z)}
    : OrderPreserving (λ y, op y z).
  Proof.
  repeat (split; try apply _).
  intros x y E.
  rewrite 2!(commutativity _ z).
  apply order_preserving;trivial.
  Qed.

  Lemma strictly_order_preserving_flip {op} `{!Commutative op}
    `{!StrictlyOrderPreserving (op z)}
    : StrictlyOrderPreserving (λ y, op y z).
  Proof.
  repeat (split; try apply _).
  intros x y E.
  rewrite 2!(commutativity _ z).
  apply strictly_order_preserving;trivial.
  Qed.

  Lemma order_reflecting_flip {op} `{!Commutative op}
    `{!OrderReflecting (op z) }
    : OrderReflecting (λ y, op y z).
  Proof.
  repeat (split; try apply _).
  intros x y E.
  apply (order_reflecting (op z)).
  rewrite 2!(commutativity (f:=op) z).
  trivial.
  Qed.

  Lemma strictly_order_reflecting_flip {op} `{!Commutative op}
    `{!StrictlyOrderReflecting (op z) }
    : StrictlyOrderReflecting (λ y, op y z).
  Proof.
  repeat (split; try apply _).
  intros x y E.
  apply (strictly_order_reflecting (op z)).
  rewrite 2!(commutativity (f:=op) z).
  trivial.
  Qed.

  Lemma order_preserving_nonneg (op : R → R → R) `{!Zero R}
    `{∀ z, PropHolds (0 ≤ z) → OrderPreserving (op z)} z
    : 0 ≤ z → ∀ x y, x ≤ y → op z x ≤ op z y.
  Proof.
  auto.
  Qed.

  Lemma order_preserving_flip_nonneg (op : R → R → R) `{!Zero R}
    {E:∀ z, PropHolds (0 ≤ z) → OrderPreserving (λ y, op y z)} z
    : 0 ≤ z → ∀ x y, x ≤ y → op x z ≤ op y z.
  Proof.
  apply E.
  Qed.

  Lemma strictly_order_preserving_pos (op : R → R → R) `{!Zero R}
    {E:∀ z, PropHolds (0 < z) → StrictlyOrderPreserving (op z)} z
    : 0 < z → ∀ x y, x < y → op z x < op z y.
  Proof.
  apply E.
  Qed.

  Lemma strictly_order_preserving_flip_pos (op : R → R → R) `{!Zero R}
    {E:∀ z, PropHolds (0 < z) → StrictlyOrderPreserving (λ y, op y z)} z
    : 0 < z → ∀ x y, x < y → op x z < op y z.
  Proof.
  apply E.
  Qed.

  Lemma order_reflecting_pos (op : R → R → R) `{!Zero R}
    {E:∀ z, PropHolds (0 < z) → OrderReflecting (op z)} z
    : 0 < z → ∀ x y, op z x ≤ op z y → x ≤ y.
  Proof.
  apply E.
  Qed.

  Lemma order_reflecting_flip_pos (op : R → R → R) `{!Zero R}
    {E:∀ z, PropHolds (0 < z) → OrderReflecting (λ y, op y z)} z
    : 0 < z → ∀ x y, op x z ≤ op y z → x ≤ y.
  Proof.
  apply E.
  Qed.
End order_preserving_ops.

Lemma projected_partial_order `{Ale : Le A} `{Ble : Le B}
  (f : A → B) `{!Injective f} `{!PartialOrder Ble}
  : (∀ x y, x ≤ y ↔ f x ≤ f y) → PartialOrder Ale.
Proof.
intros P. repeat split.
- intros x. apply P. apply reflexivity.
- intros x y z E1 E2. apply P.
  transitivity (f y); apply P;trivial.
- intros x y E1 E2. apply (injective f).
  apply (antisymmetry (≤)); apply P;trivial.
Qed.

Lemma projected_total_order `{Ale : Le A} `{Ble : Le B}
  (f : A → B) `{!TotalRelation Ble}
  : (∀ x y, x ≤ y ↔ f x ≤ f y) → TotalRelation Ale.
Proof.
intros P x y.
destruct (total (≤) (f x) (f y)); [left | right]; apply P;trivial.
Qed.

Lemma projected_strict_order `{Alt : Lt A} `{Blt : Lt B}
  (f : A → B) `{!StrictOrder Blt}
  : (∀ x y, x < y ↔ f x < f y) → StrictOrder Alt.
Proof.
intros P. split.
- intros x E. destruct (irreflexivity (<) (f x)). apply P. trivial.
- intros x y z E1 E2. apply P. transitivity (f y); apply P;trivial.
Qed.

Lemma projected_pseudo_order `{Apart A} `{Alt : Lt A} `{Apart B} `{Blt : Lt B}
  (f : A → B) `{!StrongInjective f} `{!PseudoOrder Blt}
  : (∀ x y, x < y ↔ f x < f y) → PseudoOrder Alt.
Proof.
pose proof (strong_injective_mor f).
pose proof (strong_mor_a f).
pose proof (strong_mor_b f).
intros P. split; try apply _.
- intros x y E. apply (pseudo_order_antisym (f x) (f y)).
  split; apply P,E.
- intros x y E z. apply P in E.
  destruct (cotransitive E (f z)); [left | right]; apply P;trivial.
- intros x y; split; intros E.
  + apply (strong_injective f) in E.
    apply apart_iff_total_lt in E.
    destruct E; [left | right]; apply P;trivial.
  + apply (strong_extensionality f).
    apply apart_iff_total_lt.
    destruct E; [left | right]; apply P;trivial.
Qed.

Lemma projected_full_pseudo_order `{Apart A} `{Ale : Le A} `{Alt : Lt A}
  `{Apart B} `{Ble : Le B} `{Blt : Lt B}
  (f : A → B) `{!StrongInjective f} `{!FullPseudoOrder Ble Blt}
  : (∀ x y, x ≤ y ↔ f x ≤ f y) → (∀ x y, x < y ↔ f x < f y) → FullPseudoOrder Ale Alt.
Proof.
intros P1 P2. split.
- apply (projected_pseudo_order f);assumption.
- intros x y; split; intros E.
  + intros F. destruct (le_not_lt_flip (f y) (f x));[apply P1|apply P2];trivial.
  + apply P1. apply not_lt_le_flip.
    intros F. apply E,P2. trivial.
Qed.

Instance id_order_morphism `{PartialOrder A} : Order_Pair (_:Le A) (_:Le A) := {}.

Instance id_order_preserving `{PartialOrder A} : OrderPreserving (@id A).
Proof.
split; try apply _.
trivial.
Qed.

Instance id_order_reflecting `{PartialOrder A} : OrderReflecting (@id A).
Proof.
split; try apply _. trivial.
Qed.

Section composition.
  Context {A B C} `{Le A} `{Le B} `{Le C} (f : A → B) (g : B → C).

  (* TODO replace with mode stuff? *)
  Instance compose_order_pair:
    Order_Pair (_:Le A) (_:Le B) → Order_Pair (_:Le B) (_:Le C) →
    Order_Pair (_:Le A) (_:Le C).
  Proof.
  split;[ apply order_morphism_po_a | apply order_morphism_po_b ].
  Qed.

  Instance compose_order_preserving:
    OrderPreserving f → OrderPreserving g → OrderPreserving (g ∘ f).
  Proof.
  repeat (split; try apply _).
  intros. unfold compose.
  do 2 apply (order_preserving _).
  trivial.
  Qed.

  Instance compose_order_reflecting:
    OrderReflecting f → OrderReflecting g → OrderReflecting (g ∘ f).
  Proof.
  split; try apply _.
  intros x y E. unfold compose in E.
  do 2 apply (order_reflecting _) in E.
  trivial.
  Qed.

  Instance compose_order_embedding:
    OrderEmbedding f → OrderEmbedding g → OrderEmbedding (g ∘ f) := {}.
End composition.

Hint Extern 4 (Order_Pair (_ ∘ _)) =>
  class_apply @compose_order_pair : typeclass_instances.
Hint Extern 4 (OrderPreserving (_ ∘ _)) =>
  class_apply @compose_order_preserving : typeclass_instances.
Hint Extern 4 (OrderReflecting (_ ∘ _)) =>
  class_apply @compose_order_reflecting : typeclass_instances.
Hint Extern 4 (OrderEmbedding (_ ∘ _)) =>
  class_apply @compose_order_embedding : typeclass_instances.

