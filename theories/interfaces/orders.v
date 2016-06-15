Require Import HoTTClasses.interfaces.abstract_algebra.

(*
In this file we describe interfaces for ordered structures. Since we are in a
constructive setting we use a pseudo order instead of a total order. Therefore
we also have to include an apartness relation.

Obviously, in case we consider decidable structures these interfaces are quite
inconvenient. Hence we will, later on, provide means to go back and forth
between the usual classical notions and these constructive notions.

On the one hand, if we have an ordinary (total) partial order (≤) with a
corresponding strict order (<), we will prove that we can construct a
FullPartialOrder and PseudoPartialOrder, respectively.

On the other hand, if equality is decidable, we will prove that we have the
usual properties like Trichotomy (<) and TotalRelation (≤).
*)

Class PartialOrder `(Ale : Le A) :=
  { po_preorder:> PreOrder (≤)
  ; po_antisym:> AntiSymmetric (≤) }.

Class TotalOrder `(Ale : Le A) :=
  { total_order_po :> PartialOrder (≤)
  ; total_order_total :> TotalRelation (≤) }.

(*
We define a variant of the order theoretic definition of meet and join
semilattices. Notice that we include a meet operation instead of the
more common:
  ∀ x y, ∃ m, m ≤ x ∧ m ≤ y ∧ ∀ z, z ≤ x → z ≤ y → m ≤ z
Our definition is both stronger and more convenient than the above.
This is needed to prove equavalence with the algebraic definition. We
do this in orders.lattices.
*)
Class MeetSemiLatticeOrder `(Ale : Le A) `{Meet A} :=
  { meet_sl_order :> PartialOrder (≤)
  ; meet_lb_l : ∀ x y, x ⊓ y ≤ x
  ; meet_lb_r : ∀ x y, x ⊓ y ≤ y
  ; meet_glb : ∀ x y z, z ≤ x → z ≤ y → z ≤ x ⊓ y }.

Class JoinSemiLatticeOrder `(Ale : Le A) `{Join A} :=
  { join_sl_order :> PartialOrder (≤)
  ; join_ub_l : ∀ x y, x ≤ x ⊔ y
  ; join_ub_r : ∀ x y, y ≤ x ⊔ y
  ; join_lub : ∀ x y z, x ≤ z → y ≤ z → x ⊔ y ≤ z }.

Class LatticeOrder `(Ale : Le A) `{Meet A} `{Join A} :=
  { lattice_order_meet :> MeetSemiLatticeOrder (≤)
  ; lattice_order_join :> JoinSemiLatticeOrder (≤) }.

Class StrictOrder `(Alt : Lt A) :=
  { strictorder_irrefl :> Irreflexive (<)
  ; strictorder_trans :> Transitive (<) }.

(* The constructive notion of a total strict total order.
   We will prove that (<) is in fact a StrictOrder. *)
Class PseudoOrder `{Aap : Apart A} (Alt : Lt A) :=
  { pseudo_order_apart : IsApart A
  ; pseudo_order_antisym : ∀ x y, ¬(x < y ∧ y < x)
  ; pseudo_order_cotrans :> CoTransitive (<)
  ; apart_iff_total_lt : ∀ x y, x ≶ y ↔ x < y ∨ y < x }.

(* A partial order (≤) with a corresponding (<). We will prove that (<) is in fact
  a StrictOrder *)
Class FullPartialOrder `{Aap : Apart A} (Ale : Le A) (Alt : Lt A) :=
  { strict_po_apart : IsApart A
  ; strict_po_po :> PartialOrder (≤)
  ; strict_po_trans :> Transitive (<)
  ; lt_iff_le_apart : ∀ x y, x < y ↔ x ≤ y ∧ x ≶ y }.

(* A pseudo order (<) with a corresponding (≤). We will prove that (≤) is in fact
  a PartialOrder. *)
Class FullPseudoOrder `{Aap : Apart A} (Ale : Le A) (Alt : Lt A) :=
  { full_pseudo_order_pseudo :> PseudoOrder Alt
  ; le_iff_not_lt_flip : ∀ x y, x ≤ y ↔ ¬y < x }.

Section order_maps.
  Context {A B : Type} {Ale: Le A} {Alt: Lt A} {Ble: Le B} {Blt: Lt B} (f : A → B).

  (* An Order_Pair is just the factoring out of the common parts of
    OrderPreserving and OrderReflecting *)
  Class Order_Pair :=
    { order_morphism_po_a : PartialOrder Ale
    ; order_morphism_po_b : PartialOrder Ble }.

  Class StrictOrder_Pair :=
    { strict_order_morphism_so_a : StrictOrder Alt
    ; strict_order_morphism_so_b : StrictOrder Blt }.

  Class OrderPreserving :=
    { order_preserving_morphism :> Order_Pair
    ; order_preserving : `(x ≤ y → f x ≤ f y) }.

  Class OrderReflecting :=
    { order_reflecting_morphism :> Order_Pair
    ; order_reflecting : `(f x ≤ f y → x ≤ y) }.

  Class OrderEmbedding :=
    { order_embedding_preserving :> OrderPreserving
    ; order_embedding_reflecting :> OrderReflecting }.

  Class OrderIsomorphism `{!Inverse f} :=
    { order_iso_embedding :> OrderEmbedding
    ; order_iso_surjective :> Surjective f }.

  Class StrictlyOrderPreserving :=
    { strictly_order_preserving_morphism :> StrictOrder_Pair
    ; strictly_order_preserving : `(x < y → f x < f y) }.

  Class StrictlyOrderReflecting :=
    { strictly_order_reflecting_morphism :> StrictOrder_Pair
    ; strictly_order_reflecting : `(f x < f y → x < y) }.

  Class StrictOrderEmbedding :=
    { strict_order_embedding_preserving :> StrictlyOrderPreserving
    ; strict_order_embedding_reflecting :> StrictlyOrderReflecting }.
End order_maps.

Arguments Order_Pair {_ _} _ _.
Arguments StrictOrder_Pair {_ _} _ _.

Hint Extern 4 (?f _ ≤ ?f _) => apply (order_preserving f).
Hint Extern 4 (?f _ < ?f _) => apply (strictly_order_preserving f).

(*
We define various classes to describe the order on the lower part of the
algebraic hierarchy. This results in the notion of a PseudoSemiRingOrder, which
specifies the order on the naturals, integers, rationals and reals. This notion
is quite similar to a strictly linearly ordered unital commutative protoring in
Davorin Lešnik's PhD thesis.
*)
Class SemiRingOrder `{Plus A} `{Mult A}
    `{Zero A} `{One A} (Ale : Le A) :=
  { srorder_po :> PartialOrder Ale
  ; srorder_semiring : SemiRing A
  ; srorder_partial_minus : ∀ x y, x ≤ y → ∃ z, y = x + z
  ; srorder_plus :> ∀ z, OrderEmbedding (z +)
  ; nonneg_mult_compat : ∀ x y, PropHolds (0 ≤ x) → PropHolds (0 ≤ y) →
                                PropHolds (0 ≤ x * y) }.

Class StrictSemiRingOrder `{Plus A} `{Mult A}
    `{Zero A} `{One A} (Alt : Lt A) :=
  { strict_srorder_so :> StrictOrder Alt
  ; strict_srorder_semiring : SemiRing A
  ; strict_srorder_partial_minus : ∀ x y, x < y → ∃ z, y = x + z
  ; strict_srorder_plus :> ∀ z, StrictOrderEmbedding (z +)
  ; pos_mult_compat : ∀ x y, PropHolds (0 < x) → PropHolds (0 < y) →
                             PropHolds (0 < x * y) }.

Class PseudoSemiRingOrder `{Apart A} `{Plus A}
    `{Mult A} `{Zero A} `{One A} (Alt : Lt A) :=
  { pseudo_srorder_strict :> PseudoOrder Alt
  ; pseudo_srorder_semiring : SemiRing A
  ; pseudo_srorder_partial_minus : ∀ x y, ¬y < x → ∃ z, y = x + z
  ; pseudo_srorder_plus :> ∀ z, StrictOrderEmbedding (z +)
  ; pseudo_srorder_mult_ext :> StrongBinaryMorphism (.*.)
  ; pseudo_srorder_pos_mult_compat : ∀ x y, PropHolds (0 < x) → PropHolds (0 < y) →
                                            PropHolds (0 < x * y) }.

Class FullPseudoSemiRingOrder `{Apart A} `{Plus A}
    `{Mult A} `{Zero A} `{One A} (Ale : Le A) (Alt : Lt A) :=
  { full_pseudo_srorder_pso :> PseudoSemiRingOrder Alt
  ; full_pseudo_srorder_le_iff_not_lt_flip : ∀ x y, x ≤ y ↔ ¬y < x }.

(* Due to bug #2528 *)
Hint Extern 7 (PropHolds (0 < _ * _)) => eapply @pos_mult_compat : typeclass_instances.
Hint Extern 7 (PropHolds (0 ≤ _ * _)) => eapply @nonneg_mult_compat : typeclass_instances.

(*
Alternatively, we could have defined the standard notion of a RingOrder:

Class RingOrder `{Equiv A} `{Plus A} `{Mult A} `{Zero A} (Ale : Le A) :=
  { ringorder_po :> PartialOrder Ale
  ; ringorder_plus :> ∀ z, OrderPreserving (z +)
  ; ringorder_mult : ∀ x y, 0 ≤ x → 0 ≤ y → 0 ≤ x * y }.

Unfortunately, this notion is too weak when we consider semirings (e.g. the
naturals). Moreover, in case of rings, we prove that this notion is equivalent
to our SemiRingOrder class (see orders.rings.from_ring_order). Hence we omit
defining such a class.

Similarly we prove that a FullSemiRingOrder and a FullPseudoRingOrder are equivalent.

Class FullPseudoRingOrder `{Apart A} `{Plus A}
    `{Mult A} `{Zero A} (Ale : Le A) (Alt : Lt A) :=
  { pseudo_ringorder_spo :> FullPseudoOrder Ale Alt
  ; pseudo_ringorder_mult_ext :> StrongSetoid_BinaryMorphism (.*.)
  ; pseudo_ringorder_plus :> ∀ z, StrictlyOrderPreserving (z +)
  ; pseudo_ringorder_mult : ∀ x y, 0 < x → 0 < y → 0 < x * y }.
*)
