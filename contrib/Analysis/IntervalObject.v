(** * Interval objects *)

From HoTT Require Import Basics Types.
From HoTT.Spaces Require Import Nat.Core.
From HoTT.Classes.interfaces Require Import canonical_names.

Local Open Scope type_scope.
Local Open Scope nat_scope.

(** We formalize Escardó and Simpson's interval objects in type theory: cancellative midpoint algebras, convex bodies, which have an operation taking the iterated midpoint [m(x 0, m(x 1, m(x 2, ...)))] of a sequence, and interval objects, which are homotopy-initial bipointed convex bodies. The iteration operator of a convex body is unique when it exists, and its existence is equivalent to the contractibility, for every sequence [x], of the type of sequences [a] with [a i = m(x i, a i.+1)] for all [i]. *)

(** ** Cancellative midpoint algebras *)

Class Midpoint A := midpoint : A -> A -> A.

(** A binary operation is medial when it satisfies the transposition law. *)
Class Medial {A} (f : A -> A -> A)
  := medial : forall x y z w, f (f x y) (f z w) = f (f x z) (f y w).

Class IsCancellativeMidpointAlgebra (A : Type) {Am : Midpoint A} :=
  { midpoint_set :: IsHSet A
  ; midpoint_idempotent :: BinaryIdempotent midpoint
  ; midpoint_commutative :: Commutative midpoint
  ; midpoint_medial :: Medial midpoint
  ; midpoint_cancellation :: forall z, RightCancellation midpoint z }.

Definition issig_IsCancellativeMidpointAlgebra (A : Type) {Am : Midpoint A}
  : _ <~> IsCancellativeMidpointAlgebra A
  := ltac:(issig).

Instance ishprop_iscancellativemidpointalgebra `{Funext} (A : Type) {Am : Midpoint A}
  : IsHProp (IsCancellativeMidpointAlgebra A).
Proof.
  napply (istrunc_equiv_istrunc _ (issig_IsCancellativeMidpointAlgebra A)).
  snapply istrunc_sigma; [exact _ | intro].
  unfold BinaryIdempotent, Idempotent, Commutative, Medial, RightCancellation.
  exact _.
Defined.

(** ** The iteration property *)

(** For a binary operation [m], an iteration operator [M] sends a sequence [x] to an element [M x] that behaves like [m(x 0, m(x 1, m(x 2, ...)))]: it unfolds once, and it is the first element of every sequence [y] with [y i = m(x i, y i.+1)]. *)
Definition IsIterationOperator@{i} {A : Type@{i}} {Am : Midpoint A} (M : (nat -> A) -> A)
  : Type@{i}
  := (forall x, M x = midpoint (x 0) (M (fun n => x n.+1)))
    * (forall x y, (forall i, y i = midpoint (x i) (y i.+1)) -> y 0 = M x).

Definition IterationOperator@{i} (A : Type@{i}) {Am : Midpoint A} : Type@{i}
  := {M : (nat -> A) -> A & IsIterationOperator M}.

(** The sequence [x] with its first [k] elements dropped. *)
Fixpoint seq_drop {A} (k : nat) (x : nat -> A) : nat -> A
  := match k with
     | 0 => x
     | k.+1 => fun n => seq_drop k x n.+1
     end.

Definition seq_drop_add@{i} {A : Type@{i}} (k : nat) (x : nat -> A) (n : nat)
  : seq_drop k x n = x (n + k).
Proof.
  induction k as [|k IHk] in n |- *.
  - exact (ap@{Set i} x (inverse@{Set} (nat_add_zero_r n))).
  - exact (IHk n.+1 @ ap@{Set i} x (inverse@{Set} (nat_add_succ_r n k))).
Defined.

Section Iteration.
  Universe i.
  Context {A : Type@{i}} {Am : Midpoint A}.

  (** The type of sequences of iterated midpoints of the tails of [x]. *)
  Definition IteratedMidpoints@{} (x : nat -> A) : Type@{i}
    := {a : nat -> A & forall i, a i = midpoint (x i) (a i.+1)}.

  (** An iteration operator determines the iterated midpoints of all tails. *)
  Definition iterated_midpoints_iteration_operator@{} (M : (nat -> A) -> A)
    (HM : IsIterationOperator M) (x : nat -> A)
    : IteratedMidpoints x.
  Proof.
    exists (fun k => M (seq_drop k x)).
    intro i.
    lhs napply (fst HM).
    exact (ap (fun z => midpoint z _) (seq_drop_add i x 0)).
  Defined.

  (** Any two iteration operators agree. *)
  Definition path_iteration_operator@{} `{Funext} (M N : (nat -> A) -> A)
    (HM : IsIterationOperator M) (HN : IsIterationOperator N)
    : M = N.
  Proof.
    funext x.
    exact (snd HN x _ (iterated_midpoints_iteration_operator M HM x).2).
  Defined.

  (** A map preserving midpoints commutes with iteration operators. *)
  Definition preserves_iteration_operator@{j} {B : Type@{j}} {Bm : Midpoint B}
    (f : A -> B) (p : forall x y, f (midpoint x y) = midpoint (f x) (f y))
    (M : (nat -> A) -> A) (HM : IsIterationOperator M)
    (N : (nat -> B) -> B) (HN : IsIterationOperator N) (x : nat -> A)
    : f (M x) = N (f o x).
  Proof.
    pose (a := iterated_midpoints_iteration_operator M HM x).
    apply (snd HN (f o x) (f o a.1)).
    intro i.
    exact (ap f (a.2 i) @ p _ _).
  Defined.

  Context `{Funext} `{IsHSet A}.

  #[export] Instance ishprop_isiterationoperator@{} (M : (nat -> A) -> A)
    : IsHProp (IsIterationOperator M)
    := _.

  (** The iteration property is a proposition. *)
  #[export] Instance ishprop_iterationoperator@{} : IsHProp (IterationOperator A).
  Proof.
    apply hprop_allpath; intros [M HM] [N HN].
    apply path_sigma_hprop; cbn.
    exact (path_iteration_operator M N HM HN).
  Defined.

  (** In the presence of an iteration operator, iterated midpoints are unique. *)
  Definition ishprop_iteratedmidpoints
    (M : (nat -> A) -> A) (HM : IsIterationOperator M) (x : nat -> A)
    : IsHProp (IteratedMidpoints x).
  Proof.
    apply hprop_allpath; intros [a p] [b q].
    apply path_sigma_hprop; cbn.
    funext k.
    (** Both [a] and [b] shifted by [k] are iterated midpoints of [x] shifted by [k], so they start with the same element. *)
    transitivity (M (fun n => x (n + k))).
    - exact (snd HM (fun n => x (n + k)) (fun n => a (n + k)) (fun i => p (i + k))).
    - exact (snd HM (fun n => x (n + k)) (fun n => b (n + k)) (fun i => q (i + k)))^.
  Defined.

  (** An iteration operator is equivalently the contractibility of all types of iterated midpoints. *)
  Definition equiv_iteration_operator_contr_iterated_midpoints
    : IterationOperator A <~> (forall x, Contr (IteratedMidpoints x)).
  Proof.
    apply equiv_iff_hprop.
    - intros [M HM] x.
      pose (ishprop_iteratedmidpoints M HM x).
      exact (contr_inhabited_hprop _ (iterated_midpoints_iteration_operator M HM x)).
    - intro c.
      exists (fun x => (center (IteratedMidpoints x)).1 0).
      split.
      + intro x.
        lhs napply (center (IteratedMidpoints x)).2.
        apply ap.
        (** The tail of the iterated midpoints of [x] is the sequence of iterated midpoints of the tail of [x]. *)
        set (a := center (IteratedMidpoints x)).
        pose (a' := (fun i => a.1 i.+1; fun i => a.2 i.+1)
                    : IteratedMidpoints (fun n => x n.+1)).
        exact (ap (fun b => b.1 0) (contr a')^).
      + intros x y p.
        exact (ap (fun b => b.1 0) (contr (y; p)))^.
  Defined.

End Iteration.

(** ** Convex bodies *)

(** A convex body is a cancellative midpoint algebra with an iteration operator. Since the iteration operator is unique, being a convex body is a property of a midpoint operation. *)
Class IsConvexBody (A : Type) {Am : Midpoint A} :=
  { convex_body_midpoint_algebra :: IsCancellativeMidpointAlgebra A
  ; convex_body_iteration : IterationOperator A }.

Definition issig_IsConvexBody (A : Type) {Am : Midpoint A}
  : _ <~> IsConvexBody A
  := ltac:(issig).

Instance ishprop_isconvexbody@{i} `{Funext} (A : Type@{i}) {Am : Midpoint A}
  : IsHProp (IsConvexBody A).
Proof.
  exact (istrunc_equiv_istrunc _ (issig_IsConvexBody A)).
Defined.

(** A bipointed convex body is a convex body with two points. *)
Record BipointedConvexBody := {
  bcb_carrier : Type;
  bcb_midpoint :: Midpoint bcb_carrier;
  bcb_isconvexbody :: IsConvexBody bcb_carrier;
  bcb_left : bcb_carrier;
  bcb_right : bcb_carrier;
}.

Coercion bcb_carrier : BipointedConvexBody >-> Sortclass.

(** A homomorphism of bipointed convex bodies preserves the two points and the midpoint operation. It automatically commutes with the iteration operators, see [preserves_iteration_operator]. *)
Definition IsConvexBodyHom {A B : BipointedConvexBody} (f : A -> B) : Type
  := (f (bcb_left A) = bcb_left B) * (f (bcb_right A) = bcb_right B)
    * (forall x y, f (midpoint x y) = midpoint (f x) (f y)).

Definition ConvexBodyHom (A B : BipointedConvexBody) : Type
  := {f : A -> B & IsConvexBodyHom f}.

Instance ishprop_isconvexbodyhom `{Funext} {A B : BipointedConvexBody} (f : A -> B)
  : IsHProp (IsConvexBodyHom f)
  := _.

(** ** Interval objects *)

(** An interval object is a homotopy-initial bipointed convex body. *)
Definition IsIntervalObject (A : BipointedConvexBody) : Type
  := forall B : BipointedConvexBody, Contr (ConvexBodyHom A B).

(** Since the underlying types of convex bodies are sets, contractibility of the type of homomorphisms amounts to existence of a homomorphism and pointwise uniqueness. *)
Definition contr_convexbodyhom_iff `{Funext} (A B : BipointedConvexBody)
  : Contr (ConvexBodyHom A B)
    <-> ConvexBodyHom A B * (forall f g : ConvexBodyHom A B, f.1 == g.1).
Proof.
  split.
  - intro c.
    refine (center _, _).
    intros f g x.
    exact (ap10 (ap pr1 (path_contr f g)) x).
  - intros [f u].
    snapply (contr_inhabited_hprop _ f).
    apply hprop_allpath; intros g h.
    apply path_sigma_hprop.
    funext x; exact (u g h x).
Defined.
