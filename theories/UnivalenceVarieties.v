(* -*- mode: coq; mode: visual-line -*- *)
(** * Varieties of univalence *)

Require Import HoTT.Basics HoTT.Types.
Require Import Fibrations Idempotents EquivalenceVarieties UnivalenceImpliesFunext.
Local Open Scope path_scope.

(** The standard univalence axiom type [Univalence_type] is defined in [UnivalenceImpliesFunext]. *)

(** A weaker form that only asserts that we can make equivalences into paths with a computation rule (no uniqueness rule). *)
Definition WeakUnivalence :=
  { etop : forall A B, (A <~> B) -> (A = B) &
    forall A B (f : A <~> B), equiv_path A B (etop A B f) = f }.

(** The same thing, stated with an incoherent notion of equivalence but a pointwise equality for the computation rule.  *)
Definition IncoherentWeakUnivalence :=
  { etop : forall A B (f : A -> B) (g : B -> A),
      (f o g == idmap) -> (g o f == idmap) -> (A = B) &
    forall A B f g H K, equiv_path A B (etop A B f g H K) == f }.

(** Finally, it even suffices to consider only just a few special cases. This is due to Ian Orton and Andrew Pitts. *)
Record VeryWeakUnivalence :=
  { unit : forall A, A = { a : A & Unit };
    flip : forall A B (C : A -> B -> Type),
        { a : A & { b : B & C a b }} = { b : B & { a : A & C a b }};
    contract : forall A, Contr A -> A = Unit;
    unit_comp : forall A a, transport idmap (unit A) a = (a;tt);
    flip_comp : forall A B C (a:A) (b:B) (c : C a b),
        transport idmap (flip A B C) (a ; (b ; c)) = (b ; (a ; c))
  }.

Theorem WeakUnivalence_implies_Univalence :
  WeakUnivalence -> Univalence_type.
Proof.
  intros [etop H] A.
  apply isequiv_from_functor_sigma.
  serapply isequiv_contr_contr.
  serapply (contr_retracttype
            (Build_RetractOf _ _
                             (fun Be => (Be.1 ; equiv_path A Be.1 Be.2))
                             (fun Bf => (Bf.1 ; etop A Bf.1 Bf.2))
                             _)).
  intros [B f].
  refine (path_sigma' (fun B => A <~> B) 1 (H A B f)).
Defined.

(** For this one and the next one, we need to assume funext to start with (so that these forms of univalence, unlike the usual one, probably don't suffice to prove funext from). *)
Theorem IncoherentWeakUnivalence_implies_Univalence `{Funext} :
  IncoherentWeakUnivalence -> Univalence_type.
Proof.
  intros [etop K].
  apply WeakUnivalence_implies_Univalence.
  transparent assert (etop' : (forall A B, (A <~> B) -> (A = B))).
  { intros A B f.
    refine (etop A B f f^-1 _ _).
    - intros x; apply eisretr.
    - intros x; apply eissect. }
  exists etop'.
  intros A B f.
  apply path_equiv, path_arrow, K.
Defined.

Theorem VeryWeakUnivalence_implies_Univalence `{Funext} :
  VeryWeakUnivalence -> Univalence_type.
Proof.
  intros vwu. apply WeakUnivalence_implies_Univalence.
  simple refine (_;_).
  { intros A B f.
    refine (unit vwu A @ _ @ (unit vwu B)^).
    refine (_ @ flip vwu A B (fun a b => f a = b) @ _).
    - apply ap, path_arrow; intros a.
      symmetry; rapply (contract vwu).
    - apply ap, path_arrow; intros b.
      apply (contract vwu), fcontr_isequiv; exact _. }
  { intros A B f.
    apply path_equiv, path_arrow; intros a; cbn.
    rewrite !transport_pp.
    refine (moveR_transport_V idmap (unit vwu B) _ (f a) _).
    rewrite !(unit_comp vwu).
    rewrite <- !transport_compose.
    rewrite (transport_sigma' (C := fun P (a0:A) => P a0)); cbn.
    refine (ap _ _ @ _).
    1:{ apply ap, ap.
        exact (path_contr _ (f a ; 1)). }
    rewrite (flip_comp vwu).
    rewrite transport_sigma'; cbn.
    apply ap, path_contr. }
Defined.
