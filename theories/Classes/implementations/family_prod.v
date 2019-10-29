Require Import
  Coq.Unicode.Utf8
  HoTT.Basics.Overture
  HoTT.Classes.implementations.list.

(** The following section implements a datatype [FamilyProd] which
    is a kind of product/tuple. *)

Section family_prod.
  Context {I : Type}.

  (** [FamilyProd F ℓ] is a product type defined by
  
      <<
        FamilyProd F [i1;i2;...;in] = F i1 * F i2 * ... * F in * Unit
      >>

      It is convenient to have the [Unit] in the end.
  *)

  Definition FamilyProd (F : I → Type) : list I → Type
    := fold_right (λ (i:I) (A:Type), F i * A) Unit.

  (** Map function for [FamilyProd F ℓ],

      <<
        map_family_prod f (x1, x2, ..., xn, tt)
        = (f x1, f x2, ..., f xn, tt)
      >> *)

  Fixpoint map_family_prod {F G : I → Type} {ℓ : list I}
      (f : ∀ i, F i → G i)
      : FamilyProd F ℓ → FamilyProd G ℓ :=
    match ℓ with
    | nil => const tt
    | i :: ℓ' => λ '(x,s), (f i x, map_family_prod f s)
    end.

  (** [for_all_family_prod F P (x1, ..., xn, tt) = True] if
      [P i1 x1 ∧ P i2 x2 ∧ ... ∧ P in xn] holds. *)

  Fixpoint for_all_family_prod (F : I → Type) {ℓ : list I}
      (P : ∀ i, F i -> Type) : FamilyProd F ℓ → Type :=
    match ℓ with
    | nil => λ _, True
    | i :: ℓ' => λ '(x,s), P i x ∧ for_all_family_prod F P s
    end.

  (** [for_all_2_family_prod F G R (x1,...,xn,tt) (y1,...,yn,tt) = True]
      if [R i1 x1 y1 ∧ R i2 x2 y2 ∧ ... ∧ P in xn yn] holds. *)

  Fixpoint for_all_2_family_prod (F G : I → Type) {ℓ : list I}
      (R : ∀ i, F i -> G i -> Type)
      : FamilyProd F ℓ → FamilyProd G ℓ → Type :=
    match ℓ with
    | nil => λ _ _, True
    | i :: ℓ' => λ '(x,s) '(y,t), R i x y ∧ for_all_2_family_prod F G R s t
    end.

  (** If [R : ∀ i, relation (F i)] is a family of relations indexed by
      [i:I] and [R i] is reflexive for all [i], then

      <<
        for_all_2_family_prod F F R s s
      >>

      holds. *)
  Lemma reflexive_for_all_2_family_prod (F : I → Type)
    (R : ∀ i, Relation (F i)) `{!∀ i, Reflexive (R i)}
    {ℓ : list I} (s : FamilyProd F ℓ)
    : for_all_2_family_prod F F R s s.
  Proof with try reflexivity.
    induction ℓ...
    split...
    apply IHℓ.
  Defined.
End family_prod.
