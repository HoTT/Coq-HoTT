Require Import
  HoTT.Basics.Equivalences
  HoTT.Types.Bool
  HoTT.Types.Forall
  HoTT.Types.Sigma
  HoTT.Types.Prod
  HoTT.Classes.theory.ua_homomorphism.

Import algebra_notations ne_list.notations.

(** The following section defines product algebra [ProdAlgebra].
    Section [bin_prod_algebra] specialises the definition to
    binary product algebra. *)

Section prod_algebra.
  Context `{Funext} {σ : Signature} (I : Type) (A : I → Algebra σ).

  Definition carriers_prod_algebra : Carriers σ
    := λ (s : Sort σ), ∀ (i:I), A i s.

  Fixpoint op_prod_algebra (w : SymbolType σ)
      : (∀ i, Operation (A i) w) →
        Operation carriers_prod_algebra w :=
    match w return (∀ i, Operation (A i) w) →
                    Operation carriers_prod_algebra w
    with
    | [:_:] => idmap
    | _ ::: g => λ f p, op_prod_algebra g (λ i, f i (p i))
    end.

  Definition ops_prod_algebra (u : Symbol σ)
    : Operation carriers_prod_algebra (σ u)
    := op_prod_algebra (σ u) (λ (i:I), u ^^ A i).

  Definition ProdAlgebra : Algebra σ
    := BuildAlgebra carriers_prod_algebra ops_prod_algebra.

  Global Instance trunc_prod_algebra {n : trunc_index}
    `{!∀ i, IsTruncAlgebra n (A i)}
    : IsTruncAlgebra n ProdAlgebra.
  Proof.
    intro s. exact _.
  Qed.
End prod_algebra.

(** The next section defines the product projection homomorphisms. *)

Section hom_proj_prod_algebra.
  Context `{Funext} {σ : Signature} (I : Type) (A : I → Algebra σ).

  Definition def_proj_prod_algebra (i:I) (s : Sort σ) (c : ProdAlgebra I A s)
    : A i s
    := c i.

  Lemma oppreserving_proj_prod_algebra {w : SymbolType σ}
    (i : I) (v : ∀ i : I, Operation (A i) w) (α : Operation (A i) w)
    (P : v i = α)
    : OpPreserving (def_proj_prod_algebra i)
        (op_prod_algebra I A w v) α.
  Proof.
    induction w.
    - exact P.
    - intro p. apply (IHw (λ i, v i (p i)) (α (p i))). f_ap.
  Defined.

  Global Instance is_homomorphism_proj_prod_algebra (i:I)
    : IsHomomorphism (def_proj_prod_algebra i).
  Proof.
    intro u.
    by apply oppreserving_proj_prod_algebra.
  Defined.

  Definition hom_proj_prod_algebra (i : I)
    : Homomorphism (ProdAlgebra I A) (A i)
    := BuildHomomorphism (def_proj_prod_algebra i).

End hom_proj_prod_algebra.

(** The product algebra univarsal mapping property [ump_prod_algebra]. *)

Section ump_prod_algebra.
  Context
    `{Funext}
    {σ : Signature}
    (I : Type)
    (A : I → Algebra σ)
    (C : Algebra σ).

  Definition hom_prod_algebra_mapout
    (f : Homomorphism C (ProdAlgebra I A)) (i:I)
    : Homomorphism C (A i)
    := hom_compose (hom_proj_prod_algebra I A i) f.

  Definition def_prod_algebra_mapin (f : ∀ i, Homomorphism C (A i))
    : ∀ (s : Sort σ) , C s → ProdAlgebra I A s
    := λ (s : Sort σ) (x : C s) (i : I), f i s x.

  Lemma oppreserving_prod_algebra_mapin {w : SymbolType σ}
    (f : ∀ (i:I), Homomorphism C (A i))
    (α : ∀ (i:I), Operation (A i) w) (β : Operation C w)
    (P : ∀ (i:I), OpPreserving (f i) β (α i))
    : OpPreserving (def_prod_algebra_mapin f) β
        (op_prod_algebra I A w (λ i, α i)).
  Proof.
    induction w.
    - funext i. apply P.
    - intro x. apply IHw. intro i. apply P.
  Defined.

  Global Instance is_homomorphism_prod_algebra_mapin
    (f : ∀ (i:I), Homomorphism C (A i))
    : IsHomomorphism (def_prod_algebra_mapin f).
  Proof.
    intro u.
    apply oppreserving_prod_algebra_mapin.
    intro i.
    apply f.
  Defined.

  Definition hom_prod_algebra_mapin (f : ∀ i, Homomorphism C (A i))
    : Homomorphism C (ProdAlgebra I A)
    := BuildHomomorphism (def_prod_algebra_mapin f).

  (** Given a family of homomorphisms [h : ∀ (i:I), Homomorphism C (A i)]
      there is a unique homomorphism [f : Homomorphism C (ProdAlgebra I A)]
      such that [h i = hom_compose (pr i) f], where

      <<
        pr i = hom_proj_prod_algebra I A i
      >>

      is the ith projection homomorphism. *)

 Lemma ump_prod_algebra `{!∀ i, IsHSetAlgebra (A i)}
   : (∀ (i:I), Homomorphism C (A i)) <~> Homomorphism C (ProdAlgebra I A).
  Proof.
    apply (equiv_adjointify hom_prod_algebra_mapin hom_prod_algebra_mapout).
    - intro f. by apply path_hset_homomorphism.
    - intro f. funext i. by apply path_hset_homomorphism.
  Defined.
End ump_prod_algebra.

(** Binary product algebra. *)

Section bin_prod_algebra.
  Context `{Funext} {σ : Signature} (A B : Algebra σ).

  Definition bin_prod_algebras (b:Bool) : Algebra σ
    := if b then B else A.

  Global Instance trunc_bin_prod_algebras {n : trunc_index}
    `{!IsTruncAlgebra n A} `{!IsTruncAlgebra n B}
    : ∀ (b:Bool), IsTruncAlgebra n (bin_prod_algebras b).
  Proof.
    intros []; exact _.
  Qed.

  Definition BinProdAlgebra : Algebra σ :=
    ProdAlgebra Bool bin_prod_algebras.

  Definition fst_prod_algebra : Homomorphism BinProdAlgebra A
    := hom_proj_prod_algebra Bool bin_prod_algebras false.

  Definition snd_prod_algebra : Homomorphism BinProdAlgebra B
    := hom_proj_prod_algebra Bool bin_prod_algebras true.
End bin_prod_algebra.

Module prod_algebra_notations.

  Global Notation "A × B" := (BinProdAlgebra A B)
                             (at level 40, left associativity)
                             : Algebra_scope.

End prod_algebra_notations.

Import prod_algebra_notations.

(** Specialisation of the product algebra univarsal mapping property
    to binary product. *)

Section ump_bin_prod_algebra.
  Context
    `{Funext}
    {σ : Signature}
    (A B C : Algebra σ)
    `{!IsHSetAlgebra A} `{!IsHSetAlgebra B}.

 Lemma ump_bin_prod_algebra
   : Homomorphism C A * Homomorphism C B <~> Homomorphism C (A × B).
  Proof.
    set (k := λ (b:Bool), Homomorphism C (bin_prod_algebras A B b)).
    exact (equiv_compose
            (ump_prod_algebra Bool (bin_prod_algebras A B) C)
            (equiv_bool_forall_prod k)^-1).
  Defined.
End ump_bin_prod_algebra.
