(** * The category ω of (ℕ, ≤), and the chain categories [[n]] *)
Require Import Category.Core Category.Subcategory.Full.
Require Import Category.Sigma.Univalent.
Require Import Category.Morphisms Category.Univalent Category.Strict.
Require Import HoTT.Basics HoTT.Types HoTT.DProp HoTT.TruncType HoTT.Spaces.Nat.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Open Scope nat_scope.

(** ** Definitions *)
(** Quoting Wikipedia (http://en.wikipedia.org/wiki/Total_order##Chains):

    While chain is sometimes merely a synonym for totally ordered set,
    it can also refer to a totally ordered subset of some partially
    ordered set. The latter definition has a crucial role in Zorn's
    lemma. *)
(** We take the convention that a "chain" is a totally ordered or
    linearly ordered set; the corresponding category on that set has,
    as morphisms, the order relation. *)
(* N.B. The notation here (including that [[n]] have as objects the
   set [{0, 1, ..., n}]) was originally suggested by David Spivak.
   It's possible that we should pick a different or more common
   terminology. *)

Module Export Core.
  (** *** [[ω]], the linear order on ℕ *)
  Definition omega : PreCategory
    := @Build_PreCategory
         nat
         leq
         leq_refl
         (fun x y z p q => leq_trans q p)
         (fun _ _ _ _ _ _ _ => path_ishprop _ _)
         (fun _ _ _ => path_ishprop _ _)
         (fun _ _ _ => path_ishprop _ _)
         _.

  (** *** [[n]], a linear order on a finite set with [n + 1] elements *)
  (** Using [n + 1] elements allows us to agree with the common
      definition of an [n]-simplex, where a 0-simplex is a point, and
      a 1-simplex has two end-points, etc. *)
  Definition chain (n : nat) : PreCategory
    := { m : omega | m <= n }%category.

  (** TODO: Possibly generalize this to arbitrary sets with arbitrary
      (total?) orders on them? *)

  Module Export ChainCategoryCoreNotations.
    Notation "[ n ]" := (chain n) : category_scope.
  End ChainCategoryCoreNotations.
End Core.

Module Export Notations.
  Include ChainCategoryCoreNotations.
End Notations.

Module Utf8.
  Export Notations.

  Notation "[ ∞ ]" := omega : category_scope.
  Notation "[ 'ω' ]" := omega : category_scope.
End Utf8.


Module Export Strict.
  Definition isstrict_omega : IsStrictCategory omega.
  Proof.
    exact _.
  Defined.

  Definition isstrict_chain {n} : IsStrictCategory [n].
  Proof.
    exact _.
  Defined.
End Strict.

Module Export Univalent.
  Global Instance iscategory_omega : IsCategory omega.
  Proof.
    intros s d.
    refine (isequiv_iff_hprop _ _).
    { refine (istrunc_equiv_istrunc _ (issig_isomorphic _ _ _)); simpl; refine _. }
    { intro m; apply leq_antisym; apply m. }
  Defined.

  Definition iscategory_chain {n} : IsCategory [n].
  Proof.
    exact _.
  Defined.
End Univalent.
