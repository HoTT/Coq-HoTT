(** * The category ω of (ℕ, ≤), and the chain categories [[n]] *)
Require Import Category.Core Category.Subcategory.Full.
Require Import Category.Sigma.Univalent.
Require Import Category.Morphisms Category.Univalent Category.Strict.
Require Import HoTT.Basics.Trunc HoTT.Types.Nat HoTT.Types.Bool HoTT.TruncType HoTT.Spaces.Nat.
Import BoolSortCoercion.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Module Export Core.
  Definition omega : PreCategory
    := @Build_PreCategory
         nat
         leq
         leq_refl
         (fun x y z p q => leq_trans _ _ _ q p)
         (fun _ _ _ _ _ _ _ => path_ishprop _ _)
         (fun _ _ _ => path_ishprop _ _)
         (fun _ _ _ => path_ishprop _ _)
         _.

  Definition chain (n : nat) : PreCategory
    := { m : omega | m <= n }%category.

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
    { refine (trunc_equiv' _ (issig_isomorphic _ _ _)). }
    { intro m; apply leq_antisym; apply m. }
  Defined.

  Definition iscategory_chain {n} : IsCategory [n].
  Proof.
    exact _.
  Defined.
End Univalent.
