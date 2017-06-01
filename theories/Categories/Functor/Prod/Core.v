(** * Functors involving product categories *)
Require Import Category.Core Functor.Core Category.Prod Functor.Composition.Core.
Require Import Functor.Paths.
Require Import Types.Prod.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Local Notation fst_type := fst.
Local Notation snd_type := snd.
Local Notation pair_type := pair.

Local Open Scope morphism_scope.
Local Open Scope functor_scope.

(** ** First and second projections from a product precategory *)
Section proj.
  Context {C : PreCategory}.
  Context {D : PreCategory}.

  Definition fst : Functor (C * D) C
    := Build_Functor (C * D) C
                     (@fst _ _)
                     (fun _ _ => @fst _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition snd : Functor (C * D) D
    := Build_Functor (C * D) D
                     (@snd _ _)
                     (fun _ _ => @snd _ _)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End proj.

(** ** Product of two functors from the same domain *)
Section prod.
  Variables C D D' : PreCategory.

  Definition prod (F : Functor C D) (F' : Functor C D')
  : Functor C (D * D')
    := Build_Functor
         C (D * D')
         (fun c => (F c, F' c))
         (fun s d m => (F _1 m, F' _1 m))
         (fun _ _ _ _ _ => path_prod' (composition_of F _ _ _ _ _)
                                      (composition_of F' _ _ _ _ _))
         (fun _ => path_prod' (identity_of F _) (identity_of F' _)).
End prod.

Local Infix "*" := prod : functor_scope.

(** ** Pairing of two functors *)
Section pair.
  Variables C D C' D' : PreCategory.
  Variable F : Functor C D.
  Variable F' : Functor C' D'.

  Local Open Scope functor_scope.

  Definition pair : Functor (C * C') (D * D')
    := (F o fst) * (F' o snd).
End pair.

Local Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : functor_scope.

(** ** Partially applied functors out of a product precategory *)
Section induced.
  Variables C D E : PreCategory.

  Variable F : Functor (C * D) E.

  Local Open Scope core_scope.

  Local Ltac t :=
    simpl; intros;
    repeat (rewrite <- ?composition_of, <- ?identity_of, ?left_identity, ?right_identity; simpl);
    trivial.

  (** Note: This is just the currying exponential law. *)
  (** TODO: Come up with a better name for this? *)
  Definition induced_fst (d : D) : Functor C E.
  Proof.
    refine (Build_Functor
              C E
              (fun c => F (c, d))
              (fun _ _ m => @morphism_of _ _ F (_, _) (_, _) (m, identity d))
              _
              _);
    abstract t.
  Defined.

  Definition induced_snd (c : C) : Functor D E.
  Proof.
    refine (Build_Functor
              D E
              (fun d => F (c, d))
              (fun _ _ m => @morphism_of _ _ F (_, _) (_, _) (identity c, m))
              _
              _);
    abstract t.
  Defined.
End induced.

Local Set Warnings Append "-notation-overridden".
Module Export FunctorProdCoreNotations.
  Infix "*" := prod : functor_scope.
  Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : functor_scope.
End FunctorProdCoreNotations.
