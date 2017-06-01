(** * Functors involving coproduct categories *)
Require Import Category.Sum Functor.Core Functor.Composition.Core Functor.Identity.
Require Import Functor.Paths HoTT.Tactics Types.Forall.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

(** We save [inl] and [inr] so we can use them to refer to the functors, too.  Outside of the [Categories/] directory, they should always be referred to as [Functor.inl] and [Functor.inr], after a [Require Functor].  Outside of this file, but in the [Categories/] directory, if you do not want to depend on all of [Functor] (for e.g., speed reasons), they should be referred to as [Functor.Sum.inl] and [Functor.Sum.inr] after a [Require Functor.Sum]. *)
Local Notation type_inl := inl.
Local Notation type_inr := inr.

(** ** Injections [inl : C → C + D] and [inr : D → C + D] *)
Section sum_functors.
  Variables C D : PreCategory.

  Definition inl : Functor C (C + D)
    := Build_Functor C (C + D)
                     (@inl _ _)
                     (fun _ _ m => m)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).

  Definition inr : Functor D (C + D)
    := Build_Functor D (C + D)
                     (@inr _ _)
                     (fun _ _ m => m)
                     (fun _ _ _ _ _ => idpath)
                     (fun _ => idpath).
End sum_functors.

(** ** Coproduct of functors [F + F' : C + C' → D] *)
Section sum.
  Variables C C' D : PreCategory.

  Definition sum (F : Functor C D) (F' : Functor C' D)
  : Functor (C + C') D.
  Proof.
    refine (Build_Functor
              (C + C') D
              (fun cc'
               => match cc' with
                    | type_inl c => F c
                    | type_inr c' => F' c'
                  end)
              (fun s d
               => match s, d with
                    | type_inl cs, type_inl cd
                      => fun m : morphism _ cs cd => F _1 m
                    | type_inr c's, type_inr c'd
                      => fun m : morphism _ c's c'd => F' _1 m
                    | _, _ => fun m => match m with end
                  end%morphism)
              _
              _);
    abstract (
        repeat (intros [] || intro);
        simpl in *;
          auto with functor
      ).
  Defined.
End sum.

(** ** swap : [C + D → D + C] *)
Section swap_functor.
  Definition swap C D
  : Functor (C + D) (D + C)
    := sum (inr _ _) (inl _ _).

  Local Open Scope functor_scope.

  Definition swap_involutive_helper {C D} c
  : (swap C D) ((swap D C) c)
    = c
    := match c with type_inl _ => idpath | type_inr _ => idpath end.

  Lemma swap_involutive `{Funext} C D
  : swap C D o swap D C = 1.
  Proof.
    path_functor.
    exists (path_forall _ _ swap_involutive_helper).
    repeat (apply (@path_forall _); intro).
    repeat match goal with
               | [ |- context[transport (fun x' => forall y, @?C x' y) ?p ?f ?x] ]
                 => simpl rewrite (@transport_forall_constant _ _ C _ _ p f x)
           end.
    transport_path_forall_hammer.
      by repeat match goal with
                  | [ H : Empty |- _ ] => destruct H
                  | [ H : (_ + _)%type |- _ ] => destruct H
                  | _ => progress hnf in *
                end.
  Qed.
End swap_functor.

Module Export FunctorSumNotations.
  Notation "F + G" := (sum F G) : functor_scope.
End FunctorSumNotations.
