(** * Modalities *)
Require Import Overture types.Empty types.Arrow HProp Equivalences.
Require Import FunextVarieties.
Set Implicit Arguments.

(** Quoting the HoTT Book: *)
(** Definition 7.7.5. A _modality_ is an operation [○ : Type → Type] for which there are

    (i) functions [η^○_A : A → ○(A)] for every type [A]

    (ii) for every [A : Type] and every type family [B : ○(A) → Type], a function

         [ind_○ : (∀ a : A, ○(B(η^○_A(a)))) → (∀ z : ○(A), ○(B(z)))]

    (iii) A path [ind_○(f)(η^○_A(a)) = f(a)] for each [f : ∀ a : A, ○(B(η^○_A(a)))].

    (iv) For any [z z' : ○(A)], the function [η^○_{z = z'} : (z = z') → ○(z = z')] is an equivalence. *)

Class IsModality (mod : Type -> Type) :=
  { modality_eta : forall A, A -> mod A;
    modality_ind : forall A (B : mod A -> Type),
                     (forall a, mod (B (modality_eta a)))
                     -> forall z, mod (B z);
    modality_ind_compute : forall A B (f : forall a : A, mod (B _)) a,
                             modality_ind _ f (modality_eta a) = f a;
    modality_isequiv_eta_path :> forall A (z z' : mod A),
                                   IsEquiv (@modality_eta (z = z')) }.

Require Import Universe.

(** Needs this instance otherwise it will make A fall in set by using
    hProp_empty unlifted. *)
Instance lift_IsHProp_not_not `{Univalence} `{Funext} {A : Type@{i}} : 
  IsHProp@{i} (not@{i i} (not@{i i} A)).
Proof.
  intro.
  intros. 
  pose (@trunc_arrow H0 (not@{i i} A) Empty (trunc_S minus_two)
                     (IsTrunc_lift@{Set i Type Type Type Type} _ hprop_Empty)).
  apply i.
Defined.

Instance ismodality_notnot `{Univalence} `{Funext} : 
  IsModality (fun X : Type@{i} => 
                not@{i i} (not@{i i} X)).
Proof.
  intros.
  apply (@Build_IsModality
           (fun X => ~~ X)
           (fun (X : Type) (x : X) nx => match nx x with end)
           (fun (A : Type) (B : ~~ A -> Type) H' z nBz =>
              z (fun a => H' a (transport (fun x => not (B x))
                                          (allpath_hprop _ _)
                                          nBz))));
      repeat (intro || apply path_forall);
      try match goal with
            | [ |- appcontext[match ?x : Empty with end] ] => destruct x
          end;
      refine (isequiv_adjointify
                (fun x nx => match nx x : Empty with end)
                (fun _ => allpath_hprop z z')
                _
                _);
      repeat (intro || apply path_forall);
      apply allpath_hprop.
Defined.
