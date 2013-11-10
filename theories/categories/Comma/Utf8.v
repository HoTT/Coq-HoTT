Require Import Comma.Core.
Require Export Comma.Notations.

(** Set some notations for printing *)
Notation "x ↓ F" := (coslice_category x F) (at level 70, no associativity) : category_scope.
Notation "F ↓ x" := (slice_category x F) : category_scope.
Notation "S ↓ T" := (comma_category S T) : category_scope.
(** Set the notation for parsing; coercions will automatically decide which of the arguments are functors and which are objects, i.e., functors from the terminal category. *)
Notation "S ↓ T" := (comma_category (S : CC_Functor' _ _)
                                    (T : CC_Functor' _ _)) : category_scope.
(*Set Printing All.
Check (fun (C : Category)(D : Category)(E : Category)(S : Functor C D) (T : Functor E D) => (S ↓ T)%category).
Check (fun (D : Category)(E : Category)(S : Functor E D) (x : D) => (x ↓ S)%category).
Check (fun (D : Category)(E : Category)(S : Functor E D) (x : D) => (S ↓ x)%category).*)
