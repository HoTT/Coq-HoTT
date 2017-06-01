(** * Unicode notations for comma categories *)
Local Set Warnings Append "-notation-overridden".
Require Import Comma.Core.
Require Export Comma.Notations.
Require Import Basics.Utf8.

(** Set some notations for printing *)
Notation "C ↓ a" := (@slice_category_over C a) (only printing) : category_scope.
Notation "a ↓ C" := (@coslice_category_over C a) (only printing) : category_scope.
Notation "x ↓ F" := (coslice_category x F) (only printing) : category_scope.
Notation "F ↓ x" := (slice_category x F) (only printing) : category_scope.
Notation "S ↓ T" := (comma_category S T) (only printing) : category_scope.
(** Set the notation for parsing; coercions will automatically decide which of the arguments are functors and which are objects, i.e., functors from the terminal category. *)
Notation "S ↓ T" := (comma_category (S : CC_Functor' _ _)
                                    (T : CC_Functor' _ _)) : category_scope.
(*Set Printing All.
Check (fun (C : PreCategory)(D : PreCategory)(E : PreCategory)(S : Functor C D) (T : Functor E D) => (S ↓ T)%category).
Check (fun (D : PreCategory)(E : PreCategory)(S : Functor E D) (x : D) => (x ↓ S)%category).
Check (fun (D : PreCategory)(E : PreCategory)(S : Functor E D) (x : D) => (S ↓ x)%category).*)
