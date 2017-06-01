(** * Unicode notations for comma categories *)
Local Set Warnings Append "-notation-overridden".
Require Import LaxComma.Core.
Require Export LaxComma.Notations.
Require Import Basics.Utf8.

(** Set some notations for printing *)
Notation "'CAT' ⇓ a" := (@lax_slice_category_over _ _ _ a _) : category_scope.
Notation "a ⇓ 'CAT'" := (@lax_coslice_category_over _ _ _ a _) : category_scope.
Notation "x ⇓ F" := (lax_coslice_category x F) (only printing) : category_scope.
Notation "F ⇓ x" := (lax_slice_category x F) (only printing) : category_scope.
Notation "S ⇓ T" := (lax_comma_category S T) (only printing) : category_scope.
(** Set the notation for parsing; typeclasses will automatically decide which of the arguments are functors and which are objects, i.e., functors from the terminal category. *)
Notation "S ⇓ T" := (get_LCC S T) : category_scope.

Notation "'CAT' ⇑ a" := (@oplax_slice_category_over _ _ _ a _) : category_scope.
Notation "a ⇑ 'CAT'" := (@oplax_coslice_category_over _ _ _ a _) : category_scope.
Notation "x ⇑ F" := (oplax_coslice_category x F) (only printing) : category_scope.
Notation "F ⇑ x" := (oplax_slice_category x F) (only printing) : category_scope.
Notation "S ⇑ T" := (oplax_comma_category S T) (only printing) : category_scope.
(** Set the notation for parsing; typeclasses will automatically decide which of the arguments are functors and which are objects, i.e., functors from the terminal category. *)
Notation "S ⇑ T" := (get_OLCC S T) : category_scope.
