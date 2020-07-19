Require Export Coq.Unicode.Utf8.
Require Export HoTT.Basics.Utf8.
Require Import HoTT.Basics HoTT.Types.
Require Import Modalities.Identity.
Require Import Spaces.Circle Spaces.TwoSphere HoTT.Truncations Homotopy.Suspension.

Notation Type₀ := Type0.
Notation pr₁ := pr1.
Notation pr₂ := pr2.
Local Open Scope fibration_scope.
(*Notation "f → g" := (f -> g)%equiv : equiv_scope.*)
Notation "x ₁" := (x.1) : fibration_scope.
Notation "x ₂" := (x.2) : fibration_scope.
Notation "g ∘ f" := (g o f)%function : function_scope.
Notation "g ∘ᴱ f" := (g oE f)%equiv : equiv_scope.
Notation "f *ᴱ g" := (f *E g)%equiv : equiv_scope.
Notation "f ×ᴱ g" := (f *E g)%equiv : equiv_scope.
Notation "A × B" := (A * B)%type : type_scope.
Notation "f +ᴱ g" := (f +E g)%equiv : equiv_scope.
(** We copy the HoTT-Agda library with regard to path concatenation. *)
Notation "p • q" := (p @ q)%path : path_scope.
Notation "p '⁻¹'" := (p^)%path : path_scope.
Notation "p •' q" := (p @ q)%path : long_path_scope.
(** Add error messages so people aren't intensely confused by using an almost identical character. *)
Infix "∙" := ltac:(fail "You used '∙' (BULLET OPERATOR, #x2219) when you probably meant to use '•' (BULLET, #x2022)") (only parsing) : path_scope.
(*Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.*)
(*Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.*)
Notation "A ≃ B" := (A <~> B) : type_scope.
Notation "f '⁻¹'" := (f^-1)%function : function_scope.
Notation "f '⁻¹'" := (f^-1)%equiv : equiv_scope.
Notation "¬ x" := (~x) : type_scope.
Notation "x ≠ y" := (x <> y) : type_scope.
(*Notation "p @@ q" := (concat2 p q)%path (at level 20) : path_scope.*)

Notation "m ≤ n" := (m <= n)%trunc : trunc_scope.

(*Infix "||" := orb : bool_scope.*)
(*Infix "&&" := andb : bool_scope.*)
(*Notation "p ..1" := (pr1_path p) (at level 3) : fibration_scope.*)
(*Notation "p ..2" := (pr2_path p) (at level 3) : fibration_scope.*)

Notation "'S¹'" := Circle.
Notation "'S²'" := TwoSphere.

Notation "∥ A ∥₋₂" := (Trunc (-2) A).
Notation "❘ a ❘₋₂" := (@tr (-2) _ a) : trunc_scope.

Notation "∥ A ∥" := (Trunc (-1) A) (only parsing).
Notation "∥ A ∥₋₁" := (Trunc (-1) A).
Notation "❘ a ❘₋₁" := (@tr (-1) _ a) : trunc_scope.

Notation "x ∨ y" := (hor x y) : type_scope.
Notation "x ⊔ y" := (sum x y) : type_scope.

Notation "∥ A ∥₀" := (Trunc 0 A).
Notation "❘ a ❘₀" := (@tr 0 _ a) : trunc_scope.

Notation "∥ A ∥₁" := (Trunc 1 A).
Notation "❘ a ❘₁" := (@tr 1 _ a) : trunc_scope.

Notation "∥ A ∥₂" := (Trunc 2 A).
Notation "❘ a ❘₂" := (@tr 2 _ a) : trunc_scope.

Notation "∞" := purely.

Notation Σ := Susp.
