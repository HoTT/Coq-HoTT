Require Export Coq.Unicode.Utf8.
Require Import HoTT.Basics HoTT.Types.Arrow HoTT.Types.Prod HoTT.Types.Sum.
Require Import Modalities.Identity.
Require Import hit.Circle hit.TwoSphere hit.Truncations hit.Suspension.

Notation Type₀ := Type0.
Notation pr₁ := pr1.
Notation pr₂ := pr2.
Local Open Scope fibration_scope.
(*Notation "f → g" := (f -> g)%equiv : equiv_scope.*)
Notation "x ₁" := (x.1) (at level 3) : fibration_scope.
Notation "x ₂" := (x.2) (at level 3) : fibration_scope.
Notation "g ∘ f" := (g o f)%function (at level 40, left associativity) : function_scope.
Notation "g ∘ᴱ f" := (g oE f)%equiv (at level 40, left associativity) : equiv_scope.
Notation "f *ᴱ g" := (f *E g)%equiv (at level 40, no associativity) : equiv_scope.
Notation "f ×ᴱ g" := (f *E g)%equiv (at level 40, no associativity) : equiv_scope.
Notation "A × B" := (A * B)%type (at level 40, no associativity) : type_scope.
Notation "f +ᴱ g" := (f +E g)%equiv (at level 50, left associativity) : equiv_scope.
(** We copy the HoTT-Agda library with regard to path concatenation. *)
Notation "p • q" := (p @ q)%path (at level 20) : path_scope.
Notation "p '⁻¹'" := (p^)%path (at level 3, format "p '⁻¹'") : path_scope.
Notation "p •' q" := (p @ q)%path (at level 21, left associativity,
                                   format "'[v' p '/' '•''  q ']'") : long_path_scope.
(** Add error messages so people aren't intensely confused by using an almost identical character. *)
Infix "∙" := ltac:(fail "You used '∙' (BULLET OPERATOR, #x2219) when you probably meant to use '•' (BULLET, #x2022)") (at level 20, only parsing) : path_scope.
(*Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.*)
(*Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.*)
Notation "A ≃ B" := (A <~> B) (at level 85) : type_scope.
Notation "f '⁻¹'" := (f^-1)%function (at level 3, format "f '⁻¹'") : function_scope.
Notation "f '⁻¹'" := (f^-1)%equiv (at level 3, format "f '⁻¹'") : equiv_scope.
Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.
(*Notation "p @@ q" := (concat2 p q)%path (at level 20) : path_scope.*)

Notation "m ≤ n" := (m <= n)%trunc (at level 70, no associativity) : trunc_scope.

(*Infix "||" := orb : bool_scope.*)
(*Infix "&&" := andb : bool_scope.*)
(*Notation "p ..1" := (pr1_path p) (at level 3) : fibration_scope.*)
(*Notation "p ..2" := (pr2_path p) (at level 3) : fibration_scope.*)

Notation "'S¹'" := S1.
Notation "'S²'" := S2.

Notation "∥ A ∥₋₂" := (Trunc -2 A).
Notation "| a |₋₂" := (@tr -2 _ a) : trunc_scope.

Notation "∥ A ∥" := (Trunc -1 A) (only parsing).
Notation "∥ A ∥₋₁" := (Trunc -1 A).
Notation "| a |₋₁" := (@tr -1 _ a) : trunc_scope.

Notation "∥ A ∥₀" := (Trunc 0 A).
Notation "| a |₀" := (@tr 0 _ a) : trunc_scope.

Notation "∥ A ∥₁" := (Trunc 1 A).
Notation "| a |₁" := (@tr 1 _ a) : trunc_scope.

Notation "∥ A ∥₂" := (Trunc 2 A).
Notation "| a |₂" := (@tr 2 _ a) : trunc_scope.

Notation "∞" := purely.

Notation Σ := Susp.
