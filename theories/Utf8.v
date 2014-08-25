Require Export Coq.Unicode.Utf8.
Require Import Overture Trunc (*types.Bool*) hit.Circle hit.TwoSphere hit.minus1Trunc hit.Truncations hit.Suspension.

Notation Type₀ := Type0.
Notation pr₁ := pr1.
Notation pr₂ := pr2.
Local Open Scope fibration_scope.
Notation "x ₁" := (x.1) (at level 3) : fibration_scope.
Notation "x ₂" := (x.2) (at level 3) : fibration_scope.
Notation "g ∘ f" := (g o f) (at level 40, left associativity) : function_scope.
(** We copy the HoTT-Agda library with regard to path concatenation. *)
Notation "p • q" := (p @ q)%path (at level 20) : path_scope.
Notation "p '⁻¹'" := (p^)%path (at level 3, format "p '⁻¹'") : path_scope.
Notation "p •' q" := (p @ q)%path (at level 21, left associativity,
                                   format "'[v' p '/' '•''  q ']'") : long_path_scope.
(*Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.*)
(*Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.*)
Notation "A ≃ B" := (A <~> B)%equiv (at level 85) : equiv_scope.
Notation "f '⁻¹'" := (f^-1)%equiv (at level 3, format "f '⁻¹'") : equiv_scope.
Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.
(*Notation "p @@ q" := (concat2 p q)%path (at level 20) : path_scope.*)

Notation "m ≤ n" := (m <= n)%trunc (at level 70, no associativity) : trunc_scope.

(*Infix "||" := orb : bool_scope.*)
(*Infix "&&" := andb : bool_scope.*)
(*Notation "p ..1" := (projT1_path p) (at level 3) : fibration_scope.*)
(*Notation "p ..2" := (projT2_path p) (at level 3) : fibration_scope.*)

Notation S¹ := S1.
(*Fail Notation S² := S2. (* Lexer: Undefined Token?! *)*)
Notation "'S²'" := S2.

Notation "∥ A ∥₋₂" := (Truncation minus_two A).
Notation "| a |₋₂" := (@truncation_incl minus_two _ a) : trunc_scope.

Notation "∥ A ∥₋₁" := (Truncation (trunc_S minus_two) A).
Notation "| a |₋₁" := (@truncation_incl (trunc_S minus_two) _ a) : trunc_scope.

Notation "∥ A ∥₀" := (Truncation 0 A).
Notation "| a |₀" := (@truncation_incl 0_ a) : trunc_scope.

Notation "∥ A ∥₁" := (Truncation 1 A).
Notation "| a |₁" := (@truncation_incl 1 _ a) : trunc_scope.

Notation "∥ A ∥₂" := (Truncation 2 A).
Notation "| a |₂" := (@truncation_incl 2 _ a) : trunc_scope.

(* N.B. If you swap which one of these is [only parsing], you should also swap which one is used to display [Truncation minus_one A] above. *)
Notation "∥ A ∥" := (minus1Trunc A) (only parsing).
Notation "∥ A ∥₋₁" := (minus1Trunc A).
Notation "| a |₋₁" := (min1 a) : prop_trunc_scope.

Notation Σ := Susp.
