Require Import Paths Univalence Funext.

(** This file asserts univalence as a global axiom, along with its
   basic consequences. If you want function extensionality as well,
   use [ExtensionalityAxiom]. *)

Axiom univalence : univalence_statement.

Definition equiv_to_path := @equiv_to_path univalence.
Definition equiv_to_path_section := @equiv_to_path_section univalence.
Definition equiv_to_path_retraction := @equiv_to_path_retraction univalence.
Definition equiv_to_path_triangle := @equiv_to_path_triangle univalence.
Definition equiv_induction := @equiv_induction univalence.
