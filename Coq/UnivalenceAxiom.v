Require Import Paths Univalence Funext.

(** This file asserts univalence as a global axiom, along with its
   basic consequences, including function extensionality.  Since the
   proof that univalence implies funext has a tendency to create
   universe inconsistencies, we actually assume funext as a separate
   axiom rather than actually deriving it from univalence. *)

Axiom univalence : univalence_statement.

Set Implicit Arguments.
Definition equiv_to_path := @equiv_to_path univalence.
Definition equiv_to_path_section := @equiv_to_path_section univalence.
Definition equiv_to_path_retraction := @equiv_to_path_retraction univalence.
Definition equiv_to_path_triangle := @equiv_to_path_triangle univalence.
Definition equiv_induction := @equiv_induction univalence.

Axiom strong_funext_dep : strong_funext_dep_statement.
Definition strong_funext := strong_funext_dep_to_nondep strong_funext_dep.
Definition funext_dep := strong_to_naive_funext_dep strong_funext_dep.
Definition funext := strong_to_naive_funext strong_funext.
Definition weak_funext := funext_dep_to_weak funext_dep.
Definition funext_dep_compute := strong_funext_dep_compute strong_funext_dep.
Definition funext_compute := strong_funext_compute strong_funext.

Definition strong_funext_equiv (X Y : Type) (f g : X -> Y)
  : (f == g) <~> (forall x, f x == g x)
  := (@happly X Y f g  ;  @strong_funext X Y f g).
