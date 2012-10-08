(** Many times we need function extensionality but not the full power
   of univalence. This file can be included to get such an assumption. *)

Require Export Funext.

Axiom strong_funext_dep : forall A (P : fibration A), strong_funext_dep_statement P.

Definition strong_funext := strong_funext_dep_to_nondep strong_funext_dep.
Definition funext_dep A (P : fibration A) := strong_to_naive_funext_dep P (strong_funext_dep A P).
Definition funext := strong_to_naive_funext strong_funext.
Definition weak_funext A (P : fibration A) := funext_dep_to_weak P (funext_dep A P).
Definition funext_dep_compute A (P : fibration A) := strong_funext_dep_compute P (strong_funext_dep A P).
Definition funext_compute := strong_funext_compute strong_funext.

Definition strong_funext_equiv {X : Type} {P : fibration X} (f g : section P) :
  (f = g) <~> f == g :=
  happly_dep_equiv X P f g (strong_funext_dep X P).

Axiom eta_dep_rule : forall A (P : fibration A), eta_dep_statement P.

Definition eta_rule A B (f : A -> B) := eta_dep_rule A (fun _ => B).

(* A convenient tactic for using extensionality. *)
Ltac by_extensionality :=
  intros; unfold compose;
  match goal with 
  | [ |- ?f = ?g ] =>
    apply funext_dep ; unfold ext_dep_eq ;
    match goal with
      | [ |- forall (_ : prod _ _), _ ] => intros [? ?]
      | [ |- forall (_ : sigT _ _), _ ] => intros [? ?]
      | [ |- forall (_ : total _), _ ] => intros [? ?]
      | _ => intros
    end ;
    simpl;
    auto
  end.
