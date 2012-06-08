Require Import Paths Fibrations Contractible Equivalences Univalence Funext.

(** Here we prove that univalence implies function extensionality.  We
   keep this file separate from the statements of Univalence and
   Funext, since it has a tendency to produce universe
   inconsistencies.  With truly polymorphic universes this ought not
   to be a problem.

   Since this file makes the point that univalence implies funext,
   further development can avoid including this file and simply assume
   function extensionality as an axiom alongside univalence, in the
   knowledge that it is actually no additional requirement. *)

Section UnivalenceImpliesFunext.

  Hypothesis univalence : univalence_statement.

  Hypothesis eta_rule : forall (U V : Universe), eta_statement U V.

  (** Exponentiation preserves equivalences, i.e., if [e] is an
     equivalence then so is post-composition by [e]. *)

  Theorem equiv_exponential : forall {A B} (w : A <~> B) C,
    (C -> A) <~> (C -> B).
  Proof.
    intros A B e C.
    exists (compose e).
    generalize A B e.
    apply equiv_induction.
    assumption.
    intro D.
    apply (equiv_is_equiv (eta_equiv C D (eta_rule _ _))).
  Defined.

  (** We are ready to prove functional extensionality, starting with the
     naive non-dependent version. *)

  Theorem univalence_implies_funext (A B: Universe): funext_statement A B.
  Proof.
    intros f g p.
    (* It suffices to find a path [eta f ~~> eta g]. *)
    apply equiv_injective with (e := eta_equiv A B (eta_rule _ _)); simpl.
    (* Consider the following maps. *)
    pose (d := fun x : A => existT (fun xy => fst xy ~~> snd xy) (f x, f x) (idpath (f x))).
    pose (e := fun x : A => existT (fun xy => fst xy ~~> snd xy) (f x, g x) (p x)).
    (* If we compose [d] and [e] with [free_path_target], we get [eta
       f] and [eta g], respectively. So, if we had a path from [d] to
       [e], we would get one from [eta f] to [eta g]. *)
    pose (src_compose := equiv_exponential (free_path_source B) A).
    pose (trg_compose := equiv_exponential (free_path_target B) A).
    path_via (trg_compose e).
    path_via (trg_compose d).
    apply map.
    (* But we can get a path from [d] to [e] because [src o d = eta f
       = src o e] and composition with [src] is an equivalence. *)
    apply @equiv_injective with (e := src_compose).
    apply idpath.
  Defined.

  (** Now we use this to prove weak funext, which as we know implies
     (with dependent eta) also the strong dependent funext. *)

  Theorem univalence_implies_weak_funext (A : Universe) (P : A -> Universe):
    weak_funext_statement P.
  Proof.
    intros allcontr.
    (* We are going to replace [P] with something simpler. *)
    pose (U := (fun (_ : A) => unit : Universe)).
    assert (p : P ~~> U).
    apply univalence_implies_funext.
    intro x.
    apply equiv_to_path; auto.
    apply contr_equiv_unit.
    apply allcontr.
    rewrite p.
    (* Now this is much easier. *)
    exists (fun _ => tt).
    intro f.
    unfold U in * |- *.
    unfold section in f.
    apply (univalence_implies_funext A unit).
    intro x.
    apply contr_path, unit_contr.
    (* Oh noes!  Universe inconsistency! *)
  Admitted.

End UnivalenceImpliesFunext.
