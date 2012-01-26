Require Import Paths Fibrations Contractible Equivalences Univalence Funext.

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

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

  Hypothesis eta_rule : eta_statement.

  (** Exponentiation preserves equivalences, i.e., if [w] is an
     equivalence then so is post-composition by [w]. *)

  Theorem equiv_exponential : forall {A B} (w : A <~> B) C,
    (C -> A) <~> (C -> B).
  Proof.
    intros A B w C.
    exists (fun h => w o h).
    generalize A B w.
    apply equiv_induction.
    assumption.
    intro D.
    apply (projT2 (eta_equiv eta_rule C D)).
  Defined.

  (** We are ready to prove functional extensionality, starting with the
     naive non-dependent version. *)

  Theorem univalence_implies_funext : funext_statement.
  Proof.
    intros A B f g p.
    (* It suffices to find a path [eta f == eta g]. *)
    apply equiv_injective with (w := eta_equiv eta_rule A B).
    simpl.
    (* Consider the following maps. *)
    pose (d := fun x : A => existT (fun xy => fst xy == snd xy) (f x, f x) (idpath (f x))).
    pose (e := fun x : A => existT (fun xy => fst xy == snd xy) (f x, g x) (p x)).
    (* If we compose [d] and [e] with [free_path_target], we get [eta
       f] and [eta g], respectively. So, if we had a path from [d] to
       [e], we would get one from [eta f] to [eta g]. *)
    pose (src_compose := equiv_exponential (free_path_source B) A).
    pose (trg_compose := equiv_exponential (free_path_target B) A).
    path_via (projT1 trg_compose e).
    path_via (projT1 trg_compose d).
    (* But we can get a path from [d] to [e] because [src o d = eta f
       = src o e] and composition with [src] is an equivalence. *)
    apply equiv_injective with (w := src_compose).
    apply idpath.
  Defined.

  (** Now we use this to prove weak funext, which as we know implies
     (with dependent eta) also the strong dependent funext. *)

  Theorem univalence_implies_weak_funext : weak_funext_statement.
  Proof.
    intros X P allcontr.
    assert (eqpt : @paths (X -> Type) (fun x => unit) P).
    apply univalence_implies_funext.
    intro x.
    apply opposite, equiv_to_path, contr_equiv_unit, allcontr.
    assumption.
    assert (contrunit : is_contr (forall x:X, unit)).
    exists (fun _ => tt).
    intro f.
    apply univalence_implies_funext.
    intro x.
    assert (alltt : forall y:unit, y == tt).
    induction y; apply idpath.
    apply alltt.
    exact (transport (P := fun Q: X -> Type => is_contr (forall x, Q x)) eqpt contrunit).
    (* Oh noes!  Universe inconsistency! *)
  Admitted.

End UnivalenceImpliesFunext.
