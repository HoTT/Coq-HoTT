Require Import Basics.
Require Import Types.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.
Require Import Diagrams.ParallelPair.
Require Import Diagrams.Cocone.
Require Import Colimits.Colimit.
Require Import HIT.Coeq.

Generalizable All Variables.

(** * Coequalizer as a colimit *)

(** In this file, we define [Coequalizer] the coequalizer of two maps as the colimit of a particuliar diagram, and then show that it is equivalent to [Coeq] the primitive coequalizer defined as an HIT. *)


(** ** [Coequalizer] *)

Section Coequalizer.

  Context {A B : Type}.

  Definition IsCoequalizer (f g : B -> A)
    := IsColimit (parallel_pair f g).

  Definition Coequalizer (f g : B -> A)
    := Colimit (parallel_pair f g).

  (** ** Equivalence with [Coeq] *)

  Context {f g : B -> A}.

  Definition cocone_Coeq : Cocone (parallel_pair f g) (Coeq f g).
  Proof.
    serapply Build_Cocone.
    + intros []; [exact (coeq o g)| exact coeq].
    + intros i j phi x; destruct i, j, phi; simpl;
      [ exact (cp x) | reflexivity ].
  Defined.

  Lemma iscoequalizer_Coeq `{Funext}
    : IsColimit (parallel_pair f g) (Coeq f g).
  Proof.
    serapply (Build_IsColimit cocone_Coeq).
    serapply Build_UniversalCocone.
    intros X.
    serapply isequiv_adjointify.
    - intros C.
      serapply Coeq_rec.
      + exact (legs C false).
      + intros b.
        etransitivity.
        * exact (legs_comm C true false true b).
        * exact (legs_comm C true false false b)^.
    - intros C.
      serapply path_cocone.
      + intros i x; destruct i; simpl.
        * exact (legs_comm C true false false x).
        * reflexivity.
      + intros i j phi x; destruct i, j, phi; simpl.
        * hott_simpl.
          match goal with
          | [|- ap (Coeq_rec ?a ?b ?c) _ @ _ = _ ]
            => rewrite (Coeq_rec_beta_cp a b c)
          end.
          hott_simpl.
        * reflexivity.
    - intros F.
      apply path_forall.
      match goal with
        | [|- ?G == _ ] => simple refine (Coeq_ind (fun w => G w = F w) _ _)
      end.
      + reflexivity.
      + intros b; simpl.
        rewrite transport_paths_FlFr.
        rewrite Coeq_rec_beta_cp.
        hott_simpl.
  Defined.

  Definition equiv_Coeq_Coequalizer `{Funext}
    : Coeq f g <~> Coequalizer f g.
  Proof.
    serapply colimit_unicity.
    3: eapply iscoequalizer_Coeq.
    eapply iscolimit_colimit.
  Defined.

End Coequalizer.
