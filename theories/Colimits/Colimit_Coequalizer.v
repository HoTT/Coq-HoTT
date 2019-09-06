Require Import Basics.
Require Import Types.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.
Require Import Diagrams.CoeqDiagram.
Require Import Diagrams.Cocone.
Require Import Colimits.Colimit.
Require Import HIT.Coeq.

Generalizable All Variables.

(** * Coequalizer as a colimit *)

(** In this file, we define [Coequalizer] the coequalizer of two maps as the colimit of a particuliar diagram, and then show that it is equivalent to [Coeq] the primitive coequalizer defined as an HIT. *)


(** ** [Coequalizer] *)

Section Coequalizer.

  Context `{Funext}.

  (** The shape of a coequalizer diagram. *)

  Definition coequalizer_graph : Graph.
  Proof.
    serapply (Build_Graph Bool).
    intros i j.
    exact (if i then if j then Empty else Bool else Empty).
  Defined.

  Context {B A : Type}.

  (** The coequalizer diagram of two maps. *)

  Definition coequalizer_diagram (f g : B -> A)
    : Diagram coequalizer_graph.
  Proof.
    serapply Build_Diagram.
    1: intros []; [exact B | exact A].
    intros [] [] []; [exact f | exact g].
  Defined.

  Definition Build_coequalizer_cocone {f g : B -> A}
    `(q: A -> Q) (Hq: q o g == q o f)
    : Cocone (coequalizer_diagram f g) Q.
  Proof.
    serapply Build_Cocone.
    1: intros []; [exact (q o f) | exact q].
    intros [] [] []; [reflexivity | exact Hq].
  Defined.

  Definition IsCoequalizer (f g : B -> A)
    := IsColimit (coequalizer_diagram f g).

  Definition Coequalizer (f g : B -> A)
    := Colimit (coequalizer_diagram f g).

  (** ** Equivalence with [Coeq] *)

  Context {f g : B -> A}.

  Definition cocone_Coeq : Cocone (coequalizer_diagram f g) (Coeq f g).
  Proof.
    serapply Build_Cocone.
    + intros []; [exact (coeq o g)| exact coeq].
    + intros i j phi x; destruct i, j, phi; simpl;
      [ exact (cp x) | reflexivity ].
  Defined.

  Lemma iscoequalizer_Coeq : IsColimit (coequalizer_diagram f g) (Coeq f g).
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

  Definition equiv_Coeq_Coequalizer
    : Coeq f g <~> Coequalizer f g.
  Proof.
    serapply colimit_unicity.
    3: eapply iscoequalizer_Coeq.
    eapply iscolimit_colimit.
  Defined.

End Coequalizer.
