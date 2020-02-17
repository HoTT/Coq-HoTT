(* -*- mode: coq; mode: visual-line -*-  *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp TruncType Extensions.
Require Import Modality Accessible Nullification Lex Topological.
Require Import Colimits.Pushout Homotopy.Join.

Local Open Scope nat_scope.
Local Open Scope path_scope.


(** * Closed modalities *)

(** We begin by characterizing the modal types. *)
Section ClosedModalTypes.
  Context (U : hProp).

  Definition equiv_inO_closed (A : Type)
  : (U -> Contr A) <-> IsEquiv (fun a:A => push (inr a) : Join U A).
  Proof.
    split.
    - intros uac.
      simple refine (isequiv_adjointify _ _ _ _).
      * simple refine (Pushout_rec A _ _ _).
        + intros u; pose (uac u); exact (center A).
        + intros a; assumption.
        + intros [u a]. simpl.
          pose (uac u). apply contr.
      * intros z. pattern z.
        simple refine (Pushout_ind _ _ _ _ z).
        + intros u.
          pose (contr_inhabited_hprop U u).
          apply path_contr.
        + intros a; reflexivity.
        + intros [u a]; pose (contr_inhabited_hprop U u).
          apply path_contr.
      * intros a. reflexivity.
    - intros ? u.
      refine (contr_equiv (Join U A) (fun a:A => push (inr a))^-1).
      pose (contr_inhabited_hprop U u).
      exact _.
  Defined.

End ClosedModalTypes.

(** Exercise 7.13(ii): Closed modalities *)
Definition Cl (U : hProp) : Modality.
Proof.
  snrapply Build_Modality.
  - intros X; exact (U -> Contr X).
  - exact _.
  - intros T B T_inO f feq.
    cbn; intros u; pose (T_inO u).
    refine (contr_equiv _ f); exact _.
  - intros ; exact (Join U X).
  - intros T u.
    pose (contr_inhabited_hprop _ u).
    exact _.
  - intros T x.
    exact (push (inr x)).
  - intros A B B_inO f z.
    srefine (Pushout_ind B _ _ _ z).
    + intros u; apply center, B_inO, u.
    + intros a; apply f.
    + intros [u a].
      pose (B_inO (push (inr a)) u).
      apply path_contr.
  - intros; reflexivity.
  - intros A A_inO z z' u.
    pose (A_inO u).
    apply contr_paths_contr.
Defined.

(** The closed modality is accessible. *)
Global Instance accmodality_closed (U : hProp)
  : IsAccModality (Cl U).
Proof.
  unshelve econstructor.
  - econstructor.
    exact (fun _:U => Empty).
  - intros X; split.
    + intros X_inO u.
      pose (X_inO u).
      apply ooextendable_contr; exact _.
    + intros ext u.
      exists ((fst (ext u 1%nat) Empty_rec).1 tt); intros x.
      unfold const in ext.
      exact ((fst (snd (ext u 2) (fst (ext u 1%nat) Empty_rec).1
                       (fun _ => x)) (Empty_ind _)).1 tt).
Defined.

(** In fact, it is topological, and therefore (assuming univalence) lex.  As for topological modalities generally, we don't need to declare these as global instances, but we prove them here as local instances for exposition. *)
Local Instance topological_closed (U : hProp)
  : Topological (Cl U)
  := _.

Global Instance lex_closed `{Univalence} (U : hProp)
  : Lex (Cl U).
Proof.
  rapply lex_topological.
Defined.

(** Thus, it also has the following alternative version. *)
Definition Cl' (U : hProp) : Modality
  := Nul (Build_NullGenerators U (fun _ => Empty)).
