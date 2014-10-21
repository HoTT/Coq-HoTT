Require Import HoTT.Basics HoTT.Types.
Require Import HProp TruncType ReflectiveSubuniverse Modality.
Require Import hit.Pushout hit.Join.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Open and closed modalities and the propositional fracture theorem *)

(** Exercise 7.13(i): Open modalities *)
Definition open_modality `{Funext} (U : hProp) : Modality.
Proof.
  refine (Build_Modality_easy
           (fun X => U -> X)
           (fun X x u => x)
            _ _ _).
  - intros A B f z u.
    refine (transport B _ (f (z u) u)).
    apply path_arrow; intros u'.
    apply ap; apply path_ishprop.
  - intros A B f a.
    apply path_arrow; intros u.
    transitivity (transport B 1 (f a u));
      auto with path_hints.
    apply (ap (fun p => transport B p (f a u))).
    transitivity (path_arrow (fun _ => a) (fun _ => a) (@ap10 U _ _ _ 1));
      auto with path_hints.
    * apply ap.
      apply path_forall; intros u'.
      apply ap_const.
    * apply eta_path_arrow.
  - intros A z z'.
    refine (isequiv_adjointify _ _ _ _).
    * intros f; apply path_arrow; intros u.
      exact (ap10 (f u) u).
    * intros f; apply path_arrow; intros u.
      transitivity (path_arrow z z' (ap10 (f u))).
      + apply ap.
        apply path_forall; intros u'.
        apply (ap (fun u0 => ap10 (f u0) u')).
        apply path_ishprop.
      + apply eta_path_arrow.
    * intros p.
      apply eta_path_arrow.
Defined.

(** Exercise 7.13(ii): Closed modalities *)
Section ClosedModality.

  Context (U : hProp).

  Definition equiv_inO_closed (A : Type)
  : (U -> Contr A) <-> IsEquiv (fun a:A => push (inr a) : join U A).
  Proof.
    split.
    - intros uac.
      refine (isequiv_adjointify _ _ _ _).
      * refine (pushout_rec A _ _).
        + intros [u | a].
          { pose (uac u). exact (center A). }
          { assumption. }
        + intros [u a]. simpl.
          pose (uac u). apply contr.
      * intros z. pattern z.
        refine (pushout_ind fst snd _ _ _ z).
        + intros [u | a].
          { pose (contr_inhabited_hprop U u).
            apply path_contr. } 
          { reflexivity. }
        + intros [u a]; pose (contr_inhabited_hprop U u).
          apply path_contr.
      * intros a. reflexivity.
    - intros ? u.
      refine (contr_equiv (join U A) (fun a:A => push (inr a))^-1).
      pose (contr_inhabited_hprop U u).
      exact _.
  Defined.

  Definition closed_modality : Modality.
  Proof.
    refine (Build_Modality
              (Build_UnitSubuniverse
                 (fun X => U -> Contr X)
                 (fun X => join U X)
                 _
                 (fun X x => push (inr x))
                 _)
              _ _ _ _); cbn; try exact _.
    - intros A u.
      pose (contr_inhabited_hprop U u).
      exact _.
    - intros A B inO_A f ?; cbn in *; intros u; pose (inO_A u).
      refine (contr_equiv _ f); exact _.
    - intros A B ? f z.
      refine (pushout_ind _ _ B _ _ z).
      * intros [u | a].
        + apply center, B_inO, u.
        + apply f.
      * intros [u a].
        pose (B_inO (push (inr a)) u).
        apply path_contr.
    - reflexivity.
    - intros A A_inO z z' u.
      pose (A_inO u); exact _.
  Defined.

End ClosedModality.
