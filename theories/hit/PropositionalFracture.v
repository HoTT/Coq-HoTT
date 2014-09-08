Require Import Overture PathGroupoids Contractible HProp Equivalences EquivalenceVarieties
        UnivalenceImpliesFunext.
Require Import types.Empty types.Unit types.Arrow types.Sigma types.Paths
        types.Forall types.Prod types.Universe types.ObjectClassifier.
Require Import ReflectiveSubuniverse Modality.
Require Import hit.Pushout hit.Join.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Open and closed modalities and the propositional fracture theorem *)

(** Exercise 7.13(i): Open modalities *)
Definition open_modality `{Funext} (U : hProp) : Modality.
Proof.
  refine (Build_Modality
            (Build_UnitSubuniverse
               (fun X => U -> X)
               (fun X x u => x))
            _ _ _); unfold O, inO, O_unit.
  - intros A B f z u.
    refine (transport B _ (f (z u) u)).
    apply path_arrow; intros u'.
    apply ap; apply allpath_hprop.
  - intros A B f a.
    apply path_arrow; intros u.
    path_via (transport B 1 (f a u)).
    apply (ap (fun p => transport B p (f a u))).
    path_via (path_arrow (fun _ => a) (fun _ => a) (@ap10 U _ _ _ 1)).
    * apply ap.
      apply path_forall; intros u'.
      apply ap_const.
    * apply eta_path_arrow.
  - intros A z z'.
    refine (isequiv_adjointify _ _ _ _); unfold O.
    * intros f; apply path_arrow; intros u.
      exact (ap10 (f u) u).
    * intros f; apply path_arrow; intros u.
      path_via (path_arrow z z' (ap10 (f u))).
      + apply ap.
        apply path_forall; intros u'.
        apply (ap (fun u0 => ap10 (f u0) u')).
        apply allpath_hprop.
      + apply eta_path_arrow.
    * intros p.
      apply eta_path_arrow.
Defined.

(** Exercise 7.13(ii): Closed modalities *)
Section ClosedModality.

  Context `{Funext} (U : hProp).

  (* Not Global! *)
  Instance closed_unitsubuniverse : UnitSubuniverse
    := (Build_UnitSubuniverse
               (fun X => join U X)
               (fun X => push o (@inr U X))).

  Definition inO_closed (A : Type)
  : inO A <-> (U -> Contr A).
  Proof.
    split.
    - intros ? u.
      refine (@contr_equiv (join U A) A (O_unit A)^-1 _ _).
      pose (contr_inhabited_hprop U u).
      exact _.
    - intros uac.
      refine (isequiv_adjointify _ _ _ _);
        unfold O, O_unit, closed_unitsubuniverse.
      * refine (pushout_rectnd A _ _).
        + intros [u | a].
          { pose (uac u). exact (center A). }
          { assumption. }
        + intros [u a]. simpl.
          pose (uac u). apply contr.
      * intros z. pattern z.
        refine (pushout_rect fst snd _ _ _ z).
        + intros [u | a].
          { pose (contr_inhabited_hprop U u).
            apply path_contr. } 
          { reflexivity. }
        + intros [u a]; pose (contr_inhabited_hprop U u).
          apply path_contr.
      * intros a. reflexivity.
  Defined.

  (* Not Global! *)
  Instance closed_modality : Modality.
  Proof.
    refine (Build_Modality closed_unitsubuniverse _ _ _).
    - intros A B f z.
      refine (pushout_rect _ _ (fun z' => join U (B z')) _ _ z).
      * intros [u | a].
        + exact (push (inl u)).
        + apply f.
      * intros [u a].
        pose (contr_inhabited_hprop U u).
        apply path_contr.
    - reflexivity.
    - intros A z z'.
      apply (snd (inO_closed (z = z'))).
      intros u; pose (contr_inhabited_hprop U u).
      exact _.
  Defined.

End ClosedModality.
