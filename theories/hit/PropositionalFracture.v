(* -*- mode: coq; mode: visual-line -*-  *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp TruncType Extensions ReflectiveSubuniverse Modality Localization.
Require Import hit.Pushout hit.Join.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Open and closed modalities and the propositional fracture theorem *)

(** Exercise 7.13(i): Open modalities *)
Section OpenModality.
Context `{Funext} (U : hProp).

Definition Op : Modality.
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

Global Instance accessible_op : Accessible Op.
Proof.
  refine (Build_Accessible_Modality _ Unit (fun _ => U) _);
    intros X; split.
  - intros X_inO u.
    apply ((equiv_ooextendable_isequiv _ _)^-1).
    refine (cancelR_isequiv (fun x (u:Unit) => x)).
    apply X_inO.
  - intros ext; specialize (ext tt).
    refine (isequiv_compose (f := (fun x => unit_name x))
                            (g := (fun h => h o (@const U Unit tt)))).
    refine (isequiv_ooextendable (fun _ => X) (@const U Unit tt) ext).
Defined.

(** Thus, arguably a better definition of [Op] would be [Nul (fun (_:Unit) => U)], as it would not require [Funext], would be universe polymorphic, and would have a judgmental computation rule.  However, the above definition is also nice to know, as it doesn't use HITs.  We call the non-funext version defined by localization [Op']. *)
Definition Op' : Modality
  := nudge_modality Op.

End OpenModality.

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

  Definition Cl : Modality.
  Proof.
    refine (Build_Modality
              (Build_UnitSubuniverse
                 (fun X => join U X)
                 (fun X => U -> Contr X)
                 _
                 (fun X x => push (inr x))
                 _ _)
              _ _ _); cbn; try exact _.
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

  Global Instance accessible_cl (U : hProp) : Accessible Cl.
  Proof.
    refine (Build_Accessible_Modality Cl U (fun _ => Empty) _);
      intros X; split.
    - intros X_inO u.
      pose (X_inO u).
      apply ooextendable_contr; exact _.
    - intros ext u.
      exists ((fst (ext u 1%nat) Empty_rec).1 tt); intros x.
      unfold const in ext.
      exact ((fst (snd (ext u 2) (fst (ext u 1%nat) Empty_rec).1
                       (fun _ => x)) (Empty_ind _)).1 tt).
  Defined.

End ClosedModality.
