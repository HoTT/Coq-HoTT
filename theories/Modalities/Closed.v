(* -*- mode: coq; mode: visual-line -*-  *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp TruncType Extensions.
Require Import Modality Accessible Nullification.
Require Import hit.Pushout hit.Join.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Closed modalities *)

(** We begin by characterizing the modal types. *)
Section ClosedModalTypes.
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

End ClosedModalTypes.

Record Closed_Modality := Cl { unCl : hProp }.

(** Exercise 7.13(ii): Closed modalities *)
Module ClosedModalities <: Modalities.

  Definition Modality : Type@{u} := Closed_Modality@{a}.

  Definition O_reflector : Modality@{u a} -> Type@{i} -> Type@{i}
    := fun O X => join@{a i i} (unCl O) X.

  Definition inO_internal : Modality@{u a} -> Type@{i} -> Type@{i}
    := fun O X => unCl O -> Contr X.

  Definition O_inO_internal (O : Modality@{u a}) (T : Type@{i})
  : inO_internal@{u a i} O (O_reflector@{u a i} O T).
  Proof.
    intros u.
    pose (contr_inhabited_hprop _ u).
    exact _.
  Defined.

  Definition to (O : Modality@{u a}) (T : Type@{i})
  : T -> O_reflector@{u a i} O T
    := fun x => push (inr x).

  Definition inO_equiv_inO_internal (O : Modality@{u a}) (T U : Type@{i})
     (T_inO : inO_internal@{u a i} O T) (f : T -> U) (feq : IsEquiv@{i i} f)
  : inO_internal@{u a i} O U.
  Proof.
    intros u; pose (T_inO u).
    refine (contr_equiv _ f); exact _.
  Defined.

  Definition hprop_inO_internal `{Funext}
             (O : Modality@{u a}) (T : Type@{i})
  : IsHProp (inO_internal@{u a i} O T).
  Proof.
    exact _.
  Defined.

  Definition O_ind_internal (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa, inO_internal@{u a j} O (B oa))
             (f : forall a : A, B (to O A a))
             (z : O_reflector O A)
  : B z.
  Proof.
    refine (pushout_ind@{i a i j j} _ _ B _ _ z).
    - intros [u | a].
      + apply center, B_inO, u.
      + apply f.
    - intros [u a].
      pose (B_inO (push (inr a)) u).
      apply path_contr.
  Defined.

  Definition O_ind_beta_internal (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa, inO_internal@{u a j} O (B oa))
             (f : forall a : A, B (to O A a)) (a : A)
  : O_ind_internal O A B B_inO f (to O A a) = f a
  := 1.

  Definition minO_paths (O : Modality@{u a}) (A : Type@{i})
             (A_inO : inO_internal@{u a i} O A)
             (z z' : A)
  : inO_internal@{u a i} O (z = z').
  Proof.
    intros u; pose (A_inO u); apply contr_paths_contr.
  Defined.

End ClosedModalities.

Module ClM := Modalities_Theory ClosedModalities.
Export ClM.Coercions.
Export ClM.RSU.Coercions.

Coercion Closed_Modality_to_Modality :=
  idmap : Closed_Modality -> ClosedModalities.Modality.

(** The closed modality is accessible. *)
Module Accessible_ClosedModalities
  <: Accessible_Modalities ClosedModalities.

  Definition acc_gen
    := fun (O : ClosedModalities.Modality@{u a}) =>
         Build_NullGenerators@{a} (unCl O) (fun _ => Empty@{a}).

  Definition inO_iff_isnull_internal
             (O : ClosedModalities.Modality@{u a}) (X : Type@{i})
  : iff@{i i i}
      (ClosedModalities.inO_internal@{u a i} O X)
      (IsNull (acc_gen O) X).
  Proof.
    split.
    - intros X_inO u.
      pose (X_inO u).
      apply ooextendable_contr; exact _.
    - intros ext u.
      exists ((fst (ext u 1%nat) Empty_rec).1 tt); intros x.
      unfold const in ext.
      exact ((fst (snd (ext u 2) (fst (ext u 1%nat) Empty_rec).1
                       (fun _ => x)) (Empty_ind _)).1 tt).
  Defined.

End Accessible_ClosedModalities.

(** Thus, it also has the following alternative version. *)
Definition Cl' (U : hProp) : Nullification_Modality
  := Nul (Build_NullGenerators U (fun _ => Empty)).
