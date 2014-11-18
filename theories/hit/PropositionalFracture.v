(* -*- mode: coq; mode: visual-line -*-  *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp TruncType Extensions ReflectiveSubuniverse Modality.
Require Import hit.Pushout hit.Join hit.Localization hit.Nullification.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Open and closed modalities and the propositional fracture theorem *)

Record Open_Modality :=
  Op { funext_Op : Funext ;
       unOp : hProp
     }.

(** Exercise 7.13(i): Open modalities *)
Module OpenModalities_easy <: EasyModalities.

  Definition Modality : Type@{u} := Open_Modality@{a}.

  Definition O_reflector : Modality@{u a} -> Type@{i} -> Type@{i}
    := fun fU X => unOp fU -> X.

  Definition to (O : Modality@{u a}) (T : Type@{i}) : T -> O_reflector@{u a i} O T
    := fun x u => x.

  Definition O_indO (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector O A -> Type@{j})
             (f : forall a, O_reflector@{u a j} O (B (to@{u a i} O A a)))
    : forall z, O_reflector@{u a j} O (B z).
  Proof.
    intros z u; pose (funext_Op O).
    refine (transport@{i j} B _ (f (z u) u)).
    apply path_arrow; intros u'.
    unfold to; apply ap; apply path_ishprop.
  Defined.

  Definition O_indO_beta (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} O A -> Type@{j})
             (f : forall a, O_reflector@{u a j} O (B (to O A a))) (a : A)
  : O_indO O A B f (to O A a) = f a.
  Proof.
    pose (funext_Op O); apply path_arrow; intros u.
    transitivity (transport B 1 (f a u));
      auto with path_hints.
    apply (ap (fun p => transport B p (f a u))).
    transitivity (path_arrow (fun _ => a) (fun _ => a) (@ap10 (unOp O) _ _ _ 1));
      auto with path_hints.
    * apply ap@{i i}.
      apply path_forall; intros u'.
      apply ap_const.
    * apply eta_path_arrow.
  Defined.

  Definition minO_pathsO (O : Modality@{u a}) (A : Type@{i})
             (z z' : O_reflector@{u a i} O A)
  : IsEquiv@{i i} (to O (z = z')).
  Proof.
    pose (fs := funext_Op O); refine (isequiv_adjointify _ _ _ _).
    * intros f; apply path_arrow; intros u.
      exact (ap10 (f u) u).
    * intros f; apply path_arrow; intros u.
      transitivity (path_arrow z z' (ap10 (f u))).
      + unfold to; apply ap@{i i}.
        apply path_forall; intros u'.
        apply (ap (fun u0 => ap10 (f u0) u')).
        apply path_ishprop.
      + apply eta_path_arrow.
    * intros p.
      refine (eta_path_arrow _ _ _).
  Defined.

End OpenModalities_easy.

Module OpenModalities <: Modalities
  := EasyModalities_to_Modalities OpenModalities_easy.

Module OpM := Modalities_Theory OpenModalities.
Export OpM.Coercions.
Export OpM.RSU.Coercions.

Coercion Open_Modality_to_Modality :=
  idmap : Open_Modality -> OpenModalities.Modality.

(** The open modality is accessible. *)
Module Accessible_OpenModalities <: Accessible_Modalities OpenModalities.

  Definition acc_gen
    := fun (O : OpenModalities.Modality@{u a}) =>
         Build_NullGenerators@{a} Unit@{a} (fun _ => unOp O).

  Definition inO_iff_isnull_internal
             (O : OpenModalities.Modality@{u a}) (X : Type@{i})
  : iff@{i i i}
      (OpenModalities.inO_internal@{u a i} O X)
      (IsNull (acc_gen O) X).
  Proof.
    pose (funext_Op O); split.
    - intros X_inO u.
      apply (equiv_inverse (equiv_ooextendable_isequiv _ _)).
      refine (cancelR_isequiv (fun x (u:Unit) => x)).
      apply X_inO.
    - intros ext; specialize (ext tt).
      refine (isequiv_compose (f := (fun x => unit_name x))
                              (g := (fun h => h o (@const (unOp O) Unit tt)))).
      refine (isequiv_ooextendable (fun _ => X) (@const (unOp O) Unit tt) ext).
  Defined.

End Accessible_OpenModalities.

(** Thus, arguably a better definition of [Op] would be [Nul (fun (_:Unit) => U)], as it would not require [Funext] and would have a judgmental computation rule.  However, the above definition is also nice to know, as it doesn't use HITs. *)

(** Exercise 7.13(ii): Closed modalities *)

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
