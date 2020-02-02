(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Modality Accessible.

Local Open Scope path_scope.


(** * The identity modality *)

(** Everything to say here is fairly trivial. *)

Inductive Identity_Modality : Type1
  := purely : Identity_Modality.

Module Identity_Modalities <: Modalities.

  Definition Modality : Type2@{u a}
    := Identity_Modality@{a}.

  Definition O_reflector : forall (O : Modality@{u a}),
                            Type@{i} -> Type@{i}
    := fun O X => X.

  Definition In : forall (O : Modality@{u a}),
                             Type@{i} -> Type@{i}
    := fun O X => Unit.

  Definition O_inO : forall (O : Modality@{u a}) (T : Type@{i}),
                               In@{u a i} O (O_reflector@{u a i} O T)
    := fun O X => tt.

  Definition to : forall (O : Modality@{u a}) (T : Type@{i}),
                   T -> O_reflector@{u a i} O T
    := fun O X x => x.

  Definition inO_equiv_inO :
      forall (O : Modality@{u a}) (T : Type@{i}) (U : Type@{j})
             (T_inO : In@{u a i} O T) (f : T -> U) (feq : IsEquiv f),
        let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
        let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
        In@{u a j} O U
    := fun O T U _ _ _ => tt.

  Definition hprop_inO@{u a i}
  : Funext -> forall (O : Modality@{u a}) (T : Type@{i}),
                IsHProp (In@{u a i} O T)
    := fun _ O T => trunc_contr@{i}.

  Definition O_ind_internal
  : forall (O : Modality@{u a})
           (A : Type@{i}) (B : O_reflector O A -> Type@{j})
           (B_inO : forall oa, In@{u a j} O (B oa)),
      let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
      let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
      (forall a, B (to O A a)) -> forall a, B a
  := fun O A B _ f a => f a.

  Definition O_ind_beta_internal
  : forall (O : Modality@{u a})
           (A : Type@{i}) (B : O_reflector O A -> Type@{j})
           (B_inO : forall oa, In@{u a j} O (B oa))
           (f : forall a : A, B (to O A a)) (a:A),
      O_ind_internal O A B B_inO f (to O A a) = f a
    := fun _ _ _ _ _ _ => 1.

  Definition minO_paths
  : forall (O : Modality@{u a})
           (A : Type@{i}) (A_inO : In@{u a i} O A) (z z' : A),
      In@{u a i} O (z = z')
    := fun _ _ _ _ _ => tt.

  Definition IsSepFor@{u a}
    : forall (O' O : Modality@{u a}), Type@{u}
    := fun _ _ => Unit.

  Definition inO_paths_from_inSepO@{u a i iplus}
    : forall (O' O : Modality@{u a}) (sep : IsSepFor O' O)
             (A : Type@{i}) (A_inO : In@{u a i} O' A) (x y : A),
      In@{u a i} O (x = y)
    := fun _ _ _ _ _ _ _ => tt.

  Definition inSepO_from_inO_paths@{u a i iplus}
    : forall (O' O : Modality@{u a}) (sep : IsSepFor O' O)
             (A : Type@{i}),
      (forall (x y : A), In@{u a i} O (x = y)) -> In@{u a i} O' A
    := fun _ _ _ _ _ => tt.

End Identity_Modalities.

Module purelyM := Modalities_Theory Identity_Modalities.
Export purelyM.Coercions.
Export purelyM.RSU.Coercions.

Coercion Identity_Modalities_to_Modalities := idmap
  : Identity_Modality -> Identity_Modalities.Modality.


Module Accessible_Identity <: Accessible_Modalities Identity_Modalities.

  Module Import Os_Theory := Modalities_Theory Identity_Modalities.

  Definition acc_gen : Modality@{u a} -> NullGenerators@{a}
    := fun _ => Build_NullGenerators Empty (fun _ => Empty).

  Definition inO_iff_isnull@{u a i}
  : forall (O : Modality@{u a}) (X : Type@{i}),
      iff@{i i i}
        (In@{u a i} O X)
        (IsNull_Internal.IsNull@{a i} (acc_gen O) X)
  := fun O X => @pair _ (_ -> Unit)
     (fun _ => Empty_ind _)
     (fun _ => tt).

End Accessible_Identity.
