(* -*- mode: coq; mode: visual-line -*-  *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp TruncType Extensions.
Require Import Modality Accessible Nullification Lex.

Local Open Scope path_scope.


(** * Open modalities *)

Record Open_Modality :=
  Op { funext_Op : Funext ;
       unOp : hProp
     }.

Arguments Op {_} _.

(** ** Open modalities *)

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
    pose (fs := funext_Op O); simple refine (isequiv_adjointify _ _ _ _).
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

Module Import OpM := Modalities_Theory OpenModalities.
Export OpM.Coercions.
Export OpM.RSU.Coercions.

Coercion Open_Modality_to_Modality :=
  idmap : Open_Modality -> OpenModalities.Modality.

(** ** The open modality is lex *)

(** Note that unlike the case for closed and topological modalities, we can prove this without univalence (though we do of course need funext). *)
Module Import Lex_OpenModalities := Lex_Modalities_Theory OpenModalities.

Global Instance lex_open (O : Modality)
: Lex O.
Proof.
  intros A x y.
  pose (U := unOp O); pose proof (funext_Op O).
  change (Contr (U -> A) -> Contr (U -> (x = y))); intros ?.
  assert (uc : U -> Contr A).
  { intros u.
    pose (contr_inhabited_hprop U u).
    refine (contr_equiv (U -> A) (equiv_contr_forall _)). }
  simple refine (BuildContr _ _ _).
  - intros u; pose (uc u); exact (center (x=y)).
  - intros f; apply path_arrow; intros u.
    pose proof (uc u); apply path_contr.
Defined.

(** ** The open modality is accessible. *)

Module Accessible_OpenModalities <: Accessible_Modalities OpenModalities.

  Module Import Os_Theory := Modalities_Theory OpenModalities.

  Definition acc_gen
    := fun (O : OpenModalities.Modality@{u a}) =>
         Build_NullGenerators@{a} Unit@{a} (fun _ => unOp O).

  Definition inO_iff_isnull
             (O : OpenModalities.Modality@{u a}) (X : Type@{i})
  : iff@{i i i}
      (OpenModalities.In@{u a i} O X)
      (IsNull (acc_gen O) X).
  Proof.
    pose (funext_Op O); split.
    - intros X_inO u.
      apply (equiv_inverse (equiv_ooextendable_isequiv@{a a i i i i i} _ _)).
      refine (cancelR_isequiv (fun x (u:Unit) => x)).
      apply X_inO.
    - intros ext; specialize (ext tt).
      refine (isequiv_compose (f := (fun x => unit_name x))
                              (g := (fun h => h o (@const (unOp O) Unit tt)))).
      refine (isequiv_ooextendable (fun _ => X) (@const (unOp O) Unit tt) ext).
  Defined.

End Accessible_OpenModalities.

(** Thus, arguably a better definition of [Op] would be as a nullification modality, as it would not require [Funext] and would have a judgmental computation rule.  However, the above definition is also nice to know, as it doesn't use HITs.  We name the other version [Op']. *)
Definition Op' (U : hProp) : Nullification_Modality
  := Nul (Build_NullGenerators Unit (fun (_:Unit) => U)).
