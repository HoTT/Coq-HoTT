(* -*- mode: coq; mode: visual-line -*-  *)
(** * Nullification *)

Require Import HoTT.Basics HoTT.Types.
Require Import Extensions.
Require Import Modality Accessible.
Require Export Localization.    (** Nullification is a special case of localization *)

Local Open Scope path_scope.

(** Nullification is the special case of localization where the codomains of the generating maps are all [Unit].  In this case, we get a modality and not just a reflective subuniverse. *)

(** The hypotheses of this lemma may look slightly odd (why are we bothering to talk about type families dependent over [Unit]?), but they seem to be the most convenient to make the induction go through.  *)

Definition extendable_over_unit (n : nat)
  (A : Type@{a}) (C : Unit@{a} -> Type@{i}) (D : forall u, C u -> Type@{j})
  (ext : ExtendableAlong@{a a i k} n (@const A Unit tt) C)
  (ext' : forall (c : forall u, C u),
            ExtendableAlong@{a a j k} n (@const A Unit tt) (fun u => (D u (c u))))
: ExtendableAlong_Over@{a a i j k} n (@const A Unit tt) C D ext.
Proof.
  generalize dependent C; simple_induction n n IH;
    intros C D ext ext'; [exact tt | split].
  - intros g g'.
    exists ((fst (ext' (fst ext g).1)
                 (fun a => ((fst ext g).2 a)^ # (g' a))).1);
      intros a; simpl.
    apply moveR_transport_p.
    exact ((fst (ext' (fst ext g).1)
                (fun a => ((fst ext g).2 a)^ # (g' a))).2 a).
  - intros h k h' k'.
    apply IH; intros g.
    exact (snd (ext' k) (fun u => g u # h' u) k').
Defined.

Definition ooextendable_over_unit
  (A : Type) (C : Unit -> Type) (D : forall u, C u -> Type)
  (ext : ooExtendableAlong (@const A Unit tt) C)
  (ext' : forall (c : forall u, C u),
            ooExtendableAlong (@const A Unit tt) (fun u => (D u (c u))))
: ooExtendableAlong_Over (@const A Unit tt) C D ext
  := fun n => extendable_over_unit n A C D (ext n) (fun c => ext' c n).

(** We define a wrapper, as before. *)
Record Nullification_Modality := Nul { unNul : NullGenerators }.

Module Nullification_Modalities <: Modalities.

  Definition Modality : Type@{u} := Nullification_Modality@{a}.

  (** We use the localization reflective subuniverses for most of the necessary data. *)
  Module LocRSU_Data <: ReflectiveSubuniverses_Restriction_Data Localization_ReflectiveSubuniverses.
    Definition New_ReflectiveSubuniverse : let enforce := Type@{u'} : Type@{u} in Type@{u}
      := Nullification_Modality@{u'}.
    Definition ReflectiveSubuniverses_restriction
    : New_ReflectiveSubuniverse@{u a}
      -> Localization_ReflectiveSubuniverses.ReflectiveSubuniverse@{u a}
      := fun O => Loc (null_to_local_generators (unNul O)).
  End LocRSU_Data.

  Module LocRSU := ReflectiveSubuniverses_Restriction Localization_ReflectiveSubuniverses LocRSU_Data.

  Module LocRSUTh := ReflectiveSubuniverses_Theory LocRSU.

  Definition O_reflector := LocRSU.O_reflector.
  Definition In := LocRSU.In.
  Definition O_inO := @LocRSU.O_inO.
  Definition to := LocRSU.to.
  Definition inO_equiv_inO := @LocRSU.inO_equiv_inO@{u a i j k}.
  Definition hprop_inO := LocRSU.hprop_inO.

  Definition O_ind_internal (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa : O_reflector@{u a i} O A, In@{u a j} O (B oa))
             (g : forall a : A, B (to@{u a i} O A a))
  : forall x, B x.
  Proof.
    refine (Localize_ind@{a i j k}
             (null_to_local_generators@{a a} (unNul O)) A B g _); intros i.
    apply (ooextendable_over_unit@{a i j a k}); intros c.
    refine (ooextendable_postcompose@{a a j j k j j j k j k}
              (fun (_:Unit) => B (c tt)) _ _
              (fun u => transport@{i j} B (ap c (path_unit tt u))) _).
    refine (ooextendable_islocal _ i).
    apply B_inO.
  Defined.

  Definition O_ind_beta_internal (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa : O_reflector O A, In@{u a j} O (B oa))
             (f : forall a : A, B (to O A a)) (a : A)
  : O_ind_internal@{u a i j k} O A B B_inO f (to O A a) = f a
    := 1.

  Definition minO_paths (O : Modality@{u a}) (A : Type@{i})
             (A_inO : In@{u a i} O A) (z z' : A)
  : In@{u a i} O (z = z').
  Proof.
    apply (LocRSUTh.inO_paths@{u a i i}); assumption.
  Defined.

End Nullification_Modalities.

(** If you import the following module [NulM], then you can call all the reflective subuniverse functions with a [NullGenerators] as the parameter. *)
Module Import NulM := Modalities_Theory Nullification_Modalities.
(** If you don't import it, then you'll need to write [NulM.function_name]. *)
Export NulM.Coercions.
Export NulM.RSU.Coercions.

Coercion Nullification_Modality_to_Modality := idmap
  : Nullification_Modality -> Modality.

(** And here is the "real" definition of the notation [IsNull]. *)
Notation IsNull f := (In (Nul f)).

(** ** Nullification and Accessibility *)

(** Nullification modalities are accessible, essentially by definition. *)
Module Accessible_Nullification
  <: Accessible_Modalities Nullification_Modalities.

  Module Import Os_Theory := Modalities_Theory Nullification_Modalities.

  Definition acc_gen : Modality -> NullGenerators
    := unNul.

  Definition inO_iff_isnull (O : Modality@{u a}) (X : Type@{i})
  : iff@{i i i} (In@{u a i} O X) (IsNull (acc_gen O) X)
    := (idmap , idmap).

End Accessible_Nullification.


(** And accessible modalities can be nudged into nullifications. *)

Module Nudge_Modalities
       (Os : Modalities)
       (Acc : Accessible_Modalities Os).

  (** Application of modules is still "restricted to paths". *)
  Module Data <: Modalities_Restriction_Data Nullification_Modalities.
    Definition New_Modality := Os.Modality.
    Definition Modalities_restriction
    : New_Modality -> Nullification_Modalities.Modality
      := Nul o Acc.acc_gen.
  End Data.

  Module Nudged <: Modalities
    := Modalities_Restriction Nullification_Modalities Data.

End Nudge_Modalities.
