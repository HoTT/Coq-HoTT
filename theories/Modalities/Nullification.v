(* -*- mode: coq; mode: visual-line -*-  *)
(** * Nullification *)

Require Import HoTT.Basics HoTT.Types HoTT.Cubical.
Require Import Extensions.
Require Import Modality Accessible.
Require Export Localization.    (** Nullification is a special case of localization *)
Require Import Homotopy.Suspension.

Local Open Scope path_scope.

(** Nullification is the special case of localization where the codomains of the generating maps are all [Unit].  In this case, we get a modality and not just a reflective subuniverse. *)

(** The hypotheses of this lemma may look slightly odd (why are we bothering to talk about type families dependent over [Unit]?), but they seem to be the most convenient to make the induction go through.  *)

Definition extendable_over_unit (n : nat)
  (A : Type@{a}) (C : Unit -> Type@{i}) (D : forall u, C u -> Type@{j})
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

Definition ooextendable_over_unit@{i j k l m}
  (A : Type@{i}) (C : Unit -> Type@{j}) (D : forall u, C u -> Type@{k})
  (ext : ooExtendableAlong@{l l j m} (@const@{l l} A Unit tt) C)
  (ext' : forall (c : forall u, C u),
            ooExtendableAlong (@const A Unit tt) (fun u => (D u (c u))))
: ooExtendableAlong_Over (@const A Unit tt) C D ext
  := fun n => extendable_over_unit n A C D (ext n) (fun c => ext' c n).

(** A basic operation on local generators is the pointwise suspension. *)
Definition susp_nullgen@{a} (S : NullGenerators@{a}) : NullGenerators@{a}.
Proof.
  econstructor; intros i.
  exact (Susp@{a a a a a a} (S i)).
Defined.

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

  Definition O_reflector@{u a i} := LocRSU.O_reflector@{u a i}.
  Definition In@{u a i} := LocRSU.In@{u a i}.
  Definition O_inO@{u a i} := @LocRSU.O_inO@{u a i}.
  Definition to@{u a i} := LocRSU.to@{u a i}.
  Definition inO_equiv_inO := @LocRSU.inO_equiv_inO@{u a i j k}.
  Definition hprop_inO@{u a i} := LocRSU.hprop_inO@{u a i}.

  Definition O_ind_internal@{u a i j k} (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} O A -> Type@{j})
             (B_inO : forall oa : O_reflector@{u a i} O A, In@{u a j} O (B oa))
             (g : forall a : A, B (to@{u a i} O A a))
  : forall x, B x.
  Proof.
    refine (Localize_ind@{a i j k}
             (null_to_local_generators@{a a} (unNul O)) A B g _); intros i.
    apply (ooextendable_over_unit@{a i j a k}); intros c.
    refine (ooextendable_postcompose
              (fun (_:Unit) => B (c tt)) _ _
              (fun u => transport@{i j} B (ap c (path_unit@{a} tt u))) _).
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

  (** Just as for general localizations, the separated modality corresponding to a nullification is nullification at the suspension of the generators.  The proofs are a little more involved because we have to transfer across the equivalence [Susp Unit <~> Unit]. *)
  Definition IsSepFor@{u a} (O' O : Modality@{u a}) : Type@{u}
    := paths@{u} (Nul (susp_nullgen (unNul O))) O'.

  Definition inO_paths_from_inSepO@{u a i iplus}
             (O' O : Modality@{u a}) (sep : IsSepFor O' O)
             (A : Type@{i}) (A_inO : In@{u a i} O' A) (x y : A)
    : In@{u a i} O (x = y).
  Proof.
    destruct O as [S]; destruct sep; unfold In, IsLocal in *; intros i; cbn in *.
    specialize (A_inO i).
    cbn in A_inO.
    assert (ee : ooExtendableAlong (functor_susp (fun _:S i => tt)) (fun _ => A)).
    { refine (cancelL_ooextendable _ _ (fun _ => tt) _ A_inO).
      apply ooextendable_equiv.
      apply isequiv_contr_contr. }
    assert (e := fst (ooextendable_iff_functor_susp@{a a i i a a a i i iplus i a a a i i iplus i i i i i i i i i i i i iplus i i i iplus i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i} (fun _:S i => tt) _) ee (x,y)).
    cbn in e.
    refine (ooextendable_postcompose' _ _ _ _ e).
    intros b.
    symmetry; apply equiv_dp_const.
  Defined.

  Definition inSepO_from_inO_paths@{u a i iplus}
             (O' O : Modality@{u a}) (sep : IsSepFor O' O)
             (A : Type@{i}) (e : forall (x y : A), In@{u a i} O (x = y))
    : In@{u a i} O' A.
  Proof.
    destruct O as [S]; destruct sep; unfold In, IsLocal in *; intros i; cbn in *.
    apply (ooextendable_compose _ (functor_susp (fun _:S i => tt)) (fun _:Susp Unit => tt)).
    1:apply ooextendable_equiv, isequiv_contr_contr.
    apply (ooextendable_iff_functor_susp@{a a i i a a a i i iplus i a a a i i iplus i i i i i i i i i i i i iplus i i i iplus i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i i} (fun _:S i => tt)).  
    intros [x y].
    refine (ooextendable_postcompose' _ _ _ _ (e x y i)).
    intros b.
    apply equiv_dp_const.
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

Module Import AccNulM := Accessible_Modalities_Theory Nullification_Modalities Accessible_Nullification.

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
