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

Definition Nul@{a i} (S : NullGenerators@{a}) : Modality@{i}.
Proof.
  (** We use the localization reflective subuniverses for most of the necessary data. *)
  simple refine (Build_Modality' (Loc (null_to_local_generators S)) _ _).
  - exact _.
  - intros A.
    (** We take care with universes. *)
    simple notypeclasses refine (reflectsD_from_OO_ind@{i} _ _ _).
    + intros B B_inO g.
      refine (Localize_ind@{a i i i} (null_to_local_generators S) A B g _); intros i.
      apply ooextendable_over_unit; intros c.
      refine (ooextendable_postcompose@{a a i i i i i i i i}
                (fun (_:Unit) => B (c tt)) _ _
                (fun u => transport B (ap c (path_unit@{a} tt u))) _).
      refine (ooextendable_islocal _ i).
    + reflexivity.
    + apply inO_paths@{i i i}.
  Defined.

(** And here is the "real" definition of the notation [IsNull]. *)
Notation IsNull f := (In (Nul f)).

(** ** Nullification and Accessibility *)

(** Nullification modalities are accessible, essentially by definition. *)
Global Instance accmodality_nul (S : NullGenerators) : IsAccModality (Nul S).
Proof.
  unshelve econstructor.
  - exact S.
  - intros; reflexivity.
Defined.

(** And accessible modalities can be lifted to other universes. *)

Definition lift_accmodality@{a i j} (O : Subuniverse@{i}) `{IsAccModality@{a i} O}
  : Modality@{j}
  := Nul@{a j} (acc_ngen O).

Global Instance O_eq_lift_accmodality (O : Subuniverse@{i}) `{IsAccModality@{a i} O}
  : O <=> lift_accmodality O.
Proof.
  split; intros A; apply inO_iff_isnull.
Defined.
