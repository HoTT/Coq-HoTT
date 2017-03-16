(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Modality.

Local Open Scope path_scope.


(** * The double negation modality *)

(** This is Exercise 7.12 in the book.  Note that it is (apparently) *not* accessible unless we assume propositional resizing. *)

(** We are defining only one modality, but it depends on funext.  Therefore, we let the family of modalities be the type [Funext].  However, since there is a coercion [O_reflector] from [Modality] to [Funclass], we don't want to simply *define* [Modality] to be [Funext], or else we could start applying [Funext] hypotheses to types and having it act as double negation.

Instead, we define a [Record] wrapper around it.  This is the recommended best practice for all modules (with one exception, see Truncations.v).  The constructor of the record should generally be a short name (here [Notnot]) that makes sense as the reflector. *)

Record Notnot_Modality := Notnot { unNotnot : Funext }.

Module Notnot_Easy_Modalities <: EasyModalities.

  Definition Modality : Type2@{u a}
    := Notnot_Modality.

  Definition O_reflector : Modality@{u a} -> Type@{i} -> Type@{i}
    (** We call [not] explicitly with universe annotations so that [O_reflector] has the right number of universe parameters to satisfy the module type. *)
    := fun O X => not@{i i} (not@{i i} X).

  Definition to (O : Modality@{u a}) (T : Type@{i})
  : T -> O_reflector@{u a i} O T
  := fun x nx => nx x.

  Definition O_indO@{u a i j} (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} O A -> Type@{j})
  : (forall a : A, O_reflector@{u a j} O (B (to O A a))) ->
    forall z : O_reflector@{u a i} O A, O_reflector@{u a j} O (B z).
  Proof.
    intros f z nBz.
    pose (unNotnot O).          (** Access the [Funext] hypothesis *)
    apply z; intros a.
    pose proof (hprop_Empty@{i}).
    exact (f a (transport (fun x => not@{j j} (B x))
                          (path_ishprop _ _)
                          nBz)).
  Defined.

  Definition O_indO_beta@{u a i j} (O : Modality@{u a}) (A : Type@{i})
             (B : O_reflector@{u a i} O A -> Type@{j})
             (f : forall a, O_reflector@{u a j} O (B (to O A a))) (a:A)
  : O_indO O A B f (to O A a) = f a.
  Proof.
    pose (unNotnot O).
    pose proof (hprop_Empty@{j}).
    apply path_ishprop.
  Defined.

  Definition minO_pathsO@{u a i} (O : Modality@{u a}) (A : Type@{i})
             (z z' : O_reflector@{u a i} O A)
  : IsEquiv@{i i} (to@{u a i} O (z = z')).
  Proof.
    pose (unNotnot O).
    pose proof (hprop_Empty@{i});pose proof (@trunc_hprop@{i}).
    refine (isequiv_iff_hprop _ _).
    intros; apply path_ishprop.
  Defined.

End Notnot_Easy_Modalities.

Module Notnot_Modalities <: Modalities := EasyModalities_to_Modalities Notnot_Easy_Modalities.

(** After we define any family of modalities or reflective subuniverses, we give a corresponding name to the theory module, generally by postfixing the above-mentioned record constructor with [M] (for "module").  This way, one can either [Import] the theory module (here [NotnotM]) and get access to all the modality functions for the modalities in question, or not import it and access them qualified as [NotnotM.function_name]. *)
Module NotNotM := Modalities_Theory Notnot_Modalities.
Export NotNotM.Coercions.
Export NotNotM.RSU.Coercions.

(** Finally, we declare a coercion allowing us to use elements of the record wrapper as modalities. *)
Coercion Notnot_Modalities_to_Modalities := idmap
  : Notnot_Modality -> Notnot_Modalities.Modality.
