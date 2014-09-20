Require Import Basics.
Require Import types.Universe.
Require Import HSet UnivalenceImpliesFunext.
Require Import hit.epi hit.unique_choice hit.Truncations.

Open Local Scope path_scope.
Open Local Scope equiv_scope.

(** We prove that [epi + mono <-> IsEquiv] *)
Section iso.
  Context `{Univalence}.
  Variables X Y : hSet.
  Variable f : X -> Y.

  Lemma atmost1P_isinj (injf : isinj f)
  : forall y : Y, atmost1P (fun x => f x = y).
  Proof.
    unfold isinj, atmost1P in *.
    intros.
    apply injf.
    path_induction.
    reflexivity.
  Defined.

  Definition isequiv_isepi_ismono (epif : isepi f) (monof : ismono f)
  : IsEquiv f.
  Proof.
    pose proof (@isepi_issurj _ _ _ f epif) as surjf.
    pose proof (ismono_isinj _ monof) as injf.
    pose proof (unique_choice
                  (fun y x => f x = y)
                  _
                  (fun y => (@center _ (surjf y), atmost1P_isinj injf y)))
      as H_unique_choice.
    apply (isequiv_adjointify _ H_unique_choice.1).
    - intro.
      apply H_unique_choice.2.
    - intro.
      apply injf.
      apply H_unique_choice.2.
  Defined.
End iso.
