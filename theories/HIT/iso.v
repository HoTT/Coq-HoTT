Require Import HoTT.Basics.
Require Import Types.Universe.
Require Import HSet.
Require Import HIT.epi HIT.unique_choice.

Local Open Scope path_scope.

(** We prove that [epi + mono <-> IsEquiv] *)
Section iso.
  Context `{Univalence}.
  Variables X Y : HSet.
  Variable f : X -> Y.

  Lemma atmost1P_isinj (injf : IsInjective f)
  : forall y : Y, atmost1P (fun x => f x = y).
  Proof.
    intros y x x' p q.
    apply (injective f).
    exact (p @ q^).
  Defined.

  Definition isequiv_isepi_ismono (epif : isepi f) (monof : ismono f)
  : IsEquiv f.
  Proof.
    pose proof (@isepi_issurj _ _ _ f epif) as surjf.
    pose proof (isinj_ismono _ monof) as injf.
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
