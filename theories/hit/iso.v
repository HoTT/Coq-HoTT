Require Import Overture hit.epi HSet types.Universe hit.unique_choice Equivalences.

Open Local Scope path_scope.
Open Local Scope equiv_scope.

(** We prove that [epi + mono <-> IsEquiv] *)
Section iso.
  Context `{Univalence}.
  Context `{fs1 : Funext}.
  Context `{fs2 : Funext}.
  Variables X Y : hSet.
  Variable f : X -> Y.

  Lemma inj_atmost1P (injf : inj f)
  : forall y : Y, atmost1P (fun x => f x = y).
  Proof.
    unfold inj, atmost1P in *.
    intros.
    apply injf.
    path_induction.
    reflexivity.
  Defined.

  Definition isequiv_epi_mono (epif : epi f) (monof : mono f)
  : IsEquiv f.
  Proof.
    pose proof (@epi_surj fs1 _ fs2 _ _ f epif) as surjf.
    pose proof (mono_inj _ monof) as injf.
    pose proof (unique_choice
                  (fun y x => f x = y)
                  _
                  (fun y => (surjf y, inj_atmost1P injf y)))
      as H_unique_choice.
    apply (isequiv_adjointify _ H_unique_choice.1).
    - intro.
      apply H_unique_choice.2.
    - intro.
      apply injf.
      apply H_unique_choice.2.
  Defined.
End iso.
