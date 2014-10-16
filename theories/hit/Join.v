(* -*- mode: coq; mode: visual-line -*- *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp HSet.
Require Import hit.Pushout.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Joins *)

(** The join is the pushout of two types under their product. *)
Section Join.

  Context (A B : Type).

  Definition join := pushout (@fst A B) (@snd A B).

  Definition joinpp := @pp (A*B) A B fst snd.

  (** Joining with a contractible type produces a contractible type *)
  Global Instance contr_join `{Contr A} : Contr join.
  Proof.
    exists (push (inl (center A))).
    intros y; refine (pushout_ind _ _ _ _ _ y).
    - intros [a | b].
      * apply ap, ap, contr.
      * exact (pp (center A , b)).
    - intros [a b]. cbn.
      refine (_ @ apD (fun a' => joinpp (a',b)) (contr a)^).
      rewrite transport_paths_r, transport_paths_FlFr.
      rewrite ap_V, inv_V, concat_pp_p.
      unfold pushl, pushr; simpl.
      rewrite <- ap_compose; unfold compose, joinpp.
      rewrite ap_const, concat_p1.
      reflexivity.
  Defined.

End Join.
