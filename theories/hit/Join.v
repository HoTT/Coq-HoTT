(* -*- mode: coq; mode: visual-line -*- *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp HSet.
Require Import hit.Pushout.
Local Open Scope path_scope.

(** * Joins *)

(** The join is the pushout of two types under their product. *)
Section Join.

  Definition join (A : Type@{i}) (B : Type@{j})
    := pushout@{k i j k k} (@fst A B) (@snd A B).

  Definition joinpp A B := @pp (A*B) A B fst snd.

  (** Joining with a contractible type produces a contractible type *)
  Global Instance contr_join A B `{Contr A} : Contr (join A B).
  Proof.
    exists (push (inl (center A))).
    intros y; simple refine (pushout_ind _ _ _ _ _ y).
    - intros [a | b].
      * apply ap, ap, contr.
      * exact (pp (center A , b)).
    - intros [a b]. cbn.
      refine (_ @ apD (fun a' => joinpp A B (a',b)) (contr a)^).
      rewrite transport_paths_r, transport_paths_FlFr.
      rewrite ap_V, inv_V, concat_pp_p.
      unfold pushl, pushr; simpl.
      rewrite <- ap_compose; unfold joinpp.
      rewrite ap_const, concat_p1.
      reflexivity.
  Defined.

End Join.
