(* -*- mode: coq; mode: visual-line -*- *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp HSet.
Require Import HIT.Pushout HIT.Truncations.
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
    exists (pushl (center A)).
    intros y; simple refine (pushout_ind _ _ _ _ _ _ y).
    - intros a; apply ap, contr.
    - intros b; exact (pp (center A , b)).
    - intros [a b]; cbn.
      refine ( _ @ apD (fun a' => joinpp A B (a',b)) (contr a)^).
      rewrite transport_paths_r, transport_paths_FlFr; cbn.
      rewrite ap_V, inv_V, concat_pp_p.
      rewrite ap_const, concat_p1.
      reflexivity.
  Defined.

  (** Join is symmetric *)
  Definition join_sym A B : join A B <~> join B A.
  Proof.  
    unfold join; refine (pushout_sym oE _).
    refine (equiv_pushout (equiv_prod_symm A B) 1 1 _ _);
      intros [a b]; reflexivity.
  Defined.

  (** The join of hprops is an hprop *)
  Global Instance ishprop_join `{Funext} A B `{IsHProp A} `{IsHProp B} : IsHProp (join A B).
  Proof.
    apply hprop_inhabited_contr.
    unfold join.
    refine (pushout_rec _ _ _ (fun _ => path_ishprop _ _)).
    - intros a; apply contr_join.  
      exact (contr_inhabited_hprop A a).
    - intros b; refine (trunc_equiv (join B A) (join_sym B A)).
      apply contr_join.
      exact (contr_inhabited_hprop B b).
  Defined.

  (** And coincides with their disjunction *)
  Definition equiv_join_hor `{Funext} A B `{IsHProp A} `{IsHProp B} 
    : join A B <~> hor A B.
  Proof.
    apply equiv_iff_hprop.
    - refine (pushout_rec _ (fun a => tr (inl a)) (fun b => tr (inr b)) (fun _ => path_ishprop _ _)).
    - apply Trunc_rec, push.
  Defined.

End Join.
