(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import HoTT.Spaces.No.Core.

Local Open Scope path_scope.
Local Open Scope surreal_scope.

(** * Negation of surreal numbers *)

Definition negate : No -> No.
Proof.
  simple refine (No_rec No (fun x y => y <= x) (fun x y => y < x)
                 _ _ _ _ _); intros.
  - exact {{ fxR | fxL // fun r l => fxcut l r }}.
  - apply path_No; assumption.
  - cbn in *. apply le_lr; intros; [ apply dq | apply dp ].
  - cbn in *. apply lt_r with l; intros; assumption.
  - cbn in *. apply lt_l with r; intros; assumption.
Defined.

(** The following proof verifies that [No_rec] applied to a cut reduces definitionally to a cut with the expected options (although it does produce quite a large term). *)
Goal negate one = minusone.
Proof.
  apply path_No; apply le_lr; intros.
  (** Since [le_lr] only proves inequality of cuts, this would not work if [negate] didn't compute to a cut when applied to a cut. *)
  - elim l.
  - apply lt_r with r.
    apply le_lr; apply Empty_ind.
  - elim l.
  - apply lt_r with r.
    apply le_lr; apply Empty_ind.
Qed.
