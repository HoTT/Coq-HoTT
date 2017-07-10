(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import HoTT.Spaces.No.Core.

Local Open Scope path_scope.
Local Open Scope surreal_scope.

(** * Negation of surreal numbers *)

(** Negation requires the option sorts to be symmetric. *)
Class HasNegation (S : OptionSort) 
  := symmetric_options : forall L R, InSort S L R -> InSort S R L.
Existing Instance symmetric_options.

Global Instance hasnegation_maxsort : HasNegation MaxSort
  := fun _ _ _ => tt.

Global Instance hasnegation_decsort : HasNegation DecSort.
Proof.
  intros L R [? ?]; split; assumption.
Qed.

Section HasNegation.
  Context {S : OptionSort} `{HasNegation S}.
  Let No := GenNo S.

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
  Context `{InSort S Empty Empty} `{InSort S Unit Empty}.
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

  (** More useful is the following rewriting lemma. *)
  Definition negate_cut
             {L R : Type@{i} } {Sx : InSort@{i} S L R}
             (xL : L -> No@{i}) (xR : R -> No@{i})
             (xcut : forall (l : L) (r : R), xL l < xR r)
    : { nxcut : forall r l, negate (xR r) < negate (xL l) &
        negate {{ xL | xR // xcut }} =
        {{ (fun r => negate (xR r)) | (fun l => negate (xL l)) // nxcut }} }.
  Proof.
    eexists.
    reflexivity.
  Defined.

End HasNegation.
