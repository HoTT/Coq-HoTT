Require Import HoTT.Basics HoTT.Types HoTT.HIT.Pushout.

(** * Pushouts of "dependent spans". *)

Section SpanPushout.
  Context {X Y : Type} (Q : X -> Y -> Type).

  Definition spushout := @pushout {xy:X * Y & Q (fst xy) (snd xy)} X Y
                                  (fst o pr1) (snd o pr1).
  Definition spushl : X -> spushout := pushl.
  Definition spushr : Y -> spushout := pushr.
  Definition sglue {x:X} {y:Y} : Q x y -> spushl x = spushr y
    := fun q => pp ((x,y) ; q).

  Definition spushout_rec (R : Type)
             (spushl' : X -> R) (spushr' : Y -> R)
             (sglue' : forall x y (q : Q x y), spushl' x = spushr' y)
    : spushout -> R.
  Proof.
    srapply (@pushout_rec {xy:X * Y & Q (fst xy) (snd xy)} X Y
                          (fst o pr1) (snd o pr1) R spushl' spushr').
    intros [[x y] q]; cbn in *.
    apply sglue'; assumption.
  Defined.

  Definition spushout_ind (R : spushout -> Type)
             (spushl' : forall x, R (spushl x))
             (spushr' : forall y, R (spushr y))
             (sglue' : forall x y (q : Q x y), 
                 transport R (sglue q) (spushl' x) = (spushr' y))
    : forall p, R p.
  Proof.
    srapply (@pushout_ind {xy:X * Y & Q (fst xy) (snd xy)} X Y
                          (fst o pr1) (snd o pr1) R spushl' spushr').
    intros [[x y] q]; cbn in *.
    apply sglue'; assumption.
  Defined.

  Definition spushout_ind_beta_sglue (R : spushout -> Type)
             (spushl' : forall x, R (spushl x))
             (spushr' : forall y, R (spushr y))
             (sglue' : forall x y (q : Q x y), 
                 transport R (sglue q) (spushl' x) = (spushr' y))
             (x:X) (y:Y) (q:Q x y)
    : apD (spushout_ind R spushl' spushr' sglue') (sglue q) = sglue'  x y q
    := pushout_ind_beta_pp _ _ _ _ ((x,y);q).

End SpanPushout.
