Require Import HoTT.Basics HoTT.Types HoTT.Colimits.Pushout.

(** * Pushouts of "dependent spans". *)

Section SpanPushout.
  Context {X Y : Type} (Q : X -> Y -> Type).

  Definition SPushout := @Pushout {xy:X * Y & Q (fst xy) (snd xy)} X Y
                                  (fst o pr1) (snd o pr1).
  Definition spushl : X -> SPushout := pushl.
  Definition spushr : Y -> SPushout := pushr.
  Definition spglue {x:X} {y:Y} : Q x y -> spushl x = spushr y
    := fun q => pglue ((x,y) ; q).

  Definition SPushout_rec (R : Type)
             (spushl' : X -> R) (spushr' : Y -> R)
             (sglue' : forall x y (q : Q x y), spushl' x = spushr' y)
    : SPushout -> R.
  Proof.
    srapply (@Pushout_rec {xy:X * Y & Q (fst xy) (snd xy)} X Y
                          (fst o pr1) (snd o pr1) R spushl' spushr').
    intros [[x y] q]; cbn in *.
    apply sglue'; assumption.
  Defined.

  Definition SPushout_ind (R : SPushout -> Type)
             (spushl' : forall x, R (spushl x))
             (spushr' : forall y, R (spushr y))
             (sglue' : forall x y (q : Q x y), 
                 transport R (spglue q) (spushl' x) = (spushr' y))
    : forall p, R p.
  Proof.
    srapply (@Pushout_ind {xy:X * Y & Q (fst xy) (snd xy)} X Y
                          (fst o pr1) (snd o pr1) R spushl' spushr').
    intros [[x y] q]; cbn in *.
    apply sglue'; assumption.
  Defined.

  Definition spushout_ind_beta_sglue (R : SPushout -> Type)
             (spushl' : forall x, R (spushl x))
             (spushr' : forall y, R (spushr y))
             (spglue' : forall x y (q : Q x y), 
                 transport R (spglue q) (spushl' x) = (spushr' y))
             (x:X) (y:Y) (q:Q x y)
    : apD (SPushout_ind R spushl' spushr' spglue') (spglue q) = spglue'  x y q
    := Pushout_ind_beta_pglue _ _ _ _ ((x,y);q).

End SpanPushout.
