Require Import HoTT.Basics HoTT.Colimits.Pushout.
Require Import Types.Paths.

(** * Pushouts of "dependent spans". *)

Section SpanPushout.
  Context {X Y : Type} (Q : X -> Y -> Type).

  Definition SPushout := @Pushout@{up _ _ up} (sig@{up _} (fun (xy : X * Y) => Q (fst xy) (snd xy))) X Y
                                  (fst o pr1) (snd o pr1).
  Definition spushl : X -> SPushout := pushl.
  Definition spushr : Y -> SPushout := pushr.
  Definition spglue {x:X} {y:Y} : Q x y -> spushl x = spushr y
    := fun q => pglue ((x,y) ; q).

  Definition spushout_rec (R : Type)
             (spushl' : X -> R) (spushr' : Y -> R)
             (spglue' : forall x y (q : Q x y), spushl' x = spushr' y)
    : SPushout -> R.
  Proof.
    srapply (@Pushout_rec {xy:X * Y & Q (fst xy) (snd xy)} X Y
                          (fst o pr1) (snd o pr1) R spushl' spushr').
    intros [[x y] q]; cbn in *.
    apply spglue'; assumption.
  Defined.
  
  Definition spushout_rec_beta_spglue (R : Type)
             (spushl' : X -> R) (spushr' : Y -> R)
             (spglue' : forall x y (q : Q x y), spushl' x = spushr' y)
             (x:X) (y:Y) (q:Q x y)
    : ap (spushout_rec R spushl' spushr' spglue') (spglue q) = spglue' x y q
    := Pushout_rec_beta_pglue _ _ _ _ ((x, y); q).

  Definition spushout_ind (R : SPushout -> Type)
             (spushl' : forall x, R (spushl x))
             (spushr' : forall y, R (spushr y))
             (spglue' : forall x y (q : Q x y), 
                 transport R (spglue q) (spushl' x) = (spushr' y))
    : forall p, R p.
  Proof.
    srapply (@Pushout_ind {xy:X * Y & Q (fst xy) (snd xy)} X Y
                          (fst o pr1) (snd o pr1) R spushl' spushr').
    intros [[x y] q]; cbn in *.
    apply spglue'; assumption.
  Defined.

  Definition spushout_ind_beta_spglue (R : SPushout -> Type)
             (spushl' : forall x, R (spushl x))
             (spushr' : forall y, R (spushr y))
             (spglue' : forall x y (q : Q x y), 
                 transport R (spglue q) (spushl' x) = (spushr' y))
             (x:X) (y:Y) (q:Q x y)
    : apD (spushout_ind R spushl' spushr' spglue') (spglue q) = spglue'  x y q
    := Pushout_ind_beta_pglue _ _ _ _ ((x,y);q).

End SpanPushout.

Definition functor_spushout {X Y Z W : Type}
  {Q : X -> Y -> Type} {Q' : Z -> W -> Type}
  (f : X -> Z) (g : Y -> W) (h : forall x y, Q x y -> Q' (f x) (g y))
  : SPushout Q -> SPushout Q'.
Proof.
  snrapply spushout_rec.
  - exact (fun x => spushl Q' (f x)).
  - exact (fun y => spushr Q' (g y)).
  - intros x y q. apply spglue. exact (h x y q).
Defined.

Definition functor_spushout_compose {X Y X' Y' X'' Y'' : Type}
  {Q : X -> Y -> Type} {Q' : X' -> Y' -> Type} {Q'' : X'' -> Y'' -> Type}
  (f : X -> X') (g : Y -> Y') (f' : X' -> X'') (g' : Y' -> Y'')
  (h : forall x y, Q x y -> Q' (f x) (g y))
  (h' : forall x y, Q' x y -> Q'' (f' x) (g' y))
  : functor_spushout f' g' h' o functor_spushout f g h
    == functor_spushout (f' o f) (g' o g) (fun x y => h' _ _ o h x y).
Proof.
  snrapply spushout_ind.
  1,2: reflexivity.
  intros x y q; cbn beta.
  snrapply transport_paths_FFlFr'.
  apply equiv_p1_1q.
  lhs nrapply ap.
  1: nrapply spushout_rec_beta_spglue.
  lhs nrapply spushout_rec_beta_spglue.
  symmetry.
  nrapply (spushout_rec_beta_spglue Q).
Defined.

Definition functor_spushout_idmap {X Y : Type} {Q : X -> Y -> Type}
  : functor_spushout idmap idmap (fun x y (q : Q x y) => q) == idmap.
Proof.
  snrapply spushout_ind.
  1,2: reflexivity.
  intros x y q; cbn.
  snrapply transport_paths_Flr'.
  apply equiv_p1_1q.
  nrapply spushout_rec_beta_spglue.
Defined.

Definition functor_spushout_homotopic {X Y Z W : Type}
  {Q : X -> Y -> Type} {Q' : Z -> W -> Type}
  {f g : X -> Z} (h : f == g)
  {i j : Y -> W} (k : i == j)
  (l : forall x y, Q x y -> Q' (f x) (i y))
  (m : forall x y, Q x y -> Q' (g x) (j y))
  (H : forall x y q,
    spglue Q' (l x y q) @ ap (spushr Q') (k y)
      = ap (spushl Q') (h x) @ spglue Q' (m x y q))
  : functor_spushout f i l == functor_spushout g j m.
Proof.
  snrapply spushout_ind.
  - intros x; cbn.
    exact (ap (spushl Q') (h x)).
  - intros y; cbn.
    exact (ap (spushr Q') (k y)).
  - intros x y q.
    snrapply transport_paths_FlFr'.
    lhs nrapply whiskerR.
    1: apply spushout_rec_beta_spglue.
    rhs nrapply whiskerL.
    2: apply spushout_rec_beta_spglue.
    apply H.
Defined.
