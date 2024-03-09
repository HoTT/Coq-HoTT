Require Import Basics.
Require Import Pointed.Core.
Require Import Types.
Require Import Colimits.Pushout.
Require Import Cubical.DPath.
Require Import WildCat.Core WildCat.Bifunctor.

Local Open Scope pointed_scope.
Local Open Scope dpath_scope.

(* Definition of smash product *)

Definition sum_to_prod (X Y : pType) : X + Y -> X * Y
  := sum_ind _ (fun x => (x, point Y)) (fun y => (point X, y)).

Definition sum_to_bool X Y : X + Y -> Bool
  := sum_ind _ (fun _ => false) (fun _ => true).

Definition Smash@{u v w | u <= w, v <= w} (X : pType@{u}) (Y : pType@{v}) : pType@{w}
  := [Pushout@{w w w w} (sum_to_prod@{w w w} X Y) (sum_to_bool@{u v w} X Y), pushl (point X, point Y)].

Section Smash.

  Context {X Y : pType}.

  Definition sm (x : X) (y : Y) : Smash X Y := pushl (x, y).

  Definition auxl : Smash X Y := pushr false.

  Definition auxr : Smash X Y := pushr true.

  Definition gluel (x : X) : sm x pt = auxl
    := pglue (f:=sum_to_prod X Y) (g:=sum_to_bool X Y) (inl x).

  Definition gluer (y : Y) : sm pt y = auxr
    := pglue (f:=sum_to_prod X Y) (g:=sum_to_bool X Y) (inr y).

  Definition gluel' (x x' : X) : sm x pt = sm x' pt
    := gluel x @ (gluel x')^.

  Definition gluer' (y y' : Y) : sm pt y = sm pt y'
    := gluer y @ (gluer y')^.

  Definition glue (x : X) (y : Y) : sm x pt = sm pt y
    := gluel' x pt @ gluer' pt y.

  Definition glue_pt_left (y : Y) : glue pt y = gluer' pt y.
  Proof.
    refine (_ @ concat_1p _).
    apply whiskerR, concat_pV.
  Defined.

  Definition glue_pt_right (x : X) : glue x pt = gluel' x pt.
  Proof.
    refine (_ @ concat_p1 _).
    apply whiskerL, concat_pV.
  Defined.

  Definition ap_sm_left {x x' : X} (p : x = x')
    : ap (fun t => sm t pt) p = gluel' x x'.
  Proof.
    destruct p.
    symmetry.
    apply concat_pV.
  Defined.

  Definition ap_sm_right {y y' : Y} (p : y = y')
    : ap (sm pt) p = gluer' y y'.
  Proof.
    destruct p.
    symmetry.
    apply concat_pV.
  Defined.

  Definition Smash_ind {P : Smash X Y -> Type}
    (Psm : forall a b, P (sm a b)) (Pl : P auxl) (Pr : P auxr)
    (Pgl : forall a, DPath P (gluel a) (Psm a pt) Pl)
    (Pgr : forall b, DPath P (gluer b) (Psm pt b) Pr)
    : forall x : Smash X Y, P x.
  Proof.
    srapply Pushout_ind.
    + intros [a b].
      apply Psm.
    + apply (Bool_ind _ Pr Pl).
    + srapply sum_ind.
      - apply Pgl.
      - apply Pgr.
  Defined.

  Definition Smash_ind_beta_gluel {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, DPath P (gluel a) (Psm a pt) Pl)
    (Pgr : forall b, DPath P (gluer b) (Psm pt b) Pr) (a : X)
    : apD (Smash_ind Psm Pl Pr Pgl Pgr) (gluel a) = Pgl a
    := Pushout_ind_beta_pglue P _ _ _ (inl a).

  Definition Smash_ind_beta_gluer {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, DPath P (gluel a) (Psm a pt) Pl)
    (Pgr : forall b, DPath P (gluer b) (Psm pt b) Pr) (b : Y)
    : apD (Smash_ind Psm Pl Pr Pgl Pgr) (gluer b) = Pgr b
    := Pushout_ind_beta_pglue P _ _ _ (inr b).

  Definition Smash_ind_beta_gluel' {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, DPath P (gluel a) (Psm a pt) Pl)
    (Pgr : forall b, DPath P (gluer b) (Psm pt b) Pr) (a b : X)
    : apD (Smash_ind Psm Pl Pr Pgl Pgr) (gluel' a b)
    = (Pgl a) @Dp ((Pgl b)^D).
  Proof.
    lhs nrapply dp_apD_pp.
    apply ap011.
    1: apply Smash_ind_beta_gluel.
    lhs nrapply dp_apD_V.
    apply ap.
    apply Smash_ind_beta_gluel.
  Defined.

  Definition Smash_ind_beta_gluer' {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, DPath P (gluel a) (Psm a pt) Pl)
    (Pgr : forall b, DPath P (gluer b) (Psm pt b) Pr) (a b : Y)
    : apD (Smash_ind Psm Pl Pr Pgl Pgr) (gluer' a b)
    = (Pgr a) @Dp ((Pgr b)^D).
  Proof.
    lhs nrapply dp_apD_pp.
    apply ap011.
    1: apply Smash_ind_beta_gluer.
    lhs nrapply dp_apD_V.
    apply ap.
    apply Smash_ind_beta_gluer.
  Defined.

  Definition Smash_ind_beta_glue {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, DPath P (gluel a) (Psm a pt) Pl)
    (Pgr : forall b, DPath P (gluer b) (Psm pt b) Pr) (a : X) (b : Y)
    : apD (Smash_ind Psm Pl Pr Pgl Pgr) (glue a b)
    = ((Pgl a) @Dp ((Pgl pt)^D)) @Dp ((Pgr pt) @Dp ((Pgr b)^D)).
  Proof.
    lhs nrapply dp_apD_pp.
    apply ap011.
    - apply Smash_ind_beta_gluel'.
    - apply Smash_ind_beta_gluer'.
  Defined.

  Definition Smash_rec {P : Type} (Psm : X -> Y -> P) (Pl Pr : P)
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr)
    : Smash X Y -> P
    := Smash_ind Psm Pl Pr (fun x => dp_const (Pgl x)) (fun x => dp_const (Pgr x)).

  Local Open Scope path_scope.

  (* Version of smash_rec that forces (Pgl pt) and (Pgr pt) to be idpath *)
  Definition Smash_rec' {P : Type} {Psm : X -> Y -> P}
    (Pgl : forall a, Psm a pt = Psm pt pt) (Pgr : forall b, Psm pt b = Psm pt pt)
    (ql : Pgl pt = 1) (qr : Pgr pt = 1)
    : Smash X Y -> P
    := Smash_rec Psm (Psm pt pt) (Psm pt pt) Pgl Pgr.

  Definition Smash_rec_beta_gluel {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a : X)
    : ap (Smash_rec Psm Pl Pr Pgl Pgr) (gluel a) = Pgl a.
  Proof.
    rhs_V nrapply (eissect dp_const).
    apply moveL_equiv_V.
    lhs_V nrapply dp_apD_const.
    nrapply Smash_ind_beta_gluel.
  Defined.

  Definition Smash_rec_beta_gluer {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (b : Y)
    : ap (Smash_rec Psm Pl Pr Pgl Pgr) (gluer b) = Pgr b.
  Proof.
    rhs_V nrapply (eissect dp_const).
    apply moveL_equiv_V.
    lhs_V nrapply dp_apD_const.
    nrapply Smash_ind_beta_gluer.
  Defined.

  Definition Smash_rec_beta_gluel' {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a b : X)
    : ap (Smash_rec Psm Pl Pr Pgl Pgr) (gluel' a b) = Pgl a @ (Pgl b)^.
  Proof.
    lhs nrapply ap_pp.
    f_ap.
    1: apply Smash_rec_beta_gluel.
    lhs nrapply ap_V.
    apply inverse2.
    apply Smash_rec_beta_gluel.
  Defined. 

  Definition Smash_rec_beta_gluer' {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a b : Y)
    : ap (Smash_rec Psm Pl Pr Pgl Pgr) (gluer' a b) = Pgr a @ (Pgr b)^.
  Proof.
    lhs nrapply ap_pp.
    f_ap.
    1: apply Smash_rec_beta_gluer.
    lhs nrapply ap_V.
    apply inverse2.
    apply Smash_rec_beta_gluer.
  Defined.

  Definition Smash_rec_beta_glue {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a : X)
    (b : Y) : ap (Smash_rec Psm Pl Pr Pgl Pgr) (glue a b)
    = ((Pgl a) @ (Pgl pt)^) @ (Pgr pt @ (Pgr b)^).
  Proof.
    lhs nrapply ap_pp.
    f_ap.
    - apply Smash_rec_beta_gluel'.
    - apply Smash_rec_beta_gluer'.
  Defined.

End Smash.

Arguments sm : simpl never.
Arguments auxl : simpl never.
Arguments gluel : simpl never.
Arguments gluer : simpl never.

Definition functor_smash {A B X Y : pType} (f : A $-> X) (g : B $-> Y)
  : Smash A B $-> Smash X Y.
Proof.
  srapply Build_pMap.
  - snrapply (Smash_rec (fun a b => sm (f a) (g b)) auxl auxr).
    + intro b.
      rhs_V nrapply (gluel (f b)).
      exact (ap011 _ 1 (point_eq g)).
    + intro a.
      simpl.
      rhs_V nrapply (gluer (g a)).
      exact (ap011 _ (point_eq f) 1).
  - exact (ap011 _ (point_eq f) (point_eq g)).
Defined.

Definition functor_smash_idmap (X Y : pType)
  : functor_smash (@pmap_idmap X) (@pmap_idmap Y) $== pmap_idmap.
Proof.
  snrapply Build_pHomotopy.
  { snrapply Smash_ind.
    1-3: reflexivity.
    - intros x.
      nrapply transport_paths_FlFr'.
      apply equiv_p1_1q.
      rhs nrapply ap_idmap.
      lhs nrapply Smash_rec_beta_gluel.
      apply concat_1p.
    - intros y.
      nrapply transport_paths_FlFr'.
      apply equiv_p1_1q.
      rhs nrapply ap_idmap.
      lhs nrapply Smash_rec_beta_gluer.
      apply concat_1p. }
  reflexivity.
Defined.

Definition functor_smash_compose {X Y A B C D : pType}
  (f : X $-> A) (g : Y $-> B) (h : A $-> C) (k : B $-> D)
  : functor_smash (h $o f) (k $o g) $== functor_smash h k $o functor_smash f g.
Proof.
  snrapply Build_pHomotopy.
  { snrapply Smash_ind.
    1-3: reflexivity.
    - intros x.
      nrapply transport_paths_FlFr'.
      apply equiv_p1_1q.
      lhs nrapply Smash_rec_beta_gluel.
      rhs nrapply (ap_compose (functor_smash f g) _ (gluel x)).
      rhs nrapply ap.
      2: apply Smash_rec_beta_gluel.
      rhs nrapply ap_pp.
      rhs nrapply whiskerL.
      2: apply Smash_rec_beta_gluel.
      rhs nrapply concat_p_pp.
      apply whiskerR.
      rhs_V nrapply whiskerR.
      2: nrapply (ap_compose (sm _) _ (point_eq g)).
      lhs nrapply (ap011_pp sm 1 1).
      apply whiskerR.
      symmetry.
      rapply ap_compose.
    - intros y.
      nrapply transport_paths_FlFr'.
      apply equiv_p1_1q.
      lhs nrapply Smash_rec_beta_gluer.
      rhs nrapply (ap_compose (functor_smash f g) _ (gluer y)).
      rhs nrapply ap.
      2: apply Smash_rec_beta_gluer.
      rhs nrapply ap_pp.
      rhs nrapply whiskerL.
      2: apply Smash_rec_beta_gluer.
      rhs nrapply concat_p_pp.
      apply whiskerR.
      unfold point_eq, dpoint_eq.
      lhs nrapply (ap011_pp sm _ _ 1 1).
      apply whiskerR.
      rhs_V nrapply (ap011_compose sm (functor_smash h k) (dpoint_eq f) 1).
      symmetry.
      nrapply (ap011_compose' sm h). }
  simpl; pelim f g.
  by simpl; pelim h k.
Defined.

Definition functor_smash_homotopic {X Y A B : pType}
  {f h : X $-> A} {g k : Y $-> B}
  (p : f $== h) (q : g $== k)
  : functor_smash f g $== functor_smash h k.
Proof.
  snrapply Build_pHomotopy.
  { snrapply Smash_ind.
    - intros x y.
       exact (ap011 _ (p x) (q y)).
    - reflexivity.
    - reflexivity.
    - intros x.
      nrapply transport_paths_FlFr'.
      lhs nrapply concat_p1.
      lhs nrapply Smash_rec_beta_gluel.
      rhs nrapply whiskerL.
      2: nrapply Smash_rec_beta_gluel.
      rhs nrapply concat_p_pp.
      apply moveL_pM.
      lhs nrapply concat_pp_p.
      rhs_V nrapply (ap011_pp sm).
      rhs nrapply ap022.
      2: apply moveR_pM, (dpoint_eq q).
      2: apply concat_p1.
      apply moveR_Mp.
      rhs_V nrapply whiskerR.
      2: apply ap011_V.
      rhs_V nrapply ap011_pp.
      rhs nrapply ap011.
      2: apply concat_Vp.
      2: apply concat_1p.
      symmetry.
      lhs nrapply ap011_is_ap.
      lhs nrapply concat_p1.
      nrapply ap_sm_left.
    - intros y.
      nrapply transport_paths_FlFr'.
      lhs nrapply concat_p1.
      lhs nrapply Smash_rec_beta_gluer.
      rhs nrapply whiskerL.
      2: nrapply Smash_rec_beta_gluer.
      rhs nrapply concat_p_pp.
      apply moveL_pM.
      lhs nrapply concat_pp_p.
      rhs_V nrapply (ap011_pp sm).
      rhs nrapply ap022.
      3: apply moveR_pM, (dpoint_eq p).
      2: apply concat_p1.
      apply moveR_Mp.
      rhs_V nrapply whiskerR.
      2: apply ap011_V.
      rhs_V nrapply ap011_pp.
      rhs nrapply ap011.
      2: apply concat_1p.
      2: apply concat_Vp.
      symmetry.
      nrapply ap_sm_right. }
  simpl.
  by pelim p q f g h k.
Defined.

Global Instance is0bifunctor_smash : IsBifunctor Smash.
Proof.
  snrapply Build_IsBifunctor.
  - intros X.
    snrapply Build_Is0Functor.
    intros Y B g.
    exact (functor_smash (Id _) g).
  - intros Y.
    snrapply Build_Is0Functor.
    intros X A f.
    exact (functor_smash f (Id _)).
  - intros X A f Y B g.
    snrapply Build_pHomotopy.
    + snrapply Smash_ind.
      1-3: reflexivity.
      * intros x.
        nrapply transport_paths_FlFr'.
        apply equiv_p1_1q.
        lhs rapply (ap_compose (functor_smash f (Id _)) (functor_smash (Id _) g) (gluel x)).
        rhs rapply (ap_compose (functor_smash (Id _) g) (functor_smash f (Id _)) (gluel x)).
        lhs nrapply ap.
        1: apply Smash_rec_beta_gluel.
        rhs nrapply ap.
        2: apply Smash_rec_beta_gluel.
        lhs nrapply ap.
        1: apply concat_1p.
        lhs nrapply Smash_rec_beta_gluel.
        rhs nrapply (ap_pp _ _ (gluel x)).
        rhs nrapply whiskerL.
        2: apply Smash_rec_beta_gluel.
        f_ap.
        2: symmetry; apply concat_1p.
        exact (ap_compose (sm x) (functor_smash f (Id _)) (point_eq g)).
      * intros y.
        nrapply transport_paths_FlFr'.
        apply equiv_p1_1q.
        lhs rapply (ap_compose (functor_smash _ _) (functor_smash _ _) (gluer y)).
        rhs rapply (ap_compose (functor_smash (Id _) g) (functor_smash f (Id _)) (gluer y)).
        lhs nrapply ap.
        1: apply Smash_rec_beta_gluer.
        rhs nrapply ap.
        2: apply Smash_rec_beta_gluer.
        rhs nrapply ap.
        2: apply concat_1p.
        rhs nrapply Smash_rec_beta_gluer.
        lhs nrapply (ap_pp _ _ (gluer y)).
        lhs nrapply whiskerL.
        1: apply Smash_rec_beta_gluer.
        f_ap.
        2: apply concat_1p.
        exact (ap_compose (fun x => sm x y)  (functor_smash (Id _) g) (point_eq f))^.
    + apply moveL_pV.
      lhs nrapply concat_1p.
      simpl.
      cbn in f, g.
      lhs nrapply whiskerR.
      1: rapply (ap_compose (fun x => sm pt x) _ (point_eq g))^.
      rhs nrapply whiskerR.
      2: rapply (ap_compose (fun x => sm x pt) _ (point_eq f))^.
      simpl.
      by pelim f g.
Defined.

Global Instance is1bifunctor_smash : Is1Bifunctor Smash.
Proof.
  snrapply Build_Is1Bifunctor.
  - intros X.
    snrapply Build_Is1Functor.
    + intros Y B f' g' q.
      rapply (functor_smash_homotopic (Id _) q).
    + intros Y; cbn.
      rapply functor_smash_idmap.
    + intros Y A C f g.
      exact (functor_smash_compose (Id _) f (Id _) g).
  - intros Y.
    snrapply Build_Is1Functor.
    + intros X A f g q.
      rapply (functor_smash_homotopic q (Id _)).
    + intros X; cbn.
      rapply functor_smash_idmap.
    + intros X A C f g.
      exact (functor_smash_compose f (Id _) g (Id _)).
Defined.
