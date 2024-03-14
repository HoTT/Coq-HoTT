Require Import Basics.Overture Basics.PathGroupoids Basics.Tactics Basics.Equivalences.
Require Import Types.Sum Types.Bool Types.Paths Types.Forall.
Require Import WildCat.Core WildCat.Bifunctor WildCat.Equiv.
Require Import Colimits.Pushout.
Require Import Cubical.DPath.
Require Import Pointed.Core.

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

(** ** Functoriality of the smash product *)

Definition functor_smash {A B X Y : pType} (f : A $-> X) (g : B $-> Y)
  : Smash A B $-> Smash X Y.
Proof.
  srapply Build_pMap.
  - snrapply (Smash_rec (fun a b => sm (f a) (g b)) auxl auxr).
    + intro a; cbn beta.
      rhs_V nrapply (gluel (f a)).
      exact (ap011 _ 1 (point_eq g)).
    + intro b; cbn beta.
      rhs_V nrapply (gluer (g b)).
      exact (ap011 _ (point_eq f) 1).
  - simpl.
    exact (ap011 _ (point_eq f) (point_eq g)).
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
  pointed_reduce.
  snrapply Build_pHomotopy.
  { snrapply Smash_ind.
    1-3: reflexivity.
    - cbn beta.
      intros x.
      nrapply transport_paths_FlFr'.
      apply equiv_p1_1q.
      lhs nrapply Smash_rec_beta_gluel.
      symmetry.
      lhs nrapply (ap_compose (functor_smash _ _) _ (gluel x)).
      lhs nrapply ap.
      2: nrapply Smash_rec_beta_gluel.
      lhs nrapply Smash_rec_beta_gluel.
      apply concat_1p.
    - cbn beta.
      intros y.
      nrapply transport_paths_FlFr'.
      apply equiv_p1_1q.
      lhs nrapply Smash_rec_beta_gluer.
      symmetry.
      lhs nrapply (ap_compose (functor_smash _ _) _ (gluer y)).
      lhs nrapply ap.
      2: nrapply Smash_rec_beta_gluer.
      lhs nrapply Smash_rec_beta_gluer.
      apply concat_1p. }
  reflexivity.
Defined.

Definition functor_smash_homotopic {X Y A B : pType}
  {f h : X $-> A} {g k : Y $-> B}
  (p : f $== h) (q : g $== k)
  : functor_smash f g $== functor_smash h k.
Proof.
  pointed_reduce.
  snrapply Build_pHomotopy.
  { snrapply Smash_ind.
    - intros x y; simpl.
      exact (ap011 _ (p x) (q y)).
    - reflexivity.
    - reflexivity.
    - intros x.
      nrapply transport_paths_FlFr'; simpl.
      lhs nrapply concat_p1.
      lhs nrapply Smash_rec_beta_gluel.
      rhs nrapply whiskerL.
      2: nrapply Smash_rec_beta_gluel.
      induction (p x); simpl.
      rhs_V nrapply concat_pp_p.
      apply whiskerR.
      nrapply ap_pp.
    - intros y.
      nrapply transport_paths_FlFr'; simpl.
      lhs nrapply concat_p1.
      lhs nrapply Smash_rec_beta_gluer.
      rhs nrapply whiskerL.
      2: nrapply Smash_rec_beta_gluer.
      induction (q y); simpl.
      rhs_V nrapply concat_pp_p.
      apply whiskerR.
      nrapply (ap011_pp _ _ _ 1 1). }
  symmetry; simpl.
  lhs nrapply concat_p1.
  apply ap022; apply concat_p1.
Defined.

Global Instance is0bifunctor_smash : Is0Bifunctor Smash.
Proof.
  rapply Build_Is0Bifunctor'.
  nrapply Build_Is0Functor.
  intros [X Y] [A B] [f g].
  exact (functor_smash f g).
Defined.

Global Instance is1bifunctor_smash : Is1Bifunctor Smash.
Proof.
  snrapply Build_Is1Bifunctor'.
  snrapply Build_Is1Functor.
  - intros [X Y] [A B] [f g] [h i] [p q].
    exact (functor_smash_homotopic p q).
  - intros [X Y].
    exact (functor_smash_idmap X Y).
  - intros [X Y] [A B] [C D] [f g] [h i].
    exact (functor_smash_compose f g h i).
Defined.

(** ** Symmetry of the smash product *)

Definition pswap (X Y : pType) : Smash X Y $-> Smash Y X
  := Build_pMap _ _ (Smash_rec (flip sm) auxr auxl gluer gluel) 1.

Definition pswap_pswap {X Y : pType}
  : pswap X Y $o pswap Y X $== pmap_idmap.
Proof.
  snrapply Build_pHomotopy.
  - snrapply Smash_ind.
    1-3: reflexivity.
    + intros y.
      rapply (transport_paths_FFlr' (f := pswap _ _)).
      apply equiv_p1_1q.
      lhs nrapply ap.
      1: apply Smash_rec_beta_gluel.
      apply Smash_rec_beta_gluer.
    + intros x.
      rapply (transport_paths_FFlr' (f := pswap _ _)).
      apply equiv_p1_1q.
      lhs nrapply ap.
      1: apply Smash_rec_beta_gluer.
      apply Smash_rec_beta_gluel.
  - reflexivity.
Defined.

Definition pequiv_pswap {X Y : pType} : Smash X Y $<~> Smash Y X.
Proof.
  snrapply cate_adjointify.
  1,2: exact (pswap _ _).
  1,2: exact pswap_pswap.
Defined.

Definition pswap_natural {A B X Y : pType} (f : A $-> X) (g : B $-> Y)
  : pswap X Y $o functor_smash f g $== functor_smash g f $o pswap A B.
Proof.
  snrapply Build_pHomotopy.
  - snrapply Smash_ind.
    1-3: reflexivity.
    + intros a.
      nrapply transport_paths_FlFr'.
      apply equiv_p1_1q.
      rhs nrapply (ap_compose (pswap A B) _ (gluel a)).
      rhs nrapply ap.
      2: apply Smash_rec_beta_gluel.
      rhs nrapply Smash_rec_beta_gluer.
      lhs nrapply (ap_compose (functor_smash f g) (pswap X Y) (gluel a)).
      lhs nrapply ap.
      1: apply Smash_rec_beta_gluel.
      lhs nrapply (ap_pp (pswap X Y) (ap011 sm 1 (point_eq g)) (gluel (f a))).
      lhs nrapply whiskerL.
      1: apply Smash_rec_beta_gluel.
      apply whiskerR.
      symmetry.
      exact (ap_compose _ _ _).
    + intros b.
      nrapply transport_paths_FlFr'.
      apply equiv_p1_1q.
      rhs nrapply (ap_compose (pswap A B) _ (gluer b)).
      rhs nrapply ap.
      2: apply Smash_rec_beta_gluer.
      rhs nrapply Smash_rec_beta_gluel.
      lhs nrapply (ap_compose (functor_smash f g) (pswap X Y) (gluer b)).
      lhs nrapply ap.
      1: apply Smash_rec_beta_gluer.
      lhs nrapply (ap_pp (pswap X Y) (ap011 sm (point_eq f) 1) (gluer (g b))).
      lhs nrapply whiskerL.
      1: apply Smash_rec_beta_gluer.
      apply whiskerR.
      symmetry.
      exact (ap011_compose _ _ (point_eq f) 1).
  - by simpl; pelim f g.
Defined.
