Require Import Basics.
Require Import Pointed.Core.
Require Import Types.
Require Import Colimits.Pushout.
Require Import Cubical.

Local Open Scope pointed_scope.
Local Open Scope dpath_scope.

(* Definition of smash product *)

Definition sum_to_prod (X Y : pType) : X + Y -> X * Y
  := sum_ind _ (fun x => (x, point Y)) (fun y => (point X, y)).

Definition sum_to_bool X Y : X + Y -> Bool
  := sum_ind _ (fun _ => false) (fun _ => true).

Definition Smash (X Y : pType) : pType
  := [Pushout (sum_to_prod X Y) (sum_to_bool X Y), pushl (point X, point Y)].

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
