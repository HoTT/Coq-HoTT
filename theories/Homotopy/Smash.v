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
  := Build_pType (Pushout (sum_to_prod X Y) (sum_to_bool X Y))
      (pushl (point X, point Y)).

Section Smash.

  Context {X Y : pType}.

  Definition sm (x : X) (y : Y) : Smash X Y := pushl (x, y).

  Definition auxl : Smash X Y := pushr false.

  Definition auxr : Smash X Y := pushr true.

  Notation pt := (point _).

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
    serapply Pushout_ind.
    + intros [a b].
      apply Psm.
    + apply (Bool_ind _ Pr Pl).
    + serapply sum_ind; intro; apply dp_path_transport^-1.
      - apply Pgl.
      - apply Pgr.
  Defined.

  Definition Smash_ind_beta_gluel {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, DPath P (gluel a) (Psm a pt) Pl)
    (Pgr : forall b, DPath P (gluer b) (Psm pt b) Pr) (a : X)
    : dp_apD (Smash_ind Psm Pl Pr Pgl Pgr) (gluel a) = Pgl a.
  Proof.
    apply dp_apD_path_transport.
    refine (Pushout_ind_beta_pglue P _ _ _ (inl a) @ _).
    unfold sum_ind.
    by apply ap.
  Qed.

  Definition Smash_ind_beta_gluer {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, DPath P (gluel a) (Psm a pt) Pl)
    (Pgr : forall b, DPath P (gluer b) (Psm pt b) Pr) (b : Y)
    : dp_apD (Smash_ind Psm Pl Pr Pgl Pgr) (gluer b) = Pgr b.
  Proof.
    apply dp_apD_path_transport.
    refine (Pushout_ind_beta_pglue P _ _ _ (inr b) @ _).
    unfold sum_ind.
    by apply ap.
  Qed.

  Definition Smash_ind_beta_gluel' {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, DPath P (gluel a) (Psm a pt) Pl)
    (Pgr : forall b, DPath P (gluer b) (Psm pt b) Pr) (a b : X)
    : dp_apD (Smash_ind Psm Pl Pr Pgl Pgr) (gluel' a b)
    = (Pgl a) @D ((Pgl b)^D).
  Proof.
    unfold gluel'.
    rewrite dp_apD_pp, dp_apD_V.
    by rewrite 2 Smash_ind_beta_gluel.
  Qed.

  Definition Smash_ind_beta_gluer' {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, DPath P (gluel a) (Psm a pt) Pl)
    (Pgr : forall b, DPath P (gluer b) (Psm pt b) Pr) (a b : Y)
    : dp_apD (Smash_ind Psm Pl Pr Pgl Pgr) (gluer' a b)
    = (Pgr a) @D ((Pgr b)^D).
  Proof.
    unfold gluer'.
    rewrite dp_apD_pp, dp_apD_V.
    by rewrite 2 Smash_ind_beta_gluer.
  Qed.

  Definition Smash_ind_beta_glue {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, DPath P (gluel a) (Psm a pt) Pl)
    (Pgr : forall b, DPath P (gluer b) (Psm pt b) Pr) (a : X) (b : Y)
    : dp_apD (Smash_ind Psm Pl Pr Pgl Pgr) (glue a b)
    = ((Pgl a) @D ((Pgl pt)^D)) @D ((Pgr pt) @D ((Pgr b)^D)).
  Proof.
    by rewrite dp_apD_pp, Smash_ind_beta_gluel', Smash_ind_beta_gluer'.
  Qed.

  Definition Smash_rec {P : Type} (Psm : X -> Y -> P) (Pl Pr : P)
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr)
    : Smash X Y -> P := Smash_ind Psm Pl Pr
      (fun x => dp_const (Pgl x)) (fun x => dp_const (Pgr x)).

  Local Open Scope path_scope.

  (* Version of smash_rec that forces (Pgl pt) and (Pgr pt) to be idpath *)
  Definition Smash_rec' {P : Type} {Psm : X -> Y -> P}
    (Pgl : forall a, Psm a pt = Psm pt pt) (Pgr : forall b, Psm pt b = Psm pt pt)
    (ql : Pgl pt = 1) (qr : Pgr pt = 1)
    : Smash X Y -> P := Smash_rec Psm (Psm pt pt) (Psm pt pt) Pgl Pgr.

  Definition Smash_rec_beta_gluel {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a : X)
    : ap (Smash_rec Psm Pl Pr Pgl Pgr) (gluel a) = Pgl a.
  Proof.
    refine (_ @ eissect dp_const (Pgl a)).
    apply moveL_equiv_V.
    unfold Smash_rec.
    refine ((dp_apD_const (Smash_ind Psm Pl Pr (fun x : X => dp_const (Pgl x))
      (fun x : Y => dp_const (Pgr x))) (gluel a))^ @ _).
    erapply Smash_ind_beta_gluel.
  Qed.

  Definition smash_rec_beta_gluer {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (b : Y)
    : ap (Smash_rec Psm Pl Pr Pgl Pgr) (gluer b) = Pgr b.
  Proof.
    refine (_ @ eissect dp_const (Pgr b)).
    apply moveL_equiv_V.
    unfold Smash_rec.
    refine ((dp_apD_const (Smash_ind Psm Pl Pr (fun x : X => dp_const (Pgl x))
      (fun x : Y => dp_const (Pgr x))) (gluer b))^ @ _).
    erapply Smash_ind_beta_gluer.
  Qed.

  Definition Smash_rec_beta_gluel' {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a b : X)
    : ap (Smash_rec Psm Pl Pr Pgl Pgr) (gluel' a b) = Pgl a @ (Pgl b)^.
  Proof.
    rewrite ap_pp, ap_V.
    by rewrite 2 Smash_rec_beta_gluel.
  Qed.

  Definition Smash_rec_beta_gluer' {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a b : Y)
    : ap (Smash_rec Psm Pl Pr Pgl Pgr) (gluer' a b) = Pgr a @ (Pgr b)^.
  Proof.
    rewrite ap_pp, ap_V.
    by rewrite 2 smash_rec_beta_gluer.
  Qed.

  Definition smash_rec_beta_glue {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a : X)
    (b : Y) : ap (Smash_rec Psm Pl Pr Pgl Pgr) (glue a b)
    = ((Pgl a) @ (Pgl pt)^) @ (Pgr pt @ (Pgr b)^).
  Proof.
    by rewrite ap_pp, Smash_rec_beta_gluel', Smash_rec_beta_gluer'.
  Defined.

  Arguments sm : simpl never.
  Arguments auxl : simpl never.
  Arguments gluel : simpl never.
  Arguments gluer : simpl never.

End Smash.
