Require Import Basics.
Require Import Pointed.
Require Import Types.
Require Import HIT.Pushout.

Local Open Scope pointed_scope.

(* Definition of smash product *)

Definition sum_to_prod (X Y : pType) : X + Y -> X * Y
  := sum_ind _ (fun x => (x, point Y)) (fun y => (point X, y)).

Definition sum_to_bool X Y : X + Y -> Bool
  := sum_ind _ (fun _ => false) (fun _ => true).

Definition Smash (X Y : pType) : pType
  := Build_pType (pushout (sum_to_prod X Y) (sum_to_bool X Y))
      (pushl (point X, point Y)).

Section Smash.

  Context {X Y : pType}.

  Definition sm (x : X) (y : Y) : Smash X Y := pushl (x, y).

  Definition auxl : Smash X Y := pushr false.

  Definition auxr : Smash X Y := pushr true.

  Notation pt := (point _).

  Definition gluel (x : X) : sm x pt = auxl
    := pp (f:=sum_to_prod X Y) (g:=sum_to_bool X Y) (inl x).

  Definition gluer (y : Y) : sm pt y = auxr
    := pp (f:=sum_to_prod X Y) (g:=sum_to_bool X Y) (inr y).

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

  Definition smash_ind {P : Smash X Y -> Type} (Psm : forall a b, P (sm a b))
    (Pl : P auxl) (Pr : P auxr) (Pgl : forall a, gluel a # Psm a pt = Pl)
    (Pgr : forall b, gluer b # Psm pt b = Pr) (x : Smash X Y) : P x.
  Proof.
    revert x.
    serapply pushout_ind.
    + intros [a b].
      apply Psm.
    + apply (Bool_ind _ Pr Pl).
    + serapply sum_ind.
      - apply Pgl.
      - apply Pgr.
  Defined.

  Definition smash_ind_beta_gluel {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, gluel a # Psm a pt = Pl)
    (Pgr : forall b, gluer b # Psm pt b = Pr) (a : X)
    : apD (smash_ind Psm Pl Pr Pgl Pgr) (gluel a) = Pgl a
    := pushout_ind_beta_pp _ _ _ _ _.

  Definition smash_ind_beta_gluer {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, gluel a # Psm a pt = Pl)
    (Pgr : forall b, gluer b # Psm pt b = Pr) (b : Y)
    : apD (smash_ind Psm Pl Pr Pgl Pgr) (gluer b) = Pgr b
    := pushout_ind_beta_pp _ _ _ _ _.

  (* TODO: Move *)
  Definition transport_inv {A} {P : A -> Type} {x y : A} {p : x = y}
    {u : P x} {v : P y} (r : p # u = v) : p^ # v = u.
  Proof.
    apply moveR_transport_V.
    symmetry; assumption.
  Defined.

  (* TODO: Move, rename *)
  Definition transport_concat {A} {P : A -> Type} {a1 a2 a3 : A} {p1 : a1 = a2}
    {p2 : a2 = a3} {b1} {b2} {b3} (r1 : p1 # b1 = b2) (r2 : p2 # b2 = b3)
    : transport P (p1 @ p2) b1 = b3.
  Proof.
    refine (_ @ r2).
    refine (_ @ ap (transport P _) r1).
    apply transport_pp.
  Defined.

  Definition smash_ind_beta_gluel' {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, gluel a # Psm a pt = Pl)
    (Pgr : forall b, gluer b # Psm pt b = Pr) (a b : X)
    : apD (smash_ind Psm Pl Pr Pgl Pgr) (gluel' a b)
    = transport_concat (Pgl a) (transport_inv (Pgl b)).
  Proof.
    rewrite apD_pp, apD_V, smash_ind_beta_gluel, smash_ind_beta_gluel.
    reflexivity.
Defined.

  Definition smash_ind_beta_gluer' {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, gluel a # Psm a pt = Pl)
    (Pgr : forall b, gluer b # Psm pt b = Pr) (a b : Y)
    : apD (smash_ind Psm Pl Pr Pgl Pgr) (gluer' a b)
    = transport_concat (Pgr a) (transport_inv (Pgr b)).
  Proof.
    rewrite apD_pp, apD_V, smash_ind_beta_gluer, smash_ind_beta_gluer.
    reflexivity.
  Defined.

  Definition smash_ind_beta_glue {P : Smash X Y -> Type}
    {Psm : forall a b, P (sm a b)} {Pl : P auxl} {Pr : P auxr}
    (Pgl : forall a, gluel a # Psm a pt = Pl)
    (Pgr : forall b, gluer b # Psm pt b = Pr) (a : X) (b : Y)
    : apD (smash_ind Psm Pl Pr Pgl Pgr) (glue a b)
    = transport_concat
        (transport_concat (Pgl a) (transport_inv (Pgl pt)))
        (transport_concat (Pgr pt) (transport_inv (Pgr b))).
  Proof.
    rewrite apD_pp, smash_ind_beta_gluel', smash_ind_beta_gluer'.
    reflexivity.
  Defined.

  Definition smash_rec {P : Type} (Psm : X -> Y -> P) (Pl Pr : P)
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr)
    : Smash X Y -> P := smash_ind Psm Pl Pr
      (fun x => transport_const _ _ @ Pgl x)
      (fun x => transport_const _ _ @ (Pgr x)).

  Local Open Scope path_scope.

  (* Version of smash_rec that forces (Pgl pt) and (Pgr pt) to be idpath *)
  Definition smash_rec' {P : Type} {Psm : X -> Y -> P}
    (Pgl : forall a, Psm a pt = Psm pt pt) (Pgr : forall b, Psm pt b = Psm pt pt)
    (ql : Pgl pt = 1) (qr : Pgr pt = 1)
    : Smash X Y -> P := smash_rec Psm (Psm pt pt) (Psm pt pt) Pgl Pgr.

  Definition smash_rec_beta_gluel {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a : X)
    : ap (smash_rec Psm Pl Pr Pgl Pgr) (gluel a) = Pgl a.
  Proof.
    apply (cancelL (transport_const (gluel a) _)).
    refine ((apD_const _ _)^ @ _).
    rewrite smash_ind_beta_gluel.
    reflexivity.
  Defined.

  Definition smash_rec_beta_gluer {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (b : Y)
    : ap (smash_rec Psm Pl Pr Pgl Pgr) (gluer b) = Pgr b.
  Proof.
    apply (cancelL (transport_const (gluer b) _)).
    refine ((apD_const _ _)^ @ _).
    rewrite smash_ind_beta_gluer.
    reflexivity.
  Defined.

  Definition smash_rec_beta_gluel' {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a b : X)
    : ap (smash_rec Psm Pl Pr Pgl Pgr) (gluel' a b) = Pgl a @ (Pgl b)^.
  Proof.
    rewrite ap_pp, ap_V, smash_rec_beta_gluel, smash_rec_beta_gluel.
    reflexivity.
  Defined.

  Definition smash_rec_beta_gluer' {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a b : Y)
    : ap (smash_rec Psm Pl Pr Pgl Pgr) (gluer' a b) = Pgr a @ (Pgr b)^.
  Proof.
    rewrite ap_pp, ap_V, smash_rec_beta_gluer, smash_rec_beta_gluer.
    reflexivity.
  Defined.

  Definition smash_rec_beta_glue {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr)
    (a : X) (b : Y) : ap (smash_rec Psm Pl Pr Pgl Pgr) (glue a b)
    = ((Pgl a) @ (Pgl pt)^) @ (Pgr pt @ (Pgr b)^).
  Proof.
    rewrite ap_pp, smash_rec_beta_gluel', smash_rec_beta_gluer'.
    reflexivity.
  Defined.

  Arguments sm : simpl never.
  Arguments auxl : simpl never.
  Arguments gluel : simpl never.
  Arguments gluer : simpl never.

End Smash.
