Require Import Basics.Overture Basics.PathGroupoids Basics.Tactics Basics.Equivalences.
Require Import Types.Sum Types.Bool Types.Paths Types.Forall.
Require Import WildCat.Core WildCat.Bifunctor WildCat.Equiv.
Require Import Colimits.Pushout.
Require Import Cubical.DPath.
Require Import Pointed.Core.

Local Open Scope pointed_scope.
Local Open Scope dpath_scope.
Local Open Scope path_scope.

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
    + exact (Bool_ind _ Pr Pl).
    + srapply sum_ind.
      - exact Pgl.
      - exact Pgr.
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
    lhs napply dp_apD_pp.
    apply ap011.
    1: apply Smash_ind_beta_gluel.
    lhs napply dp_apD_V.
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
    lhs napply dp_apD_pp.
    apply ap011.
    1: apply Smash_ind_beta_gluer.
    lhs napply dp_apD_V.
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
    lhs napply dp_apD_pp.
    apply ap011.
    - apply Smash_ind_beta_gluel'.
    - apply Smash_ind_beta_gluer'.
  Defined.

  Definition Smash_rec {P : Type} (Psm : X -> Y -> P) (Pl Pr : P)
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr)
    : Smash X Y -> P
    := Smash_ind Psm Pl Pr (fun x => dp_const (Pgl x)) (fun x => dp_const (Pgr x)).

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
    rhs_V napply (eissect dp_const).
    apply moveL_equiv_V.
    lhs_V napply dp_apD_const.
    napply Smash_ind_beta_gluel.
  Defined.

  Definition Smash_rec_beta_gluer {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (b : Y)
    : ap (Smash_rec Psm Pl Pr Pgl Pgr) (gluer b) = Pgr b.
  Proof.
    rhs_V napply (eissect dp_const).
    apply moveL_equiv_V.
    lhs_V napply dp_apD_const.
    napply Smash_ind_beta_gluer.
  Defined.

  Definition Smash_rec_beta_gluel' {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a b : X)
    : ap (Smash_rec Psm Pl Pr Pgl Pgr) (gluel' a b) = Pgl a @ (Pgl b)^.
  Proof.
    lhs napply ap_pV.
    f_ap.
    1: apply Smash_rec_beta_gluel.
    apply inverse2.
    apply Smash_rec_beta_gluel.
  Defined.

  Definition Smash_rec_beta_gluer' {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a b : Y)
    : ap (Smash_rec Psm Pl Pr Pgl Pgr) (gluer' a b) = Pgr a @ (Pgr b)^.
  Proof.
    lhs napply ap_pV.
    f_ap.
    1: apply Smash_rec_beta_gluer.
    apply inverse2.
    apply Smash_rec_beta_gluer.
  Defined.

  Definition Smash_rec_beta_glue {P : Type} {Psm : X -> Y -> P} {Pl Pr : P}
    (Pgl : forall a, Psm a pt = Pl) (Pgr : forall b, Psm pt b = Pr) (a : X)
    (b : Y) : ap (Smash_rec Psm Pl Pr Pgl Pgr) (glue a b)
    = ((Pgl a) @ (Pgl pt)^) @ (Pgr pt @ (Pgr b)^).
  Proof.
    lhs napply ap_pp.
    f_ap.
    - apply Smash_rec_beta_gluel'.
    - apply Smash_rec_beta_gluer'.
  Defined.

End Smash.

Arguments sm : simpl never.
Arguments auxl : simpl never.
Arguments gluel : simpl never.
Arguments gluer : simpl never.

(** ** Miscellaneous lemmas about Smash *)

(** A version of [Smash_ind] specifically for proving that two functions from a [Smash] are homotopic. *)
Definition Smash_ind_FlFr {A B : pType} {P : Type} (f g : Smash A B -> P)
  (Hsm : forall a b, f (sm a b) = g (sm a b))
  (Hl : f auxl = g auxl) (Hr : f auxr = g auxr)
  (Hgluel : forall a, ap f (gluel a) @ Hl = Hsm a pt @ ap g (gluel a))
  (Hgluer : forall b, ap f (gluer b) @ Hr = Hsm pt b @ ap g (gluer b))
  : f == g.
Proof.
  snapply (Smash_ind Hsm Hl Hr).
  - intros a.
    transport_paths FlFr.
    exact (Hgluel a).
  - intros b.
    transport_paths FlFr.
    exact (Hgluer b).
Defined.

(** A version of [Smash_ind]j specifically for proving that the composition of two functions is the identity map. *)
Definition Smash_ind_FFlr {A B : pType} {P : Type}
  (f : Smash A B -> P) (g : P -> Smash A B)
  (Hsm : forall a b, g (f (sm a b)) = sm a b)
  (Hl : g (f auxl) = auxl) (Hr : g (f auxr) = auxr)
  (Hgluel : forall a, ap g (ap f (gluel a)) @ Hl = Hsm a pt @ gluel a)
  (Hgluer : forall b, ap g (ap f (gluer b)) @ Hr = Hsm pt b @ gluer b)
  : g o f == idmap.
Proof.
  snapply (Smash_ind Hsm Hl Hr).
  - intros a; cbn beta.
    transport_paths FFlr.
    exact (Hgluel a).
  - intros b; cbn beta.
    transport_paths FFlr.
    exact (Hgluer b).
Defined.

(** ** Functoriality of the smash product *)

Definition functor_smash {A B X Y : pType} (f : A $-> X) (g : B $-> Y)
  : Smash A B $-> Smash X Y.
Proof.
  srapply Build_pMap.
  - snapply (Smash_rec (fun a b => sm (f a) (g b)) auxl auxr).
    + intro a; cbn beta.
      rhs_V napply (gluel (f a)).
      exact (ap011 _ 1 (point_eq g)).
    + intro b; cbn beta.
      rhs_V napply (gluer (g b)).
      exact (ap011 _ (point_eq f) 1).
  - exact (ap011 _ (point_eq f) (point_eq g)).
Defined.

Definition functor_smash_idmap (X Y : pType)
  : functor_smash (@pmap_idmap X) (@pmap_idmap Y) $== pmap_idmap.
Proof.
  snapply Build_pHomotopy.
  { snapply Smash_ind_FlFr.
    1-3: reflexivity.
    - intros x.
      apply equiv_p1_1q.
      rhs napply ap_idmap.
      lhs napply Smash_rec_beta_gluel.
      apply concat_1p.
    - intros y.
      apply equiv_p1_1q.
      rhs napply ap_idmap.
      lhs napply Smash_rec_beta_gluer.
      apply concat_1p. }
  reflexivity.
Defined.

Definition functor_smash_compose {X Y A B C D : pType}
  (f : X $-> A) (g : Y $-> B) (h : A $-> C) (k : B $-> D)
  : functor_smash (h $o f) (k $o g) $== functor_smash h k $o functor_smash f g.
Proof.
  pointed_reduce.
  snapply Build_pHomotopy.
  { snapply Smash_ind_FlFr.
    1-3: reflexivity.
    - intros x.
      apply equiv_p1_1q.
      lhs napply Smash_rec_beta_gluel.
      symmetry.
      lhs napply (ap_compose (functor_smash _ _) _ (gluel x)).
      lhs napply ap.
      2: napply Smash_rec_beta_gluel.
      lhs napply Smash_rec_beta_gluel.
      apply concat_1p.
    - intros y.
      apply equiv_p1_1q.
      lhs napply Smash_rec_beta_gluer.
      symmetry.
      lhs napply (ap_compose (functor_smash _ _) _ (gluer y)).
      lhs napply ap.
      2: napply Smash_rec_beta_gluer.
      lhs napply Smash_rec_beta_gluer.
      apply concat_1p. }
  reflexivity.
Defined.

Definition functor_smash_homotopic {X Y A B : pType}
  {f h : X $-> A} {g k : Y $-> B}
  (p : f $== h) (q : g $== k)
  : functor_smash f g $== functor_smash h k.
Proof.
  pointed_reduce.
  snapply Build_pHomotopy.
  { snapply Smash_ind_FlFr.
    1: exact (fun x y => ap011 _ (p x) (q y)).
    1,2: reflexivity.
    - intros x.
      lhs napply concat_p1.
      lhs napply Smash_rec_beta_gluel.
      rhs napply whiskerL.
      2: napply Smash_rec_beta_gluel.
      simpl; induction (p x); simpl.
      rhs_V napply concat_pp_p.
      apply whiskerR.
      napply ap_pp.
    - intros y.
      lhs napply concat_p1.
      lhs napply Smash_rec_beta_gluer.
      rhs napply whiskerL.
      2: napply Smash_rec_beta_gluer.
      simpl; induction (q y); simpl.
      rhs_V napply concat_pp_p.
      apply whiskerR.
      exact (ap011_pp _ _ _ 1 1). }
  exact (ap022 _ (concat_p1 (p pt))^ (concat_p1 (q pt))^ @ (concat_p1 _)^).
Defined.

#[export] Instance is0bifunctor_smash : Is0Bifunctor Smash.
Proof.
  snapply Build_Is0Bifunctor'.
  1,2: exact _.
  napply Build_Is0Functor.
  intros [X Y] [A B] [f g].
  exact (functor_smash f g).
Defined.

#[export] Instance is1bifunctor_smash : Is1Bifunctor Smash.
Proof.
  snapply Build_Is1Bifunctor'.
  snapply Build_Is1Functor.
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
  snapply Build_pHomotopy.
  - snapply Smash_ind_FFlr.
    1-3: reflexivity.
    + intros y.
      apply equiv_p1_1q.
      lhs napply ap.
      1: apply Smash_rec_beta_gluel.
      napply Smash_rec_beta_gluer.
    + intros x.
      apply equiv_p1_1q.
      lhs napply ap.
      1: apply Smash_rec_beta_gluer.
      napply Smash_rec_beta_gluel.
  - reflexivity.
Defined.

Definition pequiv_pswap {X Y : pType} : Smash X Y $<~> Smash Y X.
Proof.
  snapply cate_adjointify.
  1,2: exact (pswap _ _).
  1,2: exact pswap_pswap.
Defined.

Definition pswap_natural {A B X Y : pType} (f : A $-> X) (g : B $-> Y)
  : pswap X Y $o functor_smash f g $== functor_smash g f $o pswap A B.
Proof.
  pointed_reduce.
  snapply Build_pHomotopy.
  - snapply Smash_ind_FlFr.
    1-3: reflexivity.
    + intros a.
      apply equiv_p1_1q.
      rhs napply (ap_compose (pswap _ _) _ (gluel a)).
      rhs napply ap.
      2: apply Smash_rec_beta_gluel.
      rhs napply Smash_rec_beta_gluer.
      lhs napply (ap_compose (functor_smash _ _) (pswap _ _) (gluel a)).
      lhs napply ap.
      1: apply Smash_rec_beta_gluel.
      simpl.
      lhs napply ap.
      1: apply concat_1p.
      rhs napply concat_1p.
      napply Smash_rec_beta_gluel.
    + intros b.
      apply equiv_p1_1q.
      rhs napply (ap_compose (pswap _ _) (functor_smash _ _) (gluer b)).
      rhs napply ap.
      2: apply Smash_rec_beta_gluer.
      rhs napply Smash_rec_beta_gluel.
      lhs napply (ap_compose (functor_smash _ _) (pswap _ _) (gluer b)).
      lhs napply ap.
      1: apply Smash_rec_beta_gluer.
      lhs napply ap.
      1: apply concat_1p.
      rhs napply concat_1p.
      napply Smash_rec_beta_gluer.
  - reflexivity.
Defined.
