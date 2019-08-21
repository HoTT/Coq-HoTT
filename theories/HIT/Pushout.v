(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics.
Require Import HoTT.Types.
Require Import HSet TruncType.
Require Export HIT.Coeq.
Local Open Scope path_scope.


(** * Homotopy Pushouts *)

(*
Record Span :=
  { A : Type; B : Type; C : Type;
    f : C -> A;
    g : C -> B }.

Record Cocone (S : Span) (D : Type) :=
  { i : A S -> D;
    j : B S -> D;
    h : forall c, i (f S c) = j (g S c) }.
*)

(** We define pushouts in terms of coproducts and coequalizers. *)

Definition pushout {A B C : Type} (f : A -> B) (g : A -> C) : Type
  := Coeq (inl o f) (inr o g).

Definition push {A B C : Type} {f : A -> B} {g : A -> C}
 : B+C -> pushout f g
  := @coeq _ _ (inl o f) (inr o g).

Definition pushl {A B C} {f : A -> B} {g : A -> C} (b : B) : pushout f g := push (inl b).
Definition pushr {A B C} {f : A -> B} {g : A -> C} (c : C) : pushout f g := push (inr c).

Definition pp {A B C : Type} {f : A -> B} {g : A -> C} (a : A) : pushl (f a) = pushr (g a)
  := @cp A (B+C) (inl o f) (inr o g) a.

(* Some versions with explicit parameters. *)
Definition pushl' {A B C} (f : A -> B) (g : A -> C) (b : B) : pushout f g := pushl b.
Definition pushr' {A B C} (f : A -> B) (g : A -> C) (c : C) : pushout f g := pushr c.
Definition pp' {A B C : Type} (f : A -> B) (g : A -> C) (a : A) : pushl (f a) = pushr (g a)
  := pp a.

Section PushoutInd.

  Context {A B C : Type} {f : A -> B} {g : A -> C} (P : pushout f g -> Type)
          (pushb : forall b : B, P (pushl b))
          (pushc : forall c : C, P (pushr c))
          (pusha : forall a : A, (pp a) # (pushb (f a)) = pushc (g a)).

  Definition pushout_ind
    : forall (w : pushout f g), P w
    := Coeq_ind P (fun bc => match bc with inl b => pushb b | inr c => pushc c end) pusha.

  Definition pushout_ind_beta_pushl (b:B) : pushout_ind (pushl b) = pushb b
    := 1.
  Definition pushout_ind_beta_pushr (c:C) : pushout_ind (pushr c) = pushc c
    := 1.

  Definition pushout_ind_beta_pp (a:A)
    : apD pushout_ind (pp a) = pusha a
    := Coeq_ind_beta_cp P (fun bc => match bc with inl b => pushb b | inr c => pushc c end) pusha a.

End PushoutInd.

(** But we want to allow the user to forget that we've defined pushouts in terms of coequalizers. *)
Arguments pushout : simpl never.
Arguments push : simpl never.
Arguments pp : simpl never.
Arguments pushout_ind : simpl never.
Arguments pushout_ind_beta_pp : simpl never.

Definition pushout_rec {A B C} {f : A -> B} {g : A -> C} (P : Type)
  (pushb : B -> P)
  (pushc : C -> P)
  (pusha : forall a : A, pushb (f a) = pushc (g a))
  : @pushout A B C f g -> P
  := pushout_ind (fun _ => P) pushb pushc (fun a => transport_const _ _ @ pusha a).

Definition pushout_rec_beta_pp {A B C f g} (P : Type)
  (pushb : B -> P)
  (pushc : C -> P)
  (pusha : forall a : A, pushb (f a) = pushc (g a))
  (a : A)
  : ap (pushout_rec P pushb pushc pusha) (pp a) = pusha a.
Proof.
  unfold pushout_rec.
  eapply (cancelL (transport_const (pp a) _)).
  refine ((apD_const (@pushout_ind A B C f g (fun _ => P) pushb pushc _) (pp a))^ @ _).
  refine (pushout_ind_beta_pp (fun _ => P) _ _ _ _).
Defined.

(** ** Universal property *)

Definition pushout_unrec {A B C P} (f : A -> B) (g : A -> C)
           (h : pushout f g -> P)
  : {psh : (B -> P) * (C -> P) &
           forall a, fst psh (f a) = snd psh (g a)}.
Proof.
  exists (h o pushl , h o pushr).
  intros a; cbn.
  exact (ap h (pp a)).
Defined.

Definition isequiv_pushout_rec `{Funext} {A B C} (f : A -> B) (g : A -> C) P
  : IsEquiv (fun p : {psh : (B -> P) * (C -> P) &
                            forall a, fst psh (f a) = snd psh (g a) }
             => pushout_rec P (fst p.1) (snd p.1) p.2).
Proof.
  srefine (isequiv_adjointify _ (pushout_unrec f g) _ _).
  - intros h.
    apply path_arrow; intros x.
    srefine (pushout_ind (fun x => pushout_rec P (fst (pushout_unrec f g h).1) (snd (pushout_unrec f g h).1) (pushout_unrec f g h).2 x = h x) _ _ _ x).
    + intros b; reflexivity.
    + intros c; reflexivity.
    + intros a; cbn.
      abstract (rewrite transport_paths_FlFr, pushout_rec_beta_pp;
                rewrite concat_p1; apply concat_Vp).
  - intros [[pushb pushc] pusha]; unfold pushout_unrec; cbn.
    srefine (path_sigma' _ _ _).
    + srefine (path_prod' _ _); reflexivity.
    + apply path_forall; intros a.
      abstract (rewrite transport_forall_constant, pushout_rec_beta_pp;
                reflexivity).
Defined.

Definition equiv_pushout_rec `{Funext} {A B C} (f : A -> B) (g : A -> C) P
  : {psh : (B -> P) * (C -> P) &
           forall a, fst psh (f a) = snd psh (g a) }
      <~> (pushout f g -> P)
  := BuildEquiv _ _ _ (isequiv_pushout_rec f g P).

Definition equiv_pushout_unrec `{Funext} {A B C} (f : A -> B) (g : A -> C) P
  : (pushout f g -> P)
      <~> {psh : (B -> P) * (C -> P) &
                 forall a, fst psh (f a) = snd psh (g a) }
  := equiv_inverse (equiv_pushout_rec f g P).

(** ** Symmetry *)

Definition pushout_sym_map {A B C} {f : A -> B} {g : A -> C}
  : pushout f g -> pushout g f
  := pushout_rec (pushout g f) pushr pushl (fun a : A => (pp a)^).

Lemma sect_pushout_sym_map {A B C f g} : Sect (@pushout_sym_map A C B g f) (@pushout_sym_map A B C f g).
Proof.
  unfold Sect. srapply @pushout_ind.
  - intros; reflexivity.
  - intros; reflexivity.
  - intro a.
    abstract (rewrite transport_paths_FFlr, pushout_rec_beta_pp, ap_V, pushout_rec_beta_pp; hott_simpl).
Defined.

Definition pushout_sym {A B C} {f : A -> B} {g : A -> C} : pushout f g <~> pushout g f :=
equiv_adjointify pushout_sym_map pushout_sym_map sect_pushout_sym_map sect_pushout_sym_map.

(** ** Equivalences *)

(** Pushouts preserve equivalences. *)

Section EquivPushout.
  Context {A B C f g A' B' C' f' g'}
          (eA : A <~> A') (eB : B <~> B') (eC : C <~> C')
          (p : eB o f == f' o eA) (q : eC o g == g' o eA).

  Lemma equiv_pushout
    : pushout f g <~> pushout f' g'.
  Proof.
    refine (equiv_functor_coeq' eA (equiv_functor_sum' eB eC) _ _).
    all:unfold pointwise_paths.
    all:intro; simpl; apply ap.
    + apply p.
    + apply q.
  Defined.

  Lemma equiv_pushout_pp (a : A)
    : ap equiv_pushout (pp a)
      = ap pushl (p a) @ pp (eA a) @ ap pushr (q a)^.
  Proof.
    refine (functor_coeq_beta_cp _ _ _ _ a @ _).
    refine (_ @@ 1 @@ _).
    - symmetry; refine (ap_compose inl coeq _).
    - refine (ap (ap coeq) (ap_V _ _)^ @ _).
      symmetry; refine (ap_compose inr coeq _).
  Defined.

End EquivPushout.

(** ** Sigmas *)

(** Pushouts commute with sigmas *)

Section EquivSigmaPushout.
  
  Context {X : Type}
          (A : X -> Type) (B : X -> Type) (C : X -> Type)
          (f : forall x, A x -> B x) (g : forall x, A x -> C x).

  Let esp1 : { x : X & pushout (f x) (g x) }
             -> pushout (functor_sigma idmap f) (functor_sigma idmap g).
  Proof.
    intros [x p].
    srefine (pushout_rec _ _ _ _ p).
    + intros b. exact (pushl (x;b)).
    + intros c. exact (pushr (x;c)).
    + intros a; cbn. exact (pp (x;a)).
  Defined.

  Let esp1_beta_pp (x : X) (a : A x)
    : ap esp1 (path_sigma' (fun x => pushout (f x) (g x)) 1 (pp a))
      = pp (x;a).
  Proof.
    rewrite (ap_path_sigma (fun x => pushout (f x) (g x))
                           (fun x a => esp1 (x;a)) 1 (pp a)); cbn.
    rewrite !concat_p1.
    unfold esp1; rewrite pushout_rec_beta_pp.
    reflexivity.
  Qed.

  Let esp2 : pushout (functor_sigma idmap f) (functor_sigma idmap g)
             -> { x : X & pushout (f x) (g x) }.
  Proof.
    srefine (pushout_rec _ _ _ _).
    + exact (functor_sigma idmap (fun x => @pushl _ _ _ (f x) (g x))).
    + exact (functor_sigma idmap (fun x => @pushr _ _ _ (f x) (g x))).
    + intros [x a]; unfold functor_sigma; cbn.
      srefine (path_sigma' _ 1 _); cbn.
      apply pp.
  Defined.

  Let esp2_beta_pp (x : X) (a : A x)
    : ap esp2 (pp (x;a)) = path_sigma' (fun x:X => pushout (f x) (g x)) 1 (pp a).
  Proof.
    unfold esp2.
    rewrite pushout_rec_beta_pp.
    reflexivity.
  Qed.

  Definition equiv_sigma_pushout
    : { x : X & pushout (f x) (g x) }
        <~> pushout (functor_sigma idmap f) (functor_sigma idmap g).
  Proof.
    srefine (equiv_adjointify esp1 esp2 _ _).
    - srefine (pushout_ind _ _ _ _); cbn.
      + reflexivity.
      + reflexivity.
      + intros [x a].
        rewrite transport_paths_FlFr.
        rewrite ap_idmap, concat_p1.
        apply moveR_Vp. rewrite concat_p1.
        rewrite ap_compose.
        rewrite esp2_beta_pp, esp1_beta_pp.
        reflexivity.
    - intros [x a]; revert a.
      srefine (pushout_ind _ _ _ _); cbn.
      + reflexivity.
      + reflexivity.
      + intros a.
        rewrite transport_paths_FlFr.
        rewrite concat_p1; apply moveR_Vp; rewrite concat_p1.
        rewrite (ap_compose (exist _ x) (esp2 o esp1)).
        rewrite (ap_compose esp1 esp2).
        rewrite (ap_existT (fun x => pushout (f x) (g x)) x _ _ (pp a)).
        rewrite esp1_beta_pp, esp2_beta_pp.
        reflexivity.
  Defined.

End EquivSigmaPushout.

(** ** Pushouts are associative *)

Section PushoutAssoc.

  Context {A1 A2 B C D : Type}
          (f1 : A1 -> B) (g1 : A1 -> C) (f2 : A2 -> C) (g2 : A2 -> D).

  Definition pushout_assoc_left := pushout (pushr' f1 g1 o f2) g2.
  Let pushll : B -> pushout_assoc_left
    := pushl' (pushr' f1 g1 o f2) g2 o pushl' f1 g1.
  Let pushlm : C -> pushout_assoc_left
    := pushl' (pushr' f1 g1 o f2) g2 o pushr' f1 g1.
  Let pushlr : D -> pushout_assoc_left
    := pushr' (pushr' f1 g1 o f2) g2.
  Let ppll : forall a1, pushll (f1 a1) = pushlm (g1 a1)
    := fun a1 => ap (pushl' (pushr' f1 g1 o f2) g2) (pp' f1 g1 a1).
  Let pplr : forall a2, pushlm (f2 a2) = pushlr (g2 a2)
    := fun a2 => pp' (pushr' f1 g1 o f2) g2 a2.

  Definition pushout_assoc_left_ind
             (P : pushout_assoc_left -> Type)
             (pushb : forall b, P (pushll b))
             (pushc : forall c, P (pushlm c))
             (pushd : forall d, P (pushlr d))
             (pusha1 : forall a1, (ppll a1) # pushb (f1 a1) = pushc (g1 a1))
             (pusha2 : forall a2, (pplr a2) # pushc (f2 a2) = pushd (g2 a2))
    : forall x, P x.
  Proof.
    srefine (pushout_ind _ _ pushd _).
    - srefine (pushout_ind _ pushb pushc _).
      intros a1.
      exact (transport_compose P pushl _ _ @ pusha1 a1).
    - exact pusha2.
  Defined.

  Section Pushout_Assoc_Left_Rec.

    Context (P : Type)
            (pushb : B -> P)
            (pushc : C -> P)
            (pushd : D -> P)
            (pusha1 : forall a1, pushb (f1 a1) = pushc (g1 a1))
            (pusha2 : forall a2, pushc (f2 a2) = pushd (g2 a2)).

    Definition pushout_assoc_left_rec
      : pushout_assoc_left -> P.
    Proof.
      srefine (pushout_rec _ _ pushd _).
      - srefine (pushout_rec _ pushb pushc pusha1).
      - exact pusha2.
    Defined.

    Definition pushout_assoc_left_rec_beta_ppll a1
      : ap pushout_assoc_left_rec (ppll a1) = pusha1 a1.
    Proof.
      unfold ppll.
      rewrite <- (ap_compose (pushl' (pushr' f1 g1 o f2) g2)
                             pushout_assoc_left_rec).
      change (ap (pushout_rec P pushb pushc pusha1) (pp' f1 g1 a1) = pusha1 a1).
      apply pushout_rec_beta_pp.
    Defined.

    Definition pushout_assoc_left_rec_beta_pplr a2
      : ap pushout_assoc_left_rec (pplr a2) = pusha2 a2.
    Proof.
      unfold pushout_assoc_left_rec, pplr.
      apply (pushout_rec_beta_pp (f := pushr' f1 g1 o f2) (g := g2)).
    Defined.

  End Pushout_Assoc_Left_Rec.

  Definition pushout_assoc_right := pushout f1 (pushl' f2 g2 o g1).
  Let pushrl : B -> pushout_assoc_right
    := pushl' f1 (pushl' f2 g2 o g1).
  Let pushrm : C -> pushout_assoc_right
    := pushr' f1 (pushl' f2 g2 o g1) o pushl' f2 g2.
  Let pushrr : D -> pushout_assoc_right
    := pushr' f1 (pushl' f2 g2 o g1) o pushr' f2 g2.
  Let pprl : forall a1, pushrl (f1 a1) = pushrm (g1 a1)
    := fun a1 => pp' f1 (pushl' f2 g2 o g1) a1.
  Let pprr : forall a2, pushrm (f2 a2) = pushrr (g2 a2)
    := fun a2 => ap (pushr' f1 (pushl' f2 g2 o g1)) (pp' f2 g2 a2).

  Definition pushout_assoc_right_ind
             (P : pushout_assoc_right -> Type)
             (pushb : forall b, P (pushrl b))
             (pushc : forall c, P (pushrm c))
             (pushd : forall d, P (pushrr d))
             (pusha1 : forall a1, (pprl a1) # pushb (f1 a1) = pushc (g1 a1))
             (pusha2 : forall a2, (pprr a2) # pushc (f2 a2) = pushd (g2 a2))
    : forall x, P x.
  Proof.
    srefine (pushout_ind _ pushb _ _).
    - srefine (pushout_ind _ pushc pushd _).
      intros a2.
      exact (transport_compose P pushr _ _ @ pusha2 a2).
    - exact pusha1.
  Defined.

  Section Pushout_Assoc_Right_Rec.

    Context (P : Type)
            (pushb : B -> P)
            (pushc : C -> P)
            (pushd : D -> P)
            (pusha1 : forall a1, pushb (f1 a1) = pushc (g1 a1))
            (pusha2 : forall a2, pushc (f2 a2) = pushd (g2 a2)).

    Definition pushout_assoc_right_rec
      : pushout_assoc_right -> P.
    Proof.
      srefine (pushout_rec _ pushb _ _).
      - srefine (pushout_rec _ pushc pushd pusha2).
      - exact pusha1.
    Defined.

    Definition pushout_assoc_right_rec_beta_pprl a1
      : ap pushout_assoc_right_rec (pprl a1) = pusha1 a1.
    Proof.
      unfold pushout_assoc_right_rec, pprl.
      apply (pushout_rec_beta_pp (f := f1) (g := pushl' f2 g2 o g1)).
    Defined.

    Definition pushout_assoc_right_rec_beta_pprr a2
      : ap pushout_assoc_right_rec (pprr a2) = pusha2 a2.
    Proof.
      unfold pprr.
      rewrite <- (ap_compose (pushr' f1 (pushl' f2 g2 o g1))
                             pushout_assoc_right_rec).
      change (ap (pushout_rec P pushc pushd pusha2) (pp' f2 g2 a2) = pusha2 a2).
      apply pushout_rec_beta_pp.
    Defined.

  End Pushout_Assoc_Right_Rec.

  Definition equiv_pushout_assoc
    : pushout (pushr' f1 g1 o f2) g2 <~> pushout f1 (pushl' f2 g2 o g1).
  Proof.
    srefine (equiv_adjointify _ _ _ _).
    - exact (pushout_assoc_left_rec _ pushrl pushrm pushrr pprl pprr).
    - exact (pushout_assoc_right_rec _ pushll pushlm pushlr ppll pplr).
    - abstract (
      srefine (pushout_assoc_right_ind
                 _ (fun _ => 1) (fun _ => 1) (fun _ => 1) _ _);
        intros; rewrite transport_paths_FlFr, ap_compose;
      [ rewrite pushout_assoc_right_rec_beta_pprl,
        pushout_assoc_left_rec_beta_ppll
      | rewrite pushout_assoc_right_rec_beta_pprr,
        pushout_assoc_left_rec_beta_pplr ];
      rewrite concat_p1, ap_idmap; apply concat_Vp ).
    - abstract (
      srefine (pushout_assoc_left_ind
                 _ (fun _ => 1) (fun _ => 1) (fun _ => 1) _ _);
        intros; rewrite transport_paths_FlFr, ap_compose;
      [ rewrite pushout_assoc_left_rec_beta_ppll,
        pushout_assoc_right_rec_beta_pprl
      | rewrite pushout_assoc_left_rec_beta_pplr,
        pushout_assoc_right_rec_beta_pprr ];
      rewrite concat_p1, ap_idmap; apply concat_Vp ).
  Defined.

End PushoutAssoc.

(** ** Pushouts of equvialences are equivalences *)

Global Instance isequiv_pushout_isequiv {A B C} (f : A -> B) (g : A -> C)
       `{IsEquiv _ _ f} : IsEquiv (pushr' f g).
Proof.
  srefine (isequiv_adjointify _ _ _ _).
  - srefine (pushout_rec C (g o f^-1) idmap _).
    intros a; cbn; apply ap, eissect.
  - srefine (pushout_ind _ _ _ _); cbn.
    + intros b; change (pushr' f g (g (f^-1 b)) = pushl b).
      transitivity (pushl' f g (f (f^-1 b))).
      * symmetry; apply pp.
      * apply ap, eisretr.
    + intros c; reflexivity.
    + intros a.
      abstract (
      rewrite transport_paths_FlFr, ap_compose, !concat_pp_p;
      apply moveR_Vp; apply moveR_Vp;
      rewrite pushout_rec_beta_pp, eisadj, ap_idmap, concat_p1;
      rewrite <- ap_compose, <- (ap_compose g (pushr' f g));
      exact (concat_Ap (pp' f g) (eissect f a)) ).
  - intros c; reflexivity.
Defined.

Global Instance isequiv_pushout_isequiv' {A B C} (f : A -> B) (g : A -> C)
       `{IsEquiv _ _ g} : IsEquiv (pushl' f g).
Proof.
  srefine (isequiv_adjointify _ _ _ _).
  - srefine (pushout_rec B idmap (f o g^-1) _).
    intros a; cbn. symmetry; apply ap, eissect.
  - srefine (pushout_ind _ _ _ _); cbn.
    + intros b; reflexivity.
    + intros c; change (pushl' f g (f (g^-1 c)) = pushr c).
      transitivity (pushr' f g (g (g^-1 c))).
      * apply pp.
      * apply ap, eisretr.
    + intros a.
      abstract (
      rewrite transport_paths_FlFr, ap_compose, !concat_pp_p;
      apply moveR_Vp;
      rewrite pushout_rec_beta_pp, eisadj, ap_idmap, concat_1p, ap_V;
      apply moveL_Vp;
      rewrite <- !ap_compose;
      exact (concat_Ap (pp' f g) (eissect g a)) ).
  - intros c; reflexivity.
Defined.
