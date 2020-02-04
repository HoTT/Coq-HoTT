(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics.
Require Import HoTT.Types.
Require Import HSet TruncType.
Require Export HIT.Coeq.
Local Open Scope path_scope.

(** * Homotopy Pushouts *)

(** We define pushouts in terms of coproducts and coequalizers. *)

Definition Pushout@{i j k l} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  (f : A -> B) (g : A -> C) : Type@{l}
  := Coeq@{l l} (inl o f) (inr o g).

Definition push {A B C : Type} {f : A -> B} {g : A -> C}
 : B+C -> Pushout f g
  := @coeq _ _ (inl o f) (inr o g).

Definition pushl {A B C} {f : A -> B} {g : A -> C} (b : B)
  : Pushout f g := push (inl b).
Definition pushr {A B C} {f : A -> B} {g : A -> C} (c : C)
  : Pushout f g := push (inr c).

Definition pglue {A B C : Type} {f : A -> B} {g : A -> C} (a : A)
  : pushl (f a) = pushr (g a)
  := @cglue A (B+C) (inl o f) (inr o g) a.

(* Some versions with explicit parameters. *)
Definition pushl' {A B C} (f : A -> B) (g : A -> C) (b : B) : Pushout f g := pushl b.
Definition pushr' {A B C} (f : A -> B) (g : A -> C) (c : C) : Pushout f g := pushr c.
Definition pglue' {A B C : Type} (f : A -> B) (g : A -> C) (a : A) : pushl (f a) = pushr (g a)
  := pglue a.

Section PushoutInd.

  Context {A B C : Type} {f : A -> B} {g : A -> C}
    (P : Pushout f g -> Type)
    (pushb : forall b : B, P (pushl b))
    (pushc : forall c : C, P (pushr c))
    (pusha : forall a : A, (pglue a) # (pushb (f a)) = pushc (g a)).

  Definition Pushout_ind
    : forall (w : Pushout f g), P w
    := Coeq_ind P (fun bc =>
      match bc with
        | inl b => pushb b
        | inr c => pushc c 
      end) pusha.

  Definition Pushout_ind_beta_pushl (b:B) : Pushout_ind (pushl b) = pushb b
    := 1.
  Definition Pushout_ind_beta_pushr (c:C) : Pushout_ind (pushr c) = pushc c
    := 1.

  Definition Pushout_ind_beta_pglue (a:A)
    : apD Pushout_ind (pglue a) = pusha a
    := Coeq_ind_beta_cglue P (fun bc => match bc with inl b => pushb b | inr c => pushc c end) pusha a.

End PushoutInd.

(** But we want to allow the user to forget that we've defined pushouts in terms of coequalizers. *)
Arguments Pushout : simpl never.
Arguments push : simpl never.
Arguments pglue : simpl never.
Arguments Pushout_ind : simpl never.
Arguments Pushout_ind_beta_pglue : simpl never.

Definition Pushout_rec {A B C} {f : A -> B} {g : A -> C} (P : Type)
  (pushb : B -> P)
  (pushc : C -> P)
  (pusha : forall a : A, pushb (f a) = pushc (g a))
  : @Pushout A B C f g -> P
  := Pushout_ind (fun _ => P) pushb pushc (fun a => transport_const _ _ @ pusha a).

Definition Pushout_rec_beta_pglue {A B C f g} (P : Type)
  (pushb : B -> P)
  (pushc : C -> P)
  (pusha : forall a : A, pushb (f a) = pushc (g a))
  (a : A)
  : ap (Pushout_rec P pushb pushc pusha) (pglue a) = pusha a.
Proof.
  unfold Pushout_rec.
  eapply (cancelL (transport_const (pglue a) _)).
  refine ((apD_const (@Pushout_ind A B C f g (fun _ => P) pushb pushc _) (pglue a))^ @ _).
  refine (Pushout_ind_beta_pglue (fun _ => P) _ _ _ _).
Defined.

(** ** Universal property *)

Definition pushout_unrec {A B C P} (f : A -> B) (g : A -> C)
           (h : Pushout f g -> P)
  : {psh : (B -> P) * (C -> P) &
           forall a, fst psh (f a) = snd psh (g a)}.
Proof.
  exists (h o pushl , h o pushr).
  intros a; cbn.
  exact (ap h (pglue a)).
Defined.

Definition isequiv_Pushout_rec `{Funext} {A B C} (f : A -> B) (g : A -> C) P
  : IsEquiv (fun p : {psh : (B -> P) * (C -> P) &
                            forall a, fst psh (f a) = snd psh (g a) }
             => Pushout_rec P (fst p.1) (snd p.1) p.2).
Proof.
  srefine (isequiv_adjointify _ (pushout_unrec f g) _ _).
  - intros h.
    apply path_arrow; intros x.
    srefine (Pushout_ind (fun x => Pushout_rec P (fst (pushout_unrec f g h).1) (snd (pushout_unrec f g h).1) (pushout_unrec f g h).2 x = h x) _ _ _ x).
    + intros b; reflexivity.
    + intros c; reflexivity.
    + intros a; cbn.
      abstract (rewrite transport_paths_FlFr, Pushout_rec_beta_pglue;
                rewrite concat_p1; apply concat_Vp).
  - intros [[pushb pushc] pusha]; unfold pushout_unrec; cbn.
    srefine (path_sigma' _ _ _).
    + srefine (path_prod' _ _); reflexivity.
    + apply path_forall; intros a.
      abstract (rewrite transport_forall_constant, Pushout_rec_beta_pglue;
                reflexivity).
Defined.

Definition equiv_Pushout_rec `{Funext} {A B C} (f : A -> B) (g : A -> C) P
  : {psh : (B -> P) * (C -> P) &
           forall a, fst psh (f a) = snd psh (g a) }
      <~> (Pushout f g -> P)
  := Build_Equiv _ _ _ (isequiv_Pushout_rec f g P).

Definition equiv_pushout_unrec `{Funext} {A B C} (f : A -> B) (g : A -> C) P
  : (Pushout f g -> P)
      <~> {psh : (B -> P) * (C -> P) &
                 forall a, fst psh (f a) = snd psh (g a) }
  := equiv_inverse (equiv_Pushout_rec f g P).

(** ** Symmetry *)

Definition pushout_sym_map {A B C} {f : A -> B} {g : A -> C}
  : Pushout f g -> Pushout g f
  := Pushout_rec (Pushout g f) pushr pushl (fun a : A => (pglue a)^).

Lemma sect_pushout_sym_map {A B C f g} : Sect (@pushout_sym_map A C B g f) (@pushout_sym_map A B C f g).
Proof.
  unfold Sect. srapply @Pushout_ind.
  - intros; reflexivity.
  - intros; reflexivity.
  - intro a.
    abstract (rewrite transport_paths_FFlr, Pushout_rec_beta_pglue, ap_V, Pushout_rec_beta_pglue; hott_simpl).
Defined.

Definition pushout_sym {A B C} {f : A -> B} {g : A -> C}
  : Pushout f g <~> Pushout g f :=
equiv_adjointify pushout_sym_map pushout_sym_map sect_pushout_sym_map sect_pushout_sym_map.

(** ** Functoriality *)

Definition functor_pushout
           {A B C} (f : A -> B) (g : A -> C)
           {A' B' C'} (f' : A' -> B') (g' : A' -> C')
           (h : A -> A') (k : B -> B') (l : C -> C')
           (p : k o f == f' o h) (q : l o g == g' o h)
  : Pushout f g -> Pushout f' g'.
Proof.
  unfold Pushout; serapply functor_coeq.
  - exact h.
  - exact (functor_sum k l).
  - intros a; cbn.
    apply ap, p.
  - intros a; cbn.
    apply ap, q.
Defined.

(** ** Equivalences *)

(** Pushouts preserve equivalences. *)

Section EquivPushout.
  Context {A B C f g A' B' C' f' g'}
          (eA : A <~> A') (eB : B <~> B') (eC : C <~> C')
          (p : eB o f == f' o eA) (q : eC o g == g' o eA).

  Lemma equiv_pushout
    : Pushout f g <~> Pushout f' g'.
  Proof.
    refine (equiv_functor_coeq' eA (equiv_functor_sum' eB eC) _ _).
    all:unfold pointwise_paths.
    all:intro; simpl; apply ap.
    + apply p.
    + apply q.
  Defined.

  Lemma equiv_pushout_pglue (a : A)
    : ap equiv_pushout (pglue a)
      = ap pushl (p a) @ pglue (eA a) @ ap pushr (q a)^.
  Proof.
    refine (functor_coeq_beta_cglue _ _ _ _ a @ _).
    refine (_ @@ 1 @@ _).
    - symmetry; refine (ap_compose inl coeq _).
    - refine (ap (ap coeq) (ap_V _ _)^ @ _).
      symmetry; refine (ap_compose inr coeq _).
  Defined.

End EquivPushout.

(** ** Contractibility *)

(** The pushout of a span of contractible types is contractible *)

Global Instance contr_pushout {A B C : Type} `{Contr A, Contr B, Contr C}
       (f : A -> B) (g : A -> C)
  : Contr (Pushout f g).
Proof.
  exists (pushl (center B)).
  serapply Pushout_ind.
  - intros b; apply ap, path_contr.
  - intros c.
    refine (_ @ pglue (center A) @ _).
    + apply ap, path_contr.
    + apply ap, path_contr.
  - intros a.
    rewrite transport_paths_r.
    assert (p := path_contr (center A) a).
    destruct p.
    refine ((concat_p1 _)^ @ _).
    apply whiskerL.
    change 1 with (ap (@pushr A B C f g) (idpath (g (center A)))).
    apply (ap (ap pushr)).
    apply path_contr.
Defined.

(** ** Sigmas *)

(** Pushouts commute with sigmas *)

Section EquivSigmaPushout.
  
  Context {X : Type}
          (A : X -> Type) (B : X -> Type) (C : X -> Type)
          (f : forall x, A x -> B x) (g : forall x, A x -> C x).

  Let esp1 : { x : X & Pushout (f x) (g x) }
             -> Pushout (functor_sigma idmap f) (functor_sigma idmap g).
  Proof.
    intros [x p].
    srefine (Pushout_rec _ _ _ _ p).
    + intros b. exact (pushl (x;b)).
    + intros c. exact (pushr (x;c)).
    + intros a; cbn. exact (pglue (x;a)).
  Defined.

  Let esp1_beta_pglue (x : X) (a : A x)
    : ap esp1 (path_sigma' (fun x => Pushout (f x) (g x)) 1 (pglue a))
      = pglue (x;a).
  Proof.
    rewrite (ap_path_sigma (fun x => Pushout (f x) (g x))
                           (fun x a => esp1 (x;a)) 1 (pglue a)); cbn.
    rewrite !concat_p1.
    unfold esp1; rewrite Pushout_rec_beta_pglue.
    reflexivity.
  Qed.

  Let esp2 : Pushout (functor_sigma idmap f) (functor_sigma idmap g)
             -> { x : X & Pushout (f x) (g x) }.
  Proof.
    srefine (Pushout_rec _ _ _ _).
    + exact (functor_sigma idmap (fun x => @pushl _ _ _ (f x) (g x))).
    + exact (functor_sigma idmap (fun x => @pushr _ _ _ (f x) (g x))).
    + intros [x a]; unfold functor_sigma; cbn.
      srefine (path_sigma' _ 1 _); cbn.
      apply pglue.
  Defined.

  Let esp2_beta_pglue (x : X) (a : A x)
    : ap esp2 (pglue (x;a)) = path_sigma' (fun x:X => Pushout (f x) (g x)) 1 (pglue a).
  Proof.
    unfold esp2.
    rewrite Pushout_rec_beta_pglue.
    reflexivity.
  Qed.

  Definition equiv_sigma_pushout
    : { x : X & Pushout (f x) (g x) }
        <~> Pushout (functor_sigma idmap f) (functor_sigma idmap g).
  Proof.
    srefine (equiv_adjointify esp1 esp2 _ _).
    - srefine (Pushout_ind _ _ _ _); cbn.
      + reflexivity.
      + reflexivity.
      + intros [x a].
        rewrite transport_paths_FlFr.
        rewrite ap_idmap, concat_p1.
        apply moveR_Vp. rewrite concat_p1.
        rewrite ap_compose.
        rewrite esp2_beta_pglue, esp1_beta_pglue.
        reflexivity.
    - intros [x a]; revert a.
      srefine (Pushout_ind _ _ _ _); cbn.
      + reflexivity.
      + reflexivity.
      + intros a.
        rewrite transport_paths_FlFr.
        rewrite concat_p1; apply moveR_Vp; rewrite concat_p1.
        rewrite (ap_compose (exist _ x) (esp2 o esp1)).
        rewrite (ap_compose esp1 esp2).
        rewrite (ap_existT (fun x => Pushout (f x) (g x)) x _ _ (pglue a)).
        rewrite esp1_beta_pglue, esp2_beta_pglue.
        reflexivity.
  Defined.

End EquivSigmaPushout.

(** ** Pushouts are associative *)

Section PushoutAssoc.

  Context {A1 A2 B C D : Type}
          (f1 : A1 -> B) (g1 : A1 -> C) (f2 : A2 -> C) (g2 : A2 -> D).

  Definition pushout_assoc_left := Pushout (pushr' f1 g1 o f2) g2.
  Let pushll : B -> pushout_assoc_left
    := pushl' (pushr' f1 g1 o f2) g2 o pushl' f1 g1.
  Let pushlm : C -> pushout_assoc_left
    := pushl' (pushr' f1 g1 o f2) g2 o pushr' f1 g1.
  Let pushlr : D -> pushout_assoc_left
    := pushr' (pushr' f1 g1 o f2) g2.
  Let pgluell : forall a1, pushll (f1 a1) = pushlm (g1 a1)
    := fun a1 => ap (pushl' (pushr' f1 g1 o f2) g2) (pglue' f1 g1 a1).
  Let pgluelr : forall a2, pushlm (f2 a2) = pushlr (g2 a2)
    := fun a2 => pglue' (pushr' f1 g1 o f2) g2 a2.

  Definition pushout_assoc_left_ind
             (P : pushout_assoc_left -> Type)
             (pushb : forall b, P (pushll b))
             (pushc : forall c, P (pushlm c))
             (pushd : forall d, P (pushlr d))
             (pusha1 : forall a1, (pgluell a1) # pushb (f1 a1) = pushc (g1 a1))
             (pusha2 : forall a2, (pgluelr a2) # pushc (f2 a2) = pushd (g2 a2))
    : forall x, P x.
  Proof.
    srefine (Pushout_ind _ _ pushd _).
    - srefine (Pushout_ind _ pushb pushc _).
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
      srefine (Pushout_rec _ _ pushd _).
      - srefine (Pushout_rec _ pushb pushc pusha1).
      - exact pusha2.
    Defined.

    Definition pushout_assoc_left_rec_beta_pgluell a1
      : ap pushout_assoc_left_rec (pgluell a1) = pusha1 a1.
    Proof.
      unfold pgluell.
      rewrite <- (ap_compose (pushl' (pushr' f1 g1 o f2) g2)
                             pushout_assoc_left_rec).
      change (ap (Pushout_rec P pushb pushc pusha1) (pglue' f1 g1 a1) = pusha1 a1).
      apply Pushout_rec_beta_pglue.
    Defined.

    Definition pushout_assoc_left_rec_beta_pgluelr a2
      : ap pushout_assoc_left_rec (pgluelr a2) = pusha2 a2.
    Proof.
      unfold pushout_assoc_left_rec, pgluelr.
      apply (Pushout_rec_beta_pglue (f := pushr' f1 g1 o f2) (g := g2)).
    Defined.

  End Pushout_Assoc_Left_Rec.

  Definition pushout_assoc_right := Pushout f1 (pushl' f2 g2 o g1).
  Let pushrl : B -> pushout_assoc_right
    := pushl' f1 (pushl' f2 g2 o g1).
  Let pushrm : C -> pushout_assoc_right
    := pushr' f1 (pushl' f2 g2 o g1) o pushl' f2 g2.
  Let pushrr : D -> pushout_assoc_right
    := pushr' f1 (pushl' f2 g2 o g1) o pushr' f2 g2.
  Let pgluerl : forall a1, pushrl (f1 a1) = pushrm (g1 a1)
    := fun a1 => pglue' f1 (pushl' f2 g2 o g1) a1.
  Let pgluerr : forall a2, pushrm (f2 a2) = pushrr (g2 a2)
    := fun a2 => ap (pushr' f1 (pushl' f2 g2 o g1)) (pglue' f2 g2 a2).

  Definition pushout_assoc_right_ind
             (P : pushout_assoc_right -> Type)
             (pushb : forall b, P (pushrl b))
             (pushc : forall c, P (pushrm c))
             (pushd : forall d, P (pushrr d))
             (pusha1 : forall a1, (pgluerl a1) # pushb (f1 a1) = pushc (g1 a1))
             (pusha2 : forall a2, (pgluerr a2) # pushc (f2 a2) = pushd (g2 a2))
    : forall x, P x.
  Proof.
    srefine (Pushout_ind _ pushb _ _).
    - srefine (Pushout_ind _ pushc pushd _).
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
      srefine (Pushout_rec _ pushb _ _).
      - srefine (Pushout_rec _ pushc pushd pusha2).
      - exact pusha1.
    Defined.

    Definition pushout_assoc_right_rec_beta_pgluerl a1
      : ap pushout_assoc_right_rec (pgluerl a1) = pusha1 a1.
    Proof.
      unfold pushout_assoc_right_rec, pgluerl.
      apply (Pushout_rec_beta_pglue (f := f1) (g := pushl' f2 g2 o g1)).
    Defined.

    Definition pushout_assoc_right_rec_beta_pgluerr a2
      : ap pushout_assoc_right_rec (pgluerr a2) = pusha2 a2.
    Proof.
      unfold pgluerr.
      rewrite <- (ap_compose (pushr' f1 (pushl' f2 g2 o g1))
                             pushout_assoc_right_rec).
      change (ap (Pushout_rec P pushc pushd pusha2) (pglue' f2 g2 a2) = pusha2 a2).
      apply Pushout_rec_beta_pglue.
    Defined.

  End Pushout_Assoc_Right_Rec.

  Definition equiv_pushout_assoc
    : Pushout (pushr' f1 g1 o f2) g2 <~> Pushout f1 (pushl' f2 g2 o g1).
  Proof.
    srefine (equiv_adjointify _ _ _ _).
    - exact (pushout_assoc_left_rec _ pushrl pushrm pushrr pgluerl pgluerr).
    - exact (pushout_assoc_right_rec _ pushll pushlm pushlr pgluell pgluelr).
    - abstract (
      srefine (pushout_assoc_right_ind
                 _ (fun _ => 1) (fun _ => 1) (fun _ => 1) _ _);
        intros; rewrite transport_paths_FlFr, ap_compose;
      [ rewrite pushout_assoc_right_rec_beta_pgluerl,
        pushout_assoc_left_rec_beta_pgluell
      | rewrite pushout_assoc_right_rec_beta_pgluerr,
        pushout_assoc_left_rec_beta_pgluelr ];
      rewrite concat_p1, ap_idmap; apply concat_Vp ).
    - abstract (
      srefine (pushout_assoc_left_ind
                 _ (fun _ => 1) (fun _ => 1) (fun _ => 1) _ _);
        intros; rewrite transport_paths_FlFr, ap_compose;
      [ rewrite pushout_assoc_left_rec_beta_pgluell,
        pushout_assoc_right_rec_beta_pgluerl
      | rewrite pushout_assoc_left_rec_beta_pgluelr,
        pushout_assoc_right_rec_beta_pgluerr ];
      rewrite concat_p1, ap_idmap; apply concat_Vp ).
  Defined.

End PushoutAssoc.

(** ** Pushouts of equvialences are equivalences *)

Global Instance isequiv_pushout_isequiv {A B C} (f : A -> B) (g : A -> C)
       `{IsEquiv _ _ f} : IsEquiv (pushr' f g).
Proof.
  srefine (isequiv_adjointify _ _ _ _).
  - srefine (Pushout_rec C (g o f^-1) idmap _).
    intros a; cbn; apply ap, eissect.
  - srefine (Pushout_ind _ _ _ _); cbn.
    + intros b; change (pushr' f g (g (f^-1 b)) = pushl b).
      transitivity (pushl' f g (f (f^-1 b))).
      * symmetry; apply pglue.
      * apply ap, eisretr.
    + intros c; reflexivity.
    + intros a.
      abstract (
      rewrite transport_paths_FlFr, ap_compose, !concat_pp_p;
      apply moveR_Vp; apply moveR_Vp;
      rewrite Pushout_rec_beta_pglue, eisadj, ap_idmap, concat_p1;
      rewrite <- ap_compose, <- (ap_compose g (pushr' f g));
      exact (concat_Ap (pglue' f g) (eissect f a)) ).
  - intros c; reflexivity.
Defined.

Global Instance isequiv_pushout_isequiv' {A B C} (f : A -> B) (g : A -> C)
       `{IsEquiv _ _ g} : IsEquiv (pushl' f g).
Proof.
  srefine (isequiv_adjointify _ _ _ _).
  - srefine (Pushout_rec B idmap (f o g^-1) _).
    intros a; cbn. symmetry; apply ap, eissect.
  - srefine (Pushout_ind _ _ _ _); cbn.
    + intros b; reflexivity.
    + intros c; change (pushl' f g (f (g^-1 c)) = pushr c).
      transitivity (pushr' f g (g (g^-1 c))).
      * apply pglue.
      * apply ap, eisretr.
    + intros a.
      abstract (
      rewrite transport_paths_FlFr, ap_compose, !concat_pp_p;
      apply moveR_Vp;
      rewrite Pushout_rec_beta_pglue, eisadj, ap_idmap, concat_1p, ap_V;
      apply moveL_Vp;
      rewrite <- !ap_compose;
      exact (concat_Ap (pglue' f g) (eissect g a)) ).
  - intros c; reflexivity.
Defined.
