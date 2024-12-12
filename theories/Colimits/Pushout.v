Require Import Basics.
Require Import Types.Paths Types.Forall Types.Arrow Types.Sigma Types.Sum Types.Universe.
Require Export Colimits.Coeq.
Require Import Homotopy.IdentitySystems.

Local Open Scope path_scope.

(** * Homotopy Pushouts *)

(** We define pushouts in terms of coproducts and coequalizers. *)

Definition Pushout@{i j k l} {A : Type@{i}} {B : Type@{j}} {C : Type@{k}}
  (f : A -> B) (g : A -> C) : Type@{l}
  := Coeq@{l l _} (inl o f) (inr o g).

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
    := Coeq_ind P (sum_ind (P o push) pushb pushc) pusha.

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
Arguments Pushout_ind_beta_pglue : simpl never.
(** However, we do allow [Pushout_ind] to simplify, as it computes on point constructors. *)

Definition Pushout_rec {A B C} {f : A -> B} {g : A -> C} (P : Type)
  (pushb : B -> P)
  (pushc : C -> P)
  (pusha : forall a : A, pushb (f a) = pushc (g a))
  : @Pushout A B C f g -> P
  := @Coeq_rec _ _ (inl o f) (inr o g) P (sum_rec P pushb pushc) pusha.

Definition Pushout_rec_beta_pglue {A B C f g} (P : Type)
  (pushb : B -> P)
  (pushc : C -> P)
  (pusha : forall a : A, pushb (f a) = pushc (g a))
  (a : A)
  : ap (Pushout_rec P pushb pushc pusha) (pglue a) = pusha a.
Proof.
  nrapply Coeq_rec_beta_cglue.
Defined.

(** ** Universal property *)

Definition pushout_unrec {A B C P} (f : A -> B) (g : A -> C)
           (h : Pushout f g -> P)
  : {psh : (B -> P) * (C -> P) &
           forall a, fst psh (f a) = snd psh (g a)}.
Proof.
  exists (h o pushl, h o pushr).
  intros a; cbn.
  exact (ap h (pglue a)).
Defined.

Definition pushout_rec_unrec {A B C} (f : A -> B) (g : A -> C) P
  (e : Pushout f g -> P)
  : Pushout_rec P (e o pushl) (e o pushr) (fun a => ap e (pglue a)) == e.
Proof.
  snrapply Pushout_ind.
  1, 2: reflexivity.
  intro a; cbn beta.
  apply transport_paths_FlFr'.
  apply equiv_p1_1q.
  nrapply Pushout_rec_beta_pglue.
Defined.

Definition isequiv_Pushout_rec `{Funext} {A B C} (f : A -> B) (g : A -> C) P
  : IsEquiv (fun p : {psh : (B -> P) * (C -> P) &
                            forall a, fst psh (f a) = snd psh (g a) }
             => Pushout_rec P (fst p.1) (snd p.1) p.2).
Proof.
  srefine (isequiv_adjointify _ (pushout_unrec f g) _ _).
  - intro e. apply path_arrow. apply pushout_rec_unrec.
  - intros [[pushb pushc] pusha]; unfold pushout_unrec; cbn.
    snrapply path_sigma'.
    + reflexivity.
    + cbn. apply path_forall; intros a.
      apply Pushout_rec_beta_pglue.
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

Lemma sect_pushout_sym_map {A B C f g}
  : (@pushout_sym_map A B C f g) o (@pushout_sym_map A C B g f) == idmap.
Proof.
  srapply @Pushout_ind.
  - intros; reflexivity.
  - intros; reflexivity.
  - intro a.
    simpl.
    abstract (rewrite transport_paths_FFlr, Pushout_rec_beta_pglue, ap_V, Pushout_rec_beta_pglue; hott_simpl).
Defined.

Definition pushout_sym {A B C} {f : A -> B} {g : A -> C}
  : Pushout f g <~> Pushout g f :=
equiv_adjointify pushout_sym_map pushout_sym_map sect_pushout_sym_map sect_pushout_sym_map.

(** ** Functoriality *)

Definition functor_pushout
  {A B C} {f : A -> B} {g : A -> C}
  {A' B' C'} {f' : A' -> B'} {g' : A' -> C'}
  (h : A -> A') (k : B -> B') (l : C -> C')
  (p : k o f == f' o h) (q : l o g == g' o h)
  : Pushout f g -> Pushout f' g'.
Proof.
  unfold Pushout; srapply functor_coeq.
  - exact h.
  - exact (functor_sum k l).
  - intros a; cbn.
    apply ap, p.
  - intros a; cbn.
    apply ap, q.
Defined.

Lemma functor_pushout_homotopic
  {A B C : Type} {f : A -> B} {g : A -> C}
  {A' B' C' : Type} {f' : A' -> B'} {g' : A' -> C'}
  {h h' : A -> A'} {k k' : B -> B'} {l l' : C -> C'}
  {p : k o f == f' o h} {q : l o g == g' o h}
  {p' : k' o f == f' o h'} {q' : l' o g == g' o h'}
  (t : h == h') (u : k == k') (v : l == l')
  (i : forall a, p a @ (ap f') (t a) = u (f a) @ p' a)
  (j : forall a, q a @ (ap g') (t a) = v (g a) @ q' a)
  : functor_pushout h k l p q == functor_pushout h' k' l' p' q'.
Proof.
  srapply functor_coeq_homotopy.
  1: exact t.
  1: exact (functor_sum_homotopic u v).
  1,2: intros b; simpl.
  1,2: refine (_ @ ap_pp _ _ _ @ ap _ (ap_compose _ _ _)^).
  1,2: refine ((ap_pp _ _ _)^ @ ap _ _^).
  1: exact (i b).
  exact (j b).
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
  apply (Build_Contr _ (pushl (center B))).
  srapply Pushout_ind.
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

  Local Definition esp1 : { x : X & Pushout (f x) (g x) }
             -> Pushout (functor_sigma idmap f) (functor_sigma idmap g).
  Proof.
    intros [x p].
    srefine (Pushout_rec _ _ _ _ p).
    + intros b. exact (pushl (x;b)).
    + intros c. exact (pushr (x;c)).
    + intros a; cbn. exact (pglue (x;a)).
  Defined.

  Local Definition esp1_beta_pglue (x : X) (a : A x)
    : ap esp1 (path_sigma' (fun x => Pushout (f x) (g x)) 1 (pglue a))
      = pglue (x;a).
  Proof.
    rewrite (ap_path_sigma (fun x => Pushout (f x) (g x))
                           (fun x a => esp1 (x;a)) 1 (pglue a)); cbn.
    rewrite !concat_p1.
    unfold esp1; rewrite Pushout_rec_beta_pglue.
    reflexivity.
  Qed.

  Local Definition esp2 : Pushout (functor_sigma idmap f) (functor_sigma idmap g)
             -> { x : X & Pushout (f x) (g x) }.
  Proof.
    srefine (Pushout_rec _ _ _ _).
    + exact (functor_sigma idmap (fun x => @pushl _ _ _ (f x) (g x))).
    + exact (functor_sigma idmap (fun x => @pushr _ _ _ (f x) (g x))).
    + intros [x a]; unfold functor_sigma; cbn.
      srefine (path_sigma' _ 1 _); cbn.
      apply pglue.
  Defined.

  Local Definition esp2_beta_pglue (x : X) (a : A x)
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
        refine (transport_paths_FFlr _ _ @ _).
        refine (concat_p1 _ @@ 1 @ _).
        apply moveR_Vp; symmetry.
        refine (concat_p1 _ @ _).
        refine (ap _ (esp2_beta_pglue _ _) @ _).
        apply esp1_beta_pglue.
    - intros [x a]; revert a.
      srefine (Pushout_ind _ _ _ _); cbn.
      + reflexivity.
      + reflexivity.
      + intros a.
        rewrite transport_paths_FlFr.
        rewrite concat_p1; apply moveR_Vp; rewrite concat_p1.
        rewrite (ap_compose (exist _ x) (esp2 o esp1)).
        rewrite (ap_compose esp1 esp2).
        rewrite (ap_exist (fun x => Pushout (f x) (g x)) x _ _ (pglue a)).
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
        intros; simpl; rewrite transport_paths_FlFr, ap_compose;
      [ rewrite pushout_assoc_right_rec_beta_pgluerl,
        pushout_assoc_left_rec_beta_pgluell
      | rewrite pushout_assoc_right_rec_beta_pgluerr,
        pushout_assoc_left_rec_beta_pgluelr ];
      rewrite concat_p1, ap_idmap; apply concat_Vp ).
    - abstract (
      srefine (pushout_assoc_left_ind
                 _ (fun _ => 1) (fun _ => 1) (fun _ => 1) _ _);
        intros; simpl; rewrite transport_paths_FlFr, ap_compose;
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

(** ** Descent *)

(** We study "equifibrant" type families over a span [f : A -> B] and [g : A -> C].  By univalence, the descent property tells us that these type families correspond to type families over the pushout, and we obtain an induction principle for such type families. Dependent descent data over some particular descent data are "equifibrant" type families over this descent data.  The "equifibrancy" is only taken over the span [f : A -> B] and [g : A -> C], but there is an extra level of dependency coming from the descent data.  In this case, we obtain an induction and recursion principle, but only with a computation rule for the recursion principle.

The theory of descent is interesting to consider in itself.  However, we will use it as a means to structure the code, and to obtain induction and recursion principles that are valuable in proving the flattening lemma, and characterizing path spaces.  Thus we will gloss over the bigger picture, and not consider equivalences of descent data, nor homotopies of their sections.  We will also not elaborate on uniqueness of the induced families.

It's possible to prove the results in the Descent, Flattening and Paths Sections without univalence, by replacing all equivalences with paths, but in practice these results will be used with equivalences as input, making the form below more convenient.  See https://github.com/HoTT/Coq-HoTT/pull/2147#issuecomment-2521570830 for further information. *)

Section Descent.

  Context `{Univalence}.

  (** Descent data over [f : A -> B] and [g : A -> C] are "equifibrant" or "cartesian" type families [pod_faml : B -> Type] and [pod_famr : C -> Type].  This means that if [a : A], then the fibers [pod_faml (f a)] and [pod_famr (g a)] are equivalent, witnessed by [pod_e]. *)
  Record poDescent {A B C : Type} {f : A -> B} {g : A -> C} := {
    pod_faml (b : B) : Type;
    pod_famr (c : C) : Type;
    pod_e (a : A) : pod_faml (f a) <~> pod_famr (g a)
  }.

  Global Arguments poDescent {A B C} f g.

  (** Let [A], [B], and [C] be types, with a morphisms [f : A -> B] and [g : A -> C].  *)
  Context {A B C : Type} {f : A -> B} {g : A -> C}.

  (** Descent data induces a type family over [Pushout f g]. *)
  Definition fam_podescent (Pe : poDescent f g)
    : Pushout f g -> Type.
  Proof.
    snrapply (Pushout_rec _ (pod_faml Pe) (pod_famr Pe)).
    intro a.
    exact (path_universe_uncurried (pod_e Pe a)).
  Defined.

  (** A type family over [Pushout f g] induces descent data. *)
  Definition podescent_fam (P : Pushout f g -> Type) : poDescent f g.
  Proof.
    snrapply Build_poDescent.
    - exact (P o pushl).
    - exact (P o pushr).
    - intro a.
      exact (equiv_transport P (pglue a)).
  Defined.

  (** Transporting over [fam_podescent] along [pglue a] is given by [pod_e]. *)
  Definition transport_fam_podescent_pglue
    (Pe : poDescent f g) (a : A) (pf : pod_faml Pe (f a))
    : transport (fam_podescent Pe) (pglue a) pf = pod_e Pe a pf.
  Proof.
    nrapply transport_path_universe'.
    nrapply Pushout_rec_beta_pglue.
  Defined.

  (** A section on the descent data are fiberwise sections that respects the equivalences. *)
  Record poDescentSection {Pe : poDescent f g} := {
    pods_sectl (b : B) : pod_faml Pe b;
    pods_sectr (c : C) : pod_famr Pe c;
    pods_e (a : A)
      : pod_e Pe a (pods_sectl (f a)) = pods_sectr (g a)
  }.

  Global Arguments poDescentSection Pe : clear implicits.

  (** A descent section induces a genuine section of [fam_cdescent Pe]. *)
  Definition podescent_ind {Pe : poDescent f g}
    (s : poDescentSection Pe)
    : forall (x : Pushout f g), fam_podescent Pe x.
  Proof.
    snrapply (Pushout_ind _ (pods_sectl s) (pods_sectr s)).
    intro a.
    exact (transport_fam_podescent_pglue Pe a _ @ pods_e s a).
  Defined.

  (** We record its computation rule *)
  Definition podescent_ind_beta_pglue {Pe : poDescent f g}
    (s : poDescentSection Pe) (a : A)
    : apD (podescent_ind s) (pglue a) = transport_fam_podescent_pglue Pe a _ @ pods_e s a
    := Pushout_ind_beta_pglue _ (pods_sectl s) (pods_sectr s) _ _.

  (** Dependent descent data over descent data [Pe : poDescent f g] consists of a type families [podd_faml : forall (b : B), pod_faml Pe b -> Type] and [podd_famr : forall (c : C), pod_famr Pe c -> Type] together with coherences [podd_e a pf]. *)
  Record poDepDescent {Pe : poDescent f g} := {
    podd_faml (b : B) (pb : pod_faml Pe b) : Type;
    podd_famr (c : C) (pc : pod_famr Pe c) : Type;
    podd_e (a : A) (pf : pod_faml Pe (f a))
      : podd_faml (f a) pf <~> podd_famr (g a) (pod_e Pe a pf)
  }.

  Global Arguments poDepDescent Pe : clear implicits.

  (** A dependent type family over [fam_podescent Pe] induces dependent descent data over [Pe]. *)
  Definition podepdescent_fam {Pe : poDescent f g}
    (Q : forall (x : Pushout f g), (fam_podescent Pe) x -> Type)
    : poDepDescent Pe.
  Proof.
    snrapply Build_poDepDescent.
    - intro b; cbn.
      exact (Q (pushl b)).
    - intros c; cbn.
      exact (Q (pushr c)).
    - intros a pf.
      exact (equiv_transportDD (fam_podescent Pe) Q
               (pglue a) (transport_fam_podescent_pglue Pe a pf)).
  Defined.

  (** Dependent descent data over [Pe] induces a dependent type family over [fam_podescent Pe]. *)
  Definition fam_podepdescent {Pe : poDescent f g} (Qe : poDepDescent Pe)
    : forall (x : Pushout f g), (fam_podescent Pe x) -> Type.
  Proof.
    snrapply Pushout_ind.
    - exact (podd_faml Qe).
    - exact (podd_famr Qe).
    - intro a.
      nrapply (moveR_transport_p _ (pglue a)).
      funext pf.
      rhs nrapply transport_arrow_toconst.
      rhs nrefine (ap (podd_famr _ _) _).
      + exact (path_universe (podd_e _ _ _)).
      + lhs nrapply (ap (fun x => (transport _ x _)) (inv_V (pglue _))).
        nrapply (transport_fam_podescent_pglue _ _ _).
  Defined.

  (** A section of dependent descent data [Qe : poDepDescent Pe] are fiberwise sections [podds_sectl] and [podds_sectr], together with coherences [pods_e]. *)
  Record poDepDescentSection {Pe : poDescent f g} {Qe : poDepDescent Pe} := {
    podds_sectl (b : B) (pb : pod_faml Pe b) : podd_faml Qe b pb;
    podds_sectr (c : C) (pc : pod_famr Pe c) : podd_famr Qe c pc;
    podds_e (a : A) (pf : pod_faml Pe (f a))
      : podd_e Qe a pf (podds_sectl (f a) pf) = podds_sectr (g a) (pod_e Pe a pf)
  }.

  Global Arguments poDepDescentSection {Pe} Qe.

  (** A dependent descent section induces a genuine section over the total space of [induced_fam_pod Pe]. *)
  Definition podepdescent_ind {Pe : poDescent f g}
    {Q : forall (x : Pushout f g), (fam_podescent Pe) x -> Type}
    (s : poDepDescentSection (podepdescent_fam Q))
    : forall (x : Pushout f g) (px : fam_podescent Pe x), Q x px.
    Proof.
      nrapply (Pushout_ind _ (podds_sectl s) (podds_sectr s) _).
      intro a.
      apply dpath_forall.
      intro pf.
      apply (equiv_inj (transport (Q (pushr (g a))) (transport_fam_podescent_pglue Pe a pf))).
      rhs nrapply (apD (podds_sectr s (g a)) (transport_fam_podescent_pglue Pe a pf)).
      exact (podds_e s a pf).
    Defined.

  (** The data for a section into a constant type family. *)
  Record poDepDescentConstSection {Pe : poDescent f g} {Q : Type} := {
    poddcs_sectl (b : B) (pb : pod_faml Pe b) : Q;
    poddcs_sectr (c : C) (pc : pod_famr Pe c) : Q;
    poddcs_e (a : A) (pf : pod_faml Pe (f a))
      : poddcs_sectl (f a) pf = poddcs_sectr (g a) (pod_e Pe a pf)
  }.

  Global Arguments poDepDescentConstSection Pe Q : clear implicits.

  (** The data for a section of a constant family induces a section over the total space of [fam_podescent Pe]. *)
  Definition podepdescent_rec {Pe : poDescent f g} {Q : Type}
    (s : poDepDescentConstSection Pe Q)
    : forall (x : Pushout f g), fam_podescent Pe x -> Q.
  Proof.
    snrapply (Pushout_ind _ (poddcs_sectl s) (poddcs_sectr s)); cbn.
    intro a.
    nrapply dpath_arrow.
    intro pf.
    lhs nrapply transport_const.
    rhs nrapply (ap _ (transport_fam_podescent_pglue Pe a pf)).
    exact (poddcs_e s a pf).
  Defined.

  (** Here is the computation rule on paths. *)
  Definition podepdescent_rec_beta_pglue {Pe : poDescent f g} {Q : Type}
    (s : poDepDescentConstSection Pe Q)
    (a : A) {pf : pod_faml Pe (f a)} {pg : pod_famr Pe (g a)} (pa : pod_e Pe a pf = pg)
    : ap (sig_rec (podepdescent_rec s)) (path_sigma _ (pushl (f a); pf) (pushr (g a); pg) (pglue a) (transport_fam_podescent_pglue Pe a pf @ pa))
      = poddcs_e s a pf @ ap (poddcs_sectr s (g a)) pa.
  Proof.
    Open Scope long_path_scope.
    destruct pa.
    rhs nrapply concat_p1.
    lhs nrapply ap_sig_rec_path_sigma.
    lhs nrapply (ap (fun x => _ (ap10 x _) @ _)).
    1: nrapply Pushout_ind_beta_pglue.
    do 3 lhs nrapply concat_pp_p.
    apply moveR_Vp.
    lhs nrefine (1 @@ (1 @@ (_ @@ 1))).
    1: nrapply (ap10_dpath_arrow (fam_podescent Pe) (fun _ => Q) (pglue a)).
    lhs nrefine (1 @@ _).
    { lhs nrapply (1 @@ concat_pp_p _ _ _).
      lhs nrapply (1 @@ concat_pp_p _ _ _).
      lhs nrapply concat_V_pp.
      lhs nrapply (1 @@ concat_pp_p _ _ _).
      rewrite concat_p1.
      nrapply (1 @@ (1 @@ concat_pV_p _ _)). }
    nrapply concat_V_pp.
    Close Scope long_path_scope.
  Defined.

End Descent.

(** ** The flattening lemma *)

(** We saw above that given descent data [Pe] over a span [f : A -> B] and [g : A -> C], we obtained a type family [fam_podescent Pe] over the pushout.  The flattening lemma describes the total space [sig (fam_podescent Pe)] of this type family as a pushout of [sig (pod_faml Pe)] and [sig (pod_famr Pe)] by a certain span.  This follows from the work above, which shows that [sig (fam_podescent Pe)] has the same universal property as this pushout. *)

Section Flattening.

  Context `{Univalence} {A B C : Type} {f : A -> B} {g : A -> C} (Pe : poDescent f g).

  (** We mimic the constructors of [Pushout] for the total space.  Here are the point constructors, in curried form. *)
  Definition flatten_podl {b : B} (pb : pod_faml Pe b) : sig (fam_podescent Pe)
    := (pushl b; pb).

  Definition flatten_podr {c : C} (pc : pod_famr Pe c) : sig (fam_podescent Pe)
    := (pushr c; pc).

  (** And here is the path constructor. *)
  Definition flatten_pod_glue (a : A)
    {pf : pod_faml Pe (f a)} {pg : pod_famr Pe (g a)} (pa : pod_e Pe a pf = pg)
    : flatten_podl pf = flatten_podr pg.
  Proof.
    snrapply path_sigma.
    - by apply pglue.
    - lhs nrapply transport_fam_podescent_pglue.
      exact pa.
  Defined.

  (** Now that we've shown that [fam_podescent Pe] acts like a [Pushout] of [sig (pod_faml Pe)] and [sig (pod_famr Pe)] by an appropriate span, we can use this to prove the flattening lemma.  The maps back and forth are very easy so this could almost be a formal consequence of the induction principle. *)
  Lemma equiv_pod_flatten : sig (fam_podescent Pe) <~>
    Pushout (functor_sigma f (fun _ => idmap)) (functor_sigma g (pod_e Pe)).
  Proof.
    snrapply equiv_adjointify.
    - snrapply sig_rec.
      snrapply podepdescent_rec.
      snrapply Build_poDepDescentConstSection.
      + exact (fun b pb => pushl (b; pb)).
      + exact (fun c pc => pushr (c; pc)).
      + intros a pf.
      cbn.
      apply (@pglue _ _ _
        (functor_sigma f (fun _ => idmap)) (functor_sigma g (pod_e Pe)) (a; pf)).
    - snrapply Pushout_rec.
      + exact (fun '(b; pb) => (pushl b; pb)).
      + exact (fun '(c; pc) => (pushr c; pc)).
      + intros [a pf]; cbn.
        apply (flatten_pod_glue a 1).
    - snrapply Pushout_ind.
      1, 2: reflexivity.
      intros [a pf]; cbn.
      nrapply transport_paths_FFlr'; apply equiv_p1_1q.
      rewrite Pushout_rec_beta_pglue.
      lhs nrapply podepdescent_rec_beta_pglue.
      nrapply concat_p1.
    - intros [x px]; revert x px.
      snrapply podepdescent_ind.
      snrapply Build_poDepDescentSection.
      + by intros b pb.
      + by intros c pc.
      + intros a pf; cbn.
        lhs nrapply transportDD_is_transport.
        nrapply transport_paths_FFlr'; apply equiv_p1_1q.
        rewrite <- (concat_p1 (transport_fam_podescent_pglue _ _ _)).
        rewrite podepdescent_rec_beta_pglue. (* This needs to be in the form [transport_fam_podescent_gqglue Pe r pa @ p] to work, and the other [@ 1] introduced comes in handy as well. *)
        lhs nrapply (ap _ (concat_p1 _)).
        nrapply (Pushout_rec_beta_pglue _ _ _ _ (a; pf)).
  Defined.

End Flattening.

(** ** Characterization of path spaces *)

(** A pointed type family over a pushout has an identity system structure precisely when its associated descent data satisfies Kraus and von Raumer's induction principle, https://arxiv.org/pdf/1901.06022. *)

Section Paths.

  (** Let [f : A -> B] and [g : A -> C] be a span, with a distinguished point [b0 : B].  We could let the distinguished point be in [C], but this is symmetric by exchanging the roles of [f] and [g].  Let [Pe : poDescent f g] be descent data over [f g] with a distinguished point [p0 : pod_faml Pe b0].  Assume that any dependent descent data [Qe : poDepDescent Pe] with a distinguished point [q0 : podd_faml Qe b0 p0] has a section that respects the distinguished points.  This is the induction principle provided by Kraus and von Raumer. *)
  Context `{Univalence} {A B C : Type} {f : A -> B} {g : A -> C} (b0 : B)
    (Pe : poDescent f g) (p0 : pod_faml Pe b0)
    (based_podepdescent_ind : forall (Qe : poDepDescent Pe) (q0 : podd_faml Qe b0 p0),
      poDepDescentSection Qe)
    (based_podepdescent_ind_beta : forall (Qe : poDepDescent Pe) (q0 : podd_faml Qe b0 p0),
      podds_sectl (based_podepdescent_ind Qe q0) b0 p0 = q0).

  (** Under these hypotheses, we get an identity system structure on [fam_podescent Pe]. *)
  Local Instance idsys_flatten_podescent
    : @IsIdentitySystem _ (pushl b0) (fam_podescent Pe) p0.
  Proof.
    snrapply Build_IsIdentitySystem.
    - intros Q q0 x px.
      snrapply podepdescent_ind.
      by apply based_podepdescent_ind.
    - intros Q q0; cbn.
      nrapply (based_podepdescent_ind_beta (podepdescent_fam Q)).
  Defined.

  (** It follows that the fibers [fam_podescent Pe x] are equivalent to path spaces [(pushl a0) = x]. *)
  Definition fam_podescent_equiv_path (x : Pushout f g)
    : (pushl b0) = x <~> fam_podescent Pe x
    := @equiv_transport_identitysystem _ (pushl b0) (fam_podescent Pe) p0 _ x.

End Paths.
