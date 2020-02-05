(* -*- mode: coq; mode: visual-line -*- *)
(** * Basic facts about fibrations *)

Require Import HoTT.Basics HoTT.Types HProp EquivalenceVarieties.

Local Open Scope equiv_scope.
Local Open Scope path_scope.

(* ** Homotopy fibers *)

(** Paths in homotopy fibers can be constructed using [path_sigma] and [transport_paths_Fl]. *)

Definition equiv_path_hfiber {A B : Type} {f : A -> B} {y : B}
  (x1 x2 : hfiber f y)
: { q : x1.1 = x2.1 & x1.2 = ap f q @ x2.2 } <~> (x1 = x2).
Proof.
  refine (equiv_path_sigma _ _ _ oE _).
  refine (equiv_functor_sigma' 1 _).
  intros p; simpl.
  refine (_ oE equiv_moveR_Vp _ _ _).
  exact (equiv_concat_l (transport_paths_Fl _ _) _).
Defined.

Definition path_hfiber_uncurried {A B : Type} {f : A -> B} {y : B}
  {x1 x2 : hfiber f y}
: { q : x1.1 = x2.1 & x1.2 = ap f q @ x2.2 } -> (x1 = x2)
  := equiv_path_hfiber x1 x2.

Definition path_hfiber {A B : Type} {f : A -> B} {y : B}
  {x1 x2 : hfiber f y} (q : x1.1 = x2.1) (r : x1.2 = ap f q @ x2.2)
: x1 = x2
:= path_hfiber_uncurried (q;r).

(** If we rearrange this a bit, then it characterizes the fibers of [ap]. *)

Definition hfiber_ap {A B : Type} {f : A -> B} {x1 x2 : A}
           (p : f x1 = f x2)
: hfiber (ap f) p <~> ((x1 ; p) = (x2 ; 1) :> hfiber f (f x2)).
Proof.
  refine (equiv_path_hfiber (x1;p) (x2;1%path) oE _).
  unfold hfiber; simpl.
  refine (equiv_functor_sigma' 1 _); intros q.
  refine (_ oE equiv_path_inverse _ _).
  exact (equiv_concat_r (concat_p1 _)^ _).
Defined.

(** Homotopic maps have equivalent fibers. *)

Definition equiv_hfiber_homotopic
           {A B : Type} (f g : A -> B) (h : f == g) (b : B)
: hfiber f b <~> hfiber g b.
Proof.
  refine (Build_Equiv _ _ (fun fx => (fx.1 ; (h fx.1)^ @ fx.2)) _).
  refine (isequiv_adjointify _ (fun gx => (gx.1 ; (h gx.1) @ gx.2)) _ _);
    intros [a p]; simpl.
  - apply ap, concat_V_pp.
  - apply ap, concat_p_Vp.
Defined.

(** Commutative squares induce maps between fibers. *)

Definition functor_hfiber {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h) (b : B)
: hfiber f b -> hfiber g (k b).
Proof.
  unshelve rapply @functor_sigma.
  - exact h.
  - intros a e; exact ((p a)^ @ ap k e).
Defined.

(** ** The 3x3 lemma *)

Definition hfiber_functor_hfiber {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h) (b : B) (c : C) (q : g c = k b)
: hfiber (functor_hfiber p b) (c;q)
  <~> hfiber (functor_hfiber (fun x => (p x)^) c) (b;q^).
Proof.
  unfold hfiber, functor_hfiber, functor_sigma.
  refine (_ oE (equiv_sigma_assoc _ _)^-1).
  refine (equiv_sigma_assoc _ _ oE _).
  apply (equiv_functor_sigma' 1); intros a; cbn.
  refine (_ oE
         (equiv_functor_sigma'
            (P := fun r => { s : h a = c & s # ((p a)^ @ ap k r) = q })
            1 (fun r => equiv_path_sigma _
                          (h a; (p a)^ @ ap k r) (c; q)))^-1).
  refine (equiv_functor_sigma'
            (P := fun r => { s : f a = b & s # (((p a)^)^ @ ap g r) = q^ })
            1 (fun r => equiv_path_sigma _
                          (f a; ((p a)^)^ @ ap g r) (b; q^)) oE _).
  refine (equiv_sigma_symm _ oE _).
  refine (equiv_functor_sigma' 1 _); intros r.
  refine (equiv_functor_sigma' 1 _); intros s; cbn.
  refine (equiv_concat_l (transport_paths_Fl _ _) _ oE _).
  refine (_ oE (equiv_concat_l (transport_paths_Fl _ _) _)^-1).
  refine ((equiv_ap inverse _ _)^-1 oE _).
  refine (equiv_concat_r (inv_V q)^ _ oE _).
  apply equiv_concat_l.
  abstract (rewrite !inv_pp, !inv_V, concat_pp_p; reflexivity).
Defined.

(** ** Replacing a map with a fibration *)

Definition equiv_fibration_replacement  {B C} (f:C ->B):
  C <~> {y:B & hfiber f y}.
Proof.
  simple refine (Build_Equiv _ _ _ (Build_IsEquiv
               C {y:B & {x:C & f x = y}}
               (fun c => (f c; (c; idpath)))
               (fun c => c.2.1)
               _
               (fun c => idpath)
               _)).
  - intros [? [? []]]; reflexivity.
  - reflexivity.
Defined.

Definition hfiber_fibration {X} (x : X) (P:X->Type):
    P x <~> @hfiber (sigT P) X pr1 x.
Proof.
  simple refine (Build_Equiv _ _ _ (Build_IsEquiv
               (P x) { z : sigT P & z.1 = x }
               (fun Px => ((x; Px); idpath))
               (fun Px => transport P Px.2 Px.1.2)
               _
               (fun Px => idpath)
               _)).
  - intros [[] []]; reflexivity.
  - reflexivity.
Defined.

(** ** Exercise 4.4: The unstable octahedral axiom. *)

Section UnstableOctahedral.

  Context (n:trunc_index) {A B C} (f : A -> B) (g : B -> C).

  Definition hfiber_compose_map (b : B)
  : hfiber (g o f) (g b) -> hfiber g (g b)
    := fun x => (f x.1 ; x.2).

  Definition hfiber_hfiber_compose_map (b : B)
  : hfiber (hfiber_compose_map b) (b;1) <~> hfiber f b.
  Proof.
    unfold hfiber, hfiber_compose_map.
    refine (_ oE (equiv_sigma_assoc _ _)^-1).
    refine (equiv_functor_sigma' 1 _); intros a; simpl.
    refine (equiv_compose' (B := {p : g (f a) = g b & {q : f a = b & transport (fun y => g y = g b) q p = 1}}) _ _).
    - refine (_ oE equiv_sigma_symm _).
      apply equiv_sigma_contr; intros p.
      destruct p; simpl; exact _.
    - refine (equiv_functor_sigma' 1
                (fun p => (equiv_path_sigma _ _ _)^-1)).
  Defined.

  Definition hfiber_compose (c : C)
  : hfiber (g o f) c <~> { w : hfiber g c & hfiber f w.1 }.
  Proof.
    unfold hfiber.
    refine (equiv_sigma_assoc
              (fun x => g x = c) (fun w => {x : A & f x = w.1}) oE _).
    refine (equiv_functor_sigma' 1
             (fun b => equiv_sigma_symm (fun a p => f a = b)) oE _).
    refine (equiv_sigma_symm _ oE _).
    refine (equiv_functor_sigma' 1 _); intros a.
    refine (equiv_functor_sigma' 1
              (fun b => equiv_sigma_symm0 _ _) oE _); simpl.
    refine ((equiv_sigma_assoc' _ _)^-1 oE _).
    symmetry.
    exact (equiv_contr_sigma (fun (w:{b:B & f a = b}) => g w.1 = c)).
  Defined.

  Global Instance istruncmap_compose `{!IsTruncMap n g} `{!IsTruncMap n f}
    : IsTruncMap n (g o f).
  Proof.
    intros c.
    exact (trunc_equiv _ (hfiber_compose c)^-1).
  Defined.

End UnstableOctahedral.


(** ** Fibers of constant functions *)
Definition hfiber_constant A {B} (y y' : B)
  : hfiber (fun _ : A => y) y' <~> A * (y = y')
  := equiv_sigma_prod0 A (y = y').

Global Instance istruncmap_constant n {A B} `{!IsTrunc n A}
       (y : B) `{!forall y', IsTrunc n (y = y')}
  : IsTruncMap n (fun _ : A => y)
  := fun y' => _.

(** ** Fibers of [functor_sigma] *)

Definition hfiber_functor_sigma {A B} (P : A -> Type) (Q : B -> Type)
           (f : A -> B) (g : forall a, P a -> Q (f a))
           (b : B) (v : Q b)
: (hfiber (functor_sigma f g) (b; v)) <~>
  {w : hfiber f b & hfiber (g w.1) ((w.2)^ # v)}.
Proof.
  unfold hfiber, functor_sigma.
  equiv_via ({x : sigT P & {p : f x.1 = b & p # (g x.1 x.2) = v}}).
  { refine (equiv_functor_sigma' 1
             (fun x => (equiv_path_sigma Q _ _)^-1)). }
  refine (_ oE (equiv_sigma_assoc P _)^-1).
  equiv_via ({a:A & {q:f a = b & {p : P a & q # (g a p) = v}}}).
  { refine (equiv_functor_sigma' 1 (fun a => _)); simpl.
    refine (equiv_sigma_symm _). }
  refine (_ oE (equiv_sigma_assoc' _ _)).
  refine (equiv_functor_sigma' 1 _);
    intros [a p]; simpl.
  refine (equiv_functor_sigma' 1 _);
    intros u; simpl.
  apply equiv_moveL_transport_V.
Defined.

Global Instance istruncmap_functor_sigma n {A B P Q}
       (f : A -> B) (g : forall a, P a -> Q (f a))
       {Hf : IsTruncMap n f} {Hg : forall a, IsTruncMap n (g a)}
  : IsTruncMap n (functor_sigma f g).
Proof.
  intros [a b].
  exact (trunc_equiv _ (hfiber_functor_sigma _ _ _ _ _ _)^-1).
Defined.

(** Theorem 4.7.6 *)
Definition hfiber_functor_sigma_idmap {A} (P Q : A -> Type)
           (g : forall a, P a -> Q a)
           (b : A) (v : Q b)
: (hfiber (functor_sigma idmap g) (b; v)) <~>
   hfiber (g b) v.
Proof.
  refine (_ oE hfiber_functor_sigma P Q idmap g b v).
  exact (equiv_contr_sigma
           (fun (w:hfiber idmap b) => hfiber (g w.1) (transport Q (w.2)^ v))).
Defined.

Definition istruncmap_from_functor_sigma n {A P Q}
           (g : forall a : A, P a -> Q a)
           `{!IsTruncMap n (functor_sigma idmap g)}
  : forall a, IsTruncMap n (g a).
Proof.
  intros a v.
  exact (trunc_equiv' _ (hfiber_functor_sigma_idmap _ _ _ _ _)).
Defined.

Definition isequiv_from_functor_sigma {A} (P Q : A -> Type)
           (g : forall a, P a -> Q a)
           `{IsEquiv _ _ (functor_sigma idmap g)}
: forall (a : A), IsEquiv (g a).
Proof.
  intros a; apply isequiv_fcontr.
  apply istruncmap_from_functor_sigma.
  red; by apply fcontr_isequiv.
Defined.

(** Theorem 4.7.7 *)
Definition equiv_total_iff_equiv_fiberwise {A} (P Q : A -> Type)
           (g : forall a, P a -> Q a)
: IsEquiv (functor_sigma idmap g) <-> forall a, IsEquiv (g a).
Proof.
  split.
  - apply isequiv_from_functor_sigma.
  - intro H. apply isequiv_functor_sigma.
Defined.

(** ** Fibers of [functor_prod] *)
Definition hfiber_functor_prod {A B C D}
           (f : A -> B) (g : C -> D) y
  : hfiber (Prod.functor_prod f g) y <~> (hfiber f (fst y) * hfiber g (snd y)).
Proof.
  unfold Prod.functor_prod.
  srefine (equiv_adjointify _ _ _ _).
  - exact (fun x => ((fst x.1; ap fst x.2), (snd x.1; ap snd x.2))).
  - refine (fun xs => (((fst xs).1, (snd xs).1); _)).
    apply Prod.path_prod;simpl.
    + exact (fst xs).2.
    + exact (snd xs).2.
  - destruct y as [y1 y2]; intros [[x1 p1] [x2 p2]].
    simpl in *. destruct p1,p2. reflexivity.
  - intros [[x1 x2] p]. destruct p;cbn. reflexivity.
Defined.

Global Instance istruncmap_functor_prod n {A B C D}
       (f : A -> B) (g : C -> D)
       `{!IsTruncMap n f} `{!IsTruncMap n g}
  : IsTruncMap n (Prod.functor_prod f g).
Proof.
  intros y.
  exact (trunc_equiv _ (hfiber_functor_prod _ _ _)^-1).
Defined.

(** ** [IsTruncMap n.+1 f <-> IsTruncMap n (ap f)] *)
Global Instance istruncmap_ap {A B} n (f:A -> B) `{!IsTruncMap n.+1 f}
  : forall x y, IsTruncMap n (@ap _ _ f x y)
  := fun x x' y =>
       trunc_equiv' _ (hfiber_ap y)^-1.

Definition istruncmap_from_ap {A B} n (f:A -> B) `{!forall x y, IsTruncMap n (@ap _ _ f x y)}
  : IsTruncMap n.+1 f.
Proof.
  intros y [a p] [b q];
    destruct q;
    exact (trunc_equiv' _ (hfiber_ap p)).
Defined.

Definition equiv_istruncmap_ap `{Funext} {A B} n (f:A -> B)
  : IsTruncMap n.+1 f <~> (forall x y, IsTruncMap n (@ap _ _ f x y))
  := equiv_iff_hprop (@istruncmap_ap _ _ n f) (@istruncmap_from_ap _ _ n f).

Global Instance isequiv_ap_isembedding {A B} (f : A -> B) `{!IsEmbedding f}
  : forall x y, IsEquiv (@ap _ _ f x y).
Proof.
  intros x y. apply isequiv_fcontr,_.
Defined.

Definition isembedding_isequiv_ap {A B} (f : A -> B) `{!forall x y, IsEquiv (@ap _ _ f x y)}
  : IsEmbedding f.
Proof.
  apply istruncmap_from_ap. intros x y;red;apply fcontr_isequiv,_.
Defined.

Definition equiv_isequiv_ap_isembedding `{Funext} {A B} (f : A -> B)
  : IsEmbedding f <~> (forall x y, IsEquiv (@ap _ _ f x y)).
Proof.
  exact (equiv_iff_hprop (@isequiv_ap_isembedding _ _ f) (@isembedding_isequiv_ap _ _ f)).
Defined.
