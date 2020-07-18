(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics Types Diagrams.CommutativeSquares.

Local Open Scope equiv_scope.
Local Open Scope path_scope.

(** * Basic facts about fibrations *)

(* ** Homotopy fibers *)

(** Paths in homotopy fibers can be constructed using [path_sigma] and [transport_paths_Fl]. *)
Definition equiv_path_hfiber {A B : Type} {f : A -> B} {y : B}
  (x1 x2 : hfiber f y)
  : { q : x1.1 = x2.1 & x1.2 = ap f q @ x2.2 } <~> (x1 = x2).
Proof.
  refine (equiv_path_sigma _ _ _ oE _).
  apply equiv_functor_sigma_id.
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
  apply equiv_functor_sigma_id; intros q.
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
    intros [a p]; simpl; apply ap.
  - apply concat_V_pp.
  - apply concat_p_Vp.
Defined.

(** Commutative squares induce maps between fibers. *)
Definition functor_hfiber {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h) (b : B)
: hfiber f b -> hfiber g (k b).
Proof.
  snrapply @functor_sigma.
  - exact h.
  - intros a e; exact ((p a)^ @ ap k e).
Defined.

(** This doesn't need to be defined as an instance, since typeclass search can already find it, but we state it here for the reader's benefit. *)
Definition isequiv_functor_hfiber {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           `{IsEquiv A C h} `{IsEquiv B D k}
           (p : k o f == g o h) (b : B)
: IsEquiv (functor_hfiber p b) := _.

Definition equiv_functor_hfiber {A B C D}
           {f : A -> B} {g : C -> D} {h : A <~> C} {k : B <~> D}
           (p : k o f == g o h) (b : B)
  : hfiber f b <~> hfiber g (k b)
  := Build_Equiv _ _ (functor_hfiber p b) _.

(** A version of functor_hfiber which is functorial in both the function and the point *)
Definition functor_hfiber2 {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h) {b : B} {b' : D} (q : k b = b')
  : hfiber f b -> hfiber g b'.
Proof.
  srapply functor_sigma.
  - exact h.
  - intros a e. exact ((p a)^ @ ap k e @ q).
Defined.

Global Instance isequiv_functor_hfiber2 {A B C D}
       {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
       `{IsEquiv A C h} `{IsEquiv B D k}
       (p : k o f == g o h) {b : B} {b' : D} (q : k b = b')
  : IsEquiv (functor_hfiber2 p q).
Proof.
  refine (isequiv_functor_sigma (f := h)); intros a.
  refine (isequiv_compose (f := fun e => (p a)^ @ ap k e) (g := fun e' => e' @ q)).
Defined.

Definition equiv_functor_hfiber2 {A B C D}
           {f : A -> B} {g : C -> D} {h : A <~> C} {k : B <~> D}
           (p : k o f == g o h) {b : B} {b' : D} (q : k b = b')
  : hfiber f b <~> hfiber g b'
  := Build_Equiv _ _ (functor_hfiber2 p q) _.

Definition functor_hfiber_compose {A B C X Y Z : Type} {k : A -> B} {l : B -> C}
    {f : A -> X} {g : B -> Y} {h : C -> Z} {i : X -> Y} {j : Y -> Z}
    (H : i o f == g o k) (K : j o g == h o l)
  : forall x, functor_hfiber (comm_square_comp' H K) x
    == (functor_hfiber K (i x)) o (functor_hfiber H x : hfiber f x -> _).
Proof.
  intros x [y p].
  destruct p.
  apply (path_sigma' _ idpath).
  refine (concat_p1 _ @ _).
  refine (inv_pp _ _ @ ap _ _).
  refine ((ap_V _ _)^ @ ap _ _^).
  apply concat_p1.
Defined.

(** ** The 3x3 lemma for fibrations *)
Definition hfiber_functor_hfiber {A B C D}
  {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
  (p : k o f == g o h) (b : B) (c : C) (q : g c = k b)
  : hfiber (functor_hfiber p b) (c;q)
    <~> hfiber (functor_hfiber (fun x => (p x)^) c) (b;q^).
Proof.
  rapply (equiv_functor_sigma_id _ oE _ oE (equiv_functor_sigma_id _)^-1).
  1,3:intros; rapply equiv_path_sigma.
  refine (equiv_sigma_assoc _ _ oE _ oE (equiv_sigma_assoc _ _)^-1).
  apply equiv_functor_sigma_id; intros a; cbn.
  refine (equiv_sigma_symm _ oE _).
  do 2 (apply equiv_functor_sigma_id; intro).
  refine ((equiv_ap inverse _ _)^-1 oE _).
  refine (equiv_concat_r (inv_V q)^ _ oE _).
  apply equiv_concat_l.
  abstract (rewrite !transport_paths_Fl, !inv_pp, !inv_V, concat_pp_p; reflexivity).
Defined.

(** ** Replacing a map with a fibration *)
Definition equiv_fibration_replacement  {B C} (f:C ->B)
  : C <~> {y:B & hfiber f y}.
Proof.
  snrefine (Build_Equiv _ _ _ (
    Build_IsEquiv C {y:B & {x:C & f x = y}}
      (fun c => (f c; (c; idpath)))
      (fun c => c.2.1)
      _
      (fun c => idpath)
       _)).
  - intros [? [? []]]; reflexivity.
  - reflexivity.
Defined.

Definition hfiber_fibration {X} (x : X) (P:X->Type)
  : P x <~> @hfiber (sigT P) X pr1 x.
Proof.
  snrefine (Build_Equiv _ _ _
    (Build_IsEquiv (P x) { z : sigT P & z.1 = x }
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

  Context (n : trunc_index) {A B C : Type} (f : A -> B) (g : B -> C).

  Definition hfiber_compose_map (b : B)
    : hfiber (g o f) (g b) -> hfiber g (g b)
    := fun x => (f x.1 ; x.2).

  Definition hfiber_hfiber_compose_map (b : B)
    : hfiber (hfiber_compose_map b) (b;1) <~> hfiber f b.
  Proof.
    unfold hfiber, hfiber_compose_map.
    refine (_ oE (equiv_sigma_assoc _ _)^-1).
    apply equiv_functor_sigma_id; intros a; simpl.
    refine (_ oE _); revgoals.
    - refine (equiv_functor_sigma_id
                (fun p => (equiv_path_sigma _ _ _)^-1)).
    - cbn. refine (_ oE equiv_sigma_symm _).
      apply equiv_sigma_contr; intros p.
      destruct p; simpl; exact _.
  Defined.

  Definition hfiber_compose (c : C)
  : hfiber (g o f) c <~> { w : hfiber g c & hfiber f w.1 }.
  Proof.
    make_equiv_contr_basedpaths.
  Defined.

  Global Instance istruncmap_compose `{!IsTruncMap n g} `{!IsTruncMap n f}
    : IsTruncMap n (g o f).
  Proof.
    intros c.
    exact (trunc_equiv _ (hfiber_compose c)^-1).
  Defined.

End UnstableOctahedral.

(** ** Fibers of constant functions *)
Definition hfiber_const A {B} (y y' : B)
  : hfiber (fun _ : A => y) y' <~> A * (y = y')
  := equiv_sigma_prod0 A (y = y').

Global Instance istruncmap_const n {A B} `{!IsTrunc n A}
       (y : B) `{!forall y', IsTrunc n (y = y')}
  : IsTruncMap n (fun _ : A => y)
  := fun y' => _.

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
  intros x y. apply isequiv_contr_map,_.
Defined.

Definition equiv_ap_isembedding {A B} (f : A -> B) `{!IsEmbedding f} (x y : A)
  : (x = y) <~> (f x = f y)
  := Build_Equiv _ _ (ap f) _.

Definition isembedding_isequiv_ap {A B} (f : A -> B) `{!forall x y, IsEquiv (@ap _ _ f x y)}
  : IsEmbedding f.
Proof.
  rapply istruncmap_from_ap.
Defined.

Definition equiv_isequiv_ap_isembedding `{Funext} {A B} (f : A -> B)
  : IsEmbedding f <~> (forall x y, IsEquiv (@ap _ _ f x y)).
Proof.
  exact (equiv_iff_hprop (@isequiv_ap_isembedding _ _ f) (@isembedding_isequiv_ap _ _ f)).
Defined.
