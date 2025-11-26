From HoTT Require Import Basics Types Diagrams.CommutativeSquares HSet.

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
  snapply @functor_sigma.
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

(** A version of [functor_hfiber] which is functorial in both the function and the point *)
Definition functor_hfiber2 {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h) {b : B} {b' : D} (q : k b = b')
  : hfiber f b -> hfiber g b'.
Proof.
  srapply functor_sigma.
  - exact h.
  - intros a e. exact ((p a)^ @ ap k e @ q).
Defined.

Instance isequiv_functor_hfiber2 {A B C D}
       {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
       `{IsEquiv A C h} `{IsEquiv B D k}
       (p : k o f == g o h) {b : B} {b' : D} (q : k b = b')
  : IsEquiv (functor_hfiber2 p q).
Proof.
  refine (isequiv_functor_sigma (f := h)); intros a.
  exact (isequiv_compose (fun e => (p a)^ @ ap k e) (fun e' => e' @ q)).
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
  make_equiv_contr_basedpaths.
Defined.

(** This is a useful variant for taking a "double fiber" of two maps. *)
Definition equiv_double_fibration_replacement
  {X Y Z : Type} (f : X -> Y) (g : X -> Z)
  : X <~> {y : Y & {z : Z & {x : X & f x = y /\ g x = z}}}.
Proof.
  make_equiv_contr_basedpaths.
Defined.

Definition hfiber_fibration {X} (x : X) (P:X->Type)
  : P x <~> @hfiber (sig P) X pr1 x.
Proof.
  make_equiv_contr_basedpaths.
Defined.

(** ** Exercise 4.4: The unstable octahedral axiom. *)
Section UnstableOctahedral.

  Context (n : trunc_index) {A B C : Type} (f : A -> B) (g : B -> C).

  Definition hfiber_compose_map (c : C)
    : hfiber (g o f) c -> hfiber g c
    := fun x => (f x.1 ; x.2).

  Definition hfiber_hfiber_compose_map (b : B)
    : hfiber (hfiber_compose_map (g b)) (b;1) <~> hfiber f b.
  Proof.
    unfold hfiber, hfiber_compose_map.
    (** Once we "destruct" the equality in a sigma type, the rest is just shuffling of data and path induction. *)
    refine (_ oE equiv_functor_sigma_id (fun x => (equiv_path_sigma _ _ _)^-1)); cbn.
    make_equiv_contr_basedpaths.
  Defined.

  Definition hfiber_compose (c : C)
    : hfiber (g o f) c <~> { w : hfiber g c & hfiber f w.1 }.
  Proof.
    make_equiv_contr_basedpaths.
  Defined.

  #[export] Instance istruncmap_compose `{!IsTruncMap n g} `{!IsTruncMap n f}
    : IsTruncMap n (g o f).
  Proof.
    intros c.
    exact (istrunc_isequiv_istrunc _ (hfiber_compose c)^-1).
  Defined.

End UnstableOctahedral.

(** We characterize the fibers of [functor_forall], but only in the special case where the base map is [idmap]. This doesn't depend on anything else in this file, but can't be put in Types/Forall.v, because it requires results from Types/Sigma.v. *)
Definition hfiber_functor_forall_id `{Funext} {A : Type} {P Q : A -> Type}
  (h : forall a, P a -> Q a) (g : forall a, Q a)
  : hfiber (functor_forall_id h) g <~> (forall a, hfiber (h a) (g a)).
Proof.
  unfold hfiber, functor_forall_id, functor_forall.
  nrefine (equiv_sig_coind _ _ oE _).
  apply equiv_functor_sigma_id; intro f.
  apply equiv_apD10.
Defined.

(** ** Fibers of constant functions *)
Definition hfiber_const A {B} (y y' : B)
  : hfiber (fun _ : A => y) y' <~> A * (y = y')
  := equiv_sigma_prod0 A (y = y').

Instance istruncmap_const n {A B} `{!IsTrunc n A}
       (y : B) `{!forall y', IsTrunc n (y = y')}
  : IsTruncMap n (fun _ : A => y)
  := fun y' => _.

(** ** [IsTruncMap n.+1 f <-> IsTruncMap n (ap f)] *)
Instance istruncmap_ap {A B} n (f:A -> B) `{!IsTruncMap n.+1 f}
  : forall x y, IsTruncMap n (@ap _ _ f x y)
  := fun x x' y =>
       istrunc_equiv_istrunc _ (hfiber_ap y)^-1.

Definition istruncmap_from_ap {A B} n (f:A -> B) `{!forall x y, IsTruncMap n (@ap _ _ f x y)}
  : IsTruncMap n.+1 f.
Proof.
  intro y; apply istrunc_S.
  intros [a p] [b q];
    destruct q;
    exact (istrunc_equiv_istrunc _ (hfiber_ap p)).
Defined.

Definition equiv_istruncmap_ap `{Funext} {A B} n (f:A -> B)
  : IsTruncMap n.+1 f <~> (forall x y, IsTruncMap n (@ap _ _ f x y))
  := equiv_iff_hprop (@istruncmap_ap _ _ n f) (@istruncmap_from_ap _ _ n f).

Instance isequiv_ap_isembedding {A B} (f : A -> B) `{!IsEmbedding f}
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

(** It follows from [isembedding_isequiv_ap] and [isequiv_ap_equiv_fun] that [equiv_fun] is an embedding. *)
Instance isembedding_equiv_fun `{Funext} {A B : Type}
  : IsEmbedding (@equiv_fun A B).
Proof.
  rapply isembedding_isequiv_ap.
Defined.

Lemma ap_isinj_embedding_beta {X Y : Type} (f : X -> Y) {I : IsEmbedding f} {x0 x1 : X}
  : forall (p : f x0 = f x1), ap f (isinj_embedding f I x0 x1 p) = p.
Proof.
  equiv_intro (equiv_ap_isembedding f x0 x1) q.
  induction q. cbn.
  exact (ap _ (isinj_embedding_beta f)).
Defined.
