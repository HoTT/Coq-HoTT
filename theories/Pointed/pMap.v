From HoTT Require Import Basics Types.
Require Import Pointed.Core.

Local Open Scope pointed_scope.

(** ** Trivially pointed maps *)

(** Not infrequently we have a map between two unpointed types and want to consider it as a pointed map that trivially respects some given point in the domain. *)
Definition pmap_from_point {A B : Type} (f : A -> B) (a : A)
  : [A, a] ->* [B, f a]
  := Build_pMap f 1%path.

(** A variant of [pmap_from_point] where the domain is pointed, but the codomain is not. *)
Definition pmap_from_pointed {A : pType} {B : Type} (f : A -> B)
  : A ->* [B, f (point A)]
  := Build_pMap f 1%path.

(** The same, for a dependent pointed map. *)
Definition pforall_from_pointed {A : pType} {B : A -> Type} (f : forall x, B x)
  : pForall A (Build_pFam B (f (point A)))
  := Build_pForall A (Build_pFam B (f (point A))) f 1%path.

(* precomposing the zero map is the zero map *)
Lemma precompose_pconst {A B C : pType} (f : B ->* C)
  : f o* @pconst A B ==* pconst.
Proof.
  srapply Build_pHomotopy.
  1: intro; apply point_eq.
  exact (concat_p1 _ @ concat_1p _)^.
Defined.

(* postcomposing the zero map is the zero map *)
Lemma postcompose_pconst {A B C : pType} (f : A ->* B)
  : pconst o* f ==* @pconst A C.
Proof.
  srapply Build_pHomotopy.
  1: reflexivity.
  exact (concat_p1 _ @ concat_p1 _ @ ap_const _ _)^.
Defined.

Lemma pconst_factor {A B : pType} {f : pUnit ->* B} {g : A ->* pUnit}
  : f o* g ==* pconst.
Proof.
  refine (_ @* precompose_pconst f).
  apply pmap_postwhisker.
  symmetry.
  apply pmap_punit_pconst.
Defined.

(* We note that the inverse of [path_pmap] computes definitionally on reflexivity, and hence [path_pmap] itself computes typally so.  *)
Definition equiv_inverse_path_pmap_1 `{Funext} {A B} {f : A ->* B}
  : (equiv_path_pforall f f)^-1%equiv 1%path = reflexivity f
  := 1.

(** If we have a fiberwise pointed map, with a variable as codomain, this is an
  induction principle that allows us to assume it respects all basepoints by
  reflexivity*)
Definition fiberwise_pointed_map_rec `{H0 : Funext} {A : Type} {B : A -> pType}
  (P : forall (C : A -> pType) (g : forall a, B a ->* C a), Type)
  (H : forall (C : A -> Type) (g : forall a, B a -> C a),
     P _ (fun a => pmap_from_pointed (g a)))
  : forall (C : A -> pType) (g : forall a, B a ->* C a), P C g.
Proof.
  equiv_intros (equiv_functor_arrow' (equiv_idmap A) issig_ptype oE
    equiv_sig_coind _ _) C.
  destruct C as [C c0].
  equiv_intros (@equiv_functor_forall_id _ A _ _
    (fun a => issig_pmap (B a) [C a, c0 a]) oE
    equiv_sig_coind _ _) g.
  simpl in *. destruct g as [g g0].
  unfold point in g0. unfold functor_forall, sig_coind_uncurried. simpl.
  (* now we need to apply path induction on the homotopy g0 *)
  pose (path_forall _ c0 g0).
  assert (p = path_forall (fun x : A => g x (ispointed_type (B x))) c0 g0).
  1: reflexivity.
  induction p.
  apply moveR_equiv_V in X. induction X.
  apply H.
Defined.

(** A alternative constructor to build a [pHomotopy] between maps into [pForall] *)
Definition Build_pHomotopy_pForall `{Funext} {A B : pType} {C : B -> pType}
  {f g : A ->* ppforall b, C b} (p : forall a, f a ==* g a)
  (q : p (point A) ==* phomotopy_path (point_eq f) @* (phomotopy_path (point_eq g))^*)
  : f ==* g.
Proof.
  snapply Build_pHomotopy.
  1: intro a; exact (path_pforall (p a)).
  hnf; rapply moveR_equiv_M'.
  refine (_^ @ ap10 _ _).
  2: exact path_equiv_path_pforall_phomotopy_path.
  apply path_pforall.
  refine (phomotopy_path_pp _ _ @* _ @* q^*).
  apply phomotopy_prewhisker.
  apply phomotopy_path_V.
Defined.

(** Operations on dependent pointed maps *)

(* functorial action of [pForall A B] in [B] *)
Definition functor_pforall_right {A : pType} {B B' : pFam A}
  (f : forall a, B a -> B' a)
  (p : f (point A) (dpoint B) = dpoint B') (g : pForall A B)
    : pForall A B' :=
  Build_pForall A B' (fun a => f a (g a)) (ap (f (point A)) (dpoint_eq g) @ p).

Definition equiv_functor_pforall_id `{Funext} {A : pType} {B B' : pFam A}
  (f : forall a, B a <~> B' a) (p : f (point A) (dpoint B) = dpoint B')
  : pForall A B <~> pForall A B'.
Proof.
  refine (issig_pforall _ _ oE _ oE (issig_pforall _ _)^-1).
  srapply equiv_functor_sigma'.
  1: exact (equiv_functor_forall_id f).
  intro s; cbn.
  refine (equiv_concat_r p _ oE _).
  apply (equiv_ap' (f (point A))).
Defined.

Definition functor2_pforall_right {A : pType} {B C : pFam A}
  {g g' : forall (a : A), B a -> C a}
  {g₀ : g (point A) (dpoint B) = dpoint C}
  {g₀' : g' (point A) (dpoint B) = dpoint C} {f f' : pForall A B}
  (p : forall a, g a == g' a) (q : f ==* f')
  (r : p (point A) (dpoint B) @ g₀' = g₀)
  : functor_pforall_right g g₀ f ==* functor_pforall_right g' g₀' f'.
Proof.
  srapply Build_pHomotopy.
  1: { intro a. exact (p a (f a) @ ap (g' a) (q a)). }
  pointed_reduce_rewrite. symmetry. apply concat_Ap.
Defined.

Definition functor2_pforall_right_refl {A : pType} {B C : pFam A}
  (g : forall a, B a -> C a) (g₀ : g (point A) (dpoint B) = dpoint C)
  (f : pForall A B)
  : functor2_pforall_right (fun a => reflexivity (g a)) (phomotopy_reflexive f)
      (concat_1p _)
    ==* phomotopy_reflexive (functor_pforall_right g g₀ f).
Proof.
  pointed_reduce. reflexivity.
Defined.

(* functorial action of [pForall A (pointed_fam B)] in [B]. *)
Definition pmap_compose_ppforall {A : pType} {B B' : A -> pType}
  (g : forall a, B a ->* B' a) (f : ppforall a, B a) : ppforall a, B' a.
Proof.
  simple refine (functor_pforall_right _ _ f).
  + exact g.
  + exact (point_eq (g (point A))).
Defined.

Definition pmap_compose_ppforall_point {A : pType} {B B' : A -> pType}
  (g : forall a, B a ->* B' a)
  : pmap_compose_ppforall g (point_pforall B) ==* point_pforall B'.
Proof.
  srapply Build_pHomotopy.
  + intro x. exact (point_eq (g x)).
  + exact (concat_p1 _ @ concat_1p _)^.
Defined.

Definition pmap_compose_ppforall_compose {A : pType} {P Q R : A -> pType}
  (h : forall (a : A), Q a ->* R a) (g : forall (a : A), P a ->* Q a)
  (f : ppforall a, P a)
  : pmap_compose_ppforall (fun a => h a o* g a) f ==* pmap_compose_ppforall h (pmap_compose_ppforall g f).
Proof.
  srapply Build_pHomotopy.
  + reflexivity.
  + simpl. refine ((whiskerL _ (inverse2 _)) @ concat_pV _)^.
    refine (whiskerR _ _ @ concat_pp_p _ _ _).
    refine (ap_pp _ _ _ @ whiskerR (ap_compose _ _ _)^ _).
Defined.

Definition pmap_compose_ppforall2 {A : pType} {P Q : A -> pType} {g g' : forall (a : A), P a ->* Q a}
  {f f' : ppforall (a : A), P a} (p : forall a, g a ==* g' a) (q : f ==* f')
  : pmap_compose_ppforall g f ==* pmap_compose_ppforall g' f'.
Proof.
  srapply functor2_pforall_right.
  + exact p.
  + exact q.
  + exact (point_htpy (p (point A))).
Defined.

Definition pmap_compose_ppforall2_left {A : pType} {P Q : A -> pType} {g g' : forall (a : A), P a ->* Q a}
  (f : ppforall (a : A), P a) (p : forall a, g a ==* g' a)
  : pmap_compose_ppforall g f ==* pmap_compose_ppforall g' f :=
  pmap_compose_ppforall2 p (phomotopy_reflexive f).

Definition pmap_compose_ppforall2_right {A : pType} {P Q : A -> pType} (g : forall (a : A), P a ->* Q a)
  {f f' : ppforall (a : A), P a} (q : f ==* f')
  : pmap_compose_ppforall g f ==* pmap_compose_ppforall g f' :=
  pmap_compose_ppforall2 (fun a => phomotopy_reflexive (g a)) q.

Definition pmap_compose_ppforall2_refl `{Funext} {A : pType} {P Q : A -> pType}
  (g : forall (a : A), P a ->* Q a) (f : ppforall (a : A), P a)
  : pmap_compose_ppforall2 (fun a => phomotopy_reflexive (g a)) (phomotopy_reflexive f)
    ==* phomotopy_reflexive _.
Proof.
  unfold pmap_compose_ppforall2.
  revert Q g. refine (fiberwise_pointed_map_rec _ _). intros Q g.
  srapply functor2_pforall_right_refl.
Defined.

Definition pmap_compose_ppforall_pid_left {A : pType} {P : A -> pType}
  (f : ppforall (a : A), P a) : pmap_compose_ppforall (fun a => pmap_idmap) f ==* f.
Proof.
  srapply Build_pHomotopy.
  + reflexivity.
  + symmetry. exact (whiskerR (concat_p1 _ @ ap_idmap _) _ @ concat_pV _).
Defined.

Definition pmap_compose_ppforall_path_pforall `{Funext} {A : pType} {P Q : A -> pType}
  (g : forall a, P a ->* Q a) {f f' : ppforall a, P a} (p : f ==* f') :
  ap (pmap_compose_ppforall g) (path_pforall p) =
  path_pforall (pmap_compose_ppforall2_right g p).
Proof.
  revert f' p. refine (phomotopy_ind _ _).
  refine (ap _ path_pforall_1 @ path_pforall_1^ @ ap _ _^).
  exact (path_pforall (pmap_compose_ppforall2_refl _ _)).
Defined.
