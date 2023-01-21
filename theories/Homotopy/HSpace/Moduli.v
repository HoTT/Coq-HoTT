Require Import HSpace.Core HSpace.Coherent HSpace.Pointwise
  Pointed Homotopy.EvaluationFibration Tactics.EvalIn.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.

(** * The moduli type of H-space structures *)

(** When [A] is a left-invertible H-space, we construct an equivalence between the ("moduli") type of H-space structures on [A] and the type [A ->* (A ->** A)]. By the smash-hom adjunction for pointed types, due to Floris van Doorn in HoTT, the latter is also equivalent to the type [Smash A A ->* A].

This equivalence generalizes a formula of Arkowitz--Curjel and Copeland for spaces, and appears as Theorem 2.27 in https://arxiv.org/abs/2301.02636v1 *)

(** ** Sections of evaluation fibrations *)

(** We first show that coherent H-space structures on a pointed type correspond to pointed sections of the evaluation fibration [ev A]. *)
Definition equiv_iscohhspace_psect `{Funext} (A : pType)
  : IsCohHSpace A <~> pSect (ev A).
Proof.
  refine (issig_psect (ev A) oE _ oE (issig_iscohhspace A)^-1%equiv).
  unfold SgOp, LeftIdentity, RightIdentity.
  rapply equiv_functor_sigma_id; intro mu.
  snrapply (equiv_functor_sigma' (equiv_path_forall _ _)); intro H1; cbn.
  snrapply equiv_functor_sigma_id; intro H2; cbn.
  refine (_ oE (equiv_path_inverse _ _)).
  rapply equiv_concat_r.
  refine (_ @ (concat_p1 _)^).
  (* This does not do a rewrite, but [change]s the goal based on the type of the lemma: *)
  rewrite_refl (ap_apply_lD (path_forall (mu pt) idmap H1) pt).
  exact (apD10_path_forall _ _ H1 pt)^.
Defined.

(** Our next goal is to see that when [A] is a left-invertible H-space, then the fibration [ev A] is trivial. *)

(** This lemma says that the family [fun a => A ->* [A,a]] is trivial. *)
Lemma equiv_pmap_hspace `{Funext} {A : pType}
  (a : A) `{IsHSpace A} `{!IsEquiv (hspace_op a)}
  : (A ->* A) <~> (A ->* [A,a]).
Proof.
  nrapply equiv_pequiv_postcompose.
  rapply pequiv_hspace_left_op.
Defined.

(** The lemma gives us an equivalence on the total spaces (domains) of [ev A] and [psnd] (the projection out of the displayed product). *)
Proposition equiv_map_pmap_hspace `{Funext} {A : pType}
  `{IsHSpace A} `{forall a:A, IsEquiv (a *.)}
  : (A ->* A) * A <~> (A -> A).
Proof.
  transitivity {a : A  & {f : A -> A & f pt = a}}.
  2: exact (equiv_sigma_contr _ oE (equiv_sigma_symm _)^-1%equiv).
  refine (_ oE (equiv_sigma_prod0 _ _)^-1%equiv oE equiv_prod_symm _ _).
  apply equiv_functor_sigma_id; intro a.
  exact ((issig_pmap A [A,a])^-1%equiv oE equiv_pmap_hspace a).
Defined.

(** The above is a pointed equivalence. *)
Proposition pequiv_map_pmap_hspace `{Funext} {A : pType}
  `{IsHSpace A} `{forall a:A, IsEquiv (a *.)}
  : [(A ->* A) * A, (pmap_idmap, pt)] <~>* selfmaps A.
Proof.
  srapply Build_pEquiv'.
  1: exact equiv_map_pmap_hspace.
  cbn.
  apply path_forall, hspace_left_identity.
Defined.

(** When [A] is coherent, the pointed equivalence [pequiv_map_pmap_hspace] is a pointed equivalence over [A], i.e., a trivialization of [ev A]. *)
Proposition hspace_ev_trivialization `{Funext} {A : pType}
  `{IsCoherent A} `{forall a:A, IsEquiv (a *.)}
  : ev A o* pequiv_map_pmap_hspace ==* psnd (A:=[A ->* A, pmap_idmap]).
Proof.
  srapply Build_pHomotopy.
  { intros [f x]; cbn.
    exact (ap _ (dpoint_eq f) @ hspace_right_identity _). }
  cbn.
  refine (concat_1p _ @ _^).
  refine (concat_p1 _ @ concat_p1 _ @ _).
  refine (ap10_path_forall _ _ _ _ @ _).
  apply iscoherent.
Defined.

(** ** The equivalence [IsCohHSpace A <~> (A ->* (A ->** A))] *)

Theorem equiv_cohhspace_ppmap `{Funext} {A : pType}
  `{IsCoherent A} `{forall a:A, IsEquiv (hspace_op a)}
  : IsCohHSpace A <~> (A ->* (A ->** A)).
Proof.
  refine (_ oE equiv_iscohhspace_psect A).
  refine (_ oE (equiv_pequiv_pslice_psect _ _ _ hspace_ev_trivialization^*)^-1%equiv).
  refine (_ oE equiv_psect_psnd (A:=[A ->* A, pmap_idmap])).
  refine (equiv_pequiv_postcompose _); symmetry.
  rapply ishomogeneous.
  apply ishomogeneous_hspace.
Defined.
