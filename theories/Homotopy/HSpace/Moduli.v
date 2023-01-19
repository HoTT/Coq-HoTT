Require Import HSpace.Core HSpace.Coherent HSpace.Pointwise
  Pointed Homotopy.EvaluationFibration Tactics.EvalIn.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.

Local Notation pt := (point _).
Local Notation "[ X , x ]" := (Build_pType X x).

(** * The moduli type of H-space structures *)

(** When [A] is a left-invertible H-space, we construct an equivalence between the ("moduli") type of H-space structures on [A] and the type [A ->* (A ->** A)]. By the smash-hom adjunction for pointed types, due to Floris van Doorn in HoTT, the latter is also equivalent to the type [Smash A A ->* A].

This equivalence generalizes a formula of Arkowitz--Curjel and Copeland for spaces, and appears as Theorem 2.27 in https://arxiv.org/abs/2301.02636v1. *)

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
  : (A ->* [A,a]) <~> (A ->* A).
Proof.
  symmetry.
  nrapply equiv_pequiv_postcompose.
  snrapply Build_pEquiv'.
  - exact (Build_Equiv _ _ (hspace_op a) _).
  - cbn. rapply right_identity.
Defined.

(** The lemma gives us an equivalence on the total spaces (domains) of [ev A] and [psnd] (the projection out of the displayed product). *)
Proposition equiv_map_pmap_hspace `{Funext} {A : pType}
  `{IsHSpace A} `{forall a:A, IsEquiv (a *.)}
  : (A -> A) <~> (A ->* A) * A.
Proof.
  transitivity {a : A  & {f : A -> A & f pt = a}}.
  1: exact (equiv_sigma_symm _ oE (equiv_sigma_contr _)^-1%equiv).
  refine (equiv_prod_symm _ _ oE equiv_sigma_prod0 _ _ oE _).
  apply equiv_functor_sigma_id; intro a.
  exact (equiv_pmap_hspace a oE issig_pmap A [A,a]).
Defined.

(** If the H-space is coherent, the above is a pointed equivalence. *)
Proposition pequiv_map_pmap_hspace `{Funext} {A : pType}
  `{IsCoherent A} `{forall a:A, IsEquiv (a *.)}
  : selfmaps A <~>* [(A ->* A) * A, (pmap_idmap, pt)].
Proof.
  srapply Build_pEquiv'.
  1: exact equiv_map_pmap_hspace.
  cbn. refine (path_prod' _ idpath).
  apply path_pforall; srapply Build_pHomotopy.
  { intro k; cbn.
    apply moveR_equiv_V.
    exact (left_identity _)^. }
  cbn. refine (_ @ (concat_1p _)^ @ (concat_p1 _)^).
  apply (ap _).
  apply inverse2.
  exact iscoherent.
Defined.

(** The pointed equivalence [pequiv_map_pmap_hspace] is a pointed equivalence over [A], i.e., a trivialization of [ev A]. *)
Proposition hspace_ev_trivialization `{Funext} {A : pType}
  `{IsCoherent A} `{forall a:A, IsEquiv (a *.)}
  : ev A ==* psnd (A:=[A ->* A, pmap_idmap]) o* pequiv_map_pmap_hspace.
Proof.
  srapply Build_pHomotopy.
  1: reflexivity. (* The underlying maps agree definitionally. *)
  lazy beta.
  apply (moveR_1M _ _)^-1. (* [dpoint_eq (ev A)] is [idpath]. *)
  refine (concat_p1 _ @ _).
  unfold pequiv_map_pmap_hspace, equiv_map_pmap_hspace, ev, equiv_compose,
    Build_pEquiv', Build_pMap, pointed_equiv_fun, point_eq, dpoint_eq.
  exact (ap_snd_path_prod (z:=(_,pt)) (z':=(pt,pt)) _ _).
Defined.

(** ** The equivalence [IsCohHSpace A <~> (A ->* (A ->** A))] *)

Theorem equiv_cohhspace_ppmap `{Funext} {A : pType}
  `{IsCoherent A} `{forall a:A, IsEquiv (hspace_op a)}
  : IsCohHSpace A <~> (A ->* (A ->** A)).
Proof.
  refine (_ oE equiv_iscohhspace_psect A).
  refine (_ oE equiv_pequiv_pslice_psect _ _ _ hspace_ev_trivialization).
  refine (_ oE equiv_psect_psnd).
  refine (equiv_pequiv_postcompose _); symmetry.
  rapply ishomogeneous.
  rapply ishomogeneous_hspace.
Defined.
