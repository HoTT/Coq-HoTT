From HoTT Require Import Basics Types HSpace.Core HSpace.Coherent HSpace.Pointwise
  Pointed Homotopy.EvaluationFibration.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * The moduli type of coherent H-space structures *)

(** When [A] is a left-invertible coherent H-space, we construct an equivalence between the ("moduli") type of coherent H-space structures on [A] and the type [A ->* (A ->** A)]. By the smash-hom adjunction for pointed types, due to Floris van Doorn in HoTT, the latter is also equivalent to the type [Smash A A ->* A].

This equivalence generalizes a formula of Arkowitz--Curjel and Copeland for spaces, and appears as Theorem 2.27 in https://arxiv.org/abs/2301.02636v1 *)

(** ** Paths between H-space structures *)

(** Paths between H-space structures correspond to homotopies between the underlying binary operations which respect the identities. This is the type of the latter. *)
Definition path_ishspace_type {X : pType} (mu nu : IsHSpace X) : Type.
Proof.
  destruct mu as [mu mu_lid mu_rid], nu as [nu nu_lid nu_rid].
  refine { h : forall x0 x1, mu x0 x1 = nu x0 x1 & prod (forall x:X, _) (forall x:X, _) }.
  - exact (mu_lid x = h pt x @ nu_lid x).
  - exact (mu_rid x = h x pt @ nu_rid x).
Defined.

(** Transport of left and right identities of binary operations along paths between the underlying functions. *)
Local Definition transport_binop_lr_id `{Funext} {X : Type} {x : X}
  {mu nu : X -> X -> X} `{mu_lid : forall y, mu x y = y}
  `{mu_rid : forall y, mu y x = y} (p : mu = nu)
  : transport (fun m : X -> X -> X =>
                 (forall y, m x y = y) * (forall y, m y x = y))
      p (mu_lid, mu_rid)
    = (fun y => (ap100 p _ _)^ @ mu_lid y,
         fun y => (ap100 p _ _)^ @ mu_rid y).
Proof.
  induction p; cbn.
  apply path_prod'; funext y.
  all: exact (concat_1p _)^.
Defined.

(** Characterization of paths between H-space structures. *)
Definition equiv_path_ishspace `{Funext} {X : pType} (mu nu : IsHSpace X)
  : path_ishspace_type mu nu <~> (mu = nu).
Proof.
  destruct mu as [mu mu_lid mu_rid], nu as [nu nu_lid nu_rid];
    unfold path_ishspace_type.
  nrefine (equiv_ap_inv' issig_ishspace _ _ oE _).
  nrefine (equiv_path_sigma _ _ _ oE _); cbn.
  apply (equiv_functor_sigma' (equiv_path_arrow2 _ _)); intro h; cbn.
  nrefine (equiv_concat_l _ _ oE _).
  1: apply transport_binop_lr_id.
  nrefine (equiv_path_prod _ _ oE _); cbn.
  apply equiv_functor_prod';
    nrefine (equiv_path_forall _ _ oE _);
    apply equiv_functor_forall_id; intro x.
  all: nrefine (equiv_moveR_Vp _ _ _ oE _);
    apply equiv_concat_r;
    apply whiskerR; symmetry;
    apply ap100_path_arrow2.
Defined.

(** ** Sections of evaluation fibrations *)

(** We first show that coherent H-space structures on a pointed type correspond to pointed sections of the evaluation fibration [ev A]. *)
Definition equiv_iscohhspace_psect `{Funext} (A : pType)
  : IsCohHSpace A <~> pSect (ev A).
Proof.
  refine (issig_psect (ev A) oE _^-1%equiv oE (issig_iscohhspace A)^-1%equiv).
  unfold SgOp, LeftIdentity, RightIdentity.
  apply equiv_functor_sigma_id; intro mu.
  apply (equiv_functor_sigma' (equiv_apD10 _ _ _)); intro H1; cbn.
  apply equiv_functor_sigma_id; intro H2; cbn.
  refine (equiv_path_inverse _ _ oE _).
  apply equiv_concat_r.
  apply concat_p1.
Defined.

(** Our next goal is to see that when [A] is a left-invertible H-space, then the fibration [ev A] is trivial. We begin with two results that allow the domain to be a general pointed type [B]. We'll later just need the case when [B] is [A]. *)

(** This lemma says that the family [fun a => B ->* [A,a]] is trivial. *)
Lemma equiv_pmap_hspace `{Funext} {A B : pType}
  (a : A) `{IsHSpace A} `{!IsEquiv (hspace_op a)}
  : (B ->* A) <~> (B ->* [A,a]).
Proof.
  napply pequiv_pequiv_postcompose.
  rapply pequiv_hspace_left_op.
Defined.

(** The next result is a consequence of the previous lemma. *)
Proposition equiv_map_pmap_hspace `{Funext} {A B : pType}
  `{IsHSpace A} `{forall a:A, IsEquiv (a *.)}
  : (B ->* A) * A <~> (B -> A).
Proof.
  transitivity {a : A  & {f : B -> A & f pt = a}}.
  2: exact (equiv_sigma_contr _ oE (equiv_sigma_symm _)^-1%equiv).
  refine (_ oE (equiv_sigma_prod0 _ _)^-1%equiv oE equiv_prod_symm _ _).
  apply equiv_functor_sigma_id; intro a.
  exact ((issig_pmap B [A,a])^-1%equiv oE equiv_pmap_hspace a).
Defined.

(** The equivalence [equiv_map_pmap_hspace] is pointed when [B] is [A]. (Note that [selfmaps A] is pointed at [idmap].) This is a pointed equivalence between the domains of [psnd : (A ->* A) * A ->* A] and [ev A : selfmaps A -> A], respectively. *)
Proposition pequiv_map_pmap_hspace `{Funext} {A : pType}
  `{IsHSpace A} `{forall a:A, IsEquiv (a *.)}
  : [(A ->* A) * A, (pmap_idmap, pt)] <~>* selfmaps A.
Proof.
  snapply Build_pEquiv'.
  1: exact equiv_map_pmap_hspace.
  cbn.
  apply path_forall, hspace_left_identity.
Defined.

(** When [A] is coherent, the pointed equivalence [pequiv_map_pmap_hspace] is a pointed equivalence over [A], i.e., a trivialization of [ev A]. *)
Proposition hspace_ev_trivialization `{Funext} {A : pType}
  `{IsCoherent A} `{forall a:A, IsEquiv (a *.)}
  : ev A o* pequiv_map_pmap_hspace ==* psnd (A:=[A ->* A, pmap_idmap]).
Proof.
  snapply Build_pHomotopy.
  { intros [f x]; cbn.
    exact (ap _ (dpoint_eq f) @ hspace_right_identity _). }
  cbn.
  refine (concat_1p _ @ _^).
  refine (concat_p1 _ @ concat_p1 _ @ _).
  refine (ap10_path_forall _ _ _ _ @ _).
  exact iscoherent.
Defined.

(** ** The equivalence [IsCohHSpace A <~> (A ->* (A ->** A))] *)

Theorem equiv_cohhspace_ppmap `{Funext} {A : pType}
  `{IsCoherent A} `{forall a:A, IsEquiv (hspace_op a)}
  : IsCohHSpace A <~> (A ->* (A ->** A)).
Proof.
  refine (_ oE equiv_iscohhspace_psect A).
  refine (_ oE (equiv_pequiv_pslice_psect _ _ _ hspace_ev_trivialization^*)^-1%equiv).
  refine (_ oE equiv_psect_psnd (A:=[A ->* A, pmap_idmap])).
  refine (pequiv_pequiv_postcompose _); symmetry.
  rapply pequiv_hspace_left_op.
Defined.

(** Here is a third characterization of the type of coherent H-space structures. It simply involves shuffling the data around and using [Funext]. *)
Definition equiv_iscohhspace_ptd_action `{Funext} (A : pType)
  : IsCohHSpace A <~> { act : forall a, A ->* [A,a] & act pt ==* pmap_idmap }.
Proof.
  refine (_ oE (issig_iscohhspace A)^-1).
  unfold IsPointed.
  (* First we shuffle the data on the LHS to be of this form: *)
  equiv_via {s : {act : A -> (A -> A) & forall a, act a pt = a} & {h : s.1 pt == idmap & h pt = s.2 pt}}.
  1: make_equiv.
  (* Then we break up [->*] and [==*] on the RHS using issig lemmas, and handle a trailing [@ 1]. *)
  snapply equiv_functor_sigma'.
  - refine (equiv_functor_forall_id (fun a => issig_pmap A [A,a]) oE _).
    unfold IsPointed.
    napply equiv_sig_coind.
  - cbn.
    intros [act p]; simpl.
    refine (issig_phomotopy _ _ oE _); cbn.
    apply equiv_functor_sigma_id; intro q.
    apply equiv_concat_r; symmetry; apply concat_p1.
Defined.

(** It follows that any homogeneous type is a coherent H-space.  This generalizes [ishspace_homogeneous]. *)
Definition iscohhspace_homogeneous `{Funext} {A : pType} `{IsHomogeneous A}
  : IsCohHSpace A.
Proof.
  apply (equiv_iscohhspace_ptd_action A)^-1.
  exists homogeneous_pt_id.
  exact homogeneous_pt_id_beta.
Defined.

(** One can also show directly that the H-space structure defined by [ishspace_homogeneous] is coherent. This also avoids [Funext]. *)
Definition iscoherent_homogeneous {A : pType} `{IsHomogeneous A}
  : @IsCoherent A (ishspace_homogeneous).
Proof.
  unfold IsCoherent; cbn.
  set (f := ishomogeneous pt).
  change (eisretr f pt = ap f (moveR_equiv_V pt pt (point_eq f)^) @ point_eq f).
  rewrite <- (point_eq f).
  unfold moveR_equiv_V; simpl.
  rhs napply concat_p1.
  lhs napply (eisadj f).
  apply ap.
  symmetry; apply concat_1p.
Defined.

(** Using either of these, we can "upgrade" any left-invertible H-space structure to a coherent one. This one has a prime because the direct proof below computes better. *)
Definition iscohhspace_hspace' (A : pType)
  `{IsHSpace A} `{forall a, IsEquiv (a *.)}
  : IsCohHSpace A.
Proof.
  snapply Build_IsCohHSpace.
  { napply ishspace_homogeneous.
    exact ishomogeneous_hspace. }
  exact iscoherent_homogeneous.
Defined.

(** The new multiplication is homotopic to the original one.  Relative to this, we expect that one of the identity laws also agrees, but that the other does not. *)
Definition iscohhspace_hspace'_beta_mu `{Funext} (A : pType)
  {m : IsHSpace A} `{forall a, IsEquiv (a *.)}
  : @hspace_op A (@ishspace_cohhspace A (iscohhspace_hspace' A)) = @hspace_op A m.
Proof.
  cbn. (* [*], [sg_op] and [hspace_op] all denote the original operation. *)
  funext a b.
  refine (ap (a *.) _).
  apply moveR_equiv_V.
  symmetry; apply left_identity.
Defined.

(** Here's a different proof that directly upgrades an H-space structure, leaving the multiplication and left-identity definitionally the same, but changing the right-identity. *)
Definition iscohhspace_hspace (A : pType)
  {m : IsHSpace A} `{forall a, IsEquiv (a *.)}
  : IsCohHSpace A.
Proof.
  snapply Build_IsCohHSpace.
  1: snapply Build_IsHSpace.
  - exact (@hspace_op A m).
  - exact (@hspace_left_identity A m).
  - intro a.
    lhs exact (ap (a *.) (hspace_right_identity pt))^.
    lhs exact (ap (a *.) (hspace_left_identity pt)).
    exact (hspace_right_identity a).
  - unfold IsCoherent; cbn.
    apply moveL_Vp.
    lhs napply concat_A1p.
    refine (_ @@ 1).
    apply (cancelR _ _ (hspace_left_identity pt)).
    symmetry; apply concat_A1p.
Defined.
