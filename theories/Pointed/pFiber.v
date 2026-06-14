From HoTT Require Import Basics Types.
From HoTT.WildCat Require Import Core Equiv.
Require Import HFiber.
Require Import Pointed.Core.
Require Import Pointed.pEquiv.
Require Import Pointed.Loops.

Local Open Scope pointed_scope.

(** ** Pointed fibers *)

Instance ispointed_fiber {A B : pType} (f : A ->* B) : IsPointed (hfiber f (point B))
  := (point A; point_eq f).

Definition pfiber {A B : pType} (f : A ->* B) : pType := [hfiber f (point B), _].

Definition pfib {A B : pType} (f : A ->* B) : pfiber f ->* A
  := Build_pMap pr1 1.

(** The double fiber object is equivalent to loops on the base. *)
Definition pfiber2_loops {A B : pType} (f : A ->* B)
  : pfiber (pfib f) <~>* loops B.
Proof.
  pointed_reduce_pmap f.
  snapply Build_pEquiv'.
  1: make_equiv_contr_basedpaths.
  reflexivity.
Defined.

Definition pfiber_fmap_loops {A B : pType} (f : A ->* B)
  : pfiber (fmap loops f) <~>* loops (pfiber f).
Proof.
  srapply Build_pEquiv'.
  { etransitivity.
    2: srapply equiv_path_sigma.
    simpl; unfold hfiber.
    srapply equiv_functor_sigma_id.
    intro p; cbn.
    refine (_ oE equiv_moveL_Mp _ _ _).
    refine (_ oE equiv_concat_r (concat_p1 _) _).
    refine (_ oE equiv_moveL_Vp _ _ _).
    refine (_ oE equiv_path_inverse _ _).
    apply equiv_concat_l.
    apply transport_paths_Fl. }
  by pointed_reduce.
Defined.

Definition pr1_pfiber_fmap_loops {A B} (f : A ->* B)
  : fmap loops (pfib f) o* pfiber_fmap_loops f
    ==* pfib (fmap loops f).
Proof.
  srapply Build_pHomotopy.
  - intros [u v].
    refine (concat_1p _ @ concat_p1 _ @ _).
    exact (@ap_pr1_path_sigma _ _ (point A; point_eq f) (point A;point_eq f) _ _).
  - abstract (pointed_reduce_rewrite; reflexivity).
Defined.

Definition pfiber_fmap_iterated_loops {A B : pType} (n : nat) (f : A ->* B)
  : pfiber (fmap (iterated_loops n) f) <~>* iterated_loops n (pfiber f).
Proof.
  induction n.
  1: reflexivity.
  refine (_ o*E pfiber_fmap_loops _ ).
  tapply (emap loops).
  exact IHn.
Defined.

Definition functor_pfiber {A B C D}
           {f : A ->* B} {g : C ->* D} {h : A ->* C} {k : B ->* D}
           (p : k o* f ==* g o* h)
  : pfiber f ->* pfiber g.
Proof.
  srapply Build_pMap.
  + cbn. exact (functor_hfiber2 p (point_eq k)).
  + srapply path_hfiber. 
    - apply point_eq.
    - refine (concat_pp_p _ _ _ @ _). apply moveR_Vp. exact (point_htpy p)^.
Defined.

Definition pequiv_pfiber {A B C D}
           {f : A ->* B} {g : C ->* D} (h : A <~>* C) (k : B <~>* D)
           (p : k o* f ==* g o* h)
  : pfiber f $<~> pfiber g
  := Build_pEquiv (functor_pfiber p) _.

Definition square_functor_pfiber {A B C D}
           {f : A ->* B} {g : C ->* D} {h : A ->* C} {k : B ->* D}
           (p : k o* f ==* g o* h)
  : h o* pfib f ==* pfib g o* functor_pfiber p.
Proof.
  srapply Build_pHomotopy.
  - intros x; reflexivity.
  - apply moveL_pV. cbn; unfold functor_sigma; cbn.
    refine (ap (concat 1) (concat_p1 _ @ _)).
    exact (ap_pr1_path_sigma
             (u := functor_hfiber2 p (point_eq k) (ispointed_fiber f))
             (v := ispointed_fiber g) (point_eq h) _).
Defined.

Definition square_pequiv_pfiber {A B C D}
           {f : A ->* B} {g : C ->* D} (h : A <~>* C) (k : B <~>* D)
           (p : k o* f ==* g o* h)
  : h o* pfib f ==* pfib g o* pequiv_pfiber h k p
  := square_functor_pfiber p.

(** The triple-fiber functor is equal to the negative of the loop space functor. *)
Definition pfiber2_fmap_loops {A B : pType} (f : A ->* B)
: pfiber2_loops f o* pfib (pfib (pfib f))
  ==* fmap loops f o* (loops_inv _ o* pfiber2_loops (pfib f)).
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _).
  - intros [[[x p] q] r]. simpl in *.
    (** Apparently [destruct q] isn't smart enough to generalize over [p]. *)
    move q before x; revert dependent x;
      refine (paths_ind_r _ _ _); intros p r; cbn.
    rewrite !concat_1p, concat_p1.
    rewrite paths_ind_r_transport.
    rewrite transport_arrow_toconst, transport_paths_Fl. 
    rewrite concat_p1, inv_V, ap_V.
    refine (((r^)..2)^ @ _).
    rewrite transport_paths_Fl; cbn.
    rewrite pr1_path_V, !ap_V, !inv_V.
    apply concat_p1.
  - reflexivity.
Qed.

(** The value of [pfiber2_loops] on a general element of the double
    fiber. *)
Definition pfiber2_loops_beta {C D : Type} {c0 : C} {d0 : D}
  (g : C -> D) (de : g c0 = d0) (c : C) (w : g c = d0) (v : c = c0)
  : pfiber2_loops (Build_pMap (A:=[C, c0]) (B:=[D, d0]) g de)
      (((c; w); v))
    = de^ @ ((ap g v)^ @ w).
Proof.
  destruct v; destruct de.
  exact ((concat_1p w)^ @ ap (concat 1) (concat_1p w)^).
Defined.

(** The path algebra underlying the pointwise part of
    [pfiber2_loops_natural], with all endpoints free. *)
Local Definition pfiber2_loops_natural_core {D : Type} {y x : D}
  (X : y = x) (l : x = x)
  : X^ @ (1 @ (((1 @ (1 @ X)^)^ @ l) @ 1)) = 1 @ (l @ 1).
Proof.
  destruct X.
  exact (ap (concat 1) (concat_1p _ @ whiskerR (concat_1p l) 1)).
Defined.

(** [pfiber2_loops] commutes with the fiber functor of a square, for an
    arbitrary square of pointed maps. *)
Definition pfiber2_loops_natural_functor {A B C D : pType}
  {f : A ->* B} {g : C ->* D} {h : A ->* C} {k : B ->* D}
  (p : k o* f ==* g o* h)
  : pfiber2_loops g o* functor_pfiber (square_functor_pfiber p)
    ==* fmap loops k o* pfiber2_loops f.
Proof.
  pointed_reduce.
  snapply Build_pHomotopy.
  - intros [[c w] v].
    cbn in v.
    revert w; revert v; revert c.
    napply paths_ind_r.
    intro w.
    refine (pfiber2_loops_beta _ _ _ _ _ @ _).
    refine (ap (fun q => dpoint_eq1^ @ (1 @ ((q^ @ ap k w) @ 1))) H @ _).
    exact (pfiber2_loops_natural_core dpoint_eq1 (ap k w)).
  - cbn; cbv beta iota delta
      [point_htpy square_functor_pfiber
       HFiber.functor_hfiber2 ispointed_fiber functor_sigma
       functor_pfiber pmap_compose pointed_htpy point_eq];
    cbn.
    generalize dependent (p point2).
    napply paths_ind_r.
    cbn.
    generalize dependent (k (f point2)).
    intros x dpe; destruct dpe.
    reflexivity.
Defined.

(** The same for an equivalence square; the underlying double-fiber map is
    [functor_pfiber] of the same square. *)
Definition pfiber2_loops_natural {A B C D : pType}
  {f : A ->* B} {g : C ->* D} (h : A <~>* C) (k : B <~>* D)
  (p : k o* f ==* g o* h)
  : pfiber2_loops g
      o* pequiv_pfiber (pequiv_pfiber h k p) h (square_pequiv_pfiber h k p)
    ==* fmap loops k o* pfiber2_loops f
  := pfiber2_loops_natural_functor p.
