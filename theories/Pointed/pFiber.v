Require Import Basics.
Require Import Types.
Require Import HFiber.
Require Import Pointed.Core.
Require Import Pointed.pEquiv.
Require Import Pointed.Loops.

Local Open Scope pointed_scope.

(** ** Pointed fibers *)

Definition pfiber {A B : pType} (f : A ->* B) : pType.
Proof.
  refine (Build_pType (hfiber f (point B)) _); try exact _.
  exists (point A).
  apply point_eq.
Defined.

Definition pfib {A B : pType} (f : A ->* B) : pfiber f ->* A
  := (Build_pMap (pfiber f) A pr1 1).

(** The double fiber object is equivalent to loops on the base. *)
Definition pfiber2_loops {A B : pType} (f : A ->* B)
  : pfiber (pfib f) <~>* loops B.
Proof.
  apply issig_pequiv'; srefine (_;_).
  { transitivity (f (point A) = point B).
    1: make_equiv_contr_basedpaths.
    apply equiv_concat_l.
    symmetry; apply point_eq. }
  cbn; apply concat_Vp.
Defined.

Definition pfiber_loops_functor {A B : pType} (f : A ->* B)
  : pfiber (loops_functor f) <~>* loops (pfiber f).
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

Definition pr1_pfiber_loops_functor {A B} (f : A ->* B)
  : loops_functor (pfib f) o* pfiber_loops_functor f
    ==* pfib (loops_functor f).
Proof.
  srapply Build_pHomotopy.
  - intros [u v].
    refine (concat_1p _ @ concat_p1 _ @ _).
    exact (@ap_pr1_path_sigma _ _ (point A; point_eq f) (point A;point_eq f) _ _).
  - abstract (pointed_reduce_rewrite; reflexivity).
Defined.

Definition pfiber_iterated_loops_functor {A B : pType} (n : nat) (f : A ->* B)
  : pfiber (iterated_loops_functor n f) <~>* iterated_loops n (pfiber f).
Proof.
  induction n.
  1: reflexivity.
  refine (_ o*E pfiber_loops_functor _ ).
  apply pequiv_loops_functor.
  apply IHn.
Defined.

Definition functor_pfiber {A B C D}
           {f : A ->* B} {g : C ->* D} {h : A ->* C} {k : B ->* D}
           (p : k o* f ==* g o* h)
  : pfiber f ->* pfiber g.
Proof.
  srapply Build_pMap.
  + cbn. refine (functor_hfiber2 p (point_eq k)).
  + srapply path_hfiber. 
    - apply point_eq.
    - refine (concat_pp_p _ _ _ @ _). apply moveR_Vp. apply (point_htpy p)^.
Defined.

Definition pequiv_pfiber {A B C D}
           {f : A ->* B} {g : C ->* D} (h : A <~>* C) (k : B <~>* D)
           (p : k o* f ==* g o* h)
  : pfiber f <~>* pfiber g
  := Build_pEquiv _ _ (functor_pfiber p) _.

Definition square_functor_pfiber {A B C D}
           {f : A ->* B} {g : C ->* D} {h : A ->* C} {k : B ->* D}
           (p : k o* f ==* g o* h)
  : h o* pfib f ==* pfib g o* functor_pfiber p.
Proof.
  srapply Build_pHomotopy.
  - intros x; reflexivity.
  - apply moveL_pV. cbn; unfold functor_sigma; cbn.
    abstract (rewrite ap_pr1_path_sigma, concat_p1; reflexivity).
Defined.

Definition square_pequiv_pfiber {A B C D}
           {f : A ->* B} {g : C ->* D} (h : A <~>* C) (k : B <~>* D)
           (p : k o* f ==* g o* h)
  : h o* pfib f ==* pfib g o* pequiv_pfiber h k p
  := square_functor_pfiber p.

(** The triple-fiber functor is equal to the negative of the loopspace functor. *)
Definition pfiber2_loops_functor {A B : pType} (f : A ->* B)
: pfiber2_loops f o* pfib (pfib (pfib f))
  ==* loops_functor f o* (loops_inv _ o* pfiber2_loops (pfib f)).
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
