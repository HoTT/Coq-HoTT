Require Import Basics.
Require Import Types.
Require Import Fibrations.
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
  apply issig_pequiv'; simple refine (_;_).
  - transitivity (f (point A) = point B).
    1:make_equiv_contr_basedpaths.
    apply equiv_concat_l.
    symmetry; apply point_eq.
  - cbn.
    apply concat_Vp.
Defined.

(** The triple-fiber functor is equal to the negative of the loopspace functor. *)
Definition pfiber2_loops_functor {A B : pType} (f : A ->* B)
: loops_inv _ o* pfiber2_loops f o* pfib (pfib (pfib f))
  ==* loops_functor f o* pfiber2_loops (pfib f).
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
    rewrite concat_p1, inv_V, ap_V. apply inverse2.
    refine (((r^)..2)^ @ _).
    rewrite transport_paths_Fl; cbn.
    rewrite concat_p1, pr1_path_V, ap_V, inv_V; reflexivity.
  - reflexivity.
Qed.
