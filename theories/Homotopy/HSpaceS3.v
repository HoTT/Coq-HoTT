From HoTT Require Import Basics.
Require Import Types.Paths Types.Universe.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core Pointed.pEquiv Pointed.pSusp.
Require Import Spaces.Spheres.
Require Import Homotopy.Suspension Homotopy.HSpace.Core.
Require Import Homotopy.HSpaceS1 Homotopy.CayleyDickson.
Require Import Homotopy.Join.Core Homotopy.Join.JoinSusp.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * The H-space structure on the 3-sphere *)

(** The pole exchange on [Sphere 0] supplies the negation for its imaginaroid structure. *)
#[export] Instance negate_s0 : Negate (Sphere 0) := susp_neg Empty.

#[export] Instance involutive_negate_s0 : Involutive negate_s0
  := susp_neg_inv Empty.

(** Conjugation reverses the fundamental loop of [Sphere 1]. *)
Definition conjugate_s1_beta_loop
  : ap (conj : Sphere 1 -> Sphere 1)
      (merid North @ (merid South)^)
    = (merid North @ (merid South)^)^.
Proof.
  lhs napply Susp_rec_beta_zigzag.
  rhs napply inv_pV.
  reflexivity.
Defined.

#[export] Instance conjugate_s1_left_inverse
  : LeftInverse sgop_s1 conj North.
Proof.
  snapply Sph1_ind.
  - reflexivity.
  - transport_paths' (transport_paths_Fl
      (f:=fun x : Sphere 1 => sgop_s1 (conj x) x)).
    symmetry.
    lhs napply concat_p1.
    pose (l := merid (North : Sphere 0) @ (merid South)^).
    lhs_V napply (ap011_diag (fun x y => sgop_s1 (conj y) x) l).
    lhs napply (ap011_is_ap (fun x y => sgop_s1 (conj y) x)).
    lhs napply (ap_idmap l @@ 1).
    lhs napply (1 @@ ap_compose conj (fun z => sgop_s1 z North) l).
    lhs napply (1 @@ ap (ap (fun z => sgop_s1 z North))
      conjugate_s1_beta_loop).
    lhs napply (1 @@ ap_V (fun z => sgop_s1 z North) l).
    lhs napply (1 @@ inverse2
      (Sph1_rec_beta_loop _ North (s1_turn North))).
    apply concat_pV.
Defined.

(** Negation on [Sphere 1] is homotopic to the identity by stability of suspension negation. This suffices for the unstructured sign law. *)
#[export] Instance factorneg_r_s1
  : FactorNegRight (negate_susp (Sphere 0) negate_s0) sgop_s1.
Proof.
  pose (N := fun x : Sphere 1 =>
    ap (susp_neg (Sphere 0)) (susp_neg_stable Empty x)
      @ susp_neg_inv (Sphere 0) x).
  intros x y.
  exact (ap (sgop_s1 x) (N y) @ (N (sgop_s1 x y))^).
Defined.

(** As in the existing circle associativity proof, univalence supplies the 1-truncation of [Sphere 1]. *)
#[export] Instance conjugate_s1_distropp `{Univalence}
  : DistrOpp sgop_s1 conj.
Proof.
  intros x y; revert x.
  snapply Sph1_ind.
  - cbn; exact (rightidentity_s1 (conj y))^.
  - revert y; snapply Sph1_ind.
    + exact (apD (fun x => ap conj (rightidentity_s1 x))
        (merid North @ (merid South)^)).
    + apply path_ishprop.
Defined.

#[export] Instance cdi_s0 `{Univalence}
  : CayleyDicksonImaginaroid (Sphere 0)
  := {| cdi_negate := negate_s0;
        cdi_negate_involutive := involutive_negate_s0;
        cdi_susp_hspace := hspace_s1;
        cdi_susp_factorneg_r := factorneg_r_s1;
        cdi_susp_conjug_left_inv := conjugate_s1_left_inverse;
        cdi_susp_conjug_distr := conjugate_s1_distropp |}.

(** Double the circle using the canonical suspension diamond, then transfer the H-space structure along the equivalence [S^1 * S^1 <~>* S^3]. No associativity of the doubled multiplication is required. *)
#[export] Instance hspace_s3 `{Univalence} : IsHSpace (psphere 3).
Proof.
  napply (ishspace_equiv_hspace (pequiv_pjoin_sphere 1 1)^-1*).
  rapply (hspace_cd (X:=psusp (Sphere 0))).
Defined.
