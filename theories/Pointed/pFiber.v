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
  apply issig_pequiv; simple refine (_;_).
  - simpl; unfold hfiber.
    refine (_ oE (equiv_sigma_assoc _ _)^-1); simpl.
    refine (_ oE (equiv_functor_sigma'
                   (P := fun a => {_ : f a = point B & a = point A})
                   (Q := fun a => {_ : a = point A & f a = point B })
                   1 (fun a => equiv_sigma_symm0 _ _))).
    refine (_ oE equiv_sigma_assoc _ (fun a => f a.1 = point B)).
    refine (_ oE equiv_contr_sigma _); simpl.
    apply equiv_concat_l.
    symmetry; apply point_eq.
  - simpl.
    apply concat_Vp.
Defined.

(** The triple-fiber functor is equal to the negative of the loopspace functor. *)
Definition pfiber2_loops_functor {A B : pType} (f : A ->* B)
: loops_inv _ o* pfiber2_loops f o* pfib (pfib (pfib f))
  ==* loops_functor f o* pfiber2_loops (pfib f).
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _).
  - intros [[xp q] r]. simpl in *.
    rewrite !transport_paths_Fl.
    rewrite inv_pp, !ap_V, !inv_V, ap_compose, !ap_pp, inv_pp.
    simpl; rewrite !concat_1p, !concat_p1.
    rewrite ap_pr1_path_basedpaths'.
    rewrite ap_V, inv_V; apply whiskerR.
    match goal with
        |- ?a = ap f (ap ?g ?z) =>
        change (a = ap f (ap (pr1 o pr1) z))
    end.
    rewrite (ap_compose pr1 pr1).
    rewrite ap_pr1_path_basedpaths'.
    (** In order to destruct [r], we have to invert it to match Paulin-Mohring path induction.  I don't know why the [set] fails to catch the [r^] in the conclusion. *)
    set (s := r^); change ((xp.2)^ = ap f (ap pr1 s)).
    clearbody s; clear r; destruct s; reflexivity.
  - reflexivity.
Qed.