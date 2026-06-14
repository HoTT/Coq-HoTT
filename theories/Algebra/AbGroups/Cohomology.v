From HoTT Require Import Basics Types Truncations.Core.
From HoTT.WildCat Require Import Core.
Require Import AbGroups.AbelianGroup.
Require Import Groups.Group Groups.Subgroup Groups.QuotientGroup.

Local Open Scope nat_scope.
Local Open Scope mc_add_scope.

(** * Cochain complexes of abelian groups and their cohomology *)

(** A cochain complex is a sequence of abelian groups with differentials whose
    consecutive composites vanish. *)
Record CochainComplex : Type := {
  cc_carrier : nat -> AbGroup ;
  cc_diff : forall n, cc_carrier n $-> cc_carrier (S n) ;
  cc_iscomplex : forall n, cc_diff (S n) $o cc_diff n == grp_homo_const
}.

(** Each differential corestricts to the kernel of the next, since the
    composite vanishes. *)
Definition cc_diff_corec (C : CochainComplex) (n : nat)
  : cc_carrier C n $-> ab_kernel (cc_diff C (S n))
  := grp_kernel_corec (cc_diff C n) (cc_iscomplex C n).

(** The [n]-th cohomology group: the kernel of the [n]-th differential modulo
    the image of the previous one. *)
Definition cohomology (C : CochainComplex) (n : nat) : AbGroup
  := match n with
     | O => ab_kernel (cc_diff C 0)
     | S n => ab_cokernel (cc_diff_corec C n)
     end.

(** In degree zero the cohomology is the kernel of the first differential. *)
Definition cohomology_zero (C : CochainComplex)
  : cohomology C 0 = ab_kernel (cc_diff C 0)
  := idpath.

(** ** Morphisms of cochain complexes and functoriality of cohomology *)

(** A morphism of cochain complexes is a degreewise map commuting with the
    differentials. *)
Record CochainMap (C D : CochainComplex) : Type := {
  cm_map : forall n, cc_carrier C n $-> cc_carrier D n ;
  cm_natural : forall n, cm_map (S n) $o cc_diff C n == cc_diff D n $o cm_map n
}.

Arguments cm_map {C D}.
Arguments cm_natural {C D}.

Section Functoriality.
  Context `{Funext} {C D : CochainComplex} (f : CochainMap C D).

  (** A cochain map restricts to the kernels of the differentials. *)
  Definition cm_kernel (n : nat)
    : ab_kernel (cc_diff C n) $-> ab_kernel (cc_diff D n).
  Proof.
    snapply grp_kernel_corec.
    - exact (grp_homo_compose (cm_map f n) (subgroup_incl _)).
    - intro x.
      lhs exact (cm_natural f n (subgroup_incl _ x))^.
      lhs napply (ap (cm_map f (S n)) x.2).
      apply grp_homo_unit.
  Defined.

  (** The kernel map commutes with the corestricted differentials. *)
  Definition cm_kernel_natural (n : nat) (c : cc_carrier C n)
    : cm_kernel (S n) (cc_diff_corec C n c) = cc_diff_corec D n (cm_map f n c).
  Proof.
    apply path_sigma_hprop.
    exact (cm_natural f n c).
  Defined.

  (** A cochain map induces a map on cohomology in every degree. *)
  Definition cohomology_functor (n : nat)
    : cohomology C n $-> cohomology D n.
  Proof.
    destruct n as [|n].
    - exact (cm_kernel 0).
    - snapply quotient_abgroup_rec.
      + exact (grp_homo_compose grp_quotient_map (cm_kernel (S n))).
      + intros y hy; strip_truncations; destruct hy as [c hc].
        lhs napply (ap (fun z => grp_quotient_map (cm_kernel (S n) z)) hc^).
        lhs napply (ap grp_quotient_map (cm_kernel_natural n c)).
        napply grp_quotient_map_trivial.
        exact (grp_image_in (cc_diff_corec D n) (cm_map f n c)).
  Defined.

End Functoriality.
