Require Import Basics Types WildCat Pointed.
Require Import Groups.Group Groups.Subgroup Groups.Kernel.
Require Import Homotopy.ExactSequence Modalities.Identity.

Local Open Scope mc_scope.
Local Open Scope mc_add_scope.
Local Open Scope path_scope.

(** * Complexes of groups *)

Definition grp_cxfib {A B C : Group} {i : A $-> B} {f : B $-> C} (cx : IsComplex i f)
  : GroupHomomorphism A (grp_kernel f)
  := grp_kernel_corec cx.

Definition grp_iso_cxfib {A B C : Group} {i : A $-> B} {f : B $-> C}
           `{IsEmbedding i} (ex : IsExact (Tr (-1)) i f)
  : GroupIsomorphism A (grp_kernel f)
  := Build_GroupIsomorphism _ _ (grp_cxfib cx_isexact) (isequiv_cxfib ex).

(** This is the same proof as for [equiv_cxfib_beta], but giving the proof is easier than specializing the general result. *)
Proposition grp_iso_cxfib_beta {A B C : Group} {i : A $-> B} {f : B $-> C}
            `{IsEmbedding i} (ex : IsExact (Tr (-1)) i f)
  : i $o (grp_iso_inverse (grp_iso_cxfib ex)) $== subgroup_incl (grp_kernel f).
Proof.
  rapply equiv_ind.
  1: exact (isequiv_cxfib ex).
  intro x.
  exact (ap (fun y => i y) (eissect _ x)).
Defined.

Definition grp_iscomplex_trivial {X Y : Group} (f : X $-> Y)
  : IsComplex (@grp_homo_const grp_trivial X) f.
Proof.
  srapply phomotopy_homotopy_hset.
  intro x; cbn.
  exact (grp_homo_unit f).
Defined.

Local Existing Instance ishprop_phomotopy_hset.
Local Existing Instance ishprop_isexact_hset.

(** A complex 0 -> A -> B of groups is purely exact if and only if the map A -> B is an embedding. *)
Lemma equiv_grp_isexact_isembedding `{Univalence} {A B : Group} (f : A $-> B)
  : IsExact purely (@grp_homo_const grp_trivial A) f <~> IsEmbedding f.
Proof.
  srapply equiv_iff_hprop.
  - intros [cx conn] b a.
    rapply (transport IsHProp (x:= hfiber f 0)).
    + apply path_universe_uncurried; symmetry.
      apply equiv_grp_hfiber.
      exact a.
    + rapply (transport IsHProp (x:= grp_trivial)).
      apply path_universe_uncurried.
      rapply Build_Equiv.
  - intro isemb_f.
    exists (grp_iscomplex_trivial f).
    intros y; rapply contr_inhabited_hprop.
    exists tt; apply path_ishprop.
Defined.


(** A complex 0 -> A -> B is purely exact if and only if the kernel of the map A -> B is trivial. *)
Corollary equiv_grp_isexact_kernel `{Univalence} {A B : Group} (f : A $-> B)
  : IsExact purely (@grp_homo_const grp_trivial A) f
            <~> (grp_kernel f = trivial_subgroup :> Subgroup _).
Proof.
  exact ((equiv_kernel_isembedding f)^-1%equiv oE equiv_grp_isexact_isembedding f).
Defined.
