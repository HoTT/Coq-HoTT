From HoTT Require Import Basics Types.
From HoTT.WildCat Require Import Core Universe Equiv NatTrans Yoneda.
Require Import Pointed.
From HoTT.Algebra.Groups Require Import Group FreeGroup.
Require Import Modalities.ReflectiveSubuniverse Truncations.Core.
Require Import Homotopy.Suspension.
Require Import Homotopy.ClassifyingSpace.
Require Import Homotopy.HomotopyGroup.

Local Open Scope trunc_scope.
Local Open Scope pointed_scope.
Import ClassifyingSpaceNotation.

(** In this file we show that the fundamental group of a bouquet of circles indexed by a type S is the free group on that type S. We begin by defining S-indexed wedges of circles as the suspension of the pointification of S. *)

Section AssumeUnivalence.

  Context `{Univalence}.

  (** An S-indexed wedge of circles a.k.a a bouquet can be defined as the suspension of the pointification of S. *)
  Definition Bouquet (S : Type) : pType := psusp (pointify S).

  #[export] Instance isconnected_bouquet (S : Type)
    : IsConnected 0 (Bouquet S).
  Proof.
    exact isconnected_susp.
  Defined.

  (** We can directly prove that it satisfies the desired equivalence together with naturality in the second argument. *)
  Lemma natequiv_pi1bouquet_rec (S : Type)
    : NatEquiv
        (opyon (Pi 1 (Bouquet S)))
        (opyon S o group_type).
  Proof.
    (** Pointify *)
    nrefine (natequiv_compose _ _).
    1: exact (natequiv_prewhisker (natequiv_pointify_r S) ptype_group).
    (** Post-compose with [pequiv_loops_bg_g] *)
    nrefine (natequiv_compose _ _).
    1: exact (natequiv_postwhisker _ (natequiv_inverse natequiv_g_loops_bg)).
    (** Loop space-suspension adjunction *)
    nrefine (natequiv_compose _ _).
    1: exact (natequiv_prewhisker
      (natequiv_loop_susp_adjoint_r (pointify S)) B).
    (** Pi1-BG adjunction *)
    rapply natequiv_bg_pi1_adjoint.
  Defined.

  (** For the rest of this file, we don't need to unfold this. *)
  Local Opaque natequiv_pi1bouquet_rec.

  Theorem equiv_pi1bouquet_rec (S : Type) (G : Group)
    : (Pi 1 (Bouquet S) $-> G) <~> (S -> G).
  Proof.
    apply natequiv_pi1bouquet_rec.
  Defined.

  #[export] Instance is1natural_equiv_pi1bouquet_rec (S : Type)
    : Is1Natural
        (opyon (Pi 1 (Bouquet S)))
        (opyon S o group_type)
        (fun G => equiv_pi1bouquet_rec S G).
  Proof.
    exact (is1natural_natequiv (natequiv_pi1bouquet_rec _)).
  Defined.

  (** We can define the inclusion map by using the previous equivalence on the identity group homomorphism. *)
  Definition pi1bouquet_incl (S : Type)
    : S -> Pi 1 (Bouquet S).
  Proof.
    rapply equiv_pi1bouquet_rec.
    exact grp_homo_id.
  Defined.

  (** The fundamental group of an S-bouquet is the free group on S. *)
  #[export] Instance isfreegroupon_pi1bouquet (S : Type)
    : IsFreeGroupOn S (Pi 1 (Bouquet S)) (pi1bouquet_incl S).
  Proof.
    apply equiv_isfreegroupon_isequiv_precomp.
    intro G.
    snapply isequiv_homotopic'.
    1: apply equiv_pi1bouquet_rec.
    intros f.
    refine (_ @ @is1natural_equiv_pi1bouquet_rec S _ _ f grp_homo_id).
    simpl; f_ap; symmetry.
    exact (cat_idr_strong f).
  Defined.

End AssumeUnivalence.
