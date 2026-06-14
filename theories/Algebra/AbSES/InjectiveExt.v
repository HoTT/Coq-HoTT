From HoTT Require Import Basics Types Truncations.Core.
From HoTT.WildCat Require Import Core.
Require Import AbGroups.AbelianGroup AbGroups.Biproduct AbGroups.AbInjective.
Require Import Algebra.AbSES.Core Algebra.AbSES.Ext.

(** * Injectivity and the vanishing of Ext

    An injective abelian group has no nontrivial extensions; the dual of
    Proposition 2.5.2. *)

(** Every extension of an injective group is trivial. *)
Definition isabinjective_ext_trivial `{Univalence} {I : AbGroup} `{IsAbInjective I}
  {B : AbGroup} (E : AbSES B I)
  : tr E = point (Ext B I).
Proof.
  pose proof (isabinjective I (middle E) (inclusion E) grp_homo_id _) as hr.
  strip_truncations.
  destruct hr as [r hr].
  pose proof (iscomplex_abses E) as hc; destruct hc as [hc0 hc1].
  pose (phi := ab_biprod_corec r (projection E) : middle E $-> ab_biprod I B).
  assert (p0 : phi $o inclusion E == ab_biprod_inl).
  { intro a; snapply path_prod'.
    - exact (hr a).
    - exact (hc0 a). }
  assert (p1 : projection E == ab_biprod_pr2 $o phi)
    by reflexivity.
  apply (ap tr).
  snapply equiv_path_abses_iso.
  exact (Build_GroupIsomorphism _ _ phi
           (short_five_lemma (F := point (AbSES B I)) phi p0 p1);
         (p0, p1)).
Defined.

(** Conversely, a group all of whose extensions are trivial is injective. *)
Definition isabinjective_from_ext_trivial `{Univalence} {I : AbGroup}
  (triv : forall (B : AbGroup) (E : AbSES B I), tr E = point (Ext B I))
  : IsAbInjective I.
Proof.
  apply (snd (iff_isabinjective_embeddings_split I)).
  intros C m hm.
  pose proof ((iff_ab_ext_trivial_split (abses_from_inclusion m))^-1
                (triv _ (abses_from_inclusion m))) as hs.
  strip_truncations.
  destruct hs as [s hsp].
  apply tr.
  exists (ab_biprod_pr1 $o projection_split_iso (abses_from_inclusion m) hsp).
  intro a.
  exact (ap ab_biprod_pr1
           (projection_split_beta (abses_from_inclusion m) hsp a)).
Defined.

(** Injectivity is equivalent to the vanishing of all extensions. *)
Definition iff_isabinjective_ext_trivial `{Univalence} (I : AbGroup)
  : IsAbInjective I
    <-> (forall (B : AbGroup) (E : AbSES B I), tr E = point (Ext B I))
  := (fun inj B E => @isabinjective_ext_trivial _ I inj B E,
      isabinjective_from_ext_trivial).
