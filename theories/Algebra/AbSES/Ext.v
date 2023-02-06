Require Import Pointed WildCat.
Require Import Truncations.SeparatedTrunc.
Require Import AbelianGroup AbHom AbProjective.
Require Import AbSES.Pullback AbSES.BaerSum AbSES.Core.

(** * The set [Ext B A] of abelian group extensions *)

Definition Ext (B A : AbGroup) := pTr 0 (AbSES B A).

(** An extension [E : AbSES B A] is trivial in [Ext B A] if and only if [E] merely splits. *)
Proposition iff_ab_ext_trivial_split `{Univalence} {B A : AbGroup} (E : AbSES B A)
  : merely {s : GroupHomomorphism B E & (projection _) $o s == idmap}
           <~> (tr E = point (Ext B A)).
Proof.
  refine (equiv_path_Tr _ _ oE _).
  srapply equiv_iff_hprop;
    apply Trunc_functor;
    apply iff_abses_trivial_split.
Defined.

Definition Ext' (B A : AbGroup) := Tr 0 (AbSES' B A).

Global Instance isbifunctor_ext' `{Univalence}
  : IsBifunctor (Ext' : AbGroup^op -> AbGroup -> Type)
  := isbifunctor_compose _ _.

(** [Ext B A] is an abelian group for any [A B : AbGroup]. The proof of commutativity is a bit faster if we separate out the proof that [Ext B A] is a group. *)
Definition grp_ext `{Univalence} (A B : AbGroup) : Group.
Proof.
  snrapply (Build_Group (Ext B A)).
  - intros E F.
    strip_truncations.
    exact (tr (abses_baer_sum E F)).
  - exact (point (Ext B A)).
  - unfold Negate.
    exact (Trunc_functor _ (abses_pullback (- grp_homo_id))).
  - repeat split.
    1: exact _.
    all: intro E.  1: intros F G.
    all: strip_truncations; unfold mon_unit, point; apply (ap tr).
    + symmetry; apply baer_sum_associative.
    + apply baer_sum_unit_l.
    + apply baer_sum_unit_r.
    + apply baer_sum_inverse_r.
    + apply baer_sum_inverse_l.
Defined.

Definition ab_ext `{Univalence} (A B : AbGroup) : AbGroup.
Proof.
  snrapply (Build_AbGroup (grp_ext B A)).
  intros E F.
  strip_truncations; cbn.
  apply ap.
  apply baer_sum_commutative.
Defined.

(** ** Extensions ending in a projective are trivial *)

Proposition abext_trivial_projective `{Univalence}
  (P : AbGroup) `{IsAbProjective P}
  : forall A, forall E : AbSES P A, tr E = point (Ext P A).
Proof.
  intros A E.
  apply iff_ab_ext_trivial_split.
  exact (fst (iff_isabprojective_surjections_split P) _ _ _ _).
Defined.

(** It follows that when [P] is projective, [Ext P A] is contractible. *)
Global Instance contr_abext_projective `{Univalence}
  (P : AbGroup) `{IsAbProjective P} {A : AbGroup}
  : Contr (Ext P A).
Proof.
  exists (point _); intro E.
  strip_truncations.
  symmetry; by apply abext_trivial_projective.
Defined.

(* Converely, if all extensions ending in [P] are trivial, then [P] is projective. *)
Proposition abext_projective_trivial `{Univalence} (P : AbGroup)
  (ext_triv : forall A, forall E : AbSES P A, tr E = point (Ext P A))
  : IsAbProjective P.
Proof.
  apply iff_isabprojective_surjections_split.
  intros E p issurj_p.
  apply (iff_ab_ext_trivial_split (abses_from_surjection p))^-1.
  apply ext_triv.
Defined.
