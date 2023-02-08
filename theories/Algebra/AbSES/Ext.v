Require Import Pointed WildCat.
Require Import Truncations.SeparatedTrunc.
Require Import AbelianGroup AbHom AbProjective.
Require Import AbSES.Pullback AbSES.BaerSum AbSES.Core.

(** * The set [Ext B A] of abelian group extensions *)

Definition Ext (B A : AbGroup@{u}) := pTr 0 (AbSES@{u v} B A).

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

Definition Ext' (B A : AbGroup@{u}) := Tr 0 (AbSES'@{u v} B A).

Global Instance isbifunctor_ext'@{u v w | u < v, v < w} `{Univalence}
  : IsBifunctor@{v v w u u v v} (Ext' : AbGroup@{u}^op -> AbGroup@{u} -> Type@{v})
  := isbifunctor_compose@{v v w w v v u u u u u u u u v v}
       _ _ (P:=isbifunctor_abses'@{w u v v}).

(** [Ext B A] is an abelian group for any [A B : AbGroup]. The proof of commutativity is a bit faster if we separate out the proof that [Ext B A] is a group. *)
Definition grp_ext@{u v +} `{Univalence} (A B : AbGroup@{u}) : Group@{v}.
Proof.
  snrapply (Build_Group@{v} (Ext@{u v} B A)).
  - intros E F.
    strip_truncations.
    exact (tr (abses_baer_sum E F)).
  - exact (point (Ext B A)).
  - unfold Negate.
    exact (Trunc_functor _ (abses_pullback (- grp_homo_id))).
  - repeat split.
    1: apply istrunc_truncation@{v v}.
    all: intro E.  1: intros F G.
    all: strip_truncations; unfold mon_unit, point; apply (ap tr).
    + symmetry; apply baer_sum_associative.
    + apply baer_sum_unit_l.
    + apply baer_sum_unit_r.
    + apply baer_sum_inverse_r.
    + apply baer_sum_inverse_l.
Defined.

Definition ab_ext@{u v | u < v} `{Univalence}
  (A B : AbGroup@{u}) : AbGroup@{v}.
Proof.
  snrapply (Build_AbGroup (grp_ext@{u v} B A)).
  intros E F.
  strip_truncations; cbn.
  apply ap.
  apply baer_sum_commutative.
Defined.

(** We can push out a fixed extension while letting the map vary, and this defines a group homomorphism. *)
Definition abses_pushout_ext@{u v w | u < v, v < w} `{Univalence}
  {B A G : AbGroup@{u}} (E : AbSES@{u v} B A)
  : GroupHomomorphism (ab_hom A G) (ab_ext B G).
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact (fun f => fmap01 (A:=AbGroup^op) Ext' _ f (tr E)).
  intros f g; cbn.
  nrapply (ap tr@{v}).
  exact (baer_sum_distributive_pushouts@{u v} f g).
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
