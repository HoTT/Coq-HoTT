Require Import Basics Types Truncations.Core.
Require Import Pointed WildCat.
Require Import Truncations.SeparatedTrunc.
Require Import AbelianGroup AbHom AbProjective.
Require Import AbSES.Pullback AbSES.BaerSum AbSES.Core.

Local Open Scope mc_scope.
Local Open Scope mc_add_scope.

(** * The set [Ext B A] of abelian group extensions *)

Definition Ext (B A : AbGroup@{u}) := pTr 0 (AbSES B A).

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

Definition Ext' (B A : AbGroup@{u}) := Tr 0 (AbSES' B A).

Global Instance isbifunctor_ext'@{u v w | u < v, v < w} `{Univalence}
  : IsBifunctor@{v v w u u v v} (Ext' : AbGroup@{u}^op -> AbGroup@{u} -> Type@{v})
  := isbifunctor_compose _ _ (P:=isbifunctor_abses').

(** [Ext B A] is an abelian group for any [A B : AbGroup]. The proof of commutativity is a bit faster if we separate out the proof that [Ext B A] is a group. *)
Definition grp_ext `{Univalence} (B A : AbGroup@{u}) : Group.
Proof.
  snrapply (Build_Group (Ext B A)).
  - intros E F.
    strip_truncations.
    exact (tr (abses_baer_sum E F)).
  - exact (point (Ext B A)).
  - unfold Negate.
    exact (Trunc_functor _ (abses_pullback (- grp_homo_id))).
  - repeat split.
    1: apply istrunc_truncation.
    all: intro E.  1: intros F G.
    all: strip_truncations; unfold mon_unit, point; apply (ap tr).
    + symmetry; apply baer_sum_associative.
    + apply baer_sum_unit_l.
    + apply baer_sum_unit_r.
    + apply baer_sum_inverse_r.
    + apply baer_sum_inverse_l.
Defined.

(** ** The bifunctor [ab_ext] *)

Definition ab_ext `{Univalence} (B A : AbGroup@{u}) : AbGroup.
Proof.
  snrapply (Build_AbGroup (grp_ext B A)).
  intros E F.
  strip_truncations; cbn.
  apply ap.
  apply baer_sum_commutative.
Defined.

Global Instance is01functor_ext `{Univalence} (B : AbGroup^op)
  : Is0Functor (ab_ext B).
Proof.
  srapply Build_Is0Functor; intros ? ? f.
  snrapply Build_GroupHomomorphism.
  1: exact (fmap01 (A:=AbGroup^op) Ext' B f).
  rapply Trunc_ind; intro E0.
  rapply Trunc_ind; intro E1.
  apply (ap tr); cbn.
  apply baer_sum_pushout.
Defined.

Global Instance is10functor_ext `{Univalence} (A : AbGroup)
  : Is0Functor (fun B : AbGroup^op => ab_ext B A).
Proof.
  srapply Build_Is0Functor; intros ? ? f; cbn.
  snrapply Build_GroupHomomorphism.
  1: exact (fmap10 (A:=AbGroup^op) Ext' f A).
  rapply Trunc_ind; intro E0.
  rapply Trunc_ind; intro E1.
  apply (ap tr); cbn.
  apply baer_sum_pullback.
Defined.

Global Instance isbifunctor_ext `{Univalence}
  : IsBifunctor (A:=AbGroup^op) ab_ext.
Proof.
  snrapply Build_IsBifunctor.
  1,2: exact _.
  intros B B' f A A' g.
  rapply Trunc_ind; intro E.
  apply (ap tr).
  apply abses_pushout_pullback_reorder.
Defined.

(** We can push out a fixed extension while letting the map vary, and this defines a group homomorphism. *)
Definition abses_pushout_ext `{Univalence}
  {B A G : AbGroup@{u}} (E : AbSES B A)
  : GroupHomomorphism (ab_hom A G) (ab_ext B G).
Proof.
  snrapply Build_GroupHomomorphism.
  1: exact (fun f => fmap01 (A:=AbGroup^op) Ext' _ f (tr E)).
  intros f g; cbn.
  nrapply (ap tr).
  exact (baer_sum_distributive_pushouts f g).
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
  apply (Build_Contr _ (point _)); intro E.
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
