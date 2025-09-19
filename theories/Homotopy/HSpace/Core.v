Require Export Classes.interfaces.canonical_names (SgOp, sg_op,
    MonUnit, mon_unit, LeftIdentity, left_identity, RightIdentity, right_identity,
    Negate, negate, Associative, simple_associativity, associativity,
    LeftInverse, left_inverse, RightInverse, right_inverse, Commutative, commutativity).
Export canonical_names.BinOpNotations.
From HoTT Require Import Basics Types Pointed WildCat.Core.
Require Import Truncations.Core Truncations.Connectedness.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** * H-spaces *)

(** A (non-coherent) H-space [X] is a pointed type with a binary operation for which the base point is a both a left and a right identity. (See Coherent.v for the notion of a coherent H-space.) We say [X] is left-invertible if left multiplication by any element is an equivalence, and dually for right-invertible. *)

Class IsHSpace (X : pType) := {
  hspace_op :: SgOp X;
  hspace_left_identity :: LeftIdentity hspace_op pt;
  hspace_right_identity :: RightIdentity hspace_op pt;
}.

#[export] Instance hspace_mon_unit {X : pType} `{IsHSpace X} : MonUnit X := pt.

Definition issig_ishspace {X : pType}
  : { mu : X -> X -> X & prod (forall x, mu pt x = x) (forall x, mu x pt = x) }
      <~> IsHSpace X := ltac:(make_equiv).

(** Left and right multiplication by the base point is always an equivalence. *)
Instance isequiv_hspace_left_op_pt {X : pType} `{IsHSpace X}
  : IsEquiv (pt *.).
Proof.
  apply (isequiv_homotopic idmap); intro x.
  exact (left_identity x)^.
Defined.

Instance isequiv_hspace_right_op_pt {X : pType} `{IsHSpace X}
  : IsEquiv (.* pt).
Proof.
  apply (isequiv_homotopic idmap); intro x.
  exact (right_identity x)^.
Defined.

Definition equiv_hspace_left_op {X : pType} `{IsHSpace X}
  (x : X) `{IsEquiv _ _ (x *.)} : X <~> X
  := Build_Equiv _ _ (x *.) _.

Definition equiv_hspace_right_op {X : pType} `{IsHSpace X}
  (x : X) `{IsEquiv _ _ (.* x)} : X <~> X
  := Build_Equiv _ _ (.* x) _.

(** Any element of an H-space defines a pointed self-map by left multiplication, in the following sense. *)
Definition pmap_hspace_left_op {X : pType} `{IsHSpace X} (x : X)
  : X ->* [X, x] := Build_pMap (x *.) (right_identity x).

(** We make [(x *.)] into a pointed equivalence (when possible). In particular, this makes [(pt *.)] into a pointed self-equivalence. We could have also used the left identity to make [(pt *.)] into a pointed self-equivalence, and then we would get a map that's equal to the identity as a pointed map; but without coherence (see Coherent.v) this is not necessarily the case for this map. *)
Definition pequiv_hspace_left_op {X : pType} `{IsHSpace X}
  (x : X) `{IsEquiv _ _ (x *.)} : X <~>* [X,x]
  := Build_pEquiv' (equiv_hspace_left_op x) (right_identity x).

(** ** Connected H-spaces *)

(** For connected H-spaces, left and right multiplication by an element is an equivalence. This is because left and right multiplication by the base point is one, and being an equivalence is a proposition. *)

Instance isequiv_hspace_left_op `{Univalence} {A : pType}
  `{IsHSpace A} `{IsConnected 0 A}
  : forall (a : A), IsEquiv (a *.).
Proof.
  napply conn_point_elim; exact _.
Defined.

Instance isequiv_hspace_right_op `{Univalence} {A : pType}
  `{IsHSpace A} `{IsConnected 0 A}
  : forall (a : A), IsEquiv (.* a).
Proof.
  napply conn_point_elim; exact _.
Defined.

(** ** Left-invertible H-spaces are homogeneous *)

(** A homogeneous structure on a pointed type [A] gives, for any point [a : A], a self-equivalence of [A] sending the base point to [a]. (This is the same data as a left-invertible right-unital binary operation.) *)
Class IsHomogeneous (A : pType)
  := ishomogeneous : forall a, A <~>* [A, a].

(** Any homogeneous structure can be modified so that the base point is mapped to the pointed identity map. *)

Definition homogeneous_pt_id {A : pType} `{IsHomogeneous A}
  : forall a, A <~>* [A,a]
  := fun a => ishomogeneous a o*E (ishomogeneous (point A))^-1*.

Definition homogeneous_pt_id_beta {A : pType} `{IsHomogeneous A}
  : homogeneous_pt_id (point A) ==* pequiv_pmap_idmap
  := peisretr _.

Definition homogeneous_pt_id_beta' `{Funext} {A : pType} `{IsHomogeneous A}
  : homogeneous_pt_id (point A) = pequiv_pmap_idmap
  := ltac:(apply path_pequiv, peisretr).

(** This modified structure makes any homogeneous type into a (left-invertible) H-space. *)
Definition ishspace_homogeneous {A : pType} `{IsHomogeneous A}
  : IsHSpace A.
Proof.
  snapply Build_IsHSpace.
  - exact (fun a b => homogeneous_pt_id a b).
  - intro a; cbn.
    apply eisretr.
  - intro a.  exact (point_eq (homogeneous_pt_id a)).
Defined.

(** Left-invertible H-spaces are homogeneous, giving a logical equivalence between left-invertible H-spaces and homogeneous types. (In fact, the type of homogeneous types with the base point sent to the pointed identity map is equivalent to the type of left-invertible coherent H-spaces, but we don't prove that here.) See [equiv_iscohhspace_ptd_action] for a closely related result. *)
Instance ishomogeneous_hspace {A : pType} `{IsHSpace A}
  `{forall a, IsEquiv (a *.)}
  : IsHomogeneous A
  := (fun a => pequiv_hspace_left_op a).

(** ** Promoting unpointed homotopies to pointed homotopies *)

(** Two pointed maps [f g : Y ->* X] into an H-space are equal if and only if they are equal as unpointed maps. (Note: This is a logical "iff", not an equivalence of types.) This was first observed by Evan Cavallo for homogeneous types. Below we show a generalization due to Egbert Rijke, which we then specialize to H-spaces. Notably, the specialization does not require left-invertibility. This appears as Lemma 2.6 in https://arxiv.org/abs/2301.02636v1 *)

(** First a version that assumes an equality of the unpointed maps. *)
Definition phomotopy_from_path_arrow {A B : pType}
  (m : forall (a : A), (point A) = (point A) -> a = a)
  (q : m pt == idmap) {f g : B ->* A} (K : pointed_fun f = pointed_fun g)
  : f ==* g.
Proof.
  napply issig_phomotopy.
  destruct f as [f fpt], g as [g gpt]; cbn in *.
  induction K.
  destruct A as [A a0]; cbn in *.
  induction fpt.
  exists (fun b => m (f b) (idpath @ gpt^)).
  apply q.
Defined.

(** Assuming [Funext], we may take [K] to be a homotopy. With a more elaborate proof, [Funext] could be avoided here and therefore in the next result as well. *)
Definition phomotopy_from_homotopy `{Funext} {A B : pType}
  (m : forall (a : A), (point A) = (point A) -> a = a)
  (q :  m pt == idmap) {f g : B ->* A} (K : f == g)
  : f ==* g
  := phomotopy_from_path_arrow m q (path_forall _ _ K).

(** We specialize to H-spaces. *)
Definition hspace_phomotopy_from_homotopy `{Funext} {A B : pType}
  `{IsHSpace A} {f g : B ->* A} (K : f == g)
  : f ==* g.
Proof.
  snapply (phomotopy_from_homotopy _ _ K).
  - intro a.
    exact (fmap loops (pmap_hspace_left_op a o* (pequiv_hspace_left_op pt)^-1*)).
  - lazy beta.
    transitivity (fmap (b:=A) loops pmap_idmap).
    2: tapply (fmap_id loops).
    tapply (fmap2 loops).
    napply peisretr.
Defined.

(** A version with actual paths. *)
Definition hspace_path_pforall_from_path_arrow `{Funext} {A B : pType}
  `{IsHSpace A} {f g : B ->* A} (K : pointed_fun f = pointed_fun g)
  : f = g.
Proof.
  apply path_pforall, hspace_phomotopy_from_homotopy.
  apply (path_arrow _ _)^-1.
  exact K.
Defined.

(** A type equivalent to an H-space is an H-space. *)
Definition ishspace_equiv_hspace {X Y : pType} `{IsHSpace Y} (f : X <~>* Y)
  : IsHSpace X.
Proof.
  snapply Build_IsHSpace.
  - exact (fun a b => f^-1 (f a * f b)).
  - intro b.
    rhs_V exact (eissect f b).
    apply ap.
    lhs exact (ap (.* f b) (point_eq f)).
    apply left_identity.
  - intro a.
    rhs_V exact (eissect f a).
    apply ap.
    lhs exact (ap (f a *.) (point_eq f)).
    apply right_identity.
Defined.

(** Every loop space is an H-space. Making this an instance breaks CayleyDickson.v because Coq finds this instance rather than the expected one. *)
Definition ishspace_loops {X : pType} : IsHSpace (loops X).
Proof.
  snapply Build_IsHSpace.
  - exact concat.
  - exact concat_1p.
  - exact concat_p1.
Defined.
