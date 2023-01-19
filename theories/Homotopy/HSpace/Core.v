Require Export Classes.interfaces.abstract_algebra.
Require Import Pointed.

Local Open Scope pointed_scope.
Local Open Scope trunc_scope.
Local Open Scope mc_mult_scope.

Local Notation pt := (point _).
Local Notation "[ X , x ]" := (Build_pType X x).

(** * H-spaces *)

(** A (noncoherent) H-space [X] is a pointed type with a binary operation for which the base point is a both a left and a right identity. (See Coherent.v for the notion of a coherent H-space.) We say [X] is left-invertible if left multiplication by any element is an equivalence, and dually for right-invertible. *)

Class IsHSpace (X : pType) := {
  hspace_op : SgOp X;
  hspace_left_identity : LeftIdentity hspace_op pt;
  hspace_right_identity : RightIdentity hspace_op pt;
}.
#[export] Existing Instances hspace_left_identity hspace_right_identity hspace_op.

Global Instance hspace_mon_unit {X : pType} `{IsHSpace X} : MonUnit X := pt.

Definition issig_ishspace {X : pType}
  : { mu : X -> X -> X & prod (forall x, mu pt x = x) (forall x, mu x pt = x) }
      <~> IsHSpace X := ltac:(make_equiv).

(** Left and right multiplication by the base point is always an equivalence. *)
Global Instance isequiv_hspace_left_op_pt {X : pType} `{IsHSpace X}
  : IsEquiv (pt *.).
Proof.
  apply (isequiv_homotopic idmap); intro x.
  exact (left_identity x)^.
Defined.

Definition equiv_hspace_left_op_pt {X : pType} `{IsHSpace X}
  : X <~> X := Build_Equiv _ _ (pt *.) _.

(** Any element of an H-space defines a pointed self-map by left multiplication. *)
Definition pmap_hspace_left_op {X : pType} `{IsHSpace X} (x : X)
  : X ->* [X, x] := Build_pMap X [X,x] (x *.) (right_identity x).

Definition equiv_hspace_left_op {A : pType} `{IsHSpace A}
  `{forall a, IsEquiv (a *.)} (a : A) : A <~> A
  := Build_Equiv _ _ (a *.) _.

Definition equiv_hspace_right_op {A : pType} `{IsHSpace A}
  `{forall a, IsEquiv (.* a)} (a : A) : A <~> A
  := Build_Equiv _ _ (.* a) _.

(** We make [(pt *.)] into a pointed equivalence using the right identity. If we'd use the left identity, we'd get a map that's equal to the identity as a pointed map, but without coherence (see Coherent.v) this is necessarily the case for this map. *)
Definition pequiv_hspace_left_op_pt {X : pType} `{IsHSpace X} : X <~>* X
  := Build_pEquiv' equiv_hspace_left_op_pt (right_identity pt).

Definition pequiv_hspace_left_op_pt_beta {X : pType} `{IsHSpace X}
  : pmap_hspace_left_op pt ==* pequiv_hspace_left_op_pt.
Proof.
  srapply Build_pHomotopy.
  1: reflexivity.
  cbn.
  exact (concat_pV _)^.
Defined.

Global Instance isequiv_hspace_right_op_pt {X : pType} `{IsHSpace X}
  : IsEquiv (.* pt).
Proof.
  apply (isequiv_homotopic idmap); intro x.
  exact (right_identity x)^.
Defined.

Definition equiv_hspace_right_op_pt {X : pType} `{IsHSpace X}
  : X <~> X := Build_Equiv _ _ (.* pt) _.

(** ** Paths between H-space structures *)

(** Paths between H-space structures correspond to homotopies between the underlying binary operations which respect the identities. This is the type of the latter. *)
Definition path_ishspace_type {X : pType} (mu nu : IsHSpace X) : Type.
Proof.
  destruct mu as [mu mu_lid mu_rid], nu as [nu nu_lid nu_rid].
  refine { h : forall x0 x1, mu x0 x1 = nu x0 x1 & prod (forall x:X, _)  (forall x:X, _) }.
  - exact (mu_lid x = h pt x @ nu_lid x).
  - exact (mu_rid x = h x pt @ nu_rid x).
Defined.

(** Transport of left and right identities of binary operations along paths between the underlying functions. *)
Local Definition transport_binop_lr_id `{Funext} {X : Type} {x : X}
  {mu nu : X -> X -> X} `{mu_lid : forall y, mu x y = y}
  `{mu_rid : forall y, mu y x = y} (p : mu = nu)
  : transport (fun m : X -> X -> X =>
                 (forall y, m x y = y) * (forall y, m y x = y))
      p (mu_lid, mu_rid)
    = (fun y => (ap100 p _ _)^ @ mu_lid y,
         fun y => (ap100 p _ _)^ @ mu_rid y).
Proof.
  induction p; cbn.
  apply path_prod'; funext y.
  all: exact (concat_1p _)^.
Defined.

(** Characterization of paths between H-space structures. *)
Definition equiv_path_ishspace `{Funext} {X : pType} (mu nu : IsHSpace X)
  : path_ishspace_type mu nu <~> (mu = nu).
Proof.
  destruct mu as [mu mu_lid mu_rid], nu as [nu nu_lid nu_rid];
    unfold path_ishspace_type.
  nrefine (equiv_ap_inv' issig_ishspace _ _ oE _).
  nrefine (equiv_path_sigma _ _ _ oE _); cbn.
  snrapply (equiv_functor_sigma' (equiv_path_arrow2 _ _)); intro h; cbn.
  nrefine (equiv_concat_l _ _ oE _).
  1: apply transport_binop_lr_id.
  nrefine (equiv_path_prod _ _ oE _); cbn.
  snrapply equiv_functor_prod';
    nrefine (equiv_path_forall _ _ oE _);
    apply equiv_functor_forall_id; intro x.
  all: nrefine (equiv_moveR_Vp _ _ _ oE _);
    apply equiv_concat_r;
    apply whiskerR; symmetry;
    apply ap100_path_arrow2.
Defined.

(** ** Connected H-spaces *)

(** For connected H-spaces, left and right mulitiplication by an element is an equivalence. This is because left and right multiplication by the base point is one, and being an equivalence is a proposition. *)

Global Instance isequiv_hspace_left_op `{Univalence} {A : pType}
  `{IsHSpace A} `{IsConnected 0 A}
  : forall (a : A), IsEquiv (a *.).
Proof.
  refine (conn_map_elim (-1) (unit_name _) _ _).
  apply Unit_ind.
  srapply (isequiv_homotopic idmap).
  intro a; symmetry.
  apply left_identity.
Defined.

Global Instance isequiv_hspace_right_op `{Univalence} {A : pType}
  `{IsHSpace A} `{IsConnected 0 A}
  : forall (a : A), IsEquiv (.* a).
Proof.
  refine (conn_map_elim (-1) (unit_name _) _ _).
  apply Unit_ind.
  srapply (isequiv_homotopic idmap).
  intro a; symmetry.
  apply right_identity.
Defined.


(** ** Results about H-spaces *)

(** *** H-spaces are homogeneous *)

(** A homogeneous structure on a pointed type [A] gives, for any point [a : A], a self-equivalence of [A] sending the base point to [a]. *)
Class IsHomogeneous (A : pType)
  := ishomogeneous : forall a, A <~>* [A, a].

(** Any homogeneous structure can be modified so that the base point is mapped to the identity. *)

Definition homogeneous_pt_id {A : pType} `{IsHomogeneous A}
  : forall a, A <~>* [A,a]
  := fun a => ishomogeneous a o*E (ishomogeneous (point A))^-1*.

Definition homogeneous_pt_id_beta `{Funext} {A : pType} `{IsHomogeneous A}
  : homogeneous_pt_id (point A) = pequiv_pmap_idmap
  := ltac:(apply path_pequiv, peisretr).

(** This modified structure makes any homogeneous type into an H-space. *)
Global Instance ishspace_homogeneous {A : pType} `{IsHomogeneous A}
  : IsHSpace A.
Proof.
  srapply Build_IsHSpace.
  - exact (fun a b => homogeneous_pt_id a b).
  - intro a; cbn.
    apply eisretr.
  - intro a; cbn.
    exact (ap _ (point_eq (ishomogeneous pt)^-1*)
                   @ point_eq (ishomogeneous a)).
Defined.

(** Left-invertible H-spaces are homogeneous, giving a logical equivalence between H-spaces and homogeneous types. *)
Global Instance ishomogeneous_hspace {A : pType} `{IsHSpace A}
  `{forall a, IsEquiv (a *.)} : IsHomogeneous A.
Proof.
  intro a.
  srapply Build_pEquiv'.
  1: exact (Build_Equiv _ _ (a *.) _).
  cbn. apply right_identity.
Defined.

(** *** Promoting unpointed homotopies to pointed homotopies *)

(** Two pointed maps [f g : Y ->* X] into an H-space type are equal if and only if they are equal as unpointed maps. (Note: This is a logical "iff", not an equivalence of types.)

This was first observed by Evan Cavallo for homogeneous types. Below we show a generalization due to Egbert Rijke, which we then specialize to H-spaces. Notably, the specialization does not require left-invertibility. *)

Definition phomotopy_from_homotopy {A B : pType}
  (m : forall (a : A), (point A) = (point A) -> a = a)
  (q : forall p, m _ p = p) {f g : B ->* A} (K : pointed_fun f = g)
  : f ==* g.
Proof.
  rapply issig_phomotopy.
  destruct f as [f fpt], g as [g gpt]; cbn in *.
  induction K.
  destruct A as [A a0]; cbn in *.
  induction fpt.
  exists (fun b => m (f b) (idpath @ gpt^)).
  apply q.
Defined.

(** Assuming [Funext], it we may take [K] to be a homotopy. *)
Definition phomotopy_from_homotopy' `{Funext} {A B : pType}
  (m : forall (a : A), (point A) = (point A) -> a = a)
  (q : forall p, m _ p = p) {f g : B ->* A} (K : f == g)
  : f ==* g
  := (phomotopy_from_homotopy m q (path_forall _ _ K)).

(** We specialize to H-spaces.*)
Definition hspace_phomotopy_from_homotopy `{Funext} {A B : pType}
  `{IsHSpace A} {f g : B ->* A} (K : f == g)
  : f ==* g.
Proof.
  srapply (phomotopy_from_homotopy' _ _ K).
  - intros a p.
    refine (_^ @ (ap ((a *.) o (pt *.)^-1) p @ _)).
    all: exact (point_eq (pmap_hspace_left_op a
                            o* pequiv_hspace_left_op_pt^-1*)).
 - intro p; lazy beta.
   apply moveR_Vp.
   pose (Q := pmap_prewhisker _ pequiv_hspace_left_op_pt_beta
                @* peisretr _).
   refine (whiskerL _ (point_htpy Q)^
             @ _ @ whiskerR (point_htpy Q) _); cbn.
   hott_simpl.
   apply concat_A1p.
Defined.

(** A version with actual paths. *)
Definition homogeneous_path_pforall_from_path_arrow `{Funext} {A B : pType}
  `{IsHSpace A} {f g : B ->* A} (K : pointed_fun f = g)
  : f = g.
Proof.
  apply path_pforall, hspace_phomotopy_from_homotopy.
  apply (path_arrow _ _)^-1.
  exact K.
Defined.
