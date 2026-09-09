From HoTT Require Import Basics Types ReflectiveSubuniverse Modality Pointed.Core Pointed.pMap.

Local Open Scope pointed_scope.

(** * Modalities, reflective subuniverses and pointed types *)

#[export] Instance ispointed_O `{O : ReflectiveSubuniverse} (X : Type)
  `{IsPointed X} : IsPointed (O X) := to O _ (point X).

Definition pto (O : ReflectiveSubuniverse@{u}) (X : pType@{u})
  : X ->* [O X, _]
  := Build_pMap (to O X) idpath.

(** If [A] is already [O]-local, then Coq knows that [pto] is an equivalence, so we can simply define: *)
Definition pequiv_pto `{O : ReflectiveSubuniverse} {X : pType} `{In O X}
  : X <~>* [O X, _] := Build_pEquiv (pto O X) _.

(** Applying [O_rec] to a pointed map yields a pointed map. *)
Definition pO_rec `{O : ReflectiveSubuniverse} {X Y : pType}
  `{In O Y} (f : X ->* Y) : [O X, _] ->* Y
  := Build_pMap (O_rec f) (O_rec_beta _ _ @ point_eq f).

Definition pO_rec_beta `{O : ReflectiveSubuniverse} {X Y : pType}
  `{In O Y} (f : X ->* Y)
  : pO_rec f o* pto O X ==* f.
Proof.
  srapply Build_pHomotopy.
  1: napply O_rec_beta.
  cbn.
  apply moveL_pV.
  exact (concat_1p _)^.
Defined.

(** A pointed version of the induction principle for a modality. *)
Definition pO_ind `{O : Modality} {X : pType} {Y : pFam [O X, _]}
 `{forall x, In O (Y x)} (f : pForall X (pfam_precompose Y (pto O X)))
  : pForall [O X, _] Y
  := Build_pForall _ Y (O_ind Y f) (O_ind_beta Y f pt @ dpoint_eq f).

Definition pO_ind_beta `{O : Modality} {X : pType} {Y : pFam [O X, _]}
 `{forall x, In O (Y x)} (f : pForall X (pfam_precompose Y (pto O X)))
  : functor_pforall_left (pO_ind f) (pto O X) ==* f.
Proof.
  srapply Build_pHomotopy.
  1: napply O_ind_beta.
  cbn; unfold moveL_equiv_V; cbn.
  apply moveL_pV.
  symmetry; lhs napply concat_1p.
  lhs napply ap_idmap.
  apply concat_1p.
Defined.

(** To show two pointed maps out of [O X] into an [O]-local type are pointed homotopic, it is enough to compare their precomposites with [pto O X]. Unlike passing through [pequiv_ptr_rec], this needs no [Funext]. And note that it goes through without assuming that [O] is a modality. *)
Definition pO_indpaths `{O : ReflectiveSubuniverse} {X Y : pType} `{In O Y}
  {f g : [O X, _] ->* Y} (h : f o* pto O X ==* g o* pto O X)
  : f ==* g.
Proof.
  snapply Build_pHomotopy.
  - exact (O_indpaths _ _ h).
  - lhs napply O_indpaths_beta.
    lhs napply (dpoint_eq h); cbn.
    exact (concat_1p _ @@ inverse2 (concat_1p _)).
Defined.

(** A pointed version of the universal property. *)
Definition pequiv_o_pto_O `{Funext}
  (O : ReflectiveSubuniverse) (P Q : pType) `{In O Q}
  : ([O P, _] ->** Q) <~>* (P ->** Q).
Proof.
  snapply Build_pEquiv.
  (* We could just use the map [e] defined in the next bullet, but we want Coq to immediately unfold the underlying map to this. *)
  - exact (Build_pMap (fun f => f o* pto O P) 1).
  (* We'll give an equivalence that definitionally has the same underlying map. *)
  - transparent assert (e : (([O P, _] ->* Q) <~> (P ->* Q))).
    + refine (issig_pmap P Q oE _ oE (issig_pmap [O P, _] Q)^-1%equiv).
      snapply equiv_functor_sigma'.
      * rapply equiv_o_to_O.
      * intro f; cbn.
      (* [reflexivity] works here, but then the underlying map won't agree definitionally with precomposition by [pto P], since pointed composition inserts a reflexivity path here. *)
      apply (equiv_concat_l 1).
    + exact (equiv_isequiv e).
Defined.

(** Precomposition with an [O]-connected pointed map is an equivalence on pointed mapping spaces into an [O]-local type.  This is a pointed version of [equiv_o_conn_map].  Note that it does not subsume [pequiv_o_pto_O], since [to O X] is only known to be [O]-connected when [O] is a modality. *)
Definition pequiv_o_conn_map `{Funext} (O : ReflectiveSubuniverse)
  {A B : pType} (f : A ->* B) `{IsConnMap O _ _ f} (Y : pType) `{In O Y}
  : (B ->** Y) <~>* (A ->** Y).
Proof.
  snapply Build_pEquiv.
  (* As in [pequiv_o_pto_O], we give the underlying map first so that Coq unfolds it to precomposition with [f]. *)
  - exact (Build_pMap (fun g => g o* f) (path_pforall (postcompose_pconst f))).
  - transparent assert (e : ((B ->* Y) <~> (A ->* Y))).
    + refine (issig_pmap A Y oE _ oE (issig_pmap B Y)^-1%equiv).
      snapply equiv_functor_sigma'.
      * rapply (equiv_o_conn_map O f (fun _ => Y)).
      * intro g; cbn.
        (* This is the path that pointed composition inserts, so the underlying map agrees definitionally with precomposition by [f]. *)
        exact (equiv_concat_l (ap g (point_eq f)) _).
    + exact (equiv_isequiv e).
Defined.

(** ** Pointed functoriality *)

Definition O_pfunctor `(O : ReflectiveSubuniverse) {X Y : pType}
  (f : X ->* Y) : [O X, _] ->* [O Y, _]
  := pO_rec (pto O Y o* f).

(** Coq knows that [O_pfunctor O f] is an equivalence whenever [f] is. *)
Definition equiv_O_pfunctor `(O : ReflectiveSubuniverse) {X Y : pType}
  (f : X ->* Y) `{IsEquiv _ _ f} : [O X, _] <~>* [O Y, _]
  := Build_pEquiv (O_pfunctor O f) _.

(** Pointed naturality of [O_pfunctor]. *)
Definition pto_O_natural `(O : ReflectiveSubuniverse) {X Y : pType}
  (f : X ->* Y) : O_pfunctor O f o* pto O X ==* pto O Y o* f
  := pO_rec_beta _.

Definition pequiv_O_inverts `(O : ReflectiveSubuniverse) {X Y : pType}
  (f : X ->* Y) `{O_inverts O f}
  : [O X, _] <~>* [O Y, _]
  := Build_pEquiv (O_pfunctor O f) _.
