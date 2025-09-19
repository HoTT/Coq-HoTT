From HoTT Require Import Basics Types ReflectiveSubuniverse Pointed.Core.

Local Open Scope pointed_scope.

(** * Modalities, reflective subuniverses and pointed types *)

(** So far, everything is about general reflective subuniverses, but in the future results about modalities can be placed here as well. *)

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
  (f : X ->* Y) : O_pfunctor O f o* pto O X ==* pto O Y o* f.
Proof.
  napply pO_rec_beta.
Defined.

Definition pequiv_O_inverts `(O : ReflectiveSubuniverse) {X Y : pType}
  (f : X ->* Y) `{O_inverts O f}
  : [O X, _] <~>* [O Y, _]
  := Build_pEquiv (O_pfunctor O f) _.
