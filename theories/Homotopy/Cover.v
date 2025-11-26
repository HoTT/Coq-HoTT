From HoTT Require Import Basics Types HFiber Truncations.Core Truncations.SeparatedTrunc Pointed
  Modalities.ReflectiveSubuniverse.

Local Open Scope pointed_scope.

(** * [O]-connected covers *)

(** Given a reflective subuniverse [O], for any type [X] and [x : O X], the [O]-connected cover of [X] at [x] is the fibre of [to O X] at [x]. *)
Definition O_cover@{u} `{O : ReflectiveSubuniverse@{u}}
  (X : Type@{u}) (x : O X) : Type@{u}
  := hfiber (to O _) x.

(** The "[O]-connected" cover is in fact [O]-connected when [O] is a modality, using [isconnected_hfiber_conn_map]. Since Coq can infer this using typeclasses, we don't restate it here. *)

(** Characterization of paths in [O_cover] is given by [equiv_path_hfiber]. *)

(* If [x] is an actual point of [X], then the connected cover is pointed. *)
Definition O_pcover@{u} (O : ReflectiveSubuniverse@{u})
  (X : Type@{u}) (x : X) : pType@{u}
  := pfiber@{u u u} (pto O [X,x]).

(** Covers commute with products *)
Definition O_pcover_prod `{O : ReflectiveSubuniverse} {X Y : pType@{u}}
  : O_pcover O (X * Y) pt <~>* [(O_pcover O X pt) * (O_pcover O Y pt), _].
Proof.
  srapply Build_pEquiv'.
  { refine (_ oE equiv_functor_sigma_id _).
    2: intro; napply equiv_path_O_prod.
    napply equiv_sigma_prod_prod. }
  napply path_prod; cbn.
  all: snapply path_sigma'.
  1,3: exact idpath.
  all: cbn.
  all: by rewrite concat_p1, concat_Vp.
Defined.

(** ** Functoriality of [O_cover] *)

(** Given [X] and [x : O X], any map [f : X -> Y] out of [X] induces a map [O_cover X x -> O_cover Y (O_functor O f x)]. *)
Definition functor_O_cover@{u v} `{O : ReflectiveSubuniverse} {X Y : Type@{u}}
  (f : X -> Y) (x : O X) : O_cover@{u} X x -> O_cover@{u} Y (O_functor O f x)
  := functor_hfiber (f:=to O _) (g:=to O _)
       (h:=f) (k:=O_functor O f) (to_O_natural O f) x.

Definition equiv_functor_O_cover `{O : ReflectiveSubuniverse}
  {X Y : Type} (f : X -> Y) `{IsEquiv _ _ f} (x : O X)
  : O_cover X x <~> O_cover Y (O_functor O f x)
  := Build_Equiv _ _ (functor_O_cover f x) _.

(** *** Pointed functoriality *)

Definition pfunctor_O_pcover `{O : ReflectiveSubuniverse} {X Y : pType}
  (f : X ->* Y) : O_pcover O X pt ->* O_pcover O Y pt
  := functor_pfiber (pto_O_natural O f).

Definition pequiv_pfunctor_O_pcover `{O : ReflectiveSubuniverse} {X Y : pType}
  (f : X ->* Y) `{IsEquiv _ _ f} : O_pcover O X pt <~>* O_pcover O Y pt
  := Build_pEquiv (pfunctor_O_pcover f) _.

(** In the case of truncations, [ptr_natural] gives a better proof of pointedness. *)
Definition pfunctor_pTr_pcover `{n : trunc_index} {X Y : pType}
  (f : X ->* Y) : O_pcover (Tr n) X pt ->* O_pcover (Tr n) Y pt
  := functor_pfiber (ptr_natural n f).

Definition pequiv_pfunctor_pTr_pcover `{n : trunc_index}
  {X Y : pType} (f : X ->* Y) `{IsEquiv _ _ f}
  : O_pcover (Tr n) X pt <~>* O_pcover (Tr n) Y pt
  := Build_pEquiv (pfunctor_pTr_pcover f) _.


(** * Components *)

(** Path components are given by specializing to [O] being set-truncation. *)
Definition comp := O_cover (O:=Tr 0).
Definition pcomp := O_pcover (Tr 0).

Definition pfunctor_pcomp {X Y : pType} := @pfunctor_pTr_pcover (-1) X Y.
Definition pequiv_pfunctor_pcomp {X Y : pType}
  := @pequiv_pfunctor_pTr_pcover (-1) X Y.

(** If a property holds at a given point, then it holds for the whole component. This yields equivalences like the following: *)
Definition equiv_comp_property `{Univalence} {X : Type} (x : X)
  (P : X -> Type) `{forall x, IsHProp (P x)} (Px : P x)
  : comp (sig P) (tr (x; Px)) <~> comp X (tr x).
Proof.
  unfold comp, O_cover, hfiber. simpl.
  refine (_ oE (equiv_sigma_assoc _ _)^-1).
  apply equiv_functor_sigma_id; intro y.
  apply equiv_iff_hprop.
  - intros [py q].
    exact (ap (Trunc_functor _ pr1) q).
  - refine (equiv_ind (equiv_path_Tr _ _) _ _).
    apply Trunc_rec; intros p; induction p.
    exact (Px; idpath).
Defined.

(** For example, we may take components of equivalences among underlying maps. *)
Definition equiv_comp_equiv_map `{Univalence} {A B : Type} (e : A <~> B)
  : comp (A <~> B) (tr e) <~> comp (A -> B) (tr (equiv_fun e)).
Proof.
  refine (_ oE equiv_functor_O_cover (issig_equiv _ _)^-1 _); cbn.
  rapply equiv_comp_property.
Defined.

