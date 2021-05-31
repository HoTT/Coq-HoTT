Require Import HoTT.Basics HoTT.Types HFiber Pullback Pointed Truncations.
Require Import Modalities.ReflectiveSubuniverse Modalities.Identity.

Local Open Scope pointed_scope.

(** * The object classifier *)

(** We prove that type families correspond to fibrations [equiv_sigma_fibration] (Theorem 4.8.3) and the projection [pointed_type : pType -> Type] is an object classifier [ispullback_square_objectclassifier] (Theorem 4.8.4). *)

(** We denote the type of all maps into a type [Y] as follows, and refer to them "bundles over Y". *)
Definition Slice (Y : Type@{u}) := { X : Type@{u} & X -> Y }.
Definition pSlice (Y : pType@{u}) := { X : pType@{u} & X ->* Y }.

Definition sigma_fibration@{u v} {Y : Type@{u}} (P : Y -> Type@{u}) : Slice@{u v} Y
  := (sig@{u u} P; pr1).

Definition sigma_fibration_inverse {Y : Type@{u}} (p : Slice Y) : Y -> Type@{u}
  := hfiber p.2.

Theorem isequiv_sigma_fibration `{Univalence} {Y : Type}
  : IsEquiv (@sigma_fibration Y).
Proof.
  srapply isequiv_adjointify.
  - exact sigma_fibration_inverse.
  - intros [X p].
    srapply path_sigma; cbn.
    + exact (path_universe (equiv_fibration_replacement _)^-1%equiv).
    + apply transport_arrow_toconst_path_universe.
  - intro P.
    funext y; cbn.
    exact ((path_universe (@hfiber_fibration  _ y P))^).
Defined.

(** Theorem 4.8.3. *)
Definition equiv_sigma_fibration `{Univalence} {Y : Type@{u}}
  : (Y -> Type@{u}) <~> { X : Type@{u} & X -> Y }
  := Build_Equiv _ _ _ isequiv_sigma_fibration.

(** The universal map is the forgetful map [pointed_type : pType -> Type]. *)

(** We construct the universal square for the object classifier. *)
Local Definition topmap {A : Type} (P : A -> Type) (e : sig P) : pType
  := Build_pType (P e.1) e.2.

(** The square commutes definitionally. *)
Definition objectclassifier_square {A : Type} (P : A -> Type)
  : P o pr1 == pointed_type o (topmap P)
  := fun e : sig P => idpath (P e.1).

(** Theorem 4.8.4. *)
Theorem ispullback_objectclassifier_square {A : Type} (P : A -> Type)
  : IsPullback (objectclassifier_square P).
Proof.
  srapply isequiv_adjointify.
  - intros [a [F p]].
    exact (a; transport idmap p^ (point F)).
  - intros [a [[T t] p]]; cbn in p.
    refine (path_sigma' _ (idpath a) _).
    by induction p.
  - reflexivity.
Defined.

(** ** Classifying bundles with specified fiber *)

Local Notation "( X , x )" := (Build_pType X x).

(** Bundles over [B] with fiber [F] correspond to pointed maps into the universe pointed at [F]. *)
Proposition equiv_sigma_fibration_p@{u v +} `{Univalence} {Y : pType@{u}} {F : Type@{u}}
  : (Y ->* (Type@{u}, F)) <~> { p : Slice@{u v} Y & hfiber p.2 (point Y) <~> F }.
Proof.
  refine (_ oE (issig_pmap _ _)^-1).
  srapply (equiv_functor_sigma' equiv_sigma_fibration); intro P; cbn.
  refine (_ oE (equiv_path_universe@{u u v} _ _)^-1%equiv).
  refine (equiv_functor_equiv _ equiv_idmap).
  apply hfiber_fibration.
Defined.

(** If the fiber [F] is pointed we may upgrade the right-hand side to pointed fiber sequences. *)
Lemma equiv_pfiber_fibration_pfibration@{u v} {Y F : pType@{u}}
  : { p : Slice@{u v} Y & hfiber p.2 (point Y) <~> F}
      <~> { p : pSlice@{u v} Y & pfiber p.2 <~>* F }.
Proof.
  equiv_via
    (sig@{v u} (fun X : Type@{u} =>
                  { x : X &
                        { p : X -> Y &
                                  { eq : p x = point Y &
                                         { e : hfiber p (point Y) <~> F
                                               & e^-1 (point F) = (x; eq) } } } })).
  - refine (_ oE _).
    + do 5 (rapply equiv_functor_sigma_id; intro).
      apply equiv_path_sigma.
    + make_equiv_contr_basedpaths.
  - refine (_ oE _).
    2: { do 5 (rapply equiv_functor_sigma_id; intro).
         exact (equiv_path_inverse _ _ oE equiv_moveL_equiv_M _ _). }
    make_equiv.
Defined.

Definition equiv_sigma_pfibration@{u v +} `{Univalence} {Y F : pType@{u}}
  : (Y ->* (Type@{u}, F)) <~> { p : pSlice@{u v} Y & pfiber p.2 <~>* F}
  := equiv_pfiber_fibration_pfibration oE equiv_sigma_fibration_p.

(** * The classifier for O-local types *)

(** Families of O-local types correspond to bundles with O-local fibers. *)
Theorem equiv_sigma_fibration_O@{u v} `{Univalence} {O : Subuniverse} {Y : Type@{u}}
  : (Y -> Type_@{u v} O) <~> { p : { X : Type@{u} & X -> Y } & MapIn O p.2 }.
Proof.
  refine (_ oE (equiv_sig_coind _ _)^-1).
  apply (equiv_functor_sigma' equiv_sigma_fibration); intro P; cbn.
  rapply equiv_forall_inO_mapinO_pr1.
Defined.

(** ** Classifying O-local bundles with specified fiber *)

(** We consider a pointed base [Y], and the universe of O-local types [Type_ O] pointed at some O-local type [F]. *)

(** Pointed maps into [Type_ O] correspond to O-local bundles with fiber [F] over the base point of [Y]. *)
Proposition equiv_sigma_fibration_Op@{u v +} `{Univalence} {O : Subuniverse}
            {Y : pType@{u}} {F : Type@{u}} `{inO : In O F}
  : (Y ->* (Type_ O, (F; inO)))
      <~> { p : { q : Slice@{u v} Y & MapIn O q.2 } & hfiber p.1.2 (point Y) <~> F }.
Proof.
  refine (_ oE (issig_pmap _ _)^-1); cbn.
  srapply (equiv_functor_sigma' equiv_sigma_fibration_O); intro P; cbn.
  refine (_ oE (equiv_path_sigma_hprop _ _)^-1%equiv); cbn.
  refine (_ oE (equiv_path_universe _ _)^-1%equiv).
  refine (equiv_functor_equiv _ equiv_idmap).
  exact (hfiber_fibration (point Y) _).
Defined.

(** When the base [Y] is connected, the fibers being O-local follow from the fact that the fiber [F] over the base point is. *)
Proposition equiv_sigma_fibration_Op_connected@{u v +} `{Univalence} {O : Subuniverse}
            {Y : pType@{u}} `{IsConnected 0 Y} {F : Type@{u}} `{inO : In O F}
  : (Y ->* (Type_ O, (F; inO)))
       <~> { p : Slice@{u v} Y & hfiber p.2 (point Y) <~> F }.
Proof.
  refine (_ oE equiv_sigma_fibration_Op).
  refine (_ oE (equiv_sigma_assoc' _ (fun p _ => hfiber p.2 (point Y) <~> F))^-1%equiv).
  srapply equiv_functor_sigma_id; intro; cbn.
  refine (_ oE equiv_sigma_symm0 _ _).
  apply equiv_sigma_contr; intro e.
  rapply contr_inhabited_hprop.
  rapply conn_point_elim@{u v u u u u u u v}.
  apply (inO_equiv_inO F e^-1).
Defined.

(** *** Classifying O-local bundles with specified pointed fiber *)

(** When the fiber [F] is pointed, the right-hand side can be upgraded to pointed fiber sequences with O-local fibers.  *)
Proposition equiv_sigma_pfibration_O `{Univalence} (O : Subuniverse)
            {Y F : pType} `{inO : In O F}
  : (Y ->* (Type_ O, (pointed_type F; inO)))
      <~> { p : { q : pSlice Y & MapIn O q.2 } & pfiber p.1.2 <~>* F }.
Proof.
  refine (_ oE equiv_sigma_fibration_Op).
  refine (_ oE equiv_sigma_symm' _ (fun q => hfiber q.2 (point Y) <~> F)).
  refine (equiv_sigma_symm' (fun q => pfiber q.2 <~>* F) _ oE _).
  by rapply (equiv_functor_sigma' equiv_pfiber_fibration_pfibration).
Defined.

(** When moreover the base [Y] is connected, the right-hand side is exactly the type of pointed fiber sequences, since the fibers being O-local follow from [F] being O-local and [Y] connected. *)
Definition equiv_sigma_pfibration_O_connected@{u v +} `{Univalence} (O : Subuniverse)
          {Y F : pType@{u}} `{IsConnected 0 Y} `{inO : In O F}
  : (Y ->* (Type_ O, (pointed_type F; inO)))
      <~> { p : pSlice@{u v} Y & pfiber p.2 <~>* F }
  := equiv_pfiber_fibration_pfibration oE equiv_sigma_fibration_Op_connected.

(** As a corollary, pointed maps into the unverse of O-local types are just pointed maps into the universe, when the base [Y] is connected. *)
Definition equiv_pmap_typeO_type_connected `{Univalence} {O : Subuniverse}
      {Y : pType@{u}} `{IsConnected 0 Y} {F : Type@{u}} `{inO : In O F}
  : (Y ->* (Type_ O, (F; inO))) <~> (Y ->* (Type@{u}, F))
  := equiv_sigma_fibration_p^-1 oE equiv_sigma_fibration_Op_connected.
