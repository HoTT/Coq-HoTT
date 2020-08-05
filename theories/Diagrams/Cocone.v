Require Import Basics.
Require Import Types.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.

Local Open Scope path_scope.
Generalizable All Variables.

(** * Cocones *)

(** A Cocone over a diagram [D] to a type [X] is a family of maps from the types of [D] to [X] making the triangles formed with the arrows of [D] commuting. *)

Class Cocone {G : Graph} (D : Diagram G) (X : Type) := {
  legs   : forall i, D i -> X;
  legs_comm  : forall i j (g : G i j), legs j o (D _f g) == legs i;
}.

Arguments Build_Cocone {G D X} legs legs_comm.
Arguments legs {G D X} C i x : rename.
Arguments legs_comm {G D X} C i j g x : rename.

Coercion legs : Cocone >-> Funclass.

Section Cocone.
  Context `{Funext} {G : Graph} {D : Diagram G} {X : Type}.

  (** [path_cocone] says when two cocones are equals (up to funext). *)

  Definition path_cocone_naive {C1 C2 : Cocone D X}
    (P := fun q' => forall (i j : G) (g : G i j) (x : D i),
      q' j (D _f g x) = q' i x)
    (path_legs : legs C1 = legs C2)
    (path_legs_comm : transport P path_legs (legs_comm C1) = legs_comm C2)
    : C1 = C2 :=
    match path_legs_comm in (_ = v1)
      return C1 = {|legs := legs C2; legs_comm := v1 |} 
    with
      | idpath => match path_legs in (_ = v0)
        return C1 = {|legs := v0; legs_comm := path_legs # (legs_comm C1) |}
      with
        | idpath => 1
      end
    end.

  Definition path_cocone {C1 C2 : Cocone D X}
    (path_legs : forall i,  C1 i == C2 i)
    (path_legs_comm : forall i j g x,
      legs_comm C1 i j g x @ path_legs i x
      = path_legs j (D _f g x) @ legs_comm C2 i j g x)
    : C1 = C2.
  Proof.
    destruct C1 as [legs pp_q], C2 as [r pp_r].
    refine (path_cocone_naive (path_forall _ _
      (fun i => path_forall _ _ (path_legs i))) _).
    cbn; funext i j f x.
    rewrite 4 transport_forall_constant, transport_paths_FlFr.
    rewrite concat_pp_p; apply moveR_Vp.
    rewrite 2 (ap_apply_lD2 (path_forall _ _
      (fun i => path_forall _ _ (path_legs i)))).
    rewrite 3 eisretr.
    apply path_legs_comm.
  Defined.

  (** Given a cocone [C] to [X] and a map from [X] to [Y], one can postcompose each map of [C] to get a cocone to [Y]. *)

  Definition cocone_postcompose (C : Cocone D X) {Y : Type}
    : (X -> Y) -> Cocone D Y.
  Proof.
    intros f.
    srapply Build_Cocone; intro i.
    1: exact (f o C i).
    intros j g x.
    exact (ap f (legs_comm _ i j g x)).
  Defined.

  (** ** Universality of a cocone. *)

  (** A colimit will be the extremity of an universal cocone. *)

  (** A cocone [C] over [D] to [X] is said universal when for all [Y] the map [cocone_postcompose] is an equivalence. In particular, given another cocone [C'] over [D] to [X'] the inverse of the map allows to recover a map [h] : [X] -> [X'] such that [C'] is [C] postcomposed with [h]. The fact that [cocone_postcompose] is an equivalence is an elegant way of stating the usual "unique existence" of category theory. *)

  Class UniversalCocone (C : Cocone D X) := {
    is_universal :> forall Y, IsEquiv (@cocone_postcompose C Y);
  }.

  Coercion is_universal : UniversalCocone >-> Funclass.

End Cocone.


(** We now prove several functoriality results, first on cocone and then on colimits. *)

Section FunctorialityCocone.

  Context `{Funext} {G: Graph}.

  (** ** Postcomposition for cocones *)

  (** Identity and associativity for the postcomposition of a cocone with a map. *)

  Definition cocone_postcompose_identity {D : Diagram G} `(C : Cocone _ D X)
    : cocone_postcompose C idmap = C.
  Proof.
    srapply path_cocone; intro i.
    1: reflexivity.
    intros j g x; simpl.
    refine (concat_p1 _ @ ap_idmap _ @ (concat_1p _)^).
  Defined.

  Definition cocone_postcompose_comp {D : Diagram G}
             `(f : X -> Y) `(g : Y -> Z) (C : Cocone D X)
    : cocone_postcompose C (g o f)
      = cocone_postcompose (cocone_postcompose C f) g.
  Proof.
    srapply path_cocone; intro i.
    1: reflexivity.
    intros j h x; simpl.
    refine (concat_p1 _ @ ap_compose _ _ _ @ (concat_1p _)^).
  Defined.

  (** ** Precomposition for cocones *)

  (** Given a cocone over [D2] and a Diagram map [m] : [D1] => [D2], one can precompose each map of the cocone by the corresponding one of [m] to get a cocone over [D1]. *)

  Definition cocone_precompose {D1 D2: Diagram G} (m : DiagramMap D1 D2) {X}
    : (Cocone D2 X) -> (Cocone D1 X).
  Proof.
    intro C.
    srapply Build_Cocone; intro i.
    1: exact (C i o m i).
    intros j g x; simpl.
    etransitivity.
    + apply ap.
      symmetry.
      apply DiagramMap_comm.
    + apply legs_comm.
  Defined.

  (** Identity and associativity for the precomposition of a cocone with a diagram map. *)

  Definition cocone_precompose_identity (D : Diagram G) (X : Type)
    : cocone_precompose (X:=X) (diagram_idmap D) == idmap.
  Proof.
    intro C; srapply path_cocone; simpl.
    1: reflexivity.
    intros; simpl.
    refine (concat_p1 _).
  Defined.

  Definition cocone_precompose_comp {D1 D2 D3 : Diagram G}
    (m2 : DiagramMap D2 D3) (m1 : DiagramMap D1 D2) (X : Type)
    : (cocone_precompose (X:=X) m1) o (cocone_precompose m2)
      == cocone_precompose (diagram_comp m2 m1).
  Proof.
    intro C; simpl.
    srapply path_cocone.
    1: reflexivity.
    intros i j g x; simpl.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    unfold CommutativeSquares.comm_square_comp.
    refine (concat_p_pp _ _ _ @ _).
    apply ap10, ap.
    rewrite 3 ap_V.
    refine ((inv_pp _ _)^ @ _).
    apply inverse2.
    rewrite ap_pp.
    apply ap.
    by rewrite ap_compose.
  Defined.

  (** Associativity of a precomposition and a postcomposition. *)

  Definition cocone_precompose_postcompose {D1 D2 : Diagram G}
             (m : DiagramMap D1 D2) `(f : X -> Y) (C : Cocone D2 X)
    : cocone_postcompose (cocone_precompose m C) f
      = cocone_precompose m (cocone_postcompose C f).
  Proof.
    srapply path_cocone; intro i.
    1: reflexivity.
    intros j g x; simpl.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    etransitivity.
    + apply ap_pp.
    + apply ap10, ap.
      symmetry.
      apply ap_compose.
  Defined.

  (** The precomposition with a diagram equivalence is an equivalence. *)

  Global Instance cocone_precompose_equiv {D1 D2 : Diagram G}
    (m : D1 ~d~ D2) (X : Type) : IsEquiv (cocone_precompose (X:=X) m).
  Proof.
    srapply isequiv_adjointify.
    1: apply (cocone_precompose (diagram_equiv_inv m)).
    + intros C.
      etransitivity.
      - apply cocone_precompose_comp.
      - rewrite diagram_inv_is_retraction.
        apply cocone_precompose_identity.
    + intros C.
      etransitivity.
      - apply cocone_precompose_comp.
      - rewrite diagram_inv_is_section.
        apply cocone_precompose_identity.
  Defined.

  (** The postcomposition with an equivalence is an equivalence. *)

  Global Instance cocone_postcompose_equiv {D : Diagram G} `(f : X <~> Y)
    : IsEquiv (fun C : Cocone D X => cocone_postcompose C f).
  Proof.
    srapply isequiv_adjointify.
    1: exact (fun C => cocone_postcompose C f^-1).
    + intros C.
      etransitivity.
      - symmetry.
        apply cocone_postcompose_comp.
      - etransitivity.
        2: apply cocone_postcompose_identity.
        apply ap.
        funext x; apply eisretr.
    + intros C.
      etransitivity.
      - symmetry.
        apply cocone_postcompose_comp.
      - etransitivity.
        2: apply cocone_postcompose_identity.
        apply ap.
        funext x; apply eissect.
  Defined.

  (** ** Universality preservation *)

  (** Universality of a cocone is preserved by composition with a (diagram) equivalence. *)

  Global Instance cocone_precompose_equiv_universality {D1 D2 : Diagram G}
    (m: D1 ~d~ D2) {X} (C : Cocone D2 X) (_ : UniversalCocone C)
    : UniversalCocone (cocone_precompose (X:=X) m C).
  Proof.
    srapply Build_UniversalCocone; intro.
    rewrite (path_forall _ _ (fun f => cocone_precompose_postcompose m f C)).
    srapply isequiv_compose.
  Defined.

  Global Instance cocone_postcompose_equiv_universality {D: Diagram G} `(f: X <~> Y)
    (C : Cocone D X) (_ : UniversalCocone C)
    : UniversalCocone (cocone_postcompose C f).
  Proof.
    srapply Build_UniversalCocone; intro.
    rewrite <- (path_forall _ _ (fun g => cocone_postcompose_comp f g C)).
    srapply isequiv_compose.
  Defined.

End FunctorialityCocone.

