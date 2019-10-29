Require Import Basics.
Require Import Types.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.

Local Open Scope path_scope.
Generalizable All Variables.

(** * Cones *)

(** A Cone over a diagram [D] to a type [X] is a family of maps from [X] to the types of [D] making the triangles formed with the arrows of [D] commuting. *)

Class Cone (X : Type) {G : Graph} (D : Diagram G) := {
  legs   : forall i, X -> D i;
  legs_comm : forall i j (g : G i j), (D _f g) o legs i == legs j;
}.

Arguments Build_Cone {X G D} legs legs_comm.
Arguments legs {X G D} C i x : rename.
Arguments legs_comm {X G D} C i j g x : rename.

Coercion legs : Cone >-> Funclass.

Section Cone.
  Context `{Funext} {X : Type} {G : Graph} {D : Diagram G}.

  (** [path_cone] says when two cones are equals (up to funext). *)

  Definition path_cocone_naive {C1 C2 : Cone X D}
    (P := fun q' => forall {i j : G} (g : G i j) (x : X),
      D _f g (q' i x) = q' j x)
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

  Definition path_cone {C1 C2 : Cone X D}
    (path_legs : forall i,  C1 i == C2 i)
    (path_legs_comm : forall i j g x,
      legs_comm C1 i j g x @ path_legs j x
      = ap (D _f g) (path_legs i x) @ legs_comm C2 i j g x)
    : C1 = C2.
  Proof.
    destruct C1 as [legs pp_q], C2 as [r pp_r].
    refine (path_cocone_naive (path_forall _ _
      (fun i => path_forall _ _ (path_legs i))) _).
    cbn; funext i j f x.
    rewrite 4 transport_forall_constant, transport_paths_FlFr.
    rewrite concat_pp_p; apply moveR_Vp.
    rewrite ap_compose.
    rewrite 2 (ap_apply_lD2 (path_forall legs r
      (fun i => path_forall (legs i) (r i) (path_legs i)))).
    rewrite 3 eisretr.
    apply path_legs_comm.
  Defined.

  (** ** Precomposition for cones *)

  (** Given a cone [C] from [X] and a map from [Y] to [X], one can precompose each map of [C] to get a cone from [Y]. *)

  Definition cone_precompose (C : Cone X D) {Y : Type} (f : Y -> X) : Cone Y D.
  Proof.
    serapply Build_Cone; intro i.
    1: exact (C i o f).
    intros j g x.
    apply legs_comm.
  Defined.

  (** ** Universality of a cone. *)

  (** A limit will be the extremity of an universal cone. *)

  (** A cone [C] over [D] from [X] is said universal when for all [Y] the map [cone_precompose] is an equivalence. In particular, given another cone [C'] over [D] from [X'] the inverse of the map allows us to recover a map [h] : [X] -> [X'] such that [C'] is [C] precomposed with [h]. The fact that [cone_precompose] is an equivalence is an elegant way of stating the usual "unique existence" of category theory. *)

  Class UniversalCone (C : Cone X D) := {
    is_universal :> forall Y, IsEquiv (@cone_precompose C Y);
  }.

  Coercion is_universal : UniversalCone >-> Funclass.

End Cone.

(** We now prove several functoriality results, first on cone and then on limits. *)

Section FunctorialityCone.

  Context `{Funext} {G : Graph}.

  (** ** Precomposition for cones *)

  (** Identity and associativity for the precomposition of a cone with a map. *)

  Definition cone_precompose_identity {D : Diagram G} `(C : Cone X _ D)
    : cone_precompose C idmap = C.
  Proof.
    serapply path_cone; intro i.
    1: reflexivity.
    intros j g x; simpl.
    refine (concat_p1 _ @ (concat_1p _)^).
  Defined.

  Definition cone_precompose_comp {D : Diagram G}
    `(f : Z -> Y) `(g : Y -> X) (C : Cone X D)
    : cone_precompose C (g o f)
    = cone_precompose (cone_precompose C g) f.
  Proof.
    serapply path_cone; intro i.
    1: reflexivity.
    intros j h x; simpl.
    refine (concat_p1 _ @ (concat_1p _)^).
  Defined.

  (** ** Postcomposition for cones *)

  (** Given a cocone over [D2] and a Diagram map [m] : [D1] => [D2], one can postcompose each map of the cone by the corresponding one of [m] to get a cone over [D1]. *)

  Definition cone_postcompose {D1 D2 : Diagram G} (m : DiagramMap D1 D2) {X}
    : (Cone X D1) -> (Cone X D2).
  Proof.
    intro C.
    serapply Build_Cone; intro i.
    1: exact (m i o C i).
    intros j g x; simpl.
    etransitivity.
    1: apply DiagramMap_comm.
    apply ap, legs_comm.
  Defined.

  (** Identity and associativity for the postcomposition of a cone with a diagram map. *)

  Definition cone_postcompose_identity (D : Diagram G) (X : Type)
    : cone_postcompose (X:=X) (diagram_idmap D) == idmap.
  Proof.
    intro C; serapply path_cone; simpl.
    1: reflexivity.
    intros; simpl.
    refine (_ @ (concat_1p _)^).
    refine (concat_p1 _ @ concat_1p _ @ ap_idmap _).
  Defined.

  Definition cone_postcompose_comp {D1 D2 D3 : Diagram G}
    (m2 : DiagramMap D2 D3) (m1 : DiagramMap D1 D2) (X : Type)
    : (cone_postcompose (X:=X) m2) o (cone_postcompose m1)
      == cone_postcompose (diagram_comp m2 m1).
  Proof.
    intro C; simpl.
    serapply path_cone.
    1: reflexivity.
    intros i j g x; simpl.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    unfold CommutativeSquares.comm_square_comp.
    refine (_ @ concat_p_pp _ _ _).
    apply ap.
    rewrite ap_pp.
    apply ap.
    symmetry.
    by apply ap_compose.
  Defined.

  (** Associativity of a postcomposition and a precomposition. *)

  Definition cone_postcompose_precompose {D1 D2 : Diagram G}
             (m : DiagramMap D1 D2) `(f : Y -> X) (C : Cone X D1)
    : cone_precompose (cone_postcompose m C) f
      = cone_postcompose m (cone_precompose C f).
  Proof.
    serapply path_cone; intro i.
    1: reflexivity.
    intros j g x; simpl.
    refine (concat_p1 _ @ _ @ (concat_1p _)^).
    reflexivity.
  Defined.

  (** The postcomposition with a diagram equivalence is an equivalence. *)

  Global Instance cone_precompose_equiv {D1 D2 : Diagram G}
    (m : D1 ~d~ D2) (X : Type) : IsEquiv (cone_postcompose (X:=X) m).
  Proof.
    serapply isequiv_adjointify.
    1: apply (cone_postcompose (diagram_equiv_inv m)).
    + intros C.
      etransitivity.
      - apply cone_postcompose_comp.
      - rewrite diagram_inv_is_section.
        apply cone_postcompose_identity.
    + intros C.
      etransitivity.
      - apply cone_postcompose_comp.
      - rewrite diagram_inv_is_retraction.
        apply cone_postcompose_identity.
  Defined.

  (** The precomposition with an equivalence is an equivalence. *)

  Global Instance cone_postcompose_equiv {D : Diagram G} `(f : Y <~> X)
    : IsEquiv (fun C : Cone X D => cone_precompose C f).
  Proof.
    serapply isequiv_adjointify.
    1: exact (fun C => cone_precompose C f^-1).
    + intros C.
      etransitivity.
      - symmetry.
        apply cone_precompose_comp.
      - etransitivity.
        2: apply cone_precompose_identity.
        apply ap.
        funext x; apply eissect.
    + intros C.
      etransitivity.
      - symmetry.
        apply cone_precompose_comp.
      - etransitivity.
        2: apply cone_precompose_identity.
        apply ap.
        funext x; apply eisretr.
  Defined.

  (** ** Universality preservation *)

  (** Universality of a cone is preserved by composition with a (diagram) equivalence. *)

  Global Instance cone_postcompose_equiv_universality {D1 D2 : Diagram G}
    (m: D1 ~d~ D2) {X} (C : Cone X D1) (_ : UniversalCone C)
    : UniversalCone (cone_postcompose (X:=X) m C).
  Proof.
    serapply Build_UniversalCone; intro.
    rewrite (path_forall _ _ (fun f => cone_postcompose_precompose m f C)).
    serapply isequiv_compose.
  Defined.

  Global Instance cone_precompose_equiv_universality {D: Diagram G} `(f: Y <~> X)
    (C : Cone X D) (_ : UniversalCone C)
    : UniversalCone (cone_precompose C f).
  Proof.
    serapply Build_UniversalCone; intro.
    rewrite <- (path_forall _ _ (fun g => cone_precompose_comp g f C)).
    serapply isequiv_compose.
  Defined.

End FunctorialityCone.

