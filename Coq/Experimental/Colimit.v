(* Colimits as phrased by Egbert Rijke and Andrej Bauer.
   THIS IS UNFINISHED WORK IN PROGRESS!  *)

Add LoadPath "..".
Require Import Paths Fibrations Equivalences Funext.

(* Because we want to avoid phrasing what a category is, we take "free" diagrams in the
   sense that a diagram is just an indexing of objects and morphisms betewen them. 
   (Question: do we lose any generality this way? Presumably not.) *)

Record Diagram := {
  obj_index : Type ;
  obj : obj_index -> Type ;
  mor_index : obj_index -> obj_index -> Type;
  mor : forall x y, mor_index x y -> (obj x -> obj y)
}.

Implicit Arguments obj [d].
Implicit Arguments mor_index [d].
Implicit Arguments mor [d x y].

(* A cocone over a given diagram with a given vertex consists of arrows into the vertex
   such that the relevant triangles commute. *)

Record Cocone (D : Diagram) (V : Type) := {
  arrow : forall (i : obj_index D), obj i -> V;
  triangle : forall (i j : obj_index D) (e : mor_index i j) (u : obj i), arrow i u ~~> arrow j (mor e u)
}.

Implicit Arguments arrow [D V i].
Implicit Arguments triangle [D i j].

(* If we have a cocone to [X] and [f : X -> Y] then we can compose arrows in the cocone
   to get a cocone to [Y]. *)

Definition cocone_compose {D X Y} : Cocone D X -> (X -> Y) -> Cocone D Y.
  Proof.
    intros K f.
    refine {| arrow := (fun i (u : obj i) => f (arrow K u)) |}.
    intros i j e u.
    apply map.
    apply triangle.
  Defined.

(* The fact that a cocone is colimiting can be expressed in terms of equivalences: a
   cocone K whose vertex is X is colimiting when the map [cocone K] which composes
   [f : X -> Y] with [K] is an equivalence. *)

Definition isColimiting {D X} (K : Cocone D X) :=
  forall Y, is_equiv (cocone_compose K (Y:=Y)).

(* If [K] is a colimiting cocone and [L] is any cocone, then there is a map
   from the vertex of [K] to the vertex of [L] which is a cocone morphism. *)
Lemma fromColimit {D X Y} (K : Cocone D X) (H : isColimiting K) (L : Cocone D Y) :
 { f : X -> Y & forall (i : obj_index D) (x : obj i), f (arrow K x) ~~> arrow L x }.
Proof.
  pose (f := ((cocone_compose K; H Y) ^-1) L).
  exists f.
  intros i x.
  destruct (H Y).
  (* STOPPED WORKING HERE. *)
Admitted.

(* We now proceed to define "rank 1 higher-inductive types without recursion", i.e.,
   higher-inductive types which are not recursive and only refer to points and paths,
   but not for example to paths between paths. For simplicity we call such a type HIT. *)

Section HITDefinition.
  (* The data for a HIT consists of types of points and paths which generate the HIT. *)

  Variable point : Type. 
  Variable path : point -> point -> Type.

  (* The HIT itself is a record consisting of: a carrier type, constructors which
     embed points and paths into the carrier, satisfies an induction principle and
     conversion rules. *)

  Record HIT := {
    (* the carrier type of HIT *)
    hit_carrier :> Type ;
    (* constructors for the carrier *)
    hit_point : point -> hit_carrier ;
    (* constructors for paths *)
    hit_path : forall {x y}, path x y -> hit_point x ~~> hit_point y ;
    (* the induction principle construst a map from the HIT, given information
       [b] on where to map points and information [i] on where to map paths. *)
    hit_rect :
      (forall (P : hit_carrier -> Type) (b : forall x, P (hit_point x))
              (i : forall {x y} (p : path x y), transport (hit_path p) (b x) ~~> b y),
        forall x, P x) ;
    (* The first conversion states that [hit_rect] maps points to as prescribed by the data [b]. *)
    hit_convert_point :
      (forall (P : hit_carrier -> Type) (b : forall x, P (hit_point x))
              (i : forall {x y} (p : path x y), transport (hit_path p) (b x) ~~> b y),
        forall x, hit_rect P b i (hit_point x) ~~> b x) ;
    (* The second conversion states that [hit_rect] acts on points as prescribed by the data [i]. *)
    hit_convert_path :
      (forall (P : hit_carrier -> Type) (b : forall x, P (hit_point x))
              (i : forall {x y} (p : path x y), transport (hit_path p) (b x) ~~> b y),
        forall {x y} (p : path x y),
          map_dep (hit_rect P b i) (hit_path p) ~~>
          map (transport (hit_path p)) (hit_convert_point P b i x) @ i _ _ p @ ! (hit_convert_point P b i y))
  }.
End HITDefinition.

Section HITNonDependent.

  (* As a first exercise we derive the non-dependent version of the induction principle. *)
  
  Variable point : Type.
  Variable path : point -> point -> Type.


  Lemma transport_nondep (X Y : Type) (u v : X) (p : u ~~> v) (y : Y) : transport (P := fun _ => Y) p y ~~> y.
  Proof.
    path_induction.
  Defined.

  Theorem hit_rect' (H : HIT point path) (X : Type) (b : point -> X)
                    (i : forall {x y}, (path x y) -> b x ~~> b y) :  H -> X.
  Proof.
    intro t.
    apply hit_rect with
      (h := H)
      (P := fun _ => X)
      (b := b)
      (x := t).
    intros x y p.
    apply @concat with (y := b x); auto.
    apply transport_nondep; apply i; auto.
  Defined.

End HITNonDependent.

(* If we have colimits then we have HITs. *)
Section HIT_from_colimit.

  Variable colimit : forall (D : Diagram), { V : Type & { C : Cocone D V & isColimiting C } }.

  Definition hit (point : Type) (path : point -> point -> Type) : HIT point path.
  Proof.
    (* We shall construct the hit for the given data as the colimit of the following diagram [D]. *)
    pose (D :=
      {| obj_index := point ;
        obj := (fun _ => unit) ;
        mor_index := path ;
        mor := (fun x y (p : path x y) tt => tt)
        |}).
    (* We take the colimit of [D]. We get a cocone [C] whose vertex is [V]. *)
    destruct (colimit D) as [V [C H]].
    (* Now we start creating the data for the HIT. The carrier is just [V],
       and the inclusion of generators is obtained from the colimiting cocone [C]. *)
    pose (h_carrier := V).
    pose (h_point := (fun x => @arrow D V C x tt)).
    pose (h_path := (fun x y (p : path x y) => @triangle D V C x y p tt)).
    (* It is a bit harder to construct the induction principle. This one we shall get
       from the universal property of [C], but we need some preparation. *)
    assert (h_rect :
      (forall (P : h_carrier -> Type) (b : forall x, P (h_point x))
              (i : forall {x y} (p : path x y), transport (h_path x y p) (b x) ~~> b y),
        forall x, P x)).
    intros P b i x.
    (* We construct a cocone on [K] with vertex [sigT P]. *)
    assert (K : Cocone D (sigT P)).
      refine {| arrow := fun v _ => existT P (h_point v) (b v) |}.
      intros u v p _.
      apply total_path with (p := h_path u v p).
      simpl.
      unfold h_carrier, h_point, h_path.
      unfold h_path, mor in i; simpl in i; apply (i u v).
    (* Because [C] is colimiting there is a map [f] from its vertex [V] to the vertex of [K],
       i.e., a map from [V] to [sigT P]. *)
    destruct (fromColimit C H K) as [f G].
    (* If we apply [f] to [x] we get an element [y] in [P x']. *)
    destruct (f x) as [x' y].
    (* To get an element in [P x], we transport [y] along a path [x' ~~> x]. But which path? *)
    (* UNFINISHED FROM HERE. *)
    
    (* However [y] is not immediately seen to be in [P x]. For that we need to use further
       properties of the colimit. *)
    unfold fromColimit, inverse in y; simpl.
    unfold cocone_compose in y; simpl.
    (* STUFF MISSING HERE *)
    
    (* Finally, we provide the HIT data. *)
    refine {| hit_carrier := h_carrier ;
              hit_point := h_point ;
              hit_path := h_path ;
              hit_rect := h_rect
      |}.
    (* WORK STILL TO BE DONE. *)
  Admitted.
End HIT_from_colimit.

(* If we have HITs then we have colimits. *)

Lemma make_total_path {A : Type} {P : A -> Type} {x y : A} (p : x ~~> y) (u : P x) (v : P y) : (transport p u ~~> v) -> ((x ; u) ~~> (y ; v)).
Proof.
  intro q.
  induction p.
  simpl in q.
  induction q.
  apply idpath.
Qed.

Axiom extensionality : funext_dep_statement.

Lemma transport_pointwise {D E : Diagram}

Theorem HIT_is_Colimiting (D : Diagram) : isColimiting D HIT (arrows D) (triangles D).
Proof.
  intros X taupsi.
  pose (tau := projT1 taupsi).
  pose (psi := projT2 taupsi).
  assert (F : hfiber (cocone_compose D HIT (arrows D) (triangles D) X) taupsi).
    pose (f := hit_rect' D X tau psi).
    exists f.
    pose (foarrows := projT1 (cocone_compose D HIT (arrows D) (triangles D) X f)).
    pose (fotriangles := projT2 (cocone_compose D HIT (arrows D) (triangles D) X f)).
    assert (zeta0 : foarrows ~~> tau).
      apply extensionality; intro i.
      apply extensionality; intro u.
      exact (hit_factor' D X tau psi i u).
    assert (zeta1 : transport zeta0 fotriangles ~~> psi).
      apply extensionality; intro i.
      apply extensionality; intro j.
      apply extensionality; intro e.
      apply extensionality; intro u.
      assert (transport zeta0 fotriangles i j e u ~~> !(hit_factor' D X tau psi i u) @
        (fotriangles i j e u) @ (hit_factor' D X tau psi j (mor e u))).
        induction zeta0. 
  intro H.
  refine {| colim := carrier D H |}.
  intro Y.
Admitted.

(* Now we prove theorems saying that Colimit and HIT "agree". *)
Theorem Colim_HIT_equiv (D : Diagram) : Colimit D <~> HIT D.
Admitted.

(* Actual existence of HIT/Colimit has to be assumed as an axiom. *)
Axiom HIT_exists : forall (D : Diagram), HIT D.

(* But once we know they exist, we can show that HITs are uniquely determined. *)
Theorem HIT_exists_and_unique (D : Diagram) : is_contr (HIT D).
