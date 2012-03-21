(* Colimits as phrased by Egbert Rijke. 
   THIS IS UNFINISHED WORK IN PROGRESS!  *)

Add LoadPath "..".
Require Import Paths Fibrations Equivalences Funext.

(* Because we want to avoid phrasing what a category is, we take "free" diagrams in the
   sense that a diagram is just an indexing of objects and morphisms betewen them. *)

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

(* The fact that a cocone is colimiting can be expressed in terms of equivalences:
   a cocone K whose vertex is X is colimiting when the map which composes [f : X -> Y]
   with [K] is an equivalence.
*)

Definition isColimiting {D X} (K : Cocone D X) :=
  forall Y, is_equiv (cocone_compose K (Y:=Y)).

(* We now proceed to define "rank 1 higher-inductive types without recursion", i.e.,
   higher-inductive types which are not recursive and only refer to points and paths,
   but not for example to paths between paths. For simplicity we call such a type HIT. *)

Section HITDefinition.
  (* The data for a HIT consists of types of points and paths which generate the HIT. *)

  Variable point : Type. 
  Variable path : point -> point -> Type.

  (* The HIT itself is a record consisting of: a carrier type, constructors which
     embed points and paths into the carrier, and induction data. *)

  Record HIT := {
    hit_carrier :> Type ; (* the carrier type of HIT *)
    hit_point : point -> hit_carrier ;
    hit_path : forall {x y}, path x y -> hit_point x ~~> hit_point y ;
    hit_rect :
      (forall (P : hit_carrier -> Type) (b : forall x, P (hit_point x)),
        (forall x y (p : path x y), transport (hit_path p) (b x) ~~> b y) -> forall x, P x) ;
    hit_convert_point :
      (forall (P : hit_carrier -> Type) (b : forall x, P (hit_point x))
        (i : forall x y (p : path x y), transport (hit_path p) (b x) ~~> b y) x,
        hit_rect P b i (hit_point x) ~~> b x) ;
    hit_convert_path :
      (forall (P : hit_carrier -> Type) (b : forall x, P (hit_point x))
        (i : forall x y (p : path x y), transport (hit_path p) (b x) ~~> b y) x y (p : path x y),
        map_dep (hit_rect P b i) 
  }.


  Record HIT (D : Diagram) := {
    hit_carrier :> Type ;
    hit_cocone : Cocone D hit_carrier
  }.

  Section HITInduction.
    Variables
      (carrier : Type)
      (Lambda : carrier -> Type) 
      (Kappa : forall (i : obj_index D) (u : obj i), Lambda (arrows i u))
      (Gamma : forall (i j : obj_index D) (e : mor_index i j) (u : obj i),
        transport (triangles i j e u) (Kappa i u) ~~> Kappa j (mor e u)).
    
    Record HIT_induction_principle := {
      hit_rect : forall (x : HIT), Lambda x ;
      hit_factor : forall (i : obj_index D) (u : obj i), hit_rect (arrows i u) ~~> Kappa i u ;
      hit_compute : forall (i j : obj_index D) (e : mor_index i j) (u : obj i),
        (map (transport (triangles i j e u)) (hit_factor i u) @ (Gamma i j e u)) 
        ~~> (map_dep (hit_rect) (triangles i j e u) @ (hit_factor j (mor e u)))
    }.
  End HITInduction.

  Record HIT

Check hit_rect.

Section NonDependentHIT.

  Variables (X : Type) 
            (Kappa : forall (i : obj_index D), obj i -> X)
            (Gamma : forall (i j : obj_index D) (e : mor_index i j) (u : obj i), (Kappa i u) ~~> Kappa j (mor e u)).

  Record HIT_induction_principle_ND := {
    hit_rect' : HIT -> X;
    hit_factor' : forall (i : obj_index D) (u : obj i), hit_rect' (arrows i u) ~~> Kappa i u;
    hit_compute' : forall (i j : obj_index D) (e : mor_index i j) (u : obj i),
         (hit_factor' i u @ Gamma i j e u) 
            ~~> map (hit_rect') (triangles i j e u) @ (hit_factor' j (mor e u))
  }.

End NonDependentHIT.

End HITDefinition.

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
