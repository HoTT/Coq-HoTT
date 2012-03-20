(* Colimits as phrased by Egbert Rijke. *)

Add LoadPath "..".
Require Import Paths Fibrations Equivalences Funext.

(* Here is the non-dependent version, there is also a dependent version. *)

Record Diagram := {
  obj_index : Type ;
  obj : obj_index -> Type ;
  mor_index : obj_index -> obj_index -> Type;
  mor : forall x y, mor_index x y -> (obj x -> obj y)
}.

Implicit Arguments obj_index [d].
Implicit Arguments obj [d].
Implicit Arguments mor_index [d].
Implicit Arguments mor [d x y].

Definition Arrow {D : Diagram} (X : Type) : Type := forall (i : @obj_index D), obj i -> X.

Definition isCocone {D : Diagram} {X : Type} (arrow : Arrow X) : Type := forall (i j : @obj_index D) (e : mor_index i j) (u : obj i), arrow i u ~~> arrow j (mor e u).

Record Cocone {D : Diagram} := {
  vertex :> Type;
  arrow : forall (i : @obj_index D), obj i -> vertex;
  triangle : forall (i j : @obj_index D) (e : mor_index i j) (u : obj i), arrow i u ~~> arrow j (mor e u)
}.

Implicit Arguments arrow [D i].
Implicit Arguments triangle [D i j].

Section ColimitDefinition.
  (* We next define what a colimit of a diagram is in terms of equivalences. *)
  
  Variables (D : Diagram) (X : Type).

  (* Cocones may be post-composed with morphisms. *)
  Definition cocone_compose (tau : @Arrow D X)(psi : isCocone(tau)) (Y : Type) (f : X -> Y) : sigT (@isCocone D Y).
  Proof.
    pose (arrow := (fun i (u : obj i) => f (tau i u))).
    exists arrow.
    intros i j e u.
    exact (map f (psi i j e u)).
  Defined.

  Definition isColimiting (arrow : @Arrow D X) (triangle : isCocone(arrow)) : Type :=
    forall (Y : Type), is_equiv (cocone_compose arrow triangle Y).
    
(*
  Record Colimit (D : Diagram) := {
    colim : @Cocone D;
    colim_equiv :  forall (Y : Type), is_equiv (cocone_compose colim Y)
  }.
*)
End ColimitDefinition.

Section HITDefinition.
  (* Definition of a HIT for a given diagram. *)
  
  Variable (D : Diagram).

  Record HIT {D : Diagram} : Type.

  Check @HIT D. (* [@HIT : Diagram -> Prop]. What has happened? *)
  
  Axiom arrows : @Arrow D (@HIT D).

  Axiom triangles : isCocone(arrows).

Section DependentHIT.
  Variables (Lambda : @HIT D -> Type) 
            (Kappa : forall (i : @obj_index D) (u : obj i), Lambda (arrows i u))
            (Gamma : forall (i j : @obj_index D) (e : mor_index i j) (u : obj i), transport (triangles i j e u) (Kappa i u) ~~> Kappa j (mor e u)).

  Record HIT_induction_principle := {
    hit_rect : forall (x : HIT), Lambda x ;
    hit_factor : forall (i : @obj_index D) (u : obj i), hit_rect (arrows i u) ~~> Kappa i u ;
    hit_compute : forall (i j : @obj_index D) (e : mor_index i j) (u : obj i),
                  (map (transport (triangles i j e u)) (hit_factor i u) @ (Gamma i j e u)) 
                  ~~> (map_dep (hit_rect) (triangles i j e u) @ (hit_factor j (mor e u)))
    }.
End DependentHIT.

Check hit_rect.

Section NonDependentHIT.

  Variables (X : Type) 
            (Kappa : forall (i : @obj_index D), obj i -> X)
            (Gamma : forall (i j : @obj_index D) (e : mor_index i j) (u : obj i), (Kappa i u) ~~> Kappa j (mor e u)).

  Record HIT_induction_principle_ND := {
    hit_rect' : HIT -> X;
    hit_factor' : forall (i : @obj_index D) (u : obj i), hit_rect' (arrows i u) ~~> Kappa i u;
    hit_compute' : forall (i j : @obj_index D) (e : mor_index i j) (u : obj i),
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
