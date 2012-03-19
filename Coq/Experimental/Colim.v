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

Record Cocone {D : Diagram} := {
  vertex :> Type;
  arrow : forall (i : @obj_index D), obj i -> vertex;
  triangle : forall (i j : @obj_index D) (e : mor_index i j) (u : obj i), arrow i u ~~> arrow j (mor e u)
}.

Implicit Arguments arrow [D i].
Implicit Arguments triangle [D i j].

Section ColimitDefinition.
  (* We next define what a colimit of a diagram is in terms of equivalences. *)

  (* Cocones may be post-composed with morphisms. *)
  Definition cocone_compose {D : Diagram} (K : @Cocone D) (Y : Type) (f : K -> Y) : @Cocone D.
  Proof.
    refine
      {| vertex := Y ; 
        arrow := (fun i (u : obj i) => f (arrow K u))
        |}.
    intros i j e u.
    apply map.
    apply triangle.
  Defined.

  Record Colimit (D : Diagram) := {
    colim : @Cocone D;
    colim_equiv :  forall (Y : Type), is_equiv (cocone_compose colim Y)
  }.
End ColimitDefinition.

Section HITDefinition.
  (* Definition of a HIT for a given diagram. *)

  Record HIT (D : Diagram) := {
    carrier :> @Cocone D;
    hit_rect : forall K : @Cocone D, carrier -> K;
    hit_factor : forall K : @Cocone D, forall (i : @obj_index D) (u : obj i), hit_rect K (arrow carrier u) ~~> arrow K u;
    hit_compute : forall K : @Cocone D, 
      forall (i j : @obj_index D) (e : mor_index i j) (u : obj i),
        hit_factor K i u @ triangle K e u ~~> map (hit_rect K) (triangle carrier e u) @ hit_factor K j (mor e u)
  }.
End HITDefinition.

Theorem HIT_to_Colim (D : Diagram) : HIT D -> Colimit D.
Proof.
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
