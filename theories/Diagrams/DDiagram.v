Require Import Basics.
Require Import Types.
Require Import Diagrams.Graph.
Require Import Diagrams.Diagram.

(** We define here the Graph ∫D, also denoted G·D *)

Definition integral {G : Graph} (D : Diagram G) : Graph.
Proof.
  serapply Build_Graph.
  + exact {i : G & D i}.
  + intros i j.
    exact {g : G i.1 j.1 & D _f g i.2 = j.2}.
Defined.

(** Then, a dependent diagram E over D is just a diagram over ∫D. *)

Definition DDiagram {G : Graph} (D : Diagram G)
  := Diagram (integral D).

(** Given a dependent diagram, we c.an recover a diagram over G by considering the Σ types. *)

  Definition diagram_sigma {G : Graph} {D : Diagram G} (E : DDiagram D)
    : Diagram G.
  Proof.
    serapply Build_Diagram.
    - intro i.
      exact {x : D i & E (i; x)}.
    - intros i j g x. simpl in *.
      exists (D _f g x.1).
      exact (@arr _ E (i; x.1) (j; D _f g x.1) (g; idpath) x.2).
  Defined.

  (** A dependent diagram is said equifibered if all its fibers are equivalences. *)

  Class Equifibered {G : Graph} {D : Diagram G} (E : DDiagram D) := {
    isequifibered i j (g : G i j) (x : D i)
      :> IsEquiv (@arr _ E (i; x) (j; D _f g x) (g; idpath));
  }.
