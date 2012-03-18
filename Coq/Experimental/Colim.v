(* Colimits as phrased by Egbert Rijke. *)

Add LoadPath "..".
Require Import Paths Fibrations Equivalences Funext.


(* Here is the non-dependent version, there is also a dependent version. *)


Record diagram := {
  obj_index : Type ;
  obj : obj_index -> Type ;
  mor_index : obj_index -> obj_index -> Type;
  mor : forall x y, mor_index x y -> (obj x -> obj y)
}.

Axiom colim : diagram -> Type.

Section ColimitConstruction.
    Variable D : diagram.

    (* The cocone maps. *)
    Axiom colim_elem: sigT (obj D) -> colim D.

    (* The cocone maps commute with the morphisms in the diagram. *)
    Axiom colim_path: forall i j (e : mor_index D i j) (u : obj D i), colim_elem (i;u) ~~> colim_elem (j ; mor D i j e u).

    (* The universal property of the cocone. *)
    Axiom colim_rect : forall (Lambda : colim D -> Type)
      (Kappa : forall (xu : sigT (obj D)), Lambda (colim_elem xu))
      (Gamma : forall i j (e : mor_index D i j) (u : obj D i), 
        transport (colim_path i j e u) (Kappa (i;u)) ~~> Kappa (j; mor D i j e u)),
      forall z : colim D, Lambda z.

  (* To be continued. *)
End ColimitConstruction.




