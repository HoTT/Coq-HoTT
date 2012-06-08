Add LoadPath "..".

Require Import Paths Fibrations Contractible Equivalences.

(** The colimit of a sequence [A 0 -> A 1 -> A 2 -> ...] *)
Section DirectLimit. (* Whoever called colimits limits? *)

  Variable A : nat -> Type.
  Variable alpha : forall n : nat, A n -> A (S n).

  Structure Cocone (T : Type) := {
    cocone_incl :> forall n : nat, A n -> T ;
    cocone_triangle : forall (n : nat) (x : A n), cocone_incl (S n) (alpha n x) ~~> cocone_incl n x
  }.

  Definition cocone_compose {X Y : Type} (C : Cocone X) (f : X -> Y) : Cocone Y.
  Proof.
    refine {| cocone_incl := fun n x => f (C n x) |}.
    intros n x.
    apply map.
    apply cocone_triangle.
  Defined.

  Definition is_colimit {X : Type} (C : Cocone X) :=
    forall (Y : Type), is_equiv (@cocone_compose X Y C).

  Lemma map_from_colimit {X : Type} (C : Cocone X) :
    is_colimit C -> forall Y (D : Cocone Y), X -> Y.
  Proof.
    intros H Y D.
    pose (e := {| equiv_map := @cocone_compose X Y C ; equiv_is_equiv := H Y |}).
    apply (e^-1 D).
  Defined.

  Axiom Colimit : { X : Type & { C : Cocone X & is_colimit C }}.
End DirectLimit.

Section ColimitOfIdentity.
  (* Sanity check. *)
  
  Variable X : Type.
  
  Let A (n : nat) := X.
  Let alpha (n : nat) := idmap X.
  
  Let colimit := Colimit A alpha.
  Let Y := pr1 colimit.
  Let C := pr1 (pr2 colimit).
  Let C_is_colimit := pr2 (pr2 colimit). 
  
  Definition Y_to_X : Y -> X.
  Proof.
    apply (map_from_colimit A alpha C C_is_colimit).
    refine {| cocone_incl := fun _ => idmap X |}.
    intros n x.
    apply idpath.
  Defined.

  Lemma Y_equiv_X : Y <~> X.
  Proof.
    apply (equiv_from_hequiv Y_to_X (C 0)).
    intro x.
    unfold Y_to_X, map_from_colimit; simpl.
    
  

