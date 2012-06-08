(** We formalize a special kind of higher-inductive types in which
   we glue some extra cells to an existing type. This is what seems
   to be needed for the first isomorphism theorem. *)

Add LoadPath "..".
Require Import Paths Fibrations Equivalences Funext.

(** Suppose [A] is a type to which we would like to glue some extra points, paths,
   2-cells, etc. We assume that the cells are always glued to ones that already
   existed in [A], i.e., if we wanted to add paths [p] and [q] as well as a 2-cell
   between them, we would have to do this in two steps. *)

(** We need iterated path spaces so that we can glue stuff in higher dimensions. *)
Fixpoint globule (n : nat) (A : Type) : Type :=
  match n with
    | 0 => (A * A)%type
    | S m => { x : A & { y : A & globule m (x ~~> y) } }
  end.

Definition globule_map {n : nat} : forall {A B : Type} (f : A -> B), globule n A -> globule n B.
Proof.
  induction n; intros A B f b.
  now exact (f (fst b), f (snd b)).
  destruct b as [x [y c]].
  fold globule in c.
  exists (f x); exists (f y).
  apply IHn with (A := x ~~> y).
  apply map.
  exact c.
Defined.

Fixpoint brane (n : nat) (A : Type) : Type :=
  match n with
    | 0 => {x : A & { y : A & x ~~> y } }
    | S m => { x : A & {y : A & brane m (x ~~> y) } }
end.

Definition edge {n : nat} : forall {A : Type}, brane n A -> globule n A.
Proof.
  induction n.
  intros A r.
  destruct r as [x [y _]].
  now exact (x,y).
  intros A r.
  destruct r as [x [y p]].
  exists x; exists y.
  apply IHn.
  exact p.
Defined.
  
Structure GlueData := {
  glue_ty : Type ;
  glue_brane : nat -> Type ;
  glue_attach : forall (n : nat), glue_brane n -> globule n glue_ty
}.

Structure HIT (G : GlueData) := {
  hit_ty :> Type ;
  hit_incl : glue_ty G -> hit_ty ;
  hit_brane : forall (n : nat), glue_brane G n -> brane n hit_ty ;
  hit_edge : forall (n : nat) (b : glue_brane G n), edge (hit_brane n b) ~~> globule_map hit_incl (glue_attach G n b) ;
  hit_rect :
    forall
      (P : fibration hit_ty)
      (i : forall x : glue_ty G, P (hit_incl x))
      (j : forall (n : nat), glue_brane G n -> brane n Type)
      (e : forall (n : nat) (b : glue_brane G n), globule_map P (edge (hit_brane n b)) ~~> edge (j n b)),
        forall (x : hit_ty), P x
  (* missing computation rules *)
}.

Axiom make_hit : forall (G : GlueData), HIT G.

Section KernelQuotient.
  (** Egbert's kernel-quotient construction. *)

  Variable A B : Type.
  Variable f : A -> B.

  Lemma next_type_data (n : nat) (A' : Type) (f' : A' -> B) : GlueData.
  Proof.
    refine
      {|
        glue_ty := A' ;
        glue_brane := (fun (k : nat) =>
          ((k ~~> n) * { l : globule n A' & { b : brane n B & edge b ~~> globule_map f' l } })%type)
      |}.
    intro m.
    intros [E [l [b p]]].
    induction E.
    exact l.
  Defined.

  (** Successive approximations to [A / ker f]. *)
  Definition approx (n : nat) : { A' : Type & A' -> B }.
  Proof.
    induction n.
    exists A; exact f.
    destruct IHn as [A' f'].
    exists (make_hit (next_type_data n A' f')).
    eapply hit_rect with (P := fun _ => B).
    intro x.
    now exact (f' x).
    intros m [p [l [b q]]].
    
    
    
  



End KernelQuotient.
