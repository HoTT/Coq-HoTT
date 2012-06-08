(**** WORK IN PROGRESS WITH Egbert Rijke ***)

Add LoadPath "..".

Require Import Paths Fibrations Contractible Funext HLevel
  Equivalences FiberEquivalences FunextEquivalences Univalence.
Require Import ExtensionalityAxiom.

Parameter X Y A : Type.
Parameter f : X -> A.
Parameter g : Y -> A.

Structure Cone (C : Type) := {
  p1 : C -> X ;
  p2 : C -> Y ;
  gamma : forall (c : C), f (p1 c) == g (p2 c)
}.

Implicit Arguments p1 [C].
Implicit Arguments p2 [C].
Implicit Arguments gamma [C].

Definition equal_cone {C : Type} (P Q : Cone C) :=
  forall (alpha : forall (c : C), p1 P c == p1 Q c)
         (beta :  forall (c : C), p2 P c == p2 Q c),
           forall (c : C), gamma P c @ map g (beta c) == map f (alpha c) @ gamma Q c.

Definition r {C : Type} (P : Cone C) {B : Type} (h : B -> C) : Cone B.
Proof.
  refine
    {| 
       p1 := fun (b : B) => p1 P (h b) ;
       p2 := fun (b : B) => p2 P (h b)
    |}.
  intro u.
  apply gamma.
Defined.

Definition is_pullback {C : Type} (P : Cone C) :=
  forall B, is_equiv (@r C P B).

(* We now try to define the pullback. *)

Definition C := { xy : X * Y & f (fst xy) == g (snd xy) }. (* This won't work. *)

Definition P : Cone C.
Proof.
  refine
    {|
      p1 := fun (u : C) => fst (pr1 u) ;
      p2 := fun (u : C) => snd (pr1 u)
    |}.
  intros [[x y] p].
  exact p.
Defined.

(* We define the inverse of r P. *)
Definition rPinv {B : Type} (Q : Cone B) : B -> C.
Proof.
  intro b.
  destruct Q as [h k alpha].
  exists (h b, k b).
  apply alpha.
Defined.

(* Is rinv really the inverse? *)
Lemma r_rPinv {B : Type} (Q : Cone B) : equal_cone (r P (rPinv Q)) Q.
Proof.
Admitted.

Lemma rPinv_r {B : Type} (h : B -> C): forall b : B, rPinv (r P h) b == h b.
Proof.
  intro b.
  destruct (r P h) as [q1 q2 delta].
  unfold rPinv; simpl.
  destruct (h b) as [[x y] p]; simpl in * |- *.
Admitted.
