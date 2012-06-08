Add LoadPath "..".
Require Import Homotopy.

(** The circle type S^1, as a higher inductive type. We define it as a Coq
   structure so that we can have several circles at the same time. Also, it's a
   bit cleaner because it avoids postulating axioms.

   Note that we have changed the original [compute_loop]. This is a good idea,
   as was explained on the HoTT list by Guillaume Brunerie, see
   http://groups.google.com/group/HomotopyTypeTheory/browse_thread/thread/c8f9eb7c678dd6f5
*)

Structure Circle := {
  circle :> Type;
  base : circle;
  loop : base == base;
  circle_rect :
    (forall (P : circle -> Type) (pt : P base) (lp : transport loop pt == pt), 
      forall x : circle, P x);
  compute_base :
    (forall (P : circle -> Type) (pt : P base) (lp : transport loop pt == pt), 
      circle_rect P pt lp base == pt);
  compute_loop :
    (forall P pt lp,
      map_dep (circle_rect P pt lp) loop
      == map (transport loop) (compute_base P pt lp) @ lp @ !compute_base P pt lp)
}.

(* Old compute_loop:

    (forall (P : circle -> Type) (pt : P base) (lp : transport loop pt == pt), 
      (! map (transport loop) (compute_base P pt lp)
        @ (map_dep (circle_rect P pt lp) loop)
        @ (compute_base P pt lp))
      == lp)
*)

Implicit Arguments base [c].
Implicit Arguments loop [c].

Section Non_dependent.

  (** From this we can derive the non-dependent version of the
     eliminator, with its propositional computation rules. *)

  Variable circle : Circle.

  Definition circle_rect' :
    forall (B : Type) (pt : B) (lp : pt == pt), circle -> B.
  Proof.
    intros B pt lp.
    apply circle_rect with (P := fun x => B) (pt := pt).
    (* Since [pt] doesn't depend on [loop], the source [transport loop
       pt] is equivalent to [pt].  The lemma which says this is
       [trans_trivial], so it is tempting to write [apply
       trans_trivial].  However, that would use it to solve the whole
       goal, rather than allowing us to incorporate [lp] as well.  We
       also need to be careful with our path-constructing tactics, lest
       they overzealously use an identity path where we want to use a
       nontrivial self-path. *)
    apply @concat with (y := pt).
    apply trans_trivial.
    exact lp.
  Defined.

  Definition compute_base' :
    forall (B : Type) (pt : B) (lp : pt == pt),
      circle_rect' B pt lp base == pt.
  Proof.
    intros B pt lp.
    unfold circle_rect'.
    apply compute_base with (P := fun x => B).
  Defined.

  Lemma map_dep_trivial2 {A B} {x y : A} (f : A -> B) (p: x == y):
    map f p == !trans_trivial p (f x) @ map_dep f p.
  Proof.
    path_induction.
  Defined.

  Definition compute_loop' : forall B pt lp,
    map (circle_rect' B pt lp) loop
    == compute_base' B pt lp @ lp @ !compute_base' B pt lp.
  Proof.
    intros B pt lp.
    eapply concat.
    apply map_dep_trivial2.
    moveright_onleft.
    eapply concat.
    apply compute_loop with (P := fun _ => B).
    unwhisker.
  Defined.
End Non_dependent.

(* The definition of circle gives "the best possible circle" in a given
   model. If the circle is trivial, then the model satisfies UIP. *)
Theorem circle_contr_implies_UIP  (C : Circle) :
  is_contr C -> forall (A : Type) (x y : A) (p q : x == y), p == q.
Proof.
  intros H A x y p q.
  induction p.
  pose (cq := circle_rect' C A x q).
  pose (cqb := cq base).
  pose (cqcb := compute_base' C A x q : cqb == x).
  pose (cql := map cq loop : cqb == cqb).
  pose (cqcl := compute_loop' C A x q).
  path_via (!cqcb @ cql @ cqcb).
  moveleft_onright.
  moveleft_onleft.
  cancel_units.
  cancel_opposites.
  path_via (map cq (idpath base)).
  apply contr_path2.
  assumption.
  moveright_onright.
  moveright_onleft.
  unfold cqcb, cql, cq.
  associate_left.
Defined.

(* Here is a curious fact: Streicher K implies that the circle is contractible.
   So we have K + Cirle = UIP. *)
Section Streicher_and_Circle.
  Parameter C : Circle.

  Definition Streicher_K_statement :=  forall (U : Type) (x : U) (P: x == x -> Type), P (idpath x) -> forall p, P p.

  Lemma little_lemma (A : Type) (x y : A) (p : x == y) : transport (P := fun z => z == y) p p == idpath y.
  Proof.
    path_induction.
  Defined.
  
  Lemma Circle_contractible : Streicher_K_statement -> is_contr C.
  Proof.
    intro K.
    exists base.
    intro x.
    apply circle_rect with (P := fun x => x == base) (pt := loop).
    apply K.
    apply little_lemma.
  Defined.
End Streicher_and_Circle.
