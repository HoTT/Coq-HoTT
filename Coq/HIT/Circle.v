Add LoadPath "..".
Require Import Homotopy.

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

(** The circle type S^1, as a higher inductive type. *)

Axiom circle : Type.

Axiom base : circle.
Axiom loop : base ~~> base.
 
Axiom circle_rect :
  forall (P : circle -> Type) (pt : P base) (lp : transport loop pt ~~> pt), 
    forall x : circle, P x.

Axiom compute_base :
  forall (P : circle -> Type) (pt : P base) (lp : transport loop pt ~~> pt), 
    circle_rect P pt lp base ~~> pt.

Axiom compute_loop :
  forall (P : circle -> Type) (pt : P base) (lp : transport loop pt ~~> pt), 
    (! map (transport loop) (compute_base P pt lp)
      @ (map_dep (circle_rect P pt lp) loop)
      @ (compute_base P pt lp))
    ~~> lp.

(** From this we can derive the non-dependent version of the
   eliminator, with its propositional computation rules. *)

Definition circle_rect' :
  forall (B : Type) (pt : B) (lp : pt ~~> pt), circle -> B.
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
  forall (B : Type) (pt : B) (lp : pt ~~> pt),
    circle_rect' B pt lp base ~~> pt.
Proof.
  intros B pt lp.
  unfold circle_rect'.
  apply compute_base with (P := fun x => B).
Defined.

Definition compute_loop' :
  forall (B : Type) (pt : B) (lp : pt ~~> pt),
    (! (compute_base' B pt lp)
      @ map (circle_rect' B pt lp) loop
      @ (compute_base' B pt lp))
    ~~> lp.
Proof.
  intros B pt lp.
  set (P := fun x : circle => B).
  set (lp' := trans_trivial loop pt @ lp).
  path_via (!compute_base P pt lp'
    @ !trans_trivial loop _
    @ map_dep (circle_rect P pt lp') loop
    @ compute_base P pt lp').
  unwhisker.
  moveleft_onleft.
  apply opposite, map_dep_trivial.
  path_via (!trans_trivial loop _
    @ (!map (transport loop) (compute_base P pt lp'))
    @ map_dep (circle_rect P pt lp') loop
    @ compute_base P pt lp').
  do_opposite_concat.
  associate_right.
  moveright_onleft.
  associate_left.
  apply compute_loop with (P := P) (pt := pt) (lp := lp').
Defined.

(** If the circle is contractible, then UIP holds. *)

Theorem circle_contr_implies_UIP : is_contr (circle) ->
  forall (A : Type) (x y : A) (p q : x ~~> y), p ~~> q.
Proof.
  intros H A x y p q.
  induction p.
  set (cq := circle_rect' A x q).
  set (cqb := cq base).
  set (cqcb := compute_base' A x q : cqb ~~> x).
  set (cql := map cq loop : cqb ~~> cqb).
  set (cqcl := compute_loop' A x q : (!cqcb @ cql @ cqcb ~~> q)).
  path_via (!cqcb @ cql @ cqcb).
  moveleft_onright.
  moveleft_onleft.
  cancel_units.
  cancel_opposites.
  path_via (map cq (idpath base)).
  apply contr_path2.
  assumption.
Defined.
