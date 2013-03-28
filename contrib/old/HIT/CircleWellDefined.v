Add LoadPath "..".
Require Import Homotopy Circle.

(**
   The original author of this file is Guillaume Brunerie, who proved that
   the circle is well defined. We adapt his proof to circle being a structure,
   so that we can actually have _two_ circles in the proof.

   We want to prove that two copies of the circle are equivalent (that is, that
   the higher inductive definition of circles gives indeed a unique space up to
   equivalence).

   Suppose we have two circles [C1] and [C2].

   We first define the maps [f : C1 -> C2] and [g : C2 -> C1] by induction, and
   we want to prove that they yield an equivalence. For that, we have to prove
   that for all [x : C1], there is a path from [g (f x)] to [x], and vice versa.

   Let us concentrate just on the property [P(x)] which states [g (f x) == x],
   the other one is symmetric. Then [P] is a fibration over the circle [C1],
   and we want to prove [forall x : C1, P x] by (dependent) induction on [x].

   We first need to find a term [cc_base] of type [P base]. This is easy, we
   just have to apply the computation rule for [base] twice.

   Then we have to find a term [cc_loop] of type [transport (P := P) loop
   cc_base == cc_base]. But given that we know nothing about [loop], we cannot
   prove something about it unless we prove something about all paths in the
   circle and then specialize it to [loop]. So we will find [cc_transp] which is
   of type [transport (P := P) p x == $$$] with [$$$] replaced by something
   complicated, where [p] is any path of the circle [C1], which explains how
   something like [cc_base] is transported by any loop in the circle (this is
   very easy by induction on [p] and with the [cancel_units] tactic).

   Now the difficult part begins. We have to prove that [cc_transp] specialized
   to [loop] gives indeed [transport (P := P) loop cc_base == cc_base]. We
   will here need to use the computation rule for [loop] twice and make sure
   that everything cancels (and this is ugly because each computation rule for
   loop adds two concatenations which have to pass through [map] and [!]).
*)

(* We import here the [rewr] tactic from another file used by Guillaume to
   make this file self-contained. *)

(* Very hacky rewrite tactic, this does not work very well but can be useful *)
Ltac rewr X :=
  lazymatch (type of X) with
     | @paths _ ?x ?y =>
         lazymatch goal with
           | |- @paths _ ?z _ =>
               lazymatch z with
                  | context ctx [x] =>
                      let new := context ctx [y] in
                        path_via new
               end
         end
  end.

(* We first construct a map [c2c : C1 -> C2] and its inverse for any two circles
   and prove their properties.. *)

Section CircleToCircle.

  Variable C1 C2 : Circle.

  Definition f : C1 -> C2 := circle_rect' C1 C2 base loop.
  Definition g : C2 -> C1 := circle_rect' C2 C1 base loop.

  Definition P := fun x : C1 => g (f x) == x.

  Lemma cc_base : P base.
  Proof.
    eapply concat.
    2:apply compute_base'.
    apply map.
    apply compute_base'.
  Defined.

  Lemma cc_transp {X Y : Type} (h k : X -> Y) (u v : X) (p : u == v) :
    forall q : h u == k u,
        transport (P := (fun x => h x == k x)) p q ==
        (!map h p) @ q @ (map k p).
  Proof.
    path_induction.
    cancel_units.
  Defined.

  Lemma cc_loop : transport (P := P) loop cc_base == cc_base.
  Proof.
    eapply concat.
    apply cc_transp with (h := compose g f) (k := idmap C1).
    do_compose_map.

    rewr (compute_loop' C1 _ _ _ : map f loop == _).
    apply compute_loop'.
    do_concat_map.
    apply concat_map with (f := g). (* Why do I need to make [f] explicit? *)
    undo_opposite_concat.
    rewr (compute_loop' _ _ _ _ : map g loop == _).
    apply compute_loop'.
    undo_opposite_concat.
    unfold cc_base.
    unfold g.
    do_opposite_map.
    moveright_onright.
    moveright_onright.
    undo_opposite_concat.
    associate_left.
    apply opposite.
    apply idmap_map.
  Defined.

  Lemma cc : forall x : C1, P x.
  Proof.
    apply circle_rect with cc_base, cc_loop.
  Defined.

End CircleToCircle.

Theorem circle_is_circle (C1 C2 : Circle) : C1 <~> C2.
Proof.
  exists (f C1 C2).
  apply hequiv_is_equiv with (g := g C1 C2); apply cc.
Defined.

