Require Export Equivalences UsefulEquivalences FiberEquivalences.

(** The unstable 3x3 lemma. *)

Section ThreeByThreeMaps.

  Hypotheses A B C D : Type.
  Hypotheses (f:A->B) (g:C->D) (h:A->C) (k:B->D).
  Hypothesis s:forall a, k (f a) == g (h a).

  Hypotheses (b:B).

  Definition square_fiber_map : {x:A & f x == b} -> {x:C & g x == k b}.
  Proof.
    intros [x p].
    exists (h x).
    path_via (k (f x)).
  Defined.

End ThreeByThreeMaps.

Implicit Arguments square_fiber_map [[A] [B] [C] [D]].

Section ThreeByThree.

  Hypotheses A B C D : Type.
  Hypotheses (f:A->B) (g:C->D) (h:A->C) (k:B->D).
  Hypothesis s:forall a, k (f a) == g (h a).

  Hypotheses (b:B) (c:C).
  Hypotheses (d:k b == g c).

  Let fibf := {x:A & f x == b}.
  Let fibg := {x:C & g x == k b}.

  Let fibf_to_fibg := square_fiber_map f g h k s b :
    fibf -> fibg.

  Let fibh := {x:A & h x == c}.
  Let fibk := {x:B & k x == g c}.

  Let fibh_to_fibk := square_fiber_map h k f g (fun a => !s a) c
    : fibh -> fibk.
  
  Let fibfg := {z:fibf & fibf_to_fibg z == (c ; !d)}.
  Let fibhk := {z:fibh & fibh_to_fibk z == (b ; d)}.

  Let fibfibmapf (x:A) (p:f x == b) :
    ((h x ; !s x @ map k p) == (existT (fun c' => g c' == k b) c (!d)))
    <~> {q : h x == c &
      transport (P := fun c' => g c' == k b) q (!s x @ map k p) == !d}
    := total_paths_equiv _ _ _ _.

  Let fibfibmaph (x:A) (q:h x == c) :
    ((f x ; !(!s x) @ map g q) == (existT (fun b' => k b' == g c) b d))
    <~> {p : f x == b &
      transport (P := fun b' => k b' == g c) p (!(!s x) @ map g q) == d}
    := total_paths_equiv _ _ _ _.
  
  Let fibfibfibmap (x:A) (p:f x == b) (q:h x == c) :
    (transport (P := fun c' => g c' == k b) q (!s x @ map k p) == !d)
    <~>
    (transport (P := fun b' => k b' == g c) p (!(!s x) @ map g q) == d).
  Proof.
    assert (H : transport (P := fun c' => g c' == k b) q (!s x @ map k p) ==
      !transport (P := fun b' => k b' == g c) p (!(!s x) @ map g q)).
    path_via (transport (P := fun d' => d' == k b) (map g q) (!s x @ map k p)).
    apply @map_trans with (P := fun d' => d' == k b).
    path_via (!map g q @ (!s x @ map k p)).
    apply trans_is_concat_opp.
    path_via (!transport (P := fun d' => d' == g c) (map k p) (!(!s x) @ map g q)).
    path_via (!(!map k p @ !(!s x) @ map g q)).
    undo_opposite_concat.
    associate_right.
    apply opposite, trans_is_concat_opp.
    apply opposite.
    apply @map_trans with (P := fun d' => d' == g c).
    apply equiv_inverse.
    apply @equiv_compose with
      (!transport (P := fun b' => k b' == g c) p (!(!s x) @ map g q) == !d).
    apply opposite2_equiv.
    exists (fun K:!transport p (!(!s x) @ map g q) == !d => H @ K).
    apply @concat_is_equiv_left with (p := H).
  Defined.

  Let fibfibmap (x:A) (p:f x == b) :
    {q : h x == c &
      (transport (P := fun c' => g c' == k b) q (!s x @ map k p) == !d)}
    <~>
    {q : h x == c &
      (transport (P := fun b' => k b' == g c) p (!(!s x) @ map g q) == d)}.
  Proof.
    apply total_equiv with (fibfibfibmap x p).
    intros q; exact (pr2 (fibfibfibmap x p q)).
  Defined.

  Let fibmap (x:A) :
    {p : f x == b & fibf_to_fibg (x ; p) == (c ; !d)} <~>
    {q : h x == c & fibh_to_fibk (x ; q) == (b ; d)}.
  Proof.
    apply @equiv_compose with
      ({p : f x == b & {q : h x == c &
        transport (P := fun c' => g c' == k b) q (!s x @ map k p) == !d}}).
    apply total_equiv with (g := fibfibmapf x).
    intros p. exact (pr2 (fibfibmapf x p)).
    apply @equiv_compose with
      ({q : h x == c & {p : f x == b &
        transport (P := fun b' => k b' == g c) p (!(!s x) @ map g q) == d}}).
    apply @equiv_compose with
      ({p : f x == b & {q : h x == c&
        transport (P := fun b' => k b' == g c) p (!(!s x) @ map g q) == d}}).
    apply total_equiv with (g := fibfibmap x).
    intros p; exact (pr2 (fibfibmap x p)).
    apply total_comm.
    apply equiv_inverse.
    apply total_equiv with (g := fibfibmaph x).
    intros q. exact (pr2 (fibfibmaph x q)).
  Defined.

  Definition three_by_three : fibfg <~> fibhk.
  Proof.
    apply @equiv_compose with
      ({x:A & {p:f x == b & fibf_to_fibg (x;p) == (c;!d)}}).
    apply equiv_inverse.
    apply total_assoc_sum with
      (A := A)
      (P := fun x => f x == b)
      (Q := fun xp => fibf_to_fibg xp == (c;!d)).
    apply @equiv_compose with
      ({x:A & {p:h x == c & fibh_to_fibk (x;p) == (b;d)}}).
    apply total_equiv with fibmap.
    intros x; exact (pr2 (fibmap x)).
    apply total_assoc_sum with
      (A := A)
      (P := fun x => h x == c)
      (Q := fun xp => fibh_to_fibk xp == (b;d)).
  Defined.

End ThreeByThree.

(** A version for maps that are given as fibrations. *)

Section ThreeByThreeFib.

  Hypothesis A B : Type.
  Hypothesis (P : A -> Type) (Q : B -> Type).
  Hypothesis f : A -> B.
  Hypothesis g : forall x, P x -> Q (f x).

  Hypothesis y : B.
  Hypothesis q : Q y.

  Let fibfibration (xs : {x:A & f x == y}) : Type :=
    let (x,s) := xs in { p:P x & transport s (g x p) == q }.

  Definition three_by_three_fib :
    sigT fibfibration <~> { xp : sigT P & total_map f g xp == (y;q) }.
  Proof.
    unfold fibfibration, total_map; simpl.
    apply @equiv_compose with
      (B := { x : A & { s : f x == y & {p : P x & transport s (g x p) == q}}}).
    apply equiv_inverse.
    apply total_assoc_sum with
      (P := fun x => f x == y)
      (Q := fun xs:{x : A & f x == y} =>
        let (x,s) := xs in {p : P x & transport s (g x p) == q}).
    apply @equiv_compose with
      (B := {x : A & { p : P x & (f x ; g x p) == (y ; q)}}).
    2:apply total_assoc_sum with
      (Q := fun xp:sigT P =>
        (let (x, y0) := xp in (f x ; g x y0)) == (y ; q)).
    apply @equiv_compose with
      (B := {x : A & {p : P x & {s : f x == y & transport s (g x p) == q}}}).
    set (tc := fun x => total_comm (f x == y) (P x) (fun s p => transport s (g x p) == q)).
    apply total_equiv with (g := tc).
    intros x; apply (pr2 (tc x)).
    set (tpe := fun x p => equiv_inverse
      (total_paths_equiv B Q (f x ; g x p) (y ; q))).
    set (tp := fun x => total_equiv
      (fun p => {s : f x == y & transport s (g x p) == q})
      (fun p => (f x ; g x p) == (y ; q))
      (fun p => tpe x p)
      (fun p => (pr2 (tpe x p)))).
    apply total_equiv with
      (P := fun x => {p : P x & {s : f x == y & transport s (g x p) == q}})
      (Q := fun x => {p : P x & (f x ; g x p) == (y ; q)})
      (g := tp).
    intro x; apply (pr2 (tp x)).
  Defined.

End ThreeByThreeFib.

(** The fiber of an identity map is contractible.
   This is pathspace_contr, pathspace_contr', pathspace_contr_opp
   from Contractible.v. *)
  
(** The fiber of a map to a contractible type is the total space. *)

Definition fiber_map_to_contr A B (y:B) (f:A -> B) : is_contr B ->
  {x:A & f x == y} <~> A.
Proof.
  intros Bcontr.
  exists pr1.
  apply @hequiv_is_equiv with (fun x:A =>
    (existT (fun x' => f x' == y) x (contr_path (f x) y Bcontr))).
  intros x; auto.
  intros [x p].
  simpl.
  apply total_path with (idpath x).
  apply contr_pathcontr.
  apply contr_pathcontr.
  auto.
Defined.

(** The fiber of a map between fibers (the "unstable octahedral axiom"). *)

Section FiberFibers.

  Hypothesis X Y Z : Type.
  Hypothesis f : X -> Y.
  Hypothesis g : Y -> Z.

  Hypothesis z : Z.

  Definition composite_fiber_map
    : {x:X & g (f x) == z} -> {y':Y & g y' == z}
    := square_fiber_map (g o f) g f (idmap Z) (fun x => idpath (g (f x))) z.

  Hypothesis y : Y.
  Hypothesis p : g y == z.

  Definition fiber_of_fibers :
    {w : {x:X & g (f x) == z} &
      composite_fiber_map w == (y ; p) }
    <~> {x:X & f x == y}.
  Proof.
    apply @equiv_compose with
      ({w : {x:X & f x == y} &
        square_fiber_map f (idmap Z) (g o f) g
        (fun x => !idpath (g (f x))) y w
        == (z ; !p) }).
    unfold composite_fiber_map.
    apply @equiv_compose with
      (B := {w : {x : X & g (f x) == z} &
        square_fiber_map (g o f) g f (idmap Z)
        (fun x : X => idpath (g (f x))) z w ==
        (y ; !!p)}).
    apply @trans_equiv with
      (P := fun p => {w : {x : X & g (f x) == z} &
        square_fiber_map (g o f) g f (idmap Z)
        (fun x : X => idpath (g (f x))) z w ==
        (y ; p)}).
    do_opposite_opposite.
    apply @three_by_three with
      (f := g o f)
      (g := g)
      (h := f)
      (k := idmap Z)
      (s := fun x => idpath (g (f x)))
      (d := !p).
    apply fiber_map_to_contr.
    apply pathspace_contr_opp.
  Defined.

End FiberFibers.

Implicit Arguments composite_fiber_map [[X] [Y] [Z]].
