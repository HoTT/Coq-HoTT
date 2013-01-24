Require Export Equivalences UsefulEquivalences FiberEquivalences.

(** The unstable 3x3 lemma. *)

Section ThreeByThreeMaps.

  (* Suppose we have a commutative square. *)
  Hypotheses A B C D : Type.
  Hypotheses (f : A -> B) (g : C -> D) (h : A -> C) (k : B -> D).
  Hypothesis s : forall a, k (f a) = g (h a).

  (* Consider a point in [B]. *)
  Variable (b : B).

  (* Then we get a map between the hfiber of [b] and hfiber of [k b]. *)
  Definition square_fiber_map : hfiber f b -> hfiber g (k b).
  Proof.
    intros [x p].
    exists (h x).
    path_via' (k (f x)).
    apply opposite, s.
    exact (map k p).
  Defined.

End ThreeByThreeMaps.

Implicit Arguments square_fiber_map [[A] [B] [C] [D]].

Section ThreeByThree.

  (* Again, suppose we have a commutative square. *)
  Hypotheses A B C D : Type.
  Hypotheses (f : A -> B) (g : C -> D) (h : A -> C) (k : B -> D).
  Hypothesis s : forall a, k (f a) = g (h a).

  Variables (b : B) (c : C).
  Variable (d : k b = g c).

  Let fibf := hfiber f b.
  Let fibg := hfiber g (k b).

  Let fibf_to_fibg := square_fiber_map f g h k s b :
    fibf -> fibg.

(*  Let fibh := hfiber h c. *)
(*  Let fibk := hfiber k (g c). *)

  Let fibh_to_fibk := square_fiber_map h k f g (fun a => !s a) c
    : hfiber h c -> hfiber k (g c).
  
  Let fibfg := hfiber fibf_to_fibg (c; !d). (* {z : fibf & fibf_to_fibg z = (c ; !d)} *)
  Let fibhk := hfiber fibh_to_fibk (b; d).  (* {z : hfiber h c & fibh_to_fibk z = (b ; d)} *)

  Let fibfibmapf (x : A) (p : f x = b) :
    ((h x ; !s x @ map k p) = (existT (fun c' => g c' = k b) c (!d)))
    <~>
    {q : h x = c & transport (P := fun c' => g c' = k b) q (!s x @ map k p) = !d}
    := total_paths_equiv _ _ _ _.

  Let fibfibmaph (x : A) (q : h x = c) :
    ((f x ; !(!s x) @ map g q) = (existT (fun b' => k b' = g c) b d))
    <~> {p : f x = b &
      transport (P := fun b' => k b' = g c) p (!(!s x) @ map g q) = d}
    := total_paths_equiv _ _ _ _.
  
  Let fibfibfibmap (x : A) (p : f x = b) (q : h x = c) :
    (transport (P := fun c' => g c' = k b) q (!s x @ map k p) = !d)
    <~>
    (transport (P := fun b' => k b' = g c) p (!(!s x) @ map g q) = d).
  Proof.
    apply equiv_inverse.
    apply @equiv_compose with
      (!transport (P := fun b' => k b' = g c) p (!(!s x) @ map g q) = !d).
    apply opposite2_equiv.    
    apply concat_equiv_left.
    path_via' (transport (P := fun d' => d' = k b) (map g q) (!s x @ map k p)).
    apply @map_trans with (P := fun d' => d' = k b).
    path_via' (!map g q @ (!s x @ map k p)).
    apply trans_is_concat_opp.
    path_via' (!transport (P := fun d' => d' = g c) (map k p) (!(!s x) @ map g q)).
    path_via' (!(!map k p @ !(!s x) @ map g q)).
    undo_opposite_concat.
    associate_right.
    apply map, opposite.
    rewrite opposite_opposite.
    hott_simpl. (* finishes a subgoal *)
    rewrite opposite_opposite.
    apply map.
    rewrite <- map_trans.
    reflexivity.
  Defined.

  Let fibfibmap (x : A) (p : f x = b) :
    {q : h x = c &
      (transport (P := fun c' => g c' = k b) q (!s x @ map k p) = !d)}
    <~>
    {q : h x = c &
      (transport (P := fun b' => k b' = g c) p (!(!s x) @ map g q) = d)}.
  Proof.
    apply total_equiv.
    intros q.
    apply fibfibfibmap.
  Defined.

  Let fibmap (x:A) :
    {p : f x = b & fibf_to_fibg (x ; p) = (c ; !d)} <~>
    {q : h x = c & fibh_to_fibk (x ; q) = (b ; d)}.
  Proof.
    apply @equiv_compose with
      ({p : f x = b & {q : h x = c &
        transport (P := fun c' => g c' = k b) q (!s x @ map k p) = !d}}).
    apply total_equiv.
    intros; apply fibfibmapf.
    apply @equiv_compose with
      ({q : h x = c & {p : f x = b &
        transport (P := fun b' => k b' = g c) p (!(!s x) @ map g q) = d}}).
    apply @equiv_compose with
      ({p : f x = b & {q : h x = c&
        transport (P := fun b' => k b' = g c) p (!(!s x) @ map g q) = d}}).
    apply total_equiv; intros; apply fibfibmap.
    apply total_comm.
    apply equiv_inverse.
    apply total_equiv; intros; apply fibfibmaph.
  Defined.

  Definition three_by_three : fibfg <~> fibhk.
  Proof.
    apply @equiv_compose with
      ({x : A & {p : f x = b & fibf_to_fibg (x;p) = (c;!d)}}).
    apply equiv_inverse.
    apply total_assoc_sum with
      (A := A)
      (P := fun x => f x = b)
      (Q := fun xp => fibf_to_fibg xp = (c;!d)).
    apply @equiv_compose with
      ({x : A & {p : h x = c & fibh_to_fibk (x;p) = (b;d)}}).
    apply total_equiv; intros; apply fibmap.
    unfold hfiber.
    apply total_assoc_sum with
      (A := A)
      (P := fun x => h x = c)
      (Q := fun xp => fibh_to_fibk xp = (b;d)).
  Defined.

End ThreeByThree.

(** A version for maps that are given as fibrations. *)

Section ThreeByThreeFib.

  Variable A B : Type.
  Variable (P : fibration A) (Q : fibration B).
  Variable f : A -> B.
  Variable g : forall x, P x -> Q (f x).

  Let fg : total P -> total Q := fun u => (f (pr1 u); g (pr1 u) (pr2 u)).

  Variable y : B.
  Variable q : Q y.

  Let fibfibration (xs : hfiber f y) : Type :=
    {p : P (pr1 xs) & pr2 xs # g (pr1 xs) p = q }.

  Definition three_by_three_fib :
    total fibfibration <~> {xp : total P & fg xp = (y;q) }.
  Proof.
    apply @equiv_compose with
      (B := {x : A & { s : f x = y & {p : P x & s # g x p = q}}}).
    apply equiv_inverse.
    apply total_assoc_sum with
      (P := fun x => f x = y)
      (Q := fun xs : hfiber f y =>
        {p : P (pr1 xs) & (pr2 xs) # g (pr1 xs) p = q}).
    apply @equiv_compose with
      (B := {x : A & {p : P x & (f x ; g x p) = (y ; q)}}).
    2:apply total_assoc_sum with
      (Q := fun xp : total P => fg xp = (y ; q)).
    apply @equiv_compose with
      (B := {x : A & {p : P x & {s : f x = y & s # g x p = q}}}).
    set (tc := fun x => total_comm (f x = y) (P x) (fun s p => s  # g x p = q)).
    apply total_equiv; intros; apply tc.
    set (tpe := fun x p => equiv_inverse
      (total_paths_equiv B Q (f x ; g x p) (y ; q))).
    apply total_equiv.
    intro; apply total_equiv.
    intro; apply tpe.
  Defined.

End ThreeByThreeFib.

(** The fiber of an identity map is contractible.
   This is pathspace_contr, pathspace_contr', pathspace_contr_opp
   from Contractible.v. *)
  
(** The fiber of a map to a contractible type is the total space. *)

Definition fiber_map_to_contr A B (y : B) (f : A -> B) :
  is_contr B -> hfiber f y <~> A.
Proof.
  intros Bcontr.
  apply (equiv_from_hequiv
    pr1
    ((fun x : A => (existT (fun x' => f x' = y) x (contr_path (f x) y Bcontr))))).
  intros x; auto.
  intros [x p].
  apply @total_path with (idpath x).
  simpl.
  apply contr_pathcontr.
  apply contr_pathcontr.
  assumption.
Defined.

(** The fiber of a map between fibers (the "unstable octahedral axiom"). *)

Section FiberFibers.

  Variable X Y Z : Type.
  Variable f : X -> Y.
  Variable g : Y -> Z.

  Variable z : Z.

  Definition composite_fiber_map: {x : X & g (f x) = z} -> {y' : Y & g y' = z}
    := square_fiber_map (g o f) g f (idmap Z) (fun x => idpath (g (f x))) z.

  Variable y : Y.
  Variable p : g y = z.

  Definition fiber_of_fibers :
    {w : {x : X & g (f x) = z} & composite_fiber_map w = (y ; p) }
    <~> {x : X & f x = y}.
  Proof.
    apply @equiv_compose with
      ({w : {x : X & f x = y} &
        square_fiber_map f (idmap Z) (g o f) g
        (fun x => !idpath (g (f x))) y w
        = (z ; !p) }).
    unfold composite_fiber_map.
    apply @equiv_compose with
      (B := {w : {x : X & g (f x) = z} &
        square_fiber_map (g o f) g f (idmap Z)
        (fun x : X => idpath (g (f x))) z w =
        (y ; !!p)}).

    apply @trans_equiv with
      (P := fun p : g y = z => {w : {x : X & g (f x) = z} &
        square_fiber_map (g o f) g f (idmap Z)
        (fun x : X => idpath (g (f x))) z w =
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
