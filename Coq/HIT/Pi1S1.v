Add LoadPath "..".
Require Import Homotopy Integers Circle.

(** In this file we prove that the loop space [base == base] of
   [circle] is equivalent to the integers [int]. *)

(** It is easy to define a map in one direction.  We call the function
   [wind] because [wind z] is the path that winds around the circle
   [z] times.  *)

(* We first assume that there is a circle. *)
Parameter circle : Circle.

Definition wind (z : int) : (base == base) :=
  match z with
    | zero => idpath base
    | pos n => (fix F (n : nat) :=
                  match n with
                    | 0 => loop
                    | S n' => F n' @ loop
                  end) n
    | neg n => (fix F (n : nat) :=
                  match n with
                    | 0 => !loop
                    | S n' => F n' @ !(@loop circle)
                  end) n
  end.

(** The value of [wind (succ z)] is obtained by concatenating [wind z]
   with [loop], and dually. *)

Lemma wind_succ (z : int) :
  wind z @ loop == wind (succ z).
Proof.
  induction z.
  induction n.
  auto.
  auto.
  path_via (@loop circle).
  induction n.
  apply opposite_left_inverse.
  path_via ((wind (neg n) @ !loop) @ loop).
  cancel_opposites.
Defined.

Lemma wind_pred (z : int) :
  wind z @ !loop == wind (pred z).
Proof.
  induction z.
  induction n.
  simpl; auto with path_hints.
  moveright_onright.
  path_via (!(@loop circle)).
  induction n.
  auto with path_hints.
  auto.
Defined.

(** Now we apply univalence to construct the universal cover of the
   circle, as a dependent type (i.e. a fibration). *)

Definition circle_cover : circle -> Type :=
  circle_rect' circle Type int (equiv_to_path succ_equiv).

(** Of course, the fiber over [base] is equivalent to [int]. *)

Definition fiber_toint : (circle_cover base) <~> int.
Proof.
  apply path_to_equiv.
  apply compute_base'.
Defined.

(** The following lemma says that the universal cover is a "discrete
   fibration", in the sense that any two parallel paths upstairs which
   agree downstairs must also agree upstairs.  Here is where we use
   the fact that [int] is a set. *)

Lemma circle_cover_dfib (c c' : circle) (z : circle_cover c) (z' : circle_cover c')
  (p q : (c ; z) == (c' ; z')) :
  (base_path p == base_path q) -> (p == q).
Proof.
  intros s.
  apply total_path2 with (r := s).
  assert (S : is_set (circle_cover base)).
  apply @hlevel_equiv with (A := int).
  apply path_to_equiv, opposite, compute_base'.
  apply int_is_set.
  moveleft_onleft.
  assert (S' : forall d:circle, is_set (circle_cover d)).
  apply circle_rect with (pt := S).
  apply contr_path.
  apply hlevel_inhabited_contr.
  assumption.
  apply (S' c' (pr2 (c' ; z'))).
Defined.

(** The next two lemmas say that modulo [fiber_toint], the paths
   [loop] and [!loop] act on the fiber of the universal cover by
   [succ] and [pred], respectively. *)

Lemma fiber_loop_action (x : circle_cover base) :
  fiber_toint (transport loop x) == succ (fiber_toint x).
Proof.
  expand_inverse_src fiber_toint x.
  change ((fiber_toint o transport loop o (fiber_toint^-1)) (fiber_toint x) == succ (fiber_toint x)).
  apply happly.
  path_via succ_equiv.
  path_via (fiber_toint o path_to_equiv (map circle_cover loop) o (fiber_toint ^-1)).
  apply happly; apply map; apply map.
  apply opposite, path_to_equiv_map.
  unfold fiber_toint.
  undo_opposite_to_inverse.
  undo_concat_to_compose.
  path_via (path_to_equiv (equiv_to_path succ_equiv)).
  moveright_onleft.
  moveright_onright.
  apply compute_loop'.
  apply equiv_to_path_section.
Defined.

Lemma fiber_opploop_action (x : circle_cover base) :
  fiber_toint (transport (!loop) x) == pred (fiber_toint x).
Proof.
  expand_inverse_src fiber_toint x.
  change ((fiber_toint o transport (!loop) o (fiber_toint^-1)) (fiber_toint x) == pred (fiber_toint x)).
  apply happly.
  path_via (succ_equiv ^-1).
  path_via (fiber_toint o path_to_equiv (map circle_cover (!loop)) o (fiber_toint ^-1)).
  apply happly; apply map; apply map.
  apply opposite, path_to_equiv_map.
  unfold fiber_toint.
  undo_opposite_to_inverse.
  undo_concat_to_compose.
  path_via ((path_to_equiv (equiv_to_path succ_equiv))^-1).
  path_via (path_to_equiv (! equiv_to_path succ_equiv)).
  do_opposite_map.
  path_via (!compute_base' circle Type int (equiv_to_path succ_equiv) @
    (!map circle_cover loop @
      !(!compute_base' circle Type int (equiv_to_path succ_equiv)))).
  do_opposite_concat.
  moveright_onright; moveright_onleft.
  associate_left.
  apply compute_loop'.
  apply opposite, opposite_to_inverse.
  apply equiv_to_path_section.
Defined.

(** More generally, [wind z] acts on the fiber by addition of [z]. *)

Lemma fiber_wind_action (z : int) (x : circle_cover base) :
  fiber_toint (transport (wind z) x) == zadd z (fiber_toint x).
Proof.
  induction z.
  (* positive *)
  induction n.
  (* 1 *)
  simpl.
  apply fiber_loop_action.
  (* > 1 *)
  path_via (fiber_toint (transport ((wind (pos n)) @ loop) x)).
  path_via (fiber_toint (transport loop (transport (wind (pos n)) x))).
  apply trans_concat.
  path_via (succ (fiber_toint (transport (wind (pos n)) x))).
  apply fiber_loop_action.
  path_via (succ (zadd (pos n) (fiber_toint x))).
  (* 0 *)
  auto.
  (* negative *)
  induction n.
  (* -1 *)
  simpl.
  apply fiber_opploop_action.
  (* < -1 *)
  path_via (fiber_toint (transport (wind (neg n) @ !loop) x)).
  path_via (fiber_toint (transport (!loop) (transport (wind (neg n)) x))).
  apply trans_concat.
  path_via (pred (fiber_toint (transport (wind (neg n)) x))).
  apply fiber_opploop_action.
  path_via (pred (zadd (neg n) (fiber_toint x))).
Defined.
  
(** We will need the following lemma, which says that if we transport
   a function [f : P x -> Q x] along a path [p : x == y], the
   resulting function [P y -> Q y] can be computed by transporting
   along [! p], applying [f], then transporting back along [p]. *)

Lemma trans_function {A} (P Q : A -> Type) (x y : A) (p : x == y) (f : P x -> Q x) :
  transport (P := fun x => P x -> Q x) p f == transport p o f o transport (!p).
Proof.
  induction p.
  simpl.
  path_via (idmap _ o f o idmap _).
  apply funext.
  intro z.
  auto.
Defined.

(** The following definition is central; it gives a fiberwise map from
   the putative universal cover to the path fibration based at [base].
   Applied at the fiber over [base], this will give a map from [int]
   (the fiber of the universal cover over [base]) to the loop space at
   [base].  That is the map which we want to show to be an
   equivalence, but it turns out that we need the whole fiberwise map,
   not just its component at [base]. *)

Definition cover_to_pathcirc : forall (x : circle),
  circle_cover x -> (base == x).
Proof.
  set (P := fun x => circle_cover x -> base == x).
  set (d := wind o fiber_toint : P base).
  apply (circle_rect _ P d).
  unfold d.
  apply funext.
  intro x.
  path_via (wind (fiber_toint x)).
  
  path_via ((transport loop o wind o fiber_toint o transport (!loop)) x).
  apply happly.
  apply trans_function.
  path_via (transport loop (wind (fiber_toint (transport (!loop) x)))).
  path_via (wind (succ (fiber_toint (transport (!loop) x)))).

  path_via ((wind (fiber_toint (transport (!loop) x))) @ loop).
  apply trans_is_concat.
  apply wind_succ.
  path_via (succ (pred (fiber_toint x))).
  apply fiber_opploop_action.
  apply succ_pred.
Defined.

(** We will show that the just-defined map is an equivalence on fibers
   by showing that it is an equivalence on total spaces.  We will do
   the latter by showing that both total spaces are contractible.  For
   the total path space, this is a standard fact, so we only need to
   deal with the universal cover.

   We will contract the universal cover to [fiber_toint^-1 zero] in the
   fiber over [base].  Thus we will need to produce a path to this
   point from every point of the universal cover. *)

Lemma circle_cover_contrbase_opp (z : circle_cover base) :
  (base ; fiber_toint ^-1 zero) == (base ; z).
Proof.
  apply total_path with (p := wind (fiber_toint z)).
  simpl.
  expand_inverse_trg fiber_toint z.
  equiv_moveleft.
  path_via (zadd (fiber_toint z) zero).
  expand_inverse_trg fiber_toint zero.
  apply fiber_wind_action.
  apply zero_right_unit.
Defined.

Definition circle_cover_contrbase (z : circle_cover base) :
  (base ; z) == (base ; fiber_toint ^-1 zero) :=
  ! circle_cover_contrbase_opp z.

(** You might naively think that we're done.  But actually we need to
   show that *every* point is connected by a path to our chosen
   basepoint, whereas the preceeding lemma only shows this for points
   in the fiber over [base].  Intuitively, [circle] "has no other
   points" than [base], but we always also need to deal with the
   action of [loop] in order for a statement like "every point of the
   circle" to be valid.

   More precisely, this means we need to apply [Circle_rect], and the
   following dependent type is the one to which we will apply it.  A
   point of [circle_cover_contraction c] specifies a way to contract
   every point in the fiber over [c] to the basepoint. *)

Definition circle_cover_contraction (c : circle) :=
  forall z, (c ; z) == (base ; fiber_toint ^-1 zero).

(** The following lemma is easy but subtle and important.  It says
   that if [cb] is *any* way to contract every point in the fiber over
   [c] to the basepoint, as above, and we transport [cb] along any
   path [p : c == c'], then for any point [z] in the fiber over [c'],
   the contraction of [z] to the basepoint obtained thereby is the
   concatenation of the tautological path from [z] to its
   transportation back along [!p] to the fiber over [c], followed by
   the contraction of that point over [c] which is specified by [cb].

   But I'm not sure if that description in words is actually any
   clearer than just reading the statement of the lemma.  *)

Lemma circle_cover_contr_action (c c' : circle) (l : c == c')
  (z : circle_cover c') (cb : circle_cover_contraction c) :
  transport l cb z ==
  total_path _ _ (c' ; z) (c ; transport (!l) z) (!l) (idpath _)
  @ cb (transport (!l) z).
Proof.
  induction l.
  path_via (idpath _ @ cb z).
Defined.

(** Recall that [circle_cover_contrbase] gives a contraction of every
   point in the fiber over [base] to the basepoint, so it is an
   element of [circle_cover_contraction base].  The next lemma says
   that if we transport this element along [loop], it is
   unchanged. *)

Lemma trans_basecontr_fixed :
  transport (P := circle_cover_contraction) loop circle_cover_contrbase == circle_cover_contrbase.
Proof.
  apply funext_dep.
  intro x.
  path_via (total_path _ _ (_ ; x)
    (_ ; transport (!loop) x) (!loop) (idpath _)
    @ circle_cover_contrbase (transport (!loop) x)).
  apply circle_cover_contr_action.
  apply circle_cover_dfib.
  unfold base_path.
  do_concat_map.
  path_via (!loop @ map pr1 (circle_cover_contrbase (transport (!loop) x))).
  apply @base_total_path with
    (x := (base ; x))
    (y := (base ; transport (!loop) x)).
  path_via (!wind (fiber_toint x)).
  path_via (!loop @ !wind (fiber_toint (transport (!loop) x))).
  unfold circle_cover_contrbase.
  do_opposite_map.
  apply_opposite_map.
  path_via (wind (fiber_toint (transport (!loop) x))).
  apply base_total_path.
  do_opposite_concat.
  path_via (wind (pred (fiber_toint x)) @ loop).
  apply fiber_opploop_action.
  path_via (wind (succ (pred (fiber_toint x)))).
  apply wind_succ.
  apply succ_pred.
  unfold circle_cover_contrbase.
  do_opposite_map.
  unfold circle_cover_contrbase_opp.
  apply opposite, base_total_path.
Defined.

(** Finally, we can prove that the total space of the universal cover
   is contractible. *)

Theorem circle_cover_contr: is_contr (sigT circle_cover).
Proof.
  exists (base ; fiber_toint ^-1 zero).
  intros [c z].
  generalize z. generalize c.
  exact (circle_rect _
    (fun c => forall z, (c ; z) == (base ; fiber_toint ^-1 zero))
    circle_cover_contrbase
    trans_basecontr_fixed).
Defined.

(** Now the path fibration over circle based at base also has
   contractible total space, so [cover_to_pathcirc] induces an
   equivalence between total spaces.  By the theorem about fibrations,
   it follows that it is an equivalence itself, hence it is equivalent
   to [base == base]. *)

Theorem cover_to_pathcirc_is_equiv (x : circle) : is_equiv (cover_to_pathcirc x).
Proof.
  apply fiber_is_equiv.
  apply contr_contr_equiv.
  apply circle_cover_contr.
  apply pathspace_contr.
Defined.

(** Here is the main theorem. *)

Theorem int_equiv_loopcirc : int <~> (base == @base circle).
Proof.
  apply @equiv_compose with (B := circle_cover base).
  apply path_to_equiv.
  apply opposite, compute_base'.
  exists (cover_to_pathcirc base).
  apply cover_to_pathcirc_is_equiv.
Defined.
