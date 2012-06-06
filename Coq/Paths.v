(** Basic homotopy-theoretic approach to paths. *)

Require Export Functions.

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

Inductive paths {A} : A -> A -> Type := idpath : forall x, paths x x.

(* The next line tells [coqdoc] to print [paths] as an equals sign in LaTeX. *)
(** printing == $=$ *)

(** We introduce notation [x == y] for the space [paths x y] of paths
   from [x] to [y]. We can then write [p : x == y] to indicate that
   [p] is a path from [x] to [y]. *)

Notation "x == y" := (paths x y) (at level 70).

(** The [Hint Resolve @idpath] line below means that Coq's [auto]
   tactic will automatically perform [apply idpath] if that leads to a
   successful solution of the current goal. For example if we ask it
   to construct a path [x == x], [auto] will find the identity path
   [idpath x], thanks to the [Hint Resolve].

   In general we should declare [Hint Resolve] on those theorems which
   are not very complicated but get used often to finish off
   proofs. Notice how we use the non-implicit version [@idpath] (if we
   try [Hint Resolve idpath] Coq complains that it cannot guess the
   value of the implicit argument [A]).  *)

Hint Resolve @idpath.

(** The following automated tactic applies induction on paths and then
    idpath. It can handle many easy statements.  *)

Ltac path_induction :=
  intros; repeat progress (
    match goal with
      | [ p : _ == _  |- _ ] => induction p
      | _ => idtac
    end
  ); auto.

(** You can read the tactic definition as follows. We first perform
   [intros] to move hypotheses into the context. Then we repeat while
   there is still progress: if there is a path [p] in the context,
   apply induction to it, otherwise perform the [idtac] which does
   nothing (and so no progress is made and we stop). After that, we
   perform an [auto].

   The notation [ [... |- ... ] ] is a pattern for contexts. To the
   left of the symbol [|-] we list hypotheses and to the right the
   goal. The underscore means "anything".

   In summary [path_induction] performs as many inductions on paths as
   it can, then it uses [auto].  *)

(** We now define the basic operations on paths, starting with
   concatenation. *)

Definition concat {A} {x y z : A} : (x == y) -> (y == z) -> (x == z).
Proof.
  intros A x y z p q.
  induction p.
  induction q.
  apply idpath.
Defined.

(** The concatenation of paths [p] and [q] is denoted as [p @ q]. *)

Notation "p @ q" := (concat p q) (at level 60).

(** A definition like [concat] can be used in two ways. The first and
   obvious way is as an operation which concatenates together two
   paths. The second use is a proof tactic when we want to construct a
   path [x == z] as a concatenation of paths [x == y == z]. This is
   done with [apply @concat], see examples below. We will actually
   define a tactic [path_via] which uses [concat] but is much smarter
   than just the direct application [apply @concat]. *)

(** Paths can be reversed. *)

Definition opposite {A} {x y : A} : (x == y) -> (y == x).
Proof.
  intros A x y p.
  induction p.
  apply idpath.
Defined.

(** Notation for the opposite of a path [p] is [! p]. *)

Notation "! p" := (opposite p) (at level 50).

(** Next we give names to the basic properties of concatenation of
   paths. Note that all statements are "up to a higher path", e.g.,
   the composition of [p] and the identity path is not equal to [p]
   but only connected to it with a path. *)

(** The following lemmas say that up to higher paths, the paths form a
   1-groupoid. *)

Lemma idpath_left_unit A (x y : A) (p : x == y) : idpath x @ p == p.
Proof.
  path_induction.
Defined.

Lemma idpath_right_unit A (x y : A) (p : x == y) : (p @ idpath y) == p.
Proof.
  path_induction.
Defined.

Lemma opposite_right_inverse A (x y : A) (p : x == y) : (p @ !p) == idpath x.
Proof.
 path_induction.
Defined.

Lemma opposite_left_inverse A (x y : A) (p : x == y) : (!p @ p) == idpath y.
Proof.
  path_induction.
Defined.

Lemma opposite_concat A (x y z : A) (p : x == y) (q : y == z) : !(p @ q) == !q @ !p.
Proof.
  path_induction.
Defined.

Lemma opposite_idpath A (x : A) : !(idpath x) == idpath x.
Proof.
  path_induction.
Defined.

Lemma opposite_opposite A (x y : A) (p : x == y) : !(! p) == p.
Proof.
  path_induction.
Defined.

Lemma concat_associativity A (w x y z : A) (p : w == x) (q : x == y) (r : y == z) :
  (p @ q) @ r == p @ (q @ r).
Proof.
  path_induction.
Defined.

(** Now we move on to the 2-groupoidal structure of a type.
   Concatenation of 2-paths along 1-paths is just ordinary
   concatenation in a path type, but we need a new name and notation
   for concatenation of 2-paths along points. *)

Definition concat2 {A} {x y z : A} {p p' : x == y} {q q' : y == z} :
  (p == p') -> (q == q') -> (p @ q == p' @ q').
Proof.
  path_induction.
Defined.

Notation "p @@ q" := (concat2 p q) (at level 60).

(** We also have whiskering operations. *)

Definition whisker_right {A} {x y z : A} {p p' : x == y} (q : y == z) :
  (p == p') -> (p @ q == p' @ q).
Proof.
  path_induction.
Defined.

Definition whisker_left {A} {x y z : A} {q q' : y == z} (p : x == y) :
  (q == q') -> (p @ q == p @ q').
Proof.
  path_induction.
Defined.

Definition whisker_right_toid {A} {x y : A} {p : x == x} (q : x == y) :
  (p == idpath x) -> (p @ q == q).
Proof.
  intros A x y p q a.
  apply @concat with (y := idpath x @ q).
  apply whisker_right. assumption.
  apply idpath_left_unit.
Defined.

Definition whisker_right_fromid {A} {x y : A} {p : x == x} (q : x == y) :
  (idpath x == p) -> (q == p @ q).
Proof.
  intros A x y p q a.
  apply @concat with (y := idpath x @ q).
  apply opposite, idpath_left_unit.
  apply whisker_right. assumption.
Defined.

Definition whisker_left_toid {A} {x y : A} {p : y == y} (q : x == y) :
  (p == idpath y) -> (q @ p == q).
Proof.
  intros A x y p q a.
  apply @concat with (y := q @ idpath y).
  apply whisker_left. assumption.
  apply idpath_right_unit.
Defined.

Definition whisker_left_fromid {A} {x y : A} {p : y == y} (q : x == y) :
  (idpath y == p) -> (q == q @ p).
Proof.
  intros A x y p q a.
  apply @concat with (y := q @ idpath y).
  apply opposite, idpath_right_unit.
  apply whisker_left. assumption.
Defined.

(** The interchange law for whiskering. *)

Definition whisker_interchange A (x y z : A) (p p' : x == y) (q q' : y == z)
  (a : p == p') (b : q == q') :
  (whisker_right q a) @ (whisker_left p' b) == (whisker_left p b) @ (whisker_right q' a).
Proof.
  path_induction.
Defined.

(** The interchange law for concatenation. *)

Definition concat2_interchange A (x y z : A) (p p' p'' : x == y) (q q' q'' : y == z)
  (a : p == p') (b : p' == p'') (c : q == q') (d : q' == q'') :
  (a @@ c) @ (b @@ d) == (a @ b) @@ (c @ d).
Proof.
  path_induction.
Defined.

(** Now we consider the application of functions to paths. *)

(** A path [p : x == y] in a space [A] is mapped by [f : A -> B] to a
   path [map f p : f x == f y] in [B]. *)

Lemma map {A B} {x y : A} (f : A -> B) : (x == y) -> (f x == f y).
Proof.
  path_induction.
Defined.

(** Taking opposites of 1-paths is functorial on 2-paths. *)

Definition opposite2 {A} {x y : A} {p q : x == y} (a : p == q) : (!p == !q)
  := map opposite a.
(*Proof.
  path_induction.
Defined.*)

(** The next two lemmas state that [map f p] is "functorial" in the path [p]. *)

Lemma idpath_map A B (x : A) (f : A -> B) : map f (idpath x) == idpath (f x).
Proof.
  path_induction.
Defined.

Lemma concat_map A B (x y z : A) (f : A -> B) (p : x == y) (q : y == z) :
  map f (p @ q) == (map f p) @ (map f q).
Proof.
  path_induction.
Defined.

Lemma opposite_map A B (f : A -> B) (x y : A) (p : x == y) :
  map f (! p) == ! map f p.
Proof.
  path_induction.
Defined.

(** It is also the case that [map f p] is functorial in [f].  *)

Lemma idmap_map A (x y : A) (p : x == y) : map (idmap A) p == p.
Proof.
  path_induction.
Defined.

Lemma compose_map A B C (f : A -> B) (g : B -> C) (x y : A) (p : x == y) :
  map (g o f) p == map g (map f p).
Proof.
  path_induction.
Defined.

Lemma constmap_map (A B:Type) (b:B) (x y:A) (p: x==y) :
  map (fun _=>b) p == idpath b.
Proof.
  path_induction.
Defined.

(** We can also map paths between paths. *)

Definition map2 {A B} {x y : A} {p q : x == y} (f : A -> B) :
  p == q -> (map f p == map f q)
  := map (map f).

(** The type of "homotopies" between two functions [f] and [g] is
   [forall x, f x == g x].  These can be derived from "paths" between
   functions [f == g]; the converse is function extensionality. *)

Definition happly {A B} {f g : A -> B} : (f == g) -> (forall x, f x == g x) :=
  fun p x => map (fun h => h x) p.

(** Similarly, [happly] for dependent functions. *)

Definition happly_dep {A} {P : A -> Type} {f g : forall x, P x} :
  (f == g) -> (forall x, f x == g x) :=
  fun p x => map (fun h => h x) p.

(** [happly] preserves path-concatenation and opposites. *)

Lemma happly_concat A B (f g h : A -> B) (p : f == g) (q : g == h) (x:A) :
  happly (p @ q) x == happly p x @ happly q x.
Proof.
  path_induction.
Defined.

Lemma happly_opp A B (f g : A -> B) (p : f == g) (x : A) :
  happly (!p) x == !happly p x.
Proof.
  path_induction.
Defined.

Lemma happly_dep_concat A P (f g h : forall a:A, P a) (p : f == g) (q : g == h) (x:A) :
  happly_dep (p @ q) x == happly_dep p x @ happly_dep q x.
Proof.
  path_induction.
Defined.

Lemma happly_dep_opp A P (f g : forall a:A, P a) (p : f == g) (x : A) :
  happly_dep (!p) x == !happly_dep p x.
Proof.
  path_induction.
Defined.

(** How happly interacts with map. *)

Lemma map_precompose {A B C} (f g : B -> C) (h : A -> B)
  (p : f == g) (a : A) :
  happly (map (fun f' => f' o h) p) a == happly p (h a).
Proof.
  path_induction.
Defined.

Lemma map_postcompose {A B C} (f g : A -> B) (h : B -> C)
  (p : f == g) (a : A) :
  happly (map (fun f' => h o f') p) a == map h (happly p a).
Proof.
  path_induction.
Defined.

Lemma map_precompose_dep {A B P} (f g : forall b:B, P b) (h : A -> B)
  (p : f == g) (a : A) :
  happly_dep (map (fun f' => fun a => f' (h a)) p) a == happly_dep p (h a).
Proof.
  path_induction.
Defined.

(** Paths in cartesian products. *)

Definition prod_path {X Y} (z z' : X * Y) :
  (fst z == fst z') -> (snd z == snd z') -> (z == z').
Proof.
  intros; destruct z; destruct z'.
  simpl in *; path_induction.
Defined.

(** We declare some more [Hint Resolve] hints, now in the "hint
   database" [path_hints].  In general various hints (resolve,
   rewrite, unfold hints) can be grouped into "databases". This is
   necessary as sometimes different kinds of hints cannot be mixed,
   for example because they would cause a combinatorial explosion or
   rewriting cycles.

   A specific [Hint Resolve] database [db] can be used with [auto with db]. *)

Hint Resolve
  @idpath @opposite
  idpath_left_unit idpath_right_unit
  opposite_right_inverse opposite_left_inverse
  opposite_concat opposite_idpath opposite_opposite
  @concat2
  @whisker_right @whisker_left
  @whisker_right_toid @whisker_right_fromid
  @whisker_left_toid @whisker_left_fromid
  @opposite2
  @map idpath_map concat_map idmap_map compose_map opposite_map
  @map2
 : path_hints.

(** We can add more hints to the database later. *)

(** For some reason, [apply happly] and [apply happly_dep] often seem
   to fail unification.  This tactic does the work that I think they
   should be doing. *)

Ltac apply_happly_to f' g' x' :=
  first [
      apply @happly with (f := f') (g := g') (x := x')
    | apply @happly_dep with (f := f') (g := g') (x := x')
  ].

Ltac apply_happly :=
  match goal with
    | |- ?f ?x == ?g ?x =>
      apply_happly_to f g x
    | |- ?f1 (?f2 ?x) == ?g ?x =>
      change ((f1 o f2) x == g x);
      apply_happly_to (f1 o f2) g x
    | |- ?f ?x == ?g1 (?g2 ?x) =>
      change (f x == (g1 o g2) x);
      apply_happly_to f (g1 o g2) x
    | |- ?f1 (?f2 ?x) == ?g1 (?g2) ?x =>
      change ((f1 o f2) x == (g1 o g2) x);
      apply_happly_to (f1 o f2) (g1 o g2) x
  end.

(** The following tactic is intended to be applied when we want to
   find a path between two expressions which are largely the same, but
   differ in the value of some subexpression.  Therefore, it does its
   best to "peel off" all the parts of both sides that are the same,
   repeatedly, until only the "core" bit of difference is left.  Then
   it performs an [auto] using the [path_hints] database. *)

Ltac path_simplify :=
  repeat progress first [
      apply whisker_left
    | apply whisker_right
    | apply @map
    ]; auto with path_hints.

(** The following variant allows the caller to supply an additional
   lemma to be tried (for instance, if the caller expects the core
   difference to be resolvable by using a particular lemma). *)

Ltac path_simplify' lem :=
  repeat progress first [
      apply whisker_left
    | apply whisker_right
    | apply @map
    | apply lem
    | apply opposite; apply lem
    ]; auto with path_hints.

(* This one takes a tactic rather than a lemma. *)

Ltac path_simplify'' tac :=
  repeat progress first [
      apply whisker_left
    | apply whisker_right
    | apply @map
    | tac
    | apply opposite; tac
    ]; auto with path_hints.

(** These tactics are used to construct a path [a == b] as a
   composition of paths [a == x] and [x == b].  They then apply
   [path_simplify] to both paths, along with possibly an additional
   lemma supplied by the user. *)

Ltac path_via mid :=
  apply @concat with (y := mid); path_simplify.

Ltac path_using mid lem :=
  apply @concat with (y := mid); path_simplify' lem.

Ltac path_using' mid tac :=
  apply @concat with (y := mid); path_simplify'' tac.

(** This variant does not call path_simplify. *)

Ltac path_via' mid :=
  apply @concat with (y := mid).

(** And this variant does not actually do composition; it just changes
   the form of one of the goals. *)

Ltac path_change mid :=
  match goal with
    |- ?source == ?target =>
      first [ change (source == mid) | change (mid == target) ]
  end; path_simplify.

(** Here are some tactics for reassociating concatenations.  The
   tactic [associate_right] associates both source and target of the
   goal all the way to the right, and dually for [associate_left]. *)

Ltac associate_right_in s :=
  match s with
    context cxt [ (?a @ ?b) @ ?c ] => 
    let mid := context cxt[a @ (b @ c)] in
      path_using mid concat_associativity
  end.
  
Ltac associate_right :=
  repeat progress (
    match goal with
      |- ?s == ?t => first [ associate_right_in s | associate_right_in t ]
    end
  ).

Ltac associate_left_in s :=
  match s with
    context cxt [ ?a @ (?b @ ?c) ] => 
    let mid := context cxt[(a @ b) @ c] in
      path_using mid concat_associativity
  end.

Ltac associate_left :=
  repeat progress (
    match goal with
      |- ?s == ?t => first [ associate_left_in s | associate_left_in t ]
    end
  ).

(** This tactic unwhiskers by paths on both sides, reassociating as
   necessary. *)

Ltac unwhisker :=
  associate_left;
  repeat progress apply whisker_right;
  associate_right;
  repeat progress apply whisker_left.

(** Here are some tactics for eliminating identities.  The tactic
   [cancel_units] tries to remove all identity paths and functions
   from both source and target of the goal. *)

Ltac cancel_units_in s :=
  match s with
    | context cxt [ idpath ?a @ ?p ] => 
      let mid := context cxt[p] in path_using mid idpath_left_unit
    | context cxt [ ?p @ idpath ?a ] => 
      let mid := context cxt[p] in path_using mid idpath_right_unit
    | context cxt [ map ?f (idpath ?x) ] =>
      let mid := context cxt[idpath (f x)] in path_using mid idpath_map
    | context cxt [ map (idmap _) ?p ] =>
      let mid := context cxt[p] in path_using mid idmap_map
    | context cxt [ ! (idpath ?a) ] =>
      let mid := context cxt[idpath a] in path_using mid opposite_idpath
    | context cxt [ map (fun _ => ?a) ?p ] => 
      let mid := context cxt[idpath a] in path_using mid constmap_map
    | context cxt [ ! map (fun _ => ?a) ?p ] =>
      let mid := context cxt[! idpath a] in path_using mid constmap_map
  end.

Ltac cancel_units :=
  repeat (
    match goal with
      |- ?s == ?t => first [ cancel_units_in s | cancel_units_in t ]
    end
  ).

(** And some tactics for eliminating matched pairs of opposites. *)

(** This is an auxiliary tactic which performs one step of a
   reassociation of [s] (which is the source or target of a path) so
   as to get [!p] to be closer to being concatenated on the left with
   something irreducible.  If there is more than one copy of [!p] in
   [s], then this tactic finds the first one which is concatenated on
   the left with anything (irreducible or not), or if there is no such
   occurrence of [!p], then finds the first one overall.  If this [!p]
   is already concatenated on the left with something irreducible,
   then if that something is a [p], it cancels them.  If that
   something is not a [p], then it fails.  *)

Ltac partly_cancel_left_opposite_of_in p s :=
  match s with
    | context cxt [ @concat _ ?trg _ _ (!p) p ] =>
      let mid := context cxt[ idpath trg ] in path_using mid opposite_left_inverse
    | context cxt [ !p @ (?a @ ?b) ] =>
      let mid := context cxt[ (!p @ a) @ b ] in path_using mid concat_associativity
    | context cxt [ !p @ _ ] => fail 1
    | context cxt [ (?a @ !p) @ ?b ] =>
      let mid := context cxt[ a @ (!p @ b) ] in path_using mid concat_associativity
    | context cxt [ ?a @ (?b @ !p) ] =>
      let mid := context cxt[ (a @ b) @ !p ] in path_using mid concat_associativity
  end;
  cancel_units.

(** This tactic simply calls the previous one for the source and the
   target, repeatedly, until it can no longer make progress.
   *)
Ltac cancel_left_opposite_of p := 
  repeat progress (
    match goal with
      |- ?s == ?t => first [
          partly_cancel_left_opposite_of_in p s
        | partly_cancel_left_opposite_of_in p t
      ]
    end
  ).

(** Now the same thing on the right *)

Ltac partly_cancel_right_opposite_of_in p s :=
  match s with
    | context cxt [ @concat _ ?src _ _ p (!p) ] =>
      let mid := context cxt[ idpath src ] in path_using mid opposite_right_inverse
    | context cxt [ (?a @ ?b) @ !p ] =>
      let mid := context cxt[ a @ (b @ !p) ] in path_using mid concat_associativity
    | context cxt [ _ @ !p ] => fail 1
    | context cxt [ ?a @ (!p @ ?b) ] =>
      let mid := context cxt[ (a @ !p) @ b ] in path_using mid concat_associativity
    | context cxt [ (!p @ ?a) @ ?b ] =>
      let mid := context cxt[ !p @ (a @ b) ] in path_using mid concat_associativity
  end;
  cancel_units.

Ltac cancel_right_opposite_of p := 
  repeat progress (
    match goal with
      |- ?s == ?t => first [
          partly_cancel_right_opposite_of_in p s
        | partly_cancel_right_opposite_of_in p t
      ]
    end
  ).

(** This tactic tries to cancel [!p] on both the left and the right. *)
Ltac cancel_opposite_of p :=
  cancel_left_opposite_of p;
  cancel_right_opposite_of p.

(** This tactic looks in [s] for an opposite of anything, and for the
   first one it finds, it tries to cancel it on both sides.  *)
Ltac cancel_opposites_in s :=
  match s with
    context cxt [ !(?p) ] => cancel_opposite_of p
  end.

(** Finally, this tactic repeats the previous one as long as it gets
   us somewhere.  This is most often the easiest of these tactics to
   call in an interactive proof.

   This tactic is not the be-all and end-all of opposite-canceling,
   however; it only works until it runs into an opposite that it can't
   cancel.  It can get stymied by something like [!p @ !q @ q], which
   should simplify to [!p], but the tactic simply tries to cancel
   [!p], makes no progress, and stops.  In such a situation one must
   call [cancel_opposite_of q] directly (or figure out how to write a
   smarter tactic!).  *)

Ltac cancel_opposites :=
  repeat progress (
    match goal with
      |- ?s == ?t => first [ cancel_opposites_in s | cancel_opposites_in t ]
    end
  ).

(** Now we have a sequence of fairly boring tactics, each of which
   corresponds to a simple lemma.  Each of these tactics repeatedly
   looks for occurrences, in either the source or target of the goal,
   of something whose form can be changed by the lemma in question,
   then calls [path_using] to change it.

   For each lemma the basic tactic is called [do_LEMMA].  If the lemma
   can sensibly be applied in two directions, there is also an
   [undo_LEMMA] tactic.  *)

(** Tactics for [opposite_opposite] *)

Ltac do_opposite_opposite_in s :=
  match s with
    | context cxt [ ! (! ?p) ] =>
      let mid := context cxt [ p ] in path_using mid opposite_opposite
  end.

Ltac do_opposite_opposite :=
  repeat progress (
    match goal with
      |- ?s == ?t => first [ do_opposite_opposite_in s | do_opposite_opposite_in t ]
    end
  ).

(** Tactics for [opposite_map]. *)

Ltac apply_opposite_map :=
  match goal with
    | |- map ?f' (! ?p') == ! map ?f' ?p' =>
      apply opposite_map with (f := f') (p := p')
    | |- ! map ?f' ?p' == map ?f' (! ?p') =>
      apply opposite, opposite_map with (f := f') (p := p')
  end.

Ltac do_opposite_map_in s :=
  match s with
    | context cxt [ map ?f (! ?p) ] =>
      let mid := context cxt [ ! map f p ] in path_using mid opposite_map
  end.

Ltac do_opposite_map :=
  repeat progress (
    match goal with
      |- ?s == ?t => first [ do_opposite_map_in s | do_opposite_map_in t ]
    end
  ); do_opposite_opposite.

Ltac undo_opposite_map_in s :=
  match s with
    | context cxt [ ! (map ?f ?p) ] =>
      let mid := context cxt [ map f (! p) ] in path_using mid opposite_map
  end.

Ltac undo_opposite_map :=
  repeat progress (
    match goal with
      |- ?s == ?t => first [ undo_opposite_map_in s | undo_opposite_map_in t ]
    end
  ); do_opposite_opposite.

(** Tactics for [opposite_concat]. *)

Ltac do_opposite_concat_in s :=
  match s with
    | context cxt [ (! ?p) @ (! ?q) ] =>
      let mid := context cxt [ ! (q @ p) ] in path_using mid opposite_concat
  end.

Ltac do_opposite_concat :=
  repeat progress (
    match goal with
      |- ?s == ?t => first [ do_opposite_concat_in s | do_opposite_concat_in t ]
    end
  ); do_opposite_opposite.

Ltac undo_opposite_concat_in s :=
  match s with
    | context cxt [ ! (?q @ ?p) ] =>
      let mid := context cxt [ (! p) @ (! q) ] in path_using mid opposite_concat
  end.

Ltac undo_opposite_concat :=
  repeat progress (
    match goal with
      |- ?s == ?t => first [ undo_opposite_concat_in s | undo_opposite_concat_in t ]
    end
  ); do_opposite_opposite.

(** Tactics for [compose_map].  As with [happly], [apply compose_map]
   often fail to unify, so we define a separate tactic. *)

Ltac apply_compose_map :=
  match goal with
    | |- map (?g' o ?f') ?p' == map ?g' (map ?f' ?p') =>
      apply compose_map with (g := g') (f := f') (p := p')
    | |- map ?g' (map ?f' ?p') == map (?g' o ?f') ?p' =>
      apply opposite; apply compose_map with (g := g') (f := f') (p := p')
  end.

Ltac do_compose_map_in s :=
  match s with
    | context cxt [ map (?f o ?g) ?p ] =>
      let mid := context cxt [ map f (map g p) ] in
        path_via mid; try apply_compose_map
  end.

Ltac do_compose_map :=
  repeat progress (
    match goal with
      |- ?s == ?t => first [ do_compose_map_in s | do_compose_map_in t ]
    end
  ).

Ltac undo_compose_map_in s :=
  match s with
    | context cxt [ map ?f (map ?g ?p) ] =>
      let mid := context cxt [ map (f o g) p ] in
        path_via mid; try apply_compose_map
  end.

Ltac undo_compose_map :=
  repeat progress (
    match goal with
      |- ?s == ?t => first [ undo_compose_map_in s | undo_compose_map_in t ]
    end
  ).

(** Tactics for [concat_map]. *)

Ltac do_concat_map_in s :=
  match s with
    | context cxt [ map ?f (?p @ ?q) ] =>
      let mid := context cxt [ map f p @ map f q ] in
        path_using mid (concat_map _ _ _ _ _ f p q)
  end.

Ltac do_concat_map :=
  repeat progress (
    match goal with
      |- ?s == ?t => first [ do_concat_map_in s | do_concat_map_in t ]
    end
  ).

Ltac undo_concat_map_in s :=
  match s with
    | context cxt [ map ?f ?p @ map ?f ?q ] =>
      let mid := context cxt [ map f (p @ q) ] in
        path_using mid (concat_map _ _ _ _ _ f p q)
  end.

Ltac undo_concat_map :=
  repeat progress (
    match goal with
      |- ?s == ?t => first [ undo_concat_map_in s | undo_concat_map_in t ]
    end
  ).

(** Now we return to proving lemmas about paths.
   We show that homotopies are natural with respect to paths in the domain. *) 

Lemma homotopy_naturality A B (f g : A -> B) (p : forall x, f x == g x) (x y : A) (q : x == y) :
  map f q @ p y == p x @ map g q.
Proof.
  induction q.
  cancel_units.
Defined.

Hint Resolve homotopy_naturality : path_hints.

Lemma homotopy_naturality_toid A (f : A -> A) (p : forall x, f x == x) (x y : A) (q : x == y) :
  map f q @ p y == p x @ q.
Proof.
  induction q.
  cancel_units.
Defined.

Hint Resolve homotopy_naturality_toid : path_hints.

Lemma homotopy_naturality_fromid A (f : A -> A) (p : forall x, x == f x) (x y : A) (q : x == y) :
  q @ p y == p x @ map f q.
Proof.
  induction q.
  cancel_units.
Defined.

Hint Resolve homotopy_naturality_fromid : path_hints.

(** Cancellability of concatenation on both sides. *)

Lemma concat_cancel_right A (x y z : A) (p q : x == y) (r : y == z) : (p @ r == q @ r) -> (p == q).
Proof.
  intros A x y z p q r.
  intro a.
  induction p.
  induction r.
  path_via (q @ idpath x).
Defined.

Lemma concat_cancel_left A (x y z : A) (p : x == y) (q r : y == z) : (p @ q == p @ r) -> (q == r).
Proof.
  intros A x y z p q r.
  intro a.
  induction p.
  induction r.
  path_via (idpath x @ q).
Defined.

(** If a function is homotopic to the identity, then that homotopy
   makes it a "well-pointed" endofunctor in the following sense. *)

Lemma htoid_well_pointed A (f : A -> A) (p : forall x, f x == x) (x : A) :
  map f (p x) == p (f x).
Proof.
  intros A f p x.
  apply concat_cancel_right with (r := p x).
  apply homotopy_naturality_toid.
Defined.

(** Mates *)

Lemma concat_moveright_onright A (x y z : A) (p : x == z) (q : x == y) (r : z == y) :
  (p == q @ !r) -> (p @ r == q).
Proof.
  intros A x y z p q r.
  intro a.
  path_via (q @ (!r @ r)).
  associate_left.
Defined.

Ltac moveright_onright :=
  match goal with
    | |- (?p @ ?r == ?q) =>
      apply concat_moveright_onright
    | |- (?r == ?q) =>
      path_via (idpath _ @ r); apply concat_moveright_onright
  end; do_opposite_opposite.

Lemma concat_moveleft_onright A (x y z : A) (p : x == y) (q : x == z) (r : z == y) :
  (p @ !r == q) -> (p == q @ r).
Proof.
  intros A x y z p q r.
  intro a.
  path_via (p @ (!r @ r)).
  associate_left.
Defined.

Ltac moveleft_onright :=
  match goal with
    | |- (?p == ?q @ ?r) =>
      apply concat_moveleft_onright
    | |- (?p == ?r) =>
      path_via (idpath _ @ r); apply concat_moveleft_onright
  end; do_opposite_opposite.

Lemma concat_moveleft_onleft A (x y z : A) (p : y == z) (q : x == z) (r : y == x) :
  (!r @ p == q) -> (p == r @ q).
Proof.
  intros A x y z p q r.
  intro a.
  path_via ((r @ !r) @ p).
  associate_right.
Defined.

Ltac moveleft_onleft :=
  match goal with
    | |- (?p == ?r @ ?q) =>
      apply concat_moveleft_onleft
    | |- (?p == ?r) =>
      path_via (r @ idpath _); apply concat_moveleft_onleft
  end; do_opposite_opposite.

Lemma concat_moveright_onleft A (x y z : A) (p : x == z) (q : y == z) (r : y == x) :
  (p == !r @ q) -> (r @ p == q).
Proof.
  intros A x y z p q r.
  intro a.
  path_via ((r @ !r) @ q).
  associate_right.
Defined.

Ltac moveright_onleft :=
  match goal with
    | |- (?r @ ?p == ?q) =>
      apply concat_moveright_onleft
    | |- (?r == ?q) =>
      path_via (r @ idpath _); apply concat_moveright_onleft
  end; do_opposite_opposite.
