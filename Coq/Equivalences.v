Require Export Paths Fibrations Contractible.

(** An equivalence is a map whose homotopy fibers are contractible. *)

Definition is_equiv {A B} (f : A -> B) := forall y : B, is_contr (hfiber f y).

(** [equiv A B] is the space of equivalences from [A] to [B]. *)

Definition equiv A B := { w : A -> B & is_equiv w }.

Notation "A ~=> B" := (equiv A B) (at level 55).

(** printing ~=> $\overset{\sim}{\longrightarrow}$ *)

(** Strictly speaking, an element [w] of [A ~=> B] is a _pair_
   consisting of a map [projT1 w] and the proof [projT2 w] that it is
   an equivalence. Thus, in order to apply [w] to [x] we must write
   [projT1 w x]. Coq is able to do this automatically if we declare
   that [projT1] is a _coercion_ from [equiv A B] to [A -> B]. *)

Definition equiv_coerce_to_function A B (w : A ~=> B) : (A -> B) := projT1 w.

Coercion equiv_coerce_to_function : equiv >-> Funclass.

(** Here is a tactic which helps us prove that a homotopy fiber is
   contractible.  This will be useful for showing that maps are
   equivalences. *)

Ltac contract_hfiber y p :=
  match goal with
    | [ |- is_contr (@hfiber _ _ ?f ?x) ] =>
      eexists (existT (fun z => f z ~~> x) y p);
        let z := fresh "z" in
        let q := fresh "q" in
          intros [z q]
  end.

(** Let us explain the tactic. It accepts two arguments [y] and [p]
   and attempts to contract a homotopy fiber to [existT _ y p]. It
   first looks for a goal of the form [is_contr (hfiber f x)], where
   the question marks in [?f] and [?x] are pattern variables that Coq
   should match against the actual values. If the goal is found, then
   we use [eexists] to specify that the center of retraction is at the
   element [existT _ y p] of hfiber provided by the user. After that
   we generate some fresh names and perfrom intros. *)

(** The identity map is an equivalence. *)

Definition idequiv A : A ~=> A.
Proof.
  exists (idmap A).
  intros x.
  contract_hfiber x (idpath x).
  apply total_path with (p := q).
  simpl.
  compute in q.
  path_induction.
Defined.

(** From an equivalence from [U] to [V] we can extract a map in the
   inverse direction. *)

Definition inverse {U V} (w : U ~=> V) : (V -> U) :=
  fun y => pr1 (pr1 ((pr2 w) y)).

Notation inv := inverse.

(** The extracted map in the inverse direction is actually an inverse
   (up to homotopy, of course). *)

Definition inverse_is_section {U V} (w : U ~=> V) y : w (inv w y) ~~> y :=
  pr2 (pr1 ((pr2 w) y)).

Definition inverse_is_retraction {U V} (w : U ~=> V) x : (inv w (w x)) ~~> x :=
  !base_path (pr2 ((pr2 w) (w x)) (tpair x (idpath (w x)))).

(** Here are some tactics to use for canceling inverses, and for
   introducing them. *)

Ltac cancel_inverses_in s :=
  match s with
    | context cxt [ equiv_coerce_to_function _ _ ?w (inverse ?w ?x) ] =>
      let mid := context cxt [ x ] in
        path_using mid inverse_is_section
    | context cxt [inverse ?w (equiv_coerce_to_function _ _ ?w ?x) ] =>
      let mid := context cxt [ x ] in
        path_using mid inverse_is_retraction
  end.

Ltac cancel_inverses :=
  repeat progress (
    match goal with
      | |- ?s ~~> ?t => first [ cancel_inverses_in s | cancel_inverses_in t ]
    end
  ).

Ltac expand_inverse_src w x :=
  match goal with
    | |- ?s ~~> ?t =>
      match s with
        | context cxt [ x ] =>
          first [
            let mid := context cxt [ w (inv w x) ] in
              path_via' mid;
              [ path_simplify' inverse_is_section | ]
            |
            let mid := context cxt [ inv w (w x) ] in
              path_via' mid;
              [ path_simplify' inverse_is_retraction | ]
          ]
      end
  end.

Ltac expand_inverse_trg w x :=
  match goal with
    | |- ?s ~~> ?t =>
      match t with
        | context cxt [ x ] =>
          first [
            let mid := context cxt [ w (inv w x) ] in
              path_via' mid;
              [ | path_simplify' inverse_is_section ]
            |
            let mid := context cxt [ inv w (w x) ] in
              path_via' mid;
              [ | path_simplify' inverse_is_retraction ]
          ]
      end
  end.

(** These tactics change between goals of the form [w x ~~> y] and the
   form [x ~~> inv w y], and dually. *)

Ltac equiv_moveright :=
  match goal with
    | |- equiv_coerce_to_function _ _ ?w ?a ~~> ?b =>
      apply @concat with (y := w (inv w b));
        [ apply map | apply inverse_is_section ]
    | |- (inverse ?w) ?a ~~> ?b =>
      apply @concat with (y := inverse w (w b));
        [ apply map | apply inverse_is_retraction ]
  end.

Ltac equiv_moveleft :=
  match goal with
    | |- ?a ~~> equiv_coerce_to_function _ _ ?w ?b =>
      apply @concat with (y := w (inv w a));
        [ apply opposite, inverse_is_section | apply map ]
    | |- ?a ~~> (inverse ?w) ?b =>
      apply @concat with (y := inv w (w a));
        [ apply opposite, inverse_is_retraction | apply map ]
  end.

(** This is one of the "triangle identities" for the preceeding two
   homotopies.  (It doesn't look like a triangle since we've inverted
   one of the homotopies.) *)

Definition inverse_triangle {A B} (w : A ~=> B) x :
  (map w (inverse_is_retraction w x)) ~~> (inverse_is_section w (w x)).
Proof.
  intros.
  unfold inverse_is_retraction.
  do_opposite_map.
  apply (concat (!idpath_right_unit _ _ _ _)).
  moveright_onleft.
  apply opposite.
  exact (hfiber_triangle (pr2 (pr2 w (w x)) (tpair x (idpath _)))).
Defined.


(** Equivalences are "injective on paths". *)

Lemma equiv_injective U V (w : U ~=> V) x y : (w x ~~> w y) -> (x ~~> y).
Proof.
  intro p.
  expand_inverse_src w x.
  equiv_moveright.
  assumption.
Defined.

(** Anything contractible is equivalent to the unit type. *)

Lemma contr_equiv_unit (A : Type) :
  is_contr A -> (A ~=> unit).
Proof.
  intro H.
  exists (fun x => tt).
  intro y. destruct y.
  contract_hfiber (pr1 H) (idpath tt).
  apply @total_path with (p := pr2 H z).
  apply contr_path2.
  auto.
Defined.

(** And conversely, anything equivalent to a contractible type is
   contractible. *)

Lemma contr_equiv_contr (A B : Type) :
  A ~=> B -> is_contr A -> is_contr B.
Proof.
  intros f [x ?].
  exists (f x).
  intro y.
  equiv_moveleft.
  apply p.
Defined.

(** The free path space of a type is equivalent to the type itself. *)

Definition free_path_space A := {xy : A * A & fst xy ~~> snd xy}.

Definition free_path_source A : free_path_space A ~=> A.
Proof.
  exists (fun p => fst (projT1 p)).
  intros x.
  eexists (existT _ (existT (fun (xy : A * A) => fst xy ~~> snd xy) (x,x) (idpath x)) _).
  intros [[[u v] p] q].
  simpl in * |- *.
  induction q as [a].
  induction p as [b].
  apply idpath.
Defined.

Definition free_path_target A : free_path_space A ~=> A.
Proof.
  exists (fun p => snd (projT1 p)).
  intros x.
  eexists (existT _ (existT (fun (xy : A * A) => fst xy ~~> snd xy) (x,x) (idpath x)) _).
  intros [[[u v] p] q].
  simpl in * |- *.
  induction q as [a].
  induction p as [b].
  apply idpath.
Defined.

(** We have proven that every equivalence has an inverse up to
    homotopy.  In fact, having an inverse up to homotopy is also
    enough to characterize a map as being an equivalence.  However,
    the data of an inverse up to homotopy is not equivalent to the
    data in [is_equiv] unless we add one more piece of coherence data.
    This is a homotopy version of the category-theoretic notion of
    "adjoint equivalence". *)

Definition is_adjoint_equiv {A B} (f : A -> B) :=
  { g : B -> A &
    { is_section : forall y, (f (g y)) ~~> y &
      { is_retraction : forall x, (g (f x)) ~~> x &
        forall x, (map f (is_retraction x)) ~~> (is_section (f x))
          }}}.

Definition is_equiv_to_adjoint {A B} (f: A -> B) (E : is_equiv f) : is_adjoint_equiv f :=
  let w := (tpair f E) in
    tpair (inv w) (tpair (inverse_is_section w) (tpair (inverse_is_retraction w) (inverse_triangle w))).

Definition adjoint_equiv (A B : Type) := { f: A -> B  &  is_adjoint_equiv f }.

Theorem is_adjoint_to_equiv {A B} (f: A -> B) : is_adjoint_equiv f -> is_equiv f.
Proof.
  intros [g [is_section [is_retraction triangle]]].
  intro y.
  contract_hfiber (g y) (is_section y).
  apply (total_path _
    (fun x => f x ~~> y)
    (existT _ z q)
    (existT _ (g y) (is_section y))
    (!is_retraction z @ (map g q))).
  simpl.
  path_via (!(map f (!is_retraction z @ map g q)) @ q).
  apply transport_hfiber.
  do_concat_map.
  do_opposite_map.
  undo_opposite_concat.
  (** Here is where we use triangle. *)
  path_via (!map f (map g q) @ is_section (f z) @ q).
  (** Now it's just naturality of 'is_section'. *)
  associate_right.
  moveright_onleft.
  undo_compose_map.
  apply opposite, homotopy_naturality_toid with (f := f o g).
Defined.

(** Probably equiv_to_adjoint and adjoint_to_equiv are actually
   inverse equivalences, at least if we assume function
   extensionality. *)

Lemma equiv_pointwise_idmap A (f : A -> A) (p : forall x, f x ~~> x) : is_equiv f.
Proof.
  apply is_adjoint_to_equiv.
  exists (idmap A).
  exists p.
  exists p.
  apply htoid_well_pointed.
Defined.

(** A central fact about adjoint equivalences is that any "incoherent"
   equivalence can be improved to an adjoint equivalence by changing
   one of the natural isomorphisms.  We now prove a corresponding
   result in homotopy type theory.  The proof is exactly the same as
   the usual proof for adjoint equivalences in 2-category theory.  *)

Definition adjointify {A B} (f : A -> B) (g : B -> A) :
  (forall y, f (g y) ~~> y) -> (forall x, g (f x) ~~> x ) ->
  is_adjoint_equiv f.
Proof.
  intros is_section is_retraction.
  (* We have to redefine one of the two homotopies. *)
  set (is_retraction' := fun x =>
    ( map g (map f (!is_retraction x)))
    @ (map g (is_section (f x)))
    @ (is_retraction x)).
  exists g.
  exists is_section.
  exists is_retraction'.
  intro x.
  (** Now we just play with naturality until things cancel. *)
  unfold is_retraction'.
  do_concat_map.
  undo_compose_map.
  moveleft_onleft.
  associate_left.
  path_via ((!is_section (f x)  @  map (f o g) (map f (!is_retraction x))
    @  map (f o g) (is_section (f x)))  @  map f (is_retraction x)).
  unwhisker.
  do_compose_map; auto.
  path_via (map f (!is_retraction x)  @  (!is_section (f (g (f x))))
    @  map (f o g) (is_section (f x))  @  map f (is_retraction x)).
  unwhisker.
  apply opposite, (homotopy_naturality_fromid B _ (fun y => !is_section y)).
  path_via (map f (!is_retraction x)  @  (is_section (f x) @ (!is_section (f x)))
    @  map f (is_retraction x)).
  unwhisker.
  apply opposite, (homotopy_naturality_fromid B _ (fun y => !is_section y)).
  do_opposite_map.
  cancel_right_opposite_of (is_section (f x)).
Defined.

(** Therefore, "any homotopy equivalence is an equivalence." *)

Definition hequiv_is_equiv {A B} (f : A -> B) (g : B -> A)
  (is_section : forall y, f (g y) ~~> y) (is_retraction : forall x, g (f x) ~~> x) :
  is_equiv f := is_adjoint_to_equiv f (adjointify f g is_section is_retraction).

(** All sorts of nice things follow from this theorem. *)

(** The inverse of an equivalence is an equivalence. *)

Lemma equiv_inverse {A B} (f : A ~=> B) : B ~=> A.
Proof.
  destruct (is_equiv_to_adjoint f (pr2 f)) as [g [is_section [is_retraction triangle]]].
  exists g.
  exact (hequiv_is_equiv g f is_retraction is_section).
Defined.

(** Anything homotopic to an equivalence is an equivalence. *)

Lemma equiv_homotopic {A B} (f g : A -> B) :
  (forall x, f x ~~> g x) -> is_equiv g -> is_equiv f.
Proof.
  intros p geq.
  set (g' := existT is_equiv g geq : A ~=> B).
  eapply hequiv_is_equiv.
  instantiate (1 := inv g').
  intro y.
  expand_inverse_trg g' y; auto.
  intro x.
  equiv_moveright; auto.
Defined.

(** And the 2-out-of-3 property for equivalences. *)

Definition equiv_compose {A B C} (f : A ~=> B) (g : B ~=> C) : (A ~=> C).
Proof.
  exists (g o f).
  eapply hequiv_is_equiv.
  instantiate (1 := (inv f) o (inv g)).
  intro y.
  expand_inverse_trg g y.
  expand_inverse_trg f (inv g y).
  apply idpath.
  intro x.
  expand_inverse_trg f x.
  expand_inverse_trg g (f x).
  apply idpath.
Defined.

Definition equiv_cancel_right {A B C} (f : A ~=> B) (g : B -> C) :
  is_equiv (g o f) -> is_equiv g.
Proof.
  intro H.
  set (gof := (existT _ (g o f) H) : A ~=> C).
  eapply hequiv_is_equiv.
  instantiate (1 := f o inv (gof)).
  intro y.
  expand_inverse_trg gof y.
  apply idpath.
  intro x.
  change (f (inv gof (g x)) ~~> x).
  equiv_moveright; equiv_moveright.
  change (g x ~~> g (f (inv f x))).
  cancel_inverses.
Defined.

Definition equiv_cancel_left {A B C} (f : A -> B) (g : B ~=> C) :
  is_equiv (g o f) -> is_equiv f.
Proof.
  intros H.
  set (gof := existT _ (g o f) H : A ~=> C).
  eapply hequiv_is_equiv. 
  instantiate (1 := inv gof o g).
  intros y.
  expand_inverse_trg g y.
  expand_inverse_src g (f ((inv gof o g) y)).
  apply map.
  path_via (gof ((inv gof (g y)))).
  apply inverse_is_section.
  intros x.
  path_via (inv gof (gof x)).
  apply inverse_is_retraction.
Defined.

(* It follows that any two contractible types are equivalent. *)

Definition contr_contr_equiv {A B} (f : A -> B) :
  is_contr A -> is_contr B -> is_equiv f.
Proof.
  intros Acontr Bcontr.
  apply @equiv_cancel_left with
    (g := contr_equiv_unit B Bcontr).
  exact (pr2 (contr_equiv_unit A Acontr)).
Defined.

(** The action of an equivalence on paths is an equivalence. *)

Theorem equiv_map_inv {A B} {x y : A} (f : A ~=> B) :
  (f x ~~> f y) -> (x ~~> y).
Proof.
  intro p.
  path_via (inv f (f x)).
  apply opposite, inverse_is_retraction.
  path_via' (inv f (f y)).
  apply map. assumption.
  apply inverse_is_retraction.
Defined.

Theorem equiv_map_is_equiv {A B} {x y : A} (f : A ~=> B) :
  is_equiv (@map A B x y f).
Proof.
  apply @hequiv_is_equiv with (g := equiv_map_inv f).
  intro p.
  unfold equiv_map_inv.
  do_concat_map.
  do_opposite_map.
  moveright_onleft.
  undo_compose_map.
  path_via (map (f o inv f) p @ inverse_is_section f (f y)).
  apply inverse_triangle.
  path_via (inverse_is_section f (f x) @ p).
  apply homotopy_naturality_toid with (f := f o inv f).
  apply opposite, inverse_triangle.
  intro p.
  unfold equiv_map_inv.
  moveright_onleft.
  undo_compose_map.
  apply homotopy_naturality_toid with (f := inv f o f).
Defined.

Definition equiv_map_equiv {A B} {x y : A} (f : A ~=> B) :
  (x ~~> y) ~=> (f x ~~> f y) :=
  tpair (@map A B x y f) (equiv_map_is_equiv f).

(** Path-concatenation is an equivalence. *)

Lemma concat_is_equiv_left {A} (x y z : A) (p : x ~~> y) :
  is_equiv (fun q: y ~~> z => p @ q).
Proof.
  apply @hequiv_is_equiv with (g := @concat A y x z (!p)).
  intro q.
  associate_left.
  intro q.
  associate_left.
Defined.

Definition concat_equiv_left {A} (x y z : A) (p : x ~~> y) :
  (y ~~> z) ~=> (x ~~> z) :=
  tpair (fun q: y ~~> z => p @ q) (concat_is_equiv_left x y z p).

Lemma concat_is_equiv_right {A} (x y z : A) (p : y ~~> z) :
  is_equiv (fun q : x ~~> y => q @ p).
Proof.
  apply @hequiv_is_equiv with (g := fun r : x ~~> z => r @ !p).
  intro q.
  associate_right.
  intro q.
  associate_right.
Defined.

Definition concat_equiv_right {A} (x y z : A) (p : y ~~> z) :
  (x ~~> y) ~=> (x ~~> z) :=
  tpair (fun q: x ~~> y => q @ p) (concat_is_equiv_right x y z p).

(** And we can characterize the path types of the total space of a
   fibration, up to equivalence. *)

Theorem total_paths_equiv (A : Type) (P : A -> Type) (x y : total P) :
  (x ~~> y) ~=> { p : pr1 x ~~> pr1 y & transport p (pr2 x) ~~> pr2 y }.
Proof.
  exists (fun r => existT (fun p => transport p (pr2 x) ~~> pr2 y) (base_path r) (fiber_path r)).
  eapply @hequiv_is_equiv.
  instantiate (1 := fun pq => let (p,q) := pq in total_path A P x y p q).
  intros [p q].
  eapply total_path.
  instantiate (1 := base_total_path A P x y p q).
  simpl.
  apply fiber_total_path.
  intro r.
  simpl.
  apply total_path_reconstruction.
Defined.
  
(** André Joyal suggested the following definition of equivalences,
   and to call it "h-isomorphism". *)

Definition is_hiso {A B} (f : A -> B) :=
  ( { g : B->A  &  forall x, g (f x) ~~> x } *
    { h : B->A  &  forall y, f (h y) ~~> y } )%type.

Theorem equiv_to_hiso {A B} (f : equiv A B) : is_hiso f.
Proof.
  split.
  exists (inv f).
  apply inverse_is_retraction.
  exists (inv f).
  apply inverse_is_section.
Defined.

Theorem hiso_to_equiv {A B} (f : A -> B) : is_hiso f -> is_equiv f.
Proof.
  intro H.
  destruct H as ((g, is_retraction), (h, is_section)).
  eapply hequiv_is_equiv.
  instantiate (1 := g).
  intro y.
  path_via (f (h y)).
  path_via (g (f (h (y)))).
  assumption.
Defined.

(** Of course, the harder part is showing that is_hiso is a proposition. *)
