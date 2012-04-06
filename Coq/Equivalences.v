Require Export Paths Fibrations Contractible.

(* Homotopy equivalences are a central concept in homotopy type theory.
   Before we define equivalences, let us consider when [A] and [B]
   should be considered "the same".

   The first option is to require existence of [f : A -> B] and [g : B -> A] which are
   inverses of each other, up to homotopy. We call this homotopy isomorphism
   or just "h-isomorphism", as suggested by André Joyal.

   The second option is to additionally require that [f] and [g] satisfy
   triangle identities remniscent of the triangle identities for adjunctions
   in category theory. We call this an adjoint equivalence.

   The third option is to use Vladimir Voevodsky's definition of an
   equivalence as a map whose homotopy fibers are contractible.

   We shall start with the third option. We will then show how the other
   two are related to it. *)

(** An equivalence is a map whose homotopy fibers are contractible. *)

Definition is_equiv {A B} (f : A -> B) := forall y : B, is_contr (hfiber f y).

(** [equiv A B] is the space of equivalences from [A] to [B]. It is defined
   as a structure rather than a total space because this allows us to use
   Coq's canonical structures. Also notice that we have a coercion of
   an equivalence to a map.

   The disadvantage of using a structure is that various theorems about
   total spaces cannot be used directly on the structure.
*)

Structure equiv (A B : Type) := {
  equiv_map :> A -> B ;
  equiv_is_equiv : is_equiv equiv_map
}.

Implicit Arguments equiv_map [A B].
Implicit Arguments equiv_is_equiv [A B].

Notation "A <~> B" := (equiv A B) (at level 85).

(** printing <~> $\overset{\sim}{\longrightarrow}$ *)

(** The identity map is an equivalence. *)

Definition idequiv A : A <~> A.
Proof.
  exists (idmap A).
  intros x.
  exists (existT (fun x' => x' ~~> x) x (idpath x)).
  intros [x' p].
  unfold idmap in p.
  induction p.
  auto.
Defined.

Canonical Structure idequiv.

(** We first define the inverse map and only show that it is also an
   equivalence later on, when we are ready to do it. *)

Let inverse {A B : Type} (e : A <~> B) : (B -> A) := fun y => pr1 (pr1 (equiv_is_equiv e y)).

(** The extracted map in the inverse direction is actually an inverse
   (up to homotopy, of course). *)

Definition inverse_is_section {A B : Type} (e : A <~> B) (y : B) : e (inverse e y) ~~> y :=
  pr2 (pr1 ((equiv_is_equiv e) y)).

Hint Rewrite @inverse_is_section : paths.

Definition inverse_is_retraction {A B : Type} (e : A <~> B) (x : A) : inverse e (e x) ~~> x :=
  !base_path (pr2 (equiv_is_equiv e (e x)) (x ; idpath (e x))).

Hint Rewrite @inverse_is_retraction : paths.

Definition map_equiv_o_inverse {A B : Type} (e : A <~> B) (x y : A) (p : x ~~> y) :
  map (inverse e) (map e p) ~~> inverse_is_retraction e x @ p @ !inverse_is_retraction e y.
Proof.
  path_induction.
  hott_simpl.
Defined.

Hint Rewrite @map_equiv_o_inverse : paths.

Definition map_inverse_o_equiv {A B : Type} (e : A <~> B) (u v : B) (p : u ~~> v) :
  map e (map (inverse e) p) ~~> inverse_is_section e u @ p @ !inverse_is_section e v.
Proof.
  path_induction.
  hott_simpl.
Defined.

Hint Rewrite @map_inverse_o_equiv : paths.


(** Here are some tactics to use for canceling inverses, and for introducing them. *)

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

(* These tactics are obsolete now because rewriting can do them. *)

Ltac cancel_inverses_in s :=
  match s with
    | context cxt [ equiv_map _ _ ?w (inverse ?w ?x) ] =>
      let mid := context cxt [ x ] in
        path_using mid inverse_is_section
    | context cxt [ inverse ?w (equiv_map ?w ?x) ] =>
      let mid := context cxt [ x ] in
        path_using mid inverse_is_retraction
  end.

Ltac cancel_inverses :=
  repeat progress (
    match goal with
      | |- ?s ~~> ?t => first [ cancel_inverses_in s | cancel_inverses_in t ]
    end
  ).

(* The following tactics are useful for manipulation of equivalences. *)

Ltac expand_inverse_src w x :=
  match goal with
    | |- ?s ~~> ?t =>
      match s with
        | context cxt [ x ] =>
          first [
            let mid := context cxt [ w (inverse w x) ] in
              path_via' mid;
              [ path_simplify' inverse_is_section | ]
            |
              let mid := context cxt [ inverse w (w x) ] in
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
            let mid := context cxt [ w (inverse w x) ] in
              path_via' mid;
              [ | path_simplify' inverse_is_section ]
            |
              let mid := context cxt [ inverse w (w x) ] in
                path_via' mid;
                [ | path_simplify' inverse_is_retraction ]
          ]
      end
  end.

(** These tactics change between goals of the form [w x ~~> y] and the
   form [x ~~> w^-1 y], and dually. *)

Ltac equiv_moveright :=
  match goal with
    | |- equiv_map ?w ?a ~~> ?b =>
      apply @concat with (y := w (inverse w b));
        [ apply map | apply inverse_is_section ]
    | |- (inverse ?w) ?a ~~> ?b =>
      apply @concat with (y := inverse w (w b));
        [ apply map | apply inverse_is_retraction ]
  end.

Ltac equiv_moveleft :=
  match goal with
    | |- ?a ~~> equiv_map ?w ?b =>
      apply @concat with (y := w (inverse w a));
        [ apply opposite, inverse_is_section | apply map ]
    | |- ?a ~~> (inverse ?w) ?b =>
      apply @concat with (y := inverse w (w a));
        [ apply opposite, inverse_is_retraction | apply map ]
  end.

(** Equivalences are "injective on paths". *)

Lemma equiv_injective {A B : Type} (e : A <~> B) x y : (e x ~~> e y) -> (x ~~> y).
  Proof.
  intro p.
  expand_inverse_src e x.
  equiv_moveright.
  exact p.
Defined.

(** Anything contractible is equivalent to the unit type. *)

Lemma contr_equiv_unit (A : Type) :
  is_contr A -> (A <~> unit).
Proof.
  intros [x h].
  exists (fun x => tt).
  intro y; destruct y.
  contract_hfiber x (idpath tt).
  apply @total_path with (p := h z).
  simpl.
  apply contr_path2.
  auto.
Defined.

(** And conversely, anything equivalent to a contractible type is
   contractible. *)

Lemma contr_equiv_contr (A B : Type) :
  A <~> B -> is_contr A -> is_contr B.
Proof.
  intros f [x p].
  exists (f x).
  intro y.
  equiv_moveleft.
  apply p.
Defined.

(** The free path space of a type is equivalent to the type itself. *)

Definition free_path_space A := {xy : A * A & fst xy ~~> snd xy}.

Definition free_path_source A : free_path_space A <~> A.
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

Definition free_path_target A : free_path_space A <~> A.
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

(** We now consider the notion of an adjoint equivalences and
   prove that they coincide with equivalences. *)

Structure adjoint_equiv A B := {
  adj_map : A -> B ;
  adj_adjoint : B -> A ;
  adj_is_section : (forall y, adj_map (adj_adjoint y) ~~> y) ;
  adj_is_retraction : (forall x, adj_adjoint (adj_map x) ~~> x) ;
  adj_triangle : (forall x, map adj_map (adj_is_retraction x) ~~> adj_is_section (adj_map x))
}.

(** The following property of equivalences serves to show that an
   equivalence is an adjoint equivalences. It is a triangle identity but
   it does not look like one since we have inserted one of the
   homotopies. *)

Definition inverse_triangle {A B : Type} (e : A <~> B) x :
  (map e (inverse_is_retraction e x)) ~~> (inverse_is_section e (e x)).
Proof.
  intros.
  unfold inverse_is_retraction.
  hott_simpl.
  apply (concat (!idpath_right_unit _ _ _ _)).
  hott_simpl.
  moveright_onleft.
Defined.

(** An equivalence is an adjoint equivalence. *)

Definition equiv_to_adjoint {A B} (e : A <~> B) : adjoint_equiv A B :=
  {|
    adj_map := e ;
    adj_adjoint := inverse e ;
    adj_is_section := inverse_is_section e ;
    adj_is_retraction := inverse_is_retraction e ;
    adj_triangle := inverse_triangle e |}.

Theorem adjoint_to_equiv {A B} : adjoint_equiv A B -> A <~> B.
Proof.
  intros [f g is_section is_retraction natural].
  exists f.
  intro y.
  contract_hfiber (g y) (is_section y).
  apply (@total_path _
    (fun x => f x ~~> y)
    (existT _ z q)
    (existT _ (g y) (is_section y))
    (!is_retraction z @ (map g q))).
  simpl.
  path_via (!(map f (!is_retraction z @ map g q)) @ q).
  apply transport_hfiber.
  hott_simpl.
  (** Here is where we use triangle. *)
  path_via (!map f (map g q) @ is_section (f z) @ q).
  (** Now it's just naturality of 'is_section'. *)
  associate_right.
  moveright_onleft.
  undo_compose_map.
  apply opposite, homotopy_naturality_toid with (f := f o g).
  hott_simpl.
Defined.

(** In fact, [equiv_to_adjoint] and [adjoint_to_equiv] are actually
   inverse equivalences, but proving this requires function
   extensionality.  See [FunextEquivalences.v]. *)

(** It is sometimes easier to define an adjoint equivalence than
   an equivalence. *)
Lemma equiv_pointwise_idmap A (f : A -> A) (p : forall x, f x ~~> x) : A <~> A.
Proof.
  apply adjoint_to_equiv.
  refine {| adj_map := f; adj_adjoint := idmap A; adj_is_section := p; adj_is_retraction := p |}.
  apply htoid_well_pointed.
Defined.

(** The third notion of equivalence is that of h-isomorphism. *)

Structure h_isomorphism A B := {
  hiso_map : A -> B ;
  hiso_inverse : B -> A ;
  hiso_section : (forall y, hiso_map (hiso_inverse y) ~~> y) ;
  hiso_retraction : (forall x, hiso_inverse (hiso_map x) ~~> x)
}.

(** A central fact about adjoint equivalences is that any "incoherent"
   equivalence can be improved to an adjoint equivalence by changing
   one of the natural isomorphisms.  We now prove a corresponding
   result in homotopy type theory.  The proof is exactly the same as
   the usual proof for adjoint equivalences in 2-category theory.  *)

Lemma map_retraction_section A B (f : A -> B) (g : B -> A)
  (h : forall x, f (g x) ~~> x) (u v : B) (p : u ~~> v) :
  map f (map g p) ~~> h u @ p @ ! h v.
Proof.
  path_induction.
  hott_simpl.
Defined.

Definition adjointify {A B} : h_isomorphism A B -> adjoint_equiv A B.
Proof.
  intros [f g is_section is_retraction].
  (* We have to redefine one of the two homotopies. *)
  set (is_retraction' := fun x =>
    ( map g (map f (!is_retraction x)))
    @ (map g (is_section (f x)))
    @ (is_retraction x)).
  refine {|
    adj_map := f;
    adj_adjoint := g;
    adj_is_section := is_section;
    adj_is_retraction := is_retraction' |}.
  intro x.
  (** Now we just play with naturality until things cancel. *)
  unfold is_retraction'.
  hott_simpl.
  associate_right.
  moveright_onleft.
  rewrite map_retraction_section with (h := is_section).
  hott_simpl.
  set (q := map f (is_retraction x)).
  moveright_onleft.
  associate_left.
  moveleft_onright.
  rewrite <- compose_map.
  exact (homotopy_naturality_fromid B  _ (fun y => ! is_section y) _ _ _).
Defined.

(** We have proven that every equivalence has an inverse up to
    homotopy.  In fact, having an inverse up to homotopy is also
    enough to characterize a map as being an equivalence.  However,
    the data of an inverse up to homotopy is not equivalent to the
    data in [equiv] unless we add one more piece of coherence data.
    This is a homotopy version of the category-theoretic notion of
    "adjoint equivalence". *)

(** Therefore, "any homotopy equivalence is an equivalence." *)

Definition h_isomorphism_to_equiv {A B} : h_isomorphism A B -> (A <~> B) :=
  adjoint_to_equiv o adjointify.

(** All sorts of nice things follow from this theorem. In fact, we use
   it so often that it deserves a tactic. *)

Ltac by_hiso f g :=
  apply @h_isomorphism_to_equiv;
    refine {| hiso_map := f; hiso_inverse := g |}.

(** The inverse of an equivalence is an equivalence. *)

Lemma equiv_inverse {A B} : (A <~> B) -> B <~> A.
Proof.
  intro e.
  destruct (equiv_to_adjoint e) as [f g is_section is_retraction triangle].
  by_hiso g f; auto.
Defined.

Canonical Structure equiv_inverse.

(** printing ^-1 $^{-1}$ *)

Notation "e ^-1" := (equiv_inverse e) (at level 33).

(* Rewrite rules for inverses. *)

Lemma equiv_inverse_is_inverse (A B  : Type) (f : A <~> B) : equiv_map (f^-1) ~~> inverse f.
Proof.
  apply idpath.
Defined.

Hint Rewrite equiv_inverse_is_inverse : paths.

(** Anything homotopic to an equivalence is an equivalence. *)

Lemma equiv_homotopic {A B} (f : A -> B) (g : A <~> B) :
  (forall x, f x ~~> g x) -> A <~> B.
Proof.
  intros p.
  by_hiso f (inverse g).
  intro y.
  rewrite p.
  hott_simpl.
  intro x.
  equiv_moveright; auto.
Defined.

(** And the 2-out-of-3 property for equivalences. *)

Definition equiv_compose {A B C} (f : A <~> B) (g : B <~> C) : (A <~> C).
Proof.
  by_hiso (g o f) ((inverse f) o (inverse g)); intro; unfold compose; hott_simpl.
Defined.

Canonical Structure equiv_compose.

Lemma equiv_inverse_compose (A B C : Type) (f : A <~> B) (g : B <~> C) x :
  inverse (equiv_compose f g) x ~~> inverse f (inverse g x).
Proof.
  auto.
Defined.

Hint Rewrite equiv_inverse_compose : paths.

Definition equiv_cancel_right {A B C} (f : A <~> B) (g : B -> C) :
  is_equiv (g o f) -> B <~> C.
Proof.
  intros H.
  pose (gof := {| equiv_map := g o f; equiv_is_equiv := H |}).
  by_hiso g (f o gof^-1).
  intro y.
  expand_inverse_trg gof y.
  apply idpath.
  intro x.
  change (f (gof^-1 (g x)) ~~> x).
  equiv_moveright; equiv_moveright.
  change (g x ~~> g (f (f^-1 x))).
  hott_simpl.
Defined.

Definition equiv_cancel_left {A B C} (f : A -> B) (g : B <~> C) :
  is_equiv (g o f) -> A <~> B.
Proof.
  intros H.
  pose (gof := {| equiv_map := g o f; equiv_is_equiv := H |}).
  by_hiso f (gof^-1 o g).
  intros y.
  expand_inverse_trg g y.
  expand_inverse_src g (f (((gof ^-1) o g) y)).
  apply map.
  path_via (gof ((gof^-1 (g y)))).
  hott_simpl.
  intros x.
  path_via (gof^-1 (gof x)).
  hott_simpl.
Defined.

Theorem equiv_to_hiso {A B} : A <~> B -> h_isomorphism A B.
Proof.
  intro e.
  exists e (inverse e).
  apply inverse_is_section.
  apply inverse_is_retraction.
Defined.

Theorem hiso_to_equiv {A B} : h_isomorphism A B -> A <~> B.
Proof.
  intros [f g G H].
  by_hiso f g; assumption.
Defined.

(** Of course, the harder part is showing that [is_hiso] is a
   proposition, and therefore equivalent to [is_equiv].  This also
   requires function extensionality; see [FunextEquivalences.v]. *)
