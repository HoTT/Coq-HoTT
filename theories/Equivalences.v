(** * Equivalences *)

Require Import Common Paths Fibrations Contractible.

Local Open Scope path_scope.
Local Open Scope contr_scope.

(** Homotopy equivalences are a central concept in homotopy type theory. Before we define
   equivalences, let us consider when [A] and [B] should be considered "the same".

   The first option is to require existence of [f : A -> B] and [g : B -> A] which are
   inverses of each other, up to homotopy. Homotopically speaking, we should also require
   a certain condition which is remniscent of the triangle identities for adjunctions in
   category theory. Thus we call this notion an adjoint equivalence.

   The second option is to use Vladimir Voevodsky's definition of an equivalence as a map
   whose homotopy fibers are contractible.

   An interesting third options was suggested by André Joyal: a map [f] which has separate
   left and right homotopy inverses. This too turns out to be reasonable.

   While the second options was used originally, and it is the most concise one, it makes
   much more sense to use the first one in a formalized development, as it exposes most
   directly equivalence as a structure.
*)

(** Naming convention: we use [equiv] and [Equiv] systematically to denote equivalences. *)

(** The fact that [r] is a left inverse of [s]. It is called [cancel] in ssreflect. *)
Definition section {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Record Equiv A B := BuildEquiv {
  equiv_fun :> A -> B ;
  equiv_inv : B -> A ;
  equiv_is_section : section equiv_inv equiv_fun ; 
  equiv_is_retraction : section equiv_fun equiv_inv ;
  equiv_is_adjoint : forall x : A, equiv_is_section (equiv_fun x) = ap equiv_fun (equiv_is_retraction x)
}.

Delimit Scope equiv_scope with equiv.
Local Open Scope equiv_scope.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.

(** We use the canonical structures to recover the equivalence
   structure of a map which is canonically known to be an equivalence. *)

Definition equiv_of A B := 
  fun (f : A -> B) (e : A <~> B) (_ : (f = e :> (A -> B))) => e.

Notation "[ 'equiv' 'of' f ]" := (equiv_of _ _ f _ (idpath _))
  (at level 0, format "[ 'equiv'  'of'  f ]") : equiv_scope.

Definition inverse_of (A B : Type) (e : A <~> B) (_ : batman (A -> B) e) := @equiv_inv _ _ e.

Notation "f ^-1" := (inverse_of _ _ _ (@Batman (_ -> _) f)) : equiv_scope.


(** ** Canonical constructions of equivalences *)

(** The identity map is an equivalence. *)
Canonical Structure equiv_idmap (A : Type) :=
  BuildEquiv A A idmap idmap (fun _ => 1) (fun _ => 1) (fun _ => 1).

(** A contractible type is equivalent to [unit]. *)
Definition equiv_contr_unit (A : Contr) : A <~> unit.
Proof.
  exists
    (fun (_ : A) => tt)
    (fun (_ : unit) => [ center of A ])
    (fun t : unit => match t with tt => 1 end)
    (fun x : A => contr x).
  intro x.
  apply inverse, ap_const.
Defined.

Canonical Structure equiv_contr_unit.

(** Composition of equivalences is an equivalence. *)
Definition equiv_compose {A B C : Type} (f : B <~> C) (e : A <~> B) : Equiv A C.

(**** GOT UP TO HERE. ****)

Section ContractibleHfibers.
  (** The space of equivalences is equivalent to the space of maps whose
     fibers are contractible. *)

Definition is_equiv {A B} (e : A -> B) := forall y : B, is_contr (hfiber e y).

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


(** printing <~> $\overset{\sim}{\longrightarrow}$ *)

(** The identity map is an equivalence. *)

Definition idequiv A : A <~> A.
Proof.
  exists (idmap A).
  intros x.
  exists (existT (fun x' => x' = x) x (idpath x)).
  intros [x' p].
  unfold idmap in p.
  induction p.
  auto.
Defined.

(** We first define the inverse map and only show that it is an
   equivalence later on, when we are ready to do it. *)

Let inverse {A B : Type} (e : A <~> B) : (B -> A) :=
  fun y => pr1 (pr1 (equiv_is_equiv e y)).

(** printing ^-1 $^{-1}$ *)

Notation "e ^-1" := (inverse e) (at level 33).

(** The extracted map in the inverse direction is actually an inverse
   (up to homotopy, of course). *)

Definition inverse_is_section {A B : Type} (e : A <~> B) (y : B) : e (e^-1 y) = y :=
  pr2 (pr1 ((equiv_is_equiv e) y)).

Hint Rewrite @inverse_is_section : paths.

Definition inverse_is_retraction {A B : Type} (e : A <~> B) (x : A) : e^-1 (e x) = x :=
  !base_path (pr2 (equiv_is_equiv e (e x)) (x ; idpath (e x))).

Hint Rewrite @inverse_is_retraction : paths.

Definition map_equiv_o_inverse {A B : Type} (e : A <~> B) (x y : A) (p : x = y) :
  map (e^-1) (map e p) = inverse_is_retraction e x @ p @ !inverse_is_retraction e y.
Proof.
  path_induction.
  hott_simpl.
Defined.

Hint Rewrite @map_equiv_o_inverse : paths.

Definition map_inverse_o_equiv {A B : Type} (e : A <~> B) (u v : B) (p : u = v) :
  map e (map (e^-1) p) = inverse_is_section e u @ p @ !inverse_is_section e v.
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
      eexists (existT (fun z => f z = x) y p);
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
      | |- ?s = ?t => first [ cancel_inverses_in s | cancel_inverses_in t ]
    end
  ).

(* The following tactics are useful for manipulation of equivalences. *)

Ltac expand_inverse_src w x :=
  match goal with
    | |- ?s = ?t =>
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
    | |- ?s = ?t =>
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

(** These tactics change between goals of the form [w x = y] and the
   form [x = w^-1 y], and dually. *)

Ltac equiv_moveright :=
  match goal with
    | |- equiv_map ?w ?a = ?b =>
      apply @concat with (y := w (inverse w b));
        [ apply map | apply inverse_is_section ]
    | |- (inverse ?w) ?a = ?b =>
      apply @concat with (y := inverse w (w b));
        [ apply map | apply inverse_is_retraction ]
  end.

Ltac equiv_moveleft :=
  match goal with
    | |- ?a = equiv_map ?w ?b =>
      apply @concat with (y := w (inverse w a));
        [ apply opposite, inverse_is_section | apply map ]
    | |- ?a = (inverse ?w) ?b =>
      apply @concat with (y := inverse w (w a));
        [ apply opposite, inverse_is_retraction | apply map ]
  end.

(** Equivalences are "injective on paths". *)

Lemma equiv_injective {A B : Type} (e : A <~> B) x y : (e x = e y) -> (x = y).
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

Definition free_path_space A := {xy : A * A & fst xy = snd xy}.

Definition free_path_source A : free_path_space A <~> A.
Proof.
  exists (fun p => fst (projT1 p)).
  intros x.
  eexists (existT _ (existT (fun (xy : A * A) => fst xy = snd xy) (x,x) (idpath x)) _).
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
  eexists (existT _ (existT (fun (xy : A * A) => fst xy = snd xy) (x,x) (idpath x)) _).
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
    data in [equiv] unless we add one more piece of coherence data.
    This is a homotopy version of the category-theoretic notion of
    "adjoint equivalence". *)

Structure adjoint_equiv A B := {
  adj_map : A -> B ;
  adj_adjoint : B -> A ;
  adj_is_section : (forall y, adj_map (adj_adjoint y) = y) ;
  adj_is_retraction : (forall x, adj_adjoint (adj_map x) = x) ;
  adj_triangle : (forall x, map adj_map (adj_is_retraction x) = adj_is_section (adj_map x))
}.

(** The following property of equivalences serves to show that an
   equivalence is an adjoint equivalences. It is a triangle identity but
   it does not look like one since we have inserted one of the
   homotopies. *)

Definition inverse_triangle {A B : Type} (e : A <~> B) x :
  (map e (inverse_is_retraction e x)) = (inverse_is_section e (e x)).
Proof.
  unfold inverse_is_retraction.
  hott_simpl.
  moveright_onleft.
Defined.

(** An equivalence is an adjoint equivalence and vice versa. *)

Definition equiv_to_adjoint {A B} (e : A <~> B) : adjoint_equiv A B :=
  {|
    adj_map := e ;
    adj_adjoint := e^-1 ;
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
    (fun x => f x = y)
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
  apply opposite, (homotopy_naturality_toid (f o g)).
  hott_simpl.
Defined.

Lemma adjoint_to_equiv_compute_map {A B} (e : adjoint_equiv A B) :
  equiv_map (adjoint_to_equiv e) = adj_map _ _ e.
Proof.
  destruct e; apply idpath.
Defined.

(** In fact, [equiv_to_adjoint] and [adjoint_to_equiv] are
   inverse equivalences, but proving this requires function
   extensionality.  See [FunextEquivalences.v]. *)

(** It is sometimes easier to define an adjoint equivalence than
   an equivalence, for example when we have a map which is homotopic
   to the identity. *)
Lemma equiv_pointwise_idmap A (f : A -> A) (p : forall x, f x = x) : A <~> A.
Proof.
  apply adjoint_to_equiv.
  refine {| adj_map := f; adj_adjoint := idmap A; adj_is_section := p; adj_is_retraction := p |}.
  apply htoid_well_pointed.
Defined.

(** The third notion of "equivalence" is that of a map which has an inverse up
   to homotopy but without the triangle identity (so it is a kind of
   "incoherent" adjoint equivalence. Let us call such a thing an h-equivalence
   or just [hequiv] for short. *)

Structure hequiv A B := {
  hequiv_map : A -> B ;
  hequiv_inverse : B -> A ;
  hequiv_section : (forall y, hequiv_map (hequiv_inverse y) = y) ;
  hequiv_retraction : (forall x, hequiv_inverse (hequiv_map x) = x)
}.

(** A central fact about adjoint equivalences is that any "incoherent"
   equivalence can be improved to an adjoint equivalence by changing one of the
   natural isomorphisms. We now prove a corresponding result in homotopy type
   theory. The proof is exactly the same as the usual proof for adjoint
   equivalences in 2-category theory. *)

Lemma map_retraction_section A B (f : A -> B) (g : B -> A)
  (h : forall x, f (g x) = x) (u v : B) (p : u = v) :
  map f (map g p) = h u @ p @ ! h v.
Proof.
  path_induction.
  hott_simpl.
Defined.

Definition adjointify {A B} : hequiv A B -> adjoint_equiv A B.
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
  exact (homotopy_naturality_fromid _ (fun y => ! is_section y) _).
Defined.

Lemma adjointify_compute_map {A B} (h : hequiv A B) :
  hequiv_map _ _ h = adj_map _ _ (adjointify h).
Proof.
  destruct h; apply idpath.
Defined.

(** Therefore, "any h-equivalence is an equivalence." *)

Definition hequiv_to_equiv {A B} : hequiv A B -> (A <~> B) :=
  adjoint_to_equiv o adjointify.

Lemma hequiv_to_equiv_compute_map {A B} (h : hequiv A B) :
  equiv_map (hequiv_to_equiv h) = hequiv_map _ _ h.
Proof.
  destruct h; apply idpath.
Defined.

(** All sorts of nice things follow from this theorem. *)

(** A lemma for showing that if something is an [hequiv] then
   it is an equivalence. *)

Definition is_equiv_from_hequiv {A B} {f : A -> B} (g : B -> A)
  (p : forall y, f (g y) = y) (q : forall x, g (f x) = x) : is_equiv f :=
  equiv_is_equiv (hequiv_to_equiv 
    {| hequiv_map := f ;
       hequiv_inverse := g ;
       hequiv_section := p ;
       hequiv_retraction := q |}).  

Definition equiv_from_hequiv {A B} (f : A -> B) (g : B -> A)
  (p : forall y, f (g y) = y) (q : forall x, g (f x) = x) : A <~> B :=
  hequiv_to_equiv 
    {| hequiv_map := f;
       hequiv_inverse := g;
       hequiv_section := p;
       hequiv_retraction := q |}.

(** The inverse of an equivalence is an equivalence. *)

Lemma equiv_inverse {A B} : (A <~> B) -> B <~> A.
Proof.
  intro e.
  destruct (equiv_to_adjoint e) as [f g is_section is_retraction triangle].
  apply (equiv_from_hequiv g f); auto.
Defined.

(* Rewrite rules for inverses. *)

Lemma equiv_inverse_is_inverse (A B  : Type) (f : A <~> B) : equiv_map (equiv_inverse f) = f^-1.
Proof.
  apply idpath.
Defined.

Hint Rewrite equiv_inverse_is_inverse : paths.

(** Anything homotopic to an equivalence is an equivalence. *)

Lemma equiv_homotopic {A B} (f : A -> B) (g : A <~> B) :
  (forall x, f x = g x) -> A <~> B.
Proof.
  intros p.
  apply (equiv_from_hequiv f (g^-1)).
  intro y.
  rewrite p.
  hott_simpl.
  intro x.
  equiv_moveright; auto.
Defined.

(** And the 2-out-of-3 property for equivalences. *)

Definition equiv_compose {A B C} (f : A <~> B) (g : B <~> C) : (A <~> C).
Proof.
  apply (equiv_from_hequiv (g o f) (f^-1 o g^-1)); intro; unfold compose.
  now equiv_moveright; apply inverse_is_section.
  now equiv_moveright; apply inverse_is_retraction.
Defined.

Lemma equiv_inverse_compose (A B C : Type) (f : A <~> B) (g : B <~> C) x :
  inverse (equiv_compose f g) x = f^-1 (g^-1 x).
Proof.
  auto.
Defined.

Hint Rewrite equiv_inverse_compose : paths.

Definition equiv_cancel_right {A B C} (f : A <~> B) (g : B -> C) :
  is_equiv (g o f) -> B <~> C.
Proof.
  intros H.
  pose (gof := {| equiv_map := g o f; equiv_is_equiv := H |}).
  apply (equiv_from_hequiv g (f o gof^-1)).
  intro y.
  expand_inverse_trg gof y.
  apply idpath.
  intro x.
  change (f (gof^-1 (g x)) = x).
  equiv_moveright; equiv_moveright.
  change (g x = g (f (f^-1 x))).
  hott_simpl.
Defined.

Definition equiv_cancel_left {A B C} (f : A -> B) (g : B <~> C) :
  is_equiv (g o f) -> A <~> B.
Proof.
  intros H.
  pose (gof := {| equiv_map := g o f; equiv_is_equiv := H |}).
  apply (equiv_from_hequiv f (gof^-1 o g)).
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

(** André Joyal suggested the following definition of equivalences and to call
   it "h-isomorphism" or [hiso] for short. This is even weaker than [hequiv] as
   we have a separate section and a retraction. *)

Structure is_hiso {A B} (f : A -> B) :=
  { hiso_section : B -> A ;
    hiso_is_section : (forall y, f (hiso_section y) = y) ;
    hiso_retraction : B -> A ;
    hiso_is_retraction : forall x, (hiso_retraction (f x) = x)
  }.

Implicit Arguments hiso_section [A B f].
Implicit Arguments hiso_is_section [A B f].
Implicit Arguments hiso_retraction [A B f].
Implicit Arguments hiso_is_retraction [A B f].

Definition is_hiso_from_is_equiv {A B} (f : A -> B) : is_equiv f -> is_hiso f.
Proof.
  intro feq.
  pose (e := {| equiv_map := f; equiv_is_equiv := feq |}).
  rewrite (idpath _ : f = equiv_map e).
  refine {| hiso_section := e^-1; hiso_retraction := e^-1|}.
  apply inverse_is_section.
  apply inverse_is_retraction.
Defined.

Structure hiso A B :=
  { hiso_map :> A -> B ;
    hiso_is_hiso :> is_hiso hiso_map
  }.

(** Of course, an honest equivalence is an h-isomorphism. *)
Definition hiso_from_equiv {A B} (e : A <~> B) : hiso A B :=
  {| hiso_map := equiv_map e ;
     hiso_is_hiso := 
     {| hiso_section := equiv_inverse e ;
        hiso_is_section := inverse_is_section e ;
        hiso_retraction := equiv_inverse e ;
        hiso_is_retraction := inverse_is_retraction e
     |}
  |}.

(** But also an h-isomorphism is an equivalence. *)
Definition hequiv_from_hiso {A B} : hiso A B -> hequiv A B.
Proof.
  intros [f [g G h H]].
  refine {| hequiv_map := f ; hequiv_inverse := h |}.
  intro y.
  path_via (f (g y)).
  apply map.
  path_via (h (f (g y))).
  (* Coq 8.3 wants this but 8.4 does not, so we try it. *)
  try (apply map, opposite, G).
  assumption.
Defined.

Lemma hequiv_from_hiso_compute_map {A B} (h : hiso A B) :
  hequiv_map _ _ (hequiv_from_hiso h) = hiso_map _ _ h.
Proof.
  destruct h as [? [? ? ?]].
  apply idpath.
Defined.

Definition equiv_from_hiso {A B} (f : hiso A B) : A <~> B :=
  hequiv_to_equiv (hequiv_from_hiso f).

Lemma equiv_from_hiso_compute_map {A B} (f : hiso A B) :
  equiv_map (equiv_from_hiso f) = hiso_map _ _ f.
Proof.
  destruct f as [? [? ? ?]].
  apply idpath.
Defined.

Definition is_equiv_from_is_hiso {A B} (f : A -> B) : is_hiso f -> is_equiv f.
Proof.
  intro fhiso.
  pose (h := {| hiso_map := f; hiso_is_hiso := fhiso |}).
  pose (e := equiv_from_hiso h).
  (** We would like to apply [equiv_is_equiv e], but Coq wants us to rewrite first. *)
  rewrite (idpath _ : f = hiso_map _ _ h).
  rewrite <- (equiv_from_hiso_compute_map h).
  apply (equiv_is_equiv e).
Defined.

(** Of course, the harder part is showing that being an h-isomorphism is a
   proposition, and therefore equivalent to being an equivalence. This also
   requires function extensionality; see [FunextEquivalences.v]. *)
