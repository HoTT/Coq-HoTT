Require Import ssreflect ssrfun.
Require Import Paths Fibrations Contractible.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import PathNotations.

Open Scope path_scope.

(* assia : it proves convenient to import also Cyril's alternate constructors *)
(* of inhabitants of a hfiber *)

Definition hfiber {A B} (f : A -> B) (y : B) := {x : A & f x = y}.

Definition hfiber_def {A B} (f : A -> B) (y : B) 
           (x : A) (Hx : f x = y) : hfiber f y := exist (fun x => f x = _) _ Hx.

(* nice constructors for elements of the preimage: *)

(* If (Hx : f x = y), the element of the fiber (x, Hx) *)
Notation Hfiber f Hx := (@hfiber_def _ _ f _ _ Hx).

(* The element (f x, 1) of the fiber above f x *)
Notation in_hfiber f x := (@hfiber_def _ _ f _ x (erefl _)).

Lemma hfiberP {A B} (f : A -> B) (y : B) (x : hfiber f y) : f (projT1 x) = y.
Proof. by case: x. Qed.

(* We diverge from the original Equivalence.v file by defining is_equiv *)
(* what was previously called adjoint_equiv. We bet it should prove more*)
(* efficient as an interface because it exposes the inverse of the *)
(* equivalence as an element of the signature, which we can provide *)
(* by hand or built generically at our convenience. *)

(* Infrastructure is really absent for the moment...*)
Record equiv A B := Equiv {
  equiv_fun :> A -> B ;
  equiv_adjoint : B -> A ;
  equiv_section : cancel equiv_adjoint equiv_fun; 
  equiv_retraction : cancel equiv_fun equiv_adjoint;
  equiv_coh : forall x, equiv_section (equiv_fun x) = resp equiv_fun (equiv_retraction x)
}.

Delimit Scope equiv_scope with equiv.

Notation "A <~> B" := (equiv A B) (at level 85) : equiv_scope.

Local Open Scope equiv_scope.

Definition equiv_clone A B := 
  fun (f : A -> B) (ef : A <~> B) & (f = ef :> (A -> B)) => ef.

Notation "[ 'equiv' 'of' f ]" := (@equiv_clone _ _ f _ (erefl _))
  (at level 0, format "[ 'equiv'  'of'  f ]") : form_scope.


(* Warning : in ssreflect libs, bijective means the constructive existence of a *)
(* function g such that cancel f g and cancel g f. Otherwise said, *)
(* bijective is what is called hequiv in the original Equivalence.v file. *)
(* Hence the folloing lemma bij_is_equiv is the previous adjointify. *)

(* We first define how to correct a cancel operation so that it satifies the*)
(* coherence condition wrt the application of functions on paths *)
Definition adjointify {A B}(f : A -> B) g (fK : cancel f g)(gK : cancel g f) := 
   fun a => (resp g (resp f (fK a))^-1) * (resp g (gK (f a))) * (fK a).

(* Definition alt_adjointify {A B}(f : A -> B) g (fK : cancel f g)(gK : cancel g f) :=  *)
(*   fun a => (g`_* (gK (f a))) ^ fK. *)

(* Lemma alt_adjointifyP A B (f : A -> B) g  *)
(*   (fK : cancel f g)(gK : cancel g f)(fK' := alt_adjointify fK gK) a : *)
(*    gK (f a) = f`_* (fK' a). *)
(* Proof. *)
(* rewrite /fK' /alt_adjointify. *)

(* rewrite -resp_eqp. *)

(* pose gKV : id =1 f \o g :=  (fun x => (gK x)^-1). *)
(*  rewrite  !resppM !(conj_canV gKV) -(conjpM gKV). conjpE mulpK mulpVK invpK. *)
(* Qed. *)

Lemma adjointifyP A B (f : A -> B) g 
  (fK : cancel f g)(gK : cancel g f)(fK' := adjointify fK gK) a :
   gK (f a) = f`_* (fK' a).
Proof.
pose gKV : id =1 f \o g :=  (fun x => (gK x)^-1).
 rewrite  !resppM.
About conj_canV.
rewrite !(conj_canV gKV).
rewrite -(conjpM gKV). 
rewrite conjpE.
rewrite mulpK.
rewrite mulpVK.
rewrite invpK.
Qed.

(* A function whose fibers are all contractible *)
(* This was the main definition taken in the original Equivalence.v *)
(* I should probably change its name now *)
Definition is_equiv {A B} (e : A -> B) := forall y : B, is_contr (hfiber e y).

Section EquivTheory.

Variables (A B : Type).

(* An equivalence in the main sens is an equivalence in wrt to the contractible
   fibers definitions.*)
Lemma equiv_is_equiv (f : A <~> B) : is_equiv f.
Proof.
move=> b; exists (Hfiber f (equiv_section f b)).
case=> a; case: _ / => {b}; rewrite (equiv_coh f).
by case (equiv_retraction f a).
Qed.

(* And now we prove that we can get an equivalence from a bijection *)
Definition can2_equiv (h1 : A -> B)(h2 : B -> A)(h1K : cancel h1 h2)
  (h2K : cancel h2 h1) : A <~> B := Equiv (adjointifyP h1K h2K).

End EquivTheory.

(* Homotopy equivalences are a central concept in homotopy type theory.
   Before we define equivalences, let us consider when [A] and [B]
   should be considered "the same".

   The first option is to require existence of [f : A -> B] and [g : B -> A]
   which are inverses of each other, up to homotopy. Homotopically speaking, we
   should also require a certain condition which is remniscent of the triangle
   identities for adjunctions in category theory. Thus we call this notion an
   adjoint equivalence.

   The second option is to use Vladimir Voevodsky's definition of an
   equivalence as a map whose homotopy fibers are contractible.

   An interesting third options was suggested by André Joyal: a map [f] which
   has separate left and right homotopy inverses. This too turns out to be
   reasonable.

   We shall start with the seconnd option. We will then show how the other
   two are related to it. *)

(** An equivalence is a map whose homotopy fibers are contractible. *)


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
  exists id.
  intros x.
  exists (existT (fun x' => x' = x) x 1).
  intros [x' p].
  case p.
  reflexivity.
Qed.

(** We first define the inverse map and only show that it is an
   equivalence later on, when we are ready to do it. *)
(* assia : why a Let? *)
Let inverse {A B : Type} (e : A <~> B) : (B -> A) :=
  fun y => pr1 (pr1 (equiv_is_equiv e y)).

(** printing ^-1 $^{-1}$ *)
(* assia : I must change this notation which conflicts with mine in Paths.v*)
(* This one is probably not a good one since we see too many stars now in *)
(* our expresions *)
(* assia : I lower the level so that we do not need to write (e^* ) *) 
Notation "e ^*" := (inverse e) (at level 3).

(** The extracted map in the inverse direction is actually an inverse
   (up to homotopy, of course). *)

Definition inverse_is_section {A B : Type} (e : A <~> B) (y : B) : e (e^* y) = y :=
  pr2 (pr1 ((equiv_is_equiv e) y)).

(* assia : why do we define section and not retraction ?*)
Definition inverse_is_retraction {A B : Type} (e : A <~> B) : (fun x => e^* (e x)) =1 id :=
  fun x => (base_path (pr2 (equiv_is_equiv e (e x)) (x ; 1)))^-1.

(* assia : here we see an instance of the conjugation operation defined in Paths.v *)
Lemma map_equiv_o_inverse {A B : Type} (e : A <~> B) (x y : A) (p : x = y) :
  resp e^* (resp e p) = inverse_is_retraction e x * p * (inverse_is_retraction e y)^-1.
Proof.
  set f := inverse_is_retraction e.
  apply: mulpRLr; apply: mulpRLl; rewrite invpK -(conjpE f); exact: can_respp.
Qed.

(* assia : same proof as above. *)
Lemma map_inverse_o_equiv {A B : Type} (e : A <~> B) (u v : B) (p : u = v) :
  resp e (resp e^* p) = inverse_is_section e u * p * (inverse_is_section e v)^-1.
Proof.
  set f := inverse_is_section e.
  apply: mulpRLr; apply: mulpRLl; rewrite invpK -(conjpE f); exact: can_respp.
Qed.

(** Equivalences are "injective on paths". *)

Lemma equiv_injective {A B : Type} (e : A <~> B) x y : (e x = e y) -> (x = y).
Proof. move/(resp e^*); rewrite !inverse_is_retraction; exact. Qed.

(* assia : from a proof p that f y = x we construct a point (y, p) in the hfiber f x*)

Definition mk_hfiber A B (f : A -> B) x y (p : f y = x) : hfiber f x := 
  existT (fun z => f z = x) _ p.

(** Anything contractible is equivalent to the unit type. *)


Lemma contr_equiv_unit (A : Type) : is_contr A -> (A <~> unit).
Proof.
case=> x h. 
pose f (x : A) := tt. 
exists f. 
case.
have px : f x = tt by [].
exists (mk_hfiber px) => u.
case u => y.
rewrite (h y) => i.
rewrite (contr_path2 px i) //.
exact: unit_contr.
Qed.

(** And anything equivalent to a contractible type is
   contractible. *)

Lemma contr_equiv_contr (A B : Type) : A <~> B -> is_contr A -> is_contr B.
Proof.
move=> f [x p].
exists (f x) => y.
rewrite -(inverse_is_section f y) (p (f^* y)).
reflexivity.
Qed.

(** The free path space of a type is equivalent to the type itself. *)

Definition free_path_space A := {xy : A * A & fst xy = snd xy}.

(* assia : I was unable to not prove the symmetric  A <~> free_path_space A *)
(* directly... This direction is definitively easier because we reason at a lower*)
(* level. The sequel seems to indicate that the symmetry of <~> is not that *)
(* straightforward *)
Lemma free_path_source A : free_path_space A <~> A.
pose f (x : free_path_space A) : A := (projT1 x).1.
exists f => a.
have p : f ((a, a); 1) = a by [].
exists (mk_hfiber p); rewrite /f /mk_hfiber /= in p *.
case => [] [[a1 a2]] /= ea12.
case p => /= {p}. 
case ea12 => {ea12}. 
move=> p0; case p0.
reflexivity.
Qed.


(* With qed this second proof becomes useless since we have opacified the body*)
Definition free_path_target A : free_path_space A <~> A.
Proof.
  exists (fun p => snd (projT1 p)).
  intros x.
  eexists (existT _ (existT (fun (xy : A * A) => fst xy = snd xy) (x,x) 1) _).
  intros [[[u v] p] q].
  simpl in * |- *.
  induction q as [a].
  induction p as [b].
  apply identity_refl.
Qed.


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
  adj_triangle : (forall x, resp adj_map (adj_is_retraction x) = adj_is_section (adj_map x))
}.

(** The following property of equivalences serves to show that an
   equivalence is an adjoint equivalences. It is a triangle identity but
   it does not look like one since we have inserted one of the
   homotopies. *)

Lemma inverse_triangle {A B : Type} (e : A <~> B) x :
  (resp e (inverse_is_retraction e x)) = (inverse_is_section e (e x)).
Proof.
rewrite /inverse_is_section.
rewrite /inverse_is_retraction.
rewrite /base_path.
case: e => f pf /=.

  unfold inverse_is_retraction.
  hott_simpl.
  apply (concat (!idpath_right_unit _)).
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
