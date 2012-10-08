Require Export Fibrations Contractible Equivalences.
Require Export UsefulEquivalences FiberEquivalences.

(** In type theory [f] and [g] are extensionally equal if they give equal values.
   In HoTT such an equality might be called "pointwise homotopy" or just "homotopy". *)

Definition ext_dep_eq {X} {P : X -> Type} (f g : forall x, P x) := forall x : X, f x = g x.

(** A notation for extensional equality. *)

Notation "f == g" := (ext_dep_eq f g) (at level 50).

(** The simplest notion we call "naive functional extensionality".
   This is what a type theorist would probably write down when
   thinking of types as sets and identity types as equalities: it says
   that if two functions are equal pointwise, then they are equal.  It
   comes in both ordinary and dependent versions. *)

Definition funext_statement (X Y : Type) :=
  forall (f g : X -> Y), f == g -> f = g.

Definition funext_dep_statement {X : Type} (P : fibration X) :=
  forall (f g : section P), f == g -> (f = g).

(** However, there are clearly going to be problems with this in the
   homotopy world, since "being equal" is not merely a property, but
   being equipped with a path is structure.  We should expect some
   sort of coherence or canonicity of the path from f to g relating it
   to the pointwise homotopy we started with.
   
   A natural way to state a "homotopically good" notion of function
   extensionality is to observe that there is a canonical map in the
   other direction, taking paths between functions to pointwise
   homotopies.  We can thus just ask for that map to be an
   equivalence.  We call this "strong functional extensionality."  Of
   course, it also comes in ordinary and dependent versions.  *)

Definition strong_funext_statement (X Y : Type) :=
  forall (f g : X -> Y), is_equiv (@happly X Y f g).

Definition strong_funext_dep_statement {X : Type} (P : fibration X) :=
  forall (f g : section P), is_equiv (@happly_dep X P f g).

(** From the assumption that [happly_dep] is an equivalence we build
   the corresponding equivalence. *)

Definition happly_dep_equiv
  (X : Type) (P : fibration X) (f g : section P) (H : strong_funext_dep_statement P) :
  f = g <~> f == g.
Proof.
  exists (@happly_dep X P f g).
  apply H.
Defined.
  
(** Of course, strong functional extensionality implies naive
   functional extensionality, along with a computation rule. *)

Theorem strong_to_naive_funext:
  (forall X Y, strong_funext_statement X Y) -> (forall X P, funext_statement X P).
Proof.
  intros H X Y f g.
  exact ({| equiv_map := @happly X Y f g; equiv_is_equiv := H X Y f g|} ^-1).
Defined.

Theorem strong_funext_compute
  (strong_funext : forall X Y, strong_funext_statement X Y)
  (X Y : Type) (f g : X -> Y) (p : f == g) (x : X) :
  happly (strong_to_naive_funext strong_funext X Y f g p) x = p x.
Proof.
  intros.
  unfold strong_to_naive_funext.
  unfold inverse.
  simpl.
  exact (happly_dep (pr2 (pr1 (strong_funext X Y f g p))) x).
Defined.

Theorem strong_to_naive_funext_dep {X} (P : fibration X):
  strong_funext_dep_statement P -> funext_dep_statement P.
Proof.
  intros H f g.  
  exact ({| equiv_map := @happly_dep X P f g ; equiv_is_equiv := H f g |} ^-1).
Defined.

Theorem strong_funext_dep_compute {X} (P : fibration X)
  (strong_funext_dep : strong_funext_dep_statement P)
  (f g : section P) (p : f == g) (x : X) :
  happly_dep (strong_to_naive_funext_dep P strong_funext_dep f g p) x = p x.
Proof.
  intros.
  unfold strong_to_naive_funext_dep, inverse.
  simpl.
  exact (happly_dep (pr2 (pr1 (strong_funext_dep f g p))) x).
Defined.

(** We also observe that for both strong and naive functional
   extensionality, the dependent version implies the non-dependent
   version.  *)

Theorem strong_funext_dep_to_nondep :
  (forall X (P : fibration X), strong_funext_dep_statement P) -> forall X Y, strong_funext_statement X Y.
Proof.
  intros H X Y f g. 
  exact (H X (fun x => Y) f g).
Defined.

Theorem funext_dep_to_nondep :
  (forall X (P : fibration X), funext_dep_statement P) -> forall X Y, funext_statement X Y.
Proof.
  intros H X Y f g.
  exact (H X (fun x => Y) f g).
Defined.

(** Can we go backwards, getting to strong functional extensionality
   from naive functional extensionality?  At first the prospects don't
   look good; naive functional extensionality gives us a map going
   backwards, but it doesn't assert anything *about* that map, so it
   seems unlikely that it would be an inverse to [happly].

   However, it turns out that we can go backwards; the key is to first
   forget down to an even weaker axiom, called "weak functional
   extensionality".  This has only one version, which states that the
   dependent product of a family of (continuously) contractible types
   is contractible.  *)

Definition weak_funext_statement {X : Type} (P : fibration X) :=
    (forall x : X, is_contr (P x)) -> is_contr (section P).

(** It is easy to see that naive dependent functional extensionality
   implies weak functional extensionality. *)

Theorem funext_dep_to_weak {X : Type} (P : fibration X):
  funext_dep_statement P -> weak_funext_statement P.
Proof.
  intros H C.
  exists (fun x => pr1 (C x)).
  intro; apply H.
  intro; apply contr_path, C.
Defined.

(** Another (very) weak type of functional extensionality is the
   (propositional) eta rule, which is implied by naive functional
   extensionality. *)

Definition eta {A B} (f : A -> B) :=
  fun x => f x.

(** If we remove the type anontation [Type] in the definition below,
   Coq puts [eta_statement] in [Prop]. Why? This is worrisome, as other
   things might end up in [Prop] instead of [Type] without us noticing. *)

Definition eta_statement (A B : Type) : Type :=
  forall (f : A -> B), eta f = f.

Theorem naive_funext_implies_eta (A B : Type) :
  funext_statement A B -> eta_statement A B.
Proof.
  intros funext f.
  apply funext.
  intro; apply idpath.
Defined.

(** Here is the dependent version. *)

Definition eta_dep {A} {P : A -> Type} (f : section P) :=
  fun x => f x.

Definition eta_dep_statement {A : Type} (P : fibration A) :=
  forall (f : section P), eta_dep f = f.

Theorem naive_funext_dep_implies_eta {A : Type} (P : fibration A) :
  funext_dep_statement P -> eta_dep_statement P.
Proof.
  intros funext_dep f.
  apply funext_dep.
  intro; apply idpath.
Defined.

(** A "mini" form of the desired implication (naive => strong) is that
   the eta rule does implies directly that the eta map is an
   equivalence. *)

Lemma eta_equiv (A B : Type) : eta_statement A B -> (A -> B) <~> (A -> B).
Proof.
  intros H.
  apply equiv_pointwise_idmap with (f := @eta A B).
  assumption.
Defined.

(** And the dependent version. *)

Lemma eta_dep_equiv {A : Type} (P : fibration A) :
  eta_dep_statement P -> (section P <~> section P).
Proof.
  intro H.
  apply equiv_pointwise_idmap with (f := @eta_dep A P).
  apply H.
Defined.

Section AxiomOfChoiceEquiv'.

  (** The axiom of choice says that a relation is total iff it has a choice function,
     and there is a type-theoretic version of it, which we record first. 
     
     We work with a fully dependent version of the total relation. *)

  Variable X : Type. (* the domain of the relation *)
  Variable P : fibration X. (* the codomain, which is dependent *)
  Variable Q : forall x, fibration (P x). (* the relation, which is dependent *)

  (** The usual axiom of choice for the total relation [Q]. *)
 
  Definition ac : (forall x, {y : P x & Q x y}) -> {h : section P & forall x, Q x (h x)}.
  Proof.
    intro f.
    exists (fun x => pr1 (f x)).
    intro x.
    exact (pr2 (f x)).
  Defined.

  (** And vice-versa. *)

  Definition acinv : {h : section P & forall x, Q x (h x)} -> forall x, {y : P x & Q x y}.
  Proof.
    intros [h H x].
    exists (h x).
    apply H.
  Defined.

  (** A homotopic version of the axiom of choice ought to state that [ac] is
     an equivalence. We need further assumption to exhibit this fact.
     Firstly, we assume the eta rule throghout. *)

  Hypothesis eta_dep_rule : forall Y (S : fibration Y), eta_dep_statement S.

  (** At this point we are able to provide a version of equivalence, called
     [ac_equiv'] below, in which we assume the weakest form of extensionality
     and an extra condition on [Q], namely that [Q] is single-valued in the
     sense that for every [x] any two elements of the space [{y : P x & Q x y}] 
     are connected by a path. This requirement is equivalent to
     the space being an h-prop or h-level 1 (see [HLevel]), and so [ac_equiv']
     is a form of _unuque_ choice.

     We bother proving [ac_equiv'] because it is used in the proof that weak
     extensionality implies strong extensionality. And once we have that result,
     we will be able to show a second, desired version [ac_equiv] without any
     conditions [Q].
  *)

  Definition ac_equiv'
    (total_Q_prop : forall x, forall u v : {y : P x & Q x y}, u = v)
    (weak_funext : forall Y (S : fibration Y), weak_funext_statement S) :
    (forall x, {y : P x & Q x y}) <~> {h : section P & forall x, Q x (h x)}.
  Proof.
    apply (equiv_from_hequiv ac acinv).
    intros [h H].
    unfold ac; simpl.
    fold (eta_dep H).
    rewrite (eta_dep_rule _ _ H).
    fold (eta_dep h).
    (* The obvious thing here would be to rewrite with [E X P h] but that gives
       the dreaded "Error: Abstracting over the term ... which is ill-typed".
       Instead we are going to be a bit clever, as Mike Shulman put it. *)
    (* First, the left-hand side is the image of a map [f] which is an
       equivalence because it is the pullback of an equivalence. *)
    pose (R := (fun (g : section P) => forall x, Q x (g x))).
    pose (e := eta_dep_equiv P (eta_dep_rule _ P)).
    pose (f := pullback_total_equiv R e).
    path_via (f (h; H)).
    (* The following step is not needed in Coq 8.4 but is needed in 8.3 so we try it *)
    (* To show that an equivalence is homotopic to the identity, it
       suffices to show that is idempotent, which is easy. *)
    try now apply equiv_injective with f.
    (* The other half of the proof is easier than it looks because
       we get to apply weak extensionality. *)
    intro h.
    apply contr_path.
    apply weak_funext.
    intro x.
    exists (h x).
    (* And this is precisely our assumption on [Q]. *)
    intro; apply total_Q_prop.
  Defined.

  (** Continued below in section [AxiomOfChoice]... *)
End AxiomOfChoiceEquiv'.

Section WeakToStrongFunextDep.

  (** As an intermezzo of treatment of the axiom of choice we show the
     non-obvious fact that weak functional extensionality implies *strong*
     (dependent) functional extensionality, at least in the presence of the
     dependent eta rule. *)

  Hypothesis eta_dep_rule : forall X (P : fibration X), eta_dep_statement P.

  (** Assume a fibration [P] over [X]. *)
  Variable X : Type.
  Variable P : fibration X.

  (** We want to show that [weak_funext_statement P] implies
     [strong_funext_dep_statement P], which states that [happly_dep] is an
     equivalence. We fix a section [f] over [P] and view [happly_dep f] as a map
     over [section P] between the fibrations [Q] and [R], defined below. *)

  Variable f : section P.
  
  Let Q := (fun h => f = h) : fibration (section P).
  Let R := (fun h => f == h) : fibration (section P).

  (** We need to show that [happly_dep f] is fiber-wise equivalence. It is
     sufficient to show that the induced total map [total Q] -> [total R] is an
     equivalence, which it is because [total Q] and [total R] are contractible.
     The only tricky bit is to show that [total R] is contractible. *)

  Lemma is_contr_total_Q : is_contr (total Q).
  Proof.
    exists ((f; idpath _) : total Q).
    intros [h p].
    induction p; apply idpath.
  Defined.

  Hypothesis weak_funext : forall X (S : fibration X), weak_funext_statement S.

  Lemma is_contr_total_R : is_contr (total R).
  Proof.
    (* If we knew that our total space [total R] is equivalent to
       a space of sections, we could bring in [weak_funext]. Let us
       unfold a bit to see what is going on. *)
    unfold R, total, ext_dep_eq.
    (* [total R] is exactly of the form needed for [ac_equiv'] to kick in! *)
    apply contr_equiv_contr with (A := forall x, {y : P x & f x = y}).
    apply ac_equiv'; auto.
    (* The rest is a triviality. *)
    intros x u v. apply contr_path, pathspace_contr'.
    apply weak_funext.
    intro; apply pathspace_contr'.
  Defined.

  (** Now we can prove strong extensionality. *)

  Theorem weak_to_strong_funext_dep' (g : section P) : is_equiv (@happly_dep X P f g).
  Proof.
    apply (fiber_is_equiv ((@happly_dep X P f) : forall h, Q h -> R h)).
    apply contr_contr_is_equiv.
    apply is_contr_total_Q.
    apply is_contr_total_R.
  Defined.
End WeakToStrongFunextDep.

(** Let us record the results in a more compact form. *)
Theorem weak_to_strong_funext_dep (X : Type) (P : fibration X)
    (weak_funext: forall X (P : fibration X), weak_funext_statement P)
    (eta_dep_rule : forall X (P : fibration X), eta_dep_statement P) :
    strong_funext_dep_statement P.
Proof.
  intros H f g.
  apply weak_to_strong_funext_dep'; auto.
Defined.

Section AxiomOfChoiceEquiv.
  (** We may now continue with the strong version of the axiom of choice.
     Assuming the eta rule and weak extensionality suffices to show that
     [ac] is an equivalence. *)

  Hypothesis eta_dep_rule : forall Y (S : fibration Y), eta_dep_statement S.

  Hypothesis weak_funext: forall Y (S : fibration Y), weak_funext_statement S.

  Variable X : Type. (* the domain of the relation *)
  Variable P : fibration X. (* the codomain, which is dependent *)
  Variable Q : forall x, fibration (P x). (* the relation, which is dependent *)

  Definition ac_equiv:
    (forall x, {y : P x & Q x y}) <~> {h : section P & forall x, Q x (h x)}.
  Proof.
    (* We first derive strong extensionality. *)
    pose (strong_funext_dep := fun Y (S : fibration Y) =>
      weak_to_strong_funext_dep Y S weak_funext eta_dep_rule).
    pose (funext_dep :=
      fun Y (S : fibration Y) => strong_to_naive_funext_dep S (strong_funext_dep Y S)).
    apply (equiv_from_hequiv (ac X P Q) (acinv X P Q)).
    intros [h H].
    unfold ac; simpl.
    fold (eta_dep H).
    rewrite (eta_dep_rule _ _ H).
    fold (eta_dep h).
    (* So far the proof is the same as that of [ac_equiv'] but now we deviate
       from it. Strong extensionality gives us a path [p : eta_dep h = h] in
       the base with which we can reduce the problem to having a path in the
       fiber. *)
    pose (p := funext_dep X P (eta_dep h) h (fun a => idpath (h a))).
    apply @total_path with p; simpl.
    (* We switch from a path to a homotopy, it's easier. *)
    apply funext_dep; intro x.
    (* Since [p] was constructed using [strong_to_naive_funext_dep] we should
       aim at using [strong_funext_dep_compute]. But this means we need [p]
       as an argument of [happly_dep]. So we juggle a bit. *)
    (* Our path factors through a suitable [trans_map]. *)
    apply (concat (trans_map p (fun s' (r': forall x, Q x (s' x)) => r' x) H)).
    (* Ask Mike Shulman how he thought of the next step, but I think it
       goes like this: we really want [happly_dep p] to appear, so we stick
       it in and keep fiddling until it works. *)
    path_via (happly_dep p x # H x).
    (* The uninteresting subgoal is disposed of with [trans_map]. *)
    now (apply @map_trans with (f := fun h : forall x' : X, P x' => h x)).
    (* And the interesting one with [strong_funext_dep_compute]. *)
    now rewrite (strong_funext_dep_compute P (strong_funext_dep X P)) with
      (f := eta_dep h) (g := h) (p := fun x' : X => idpath (h x')).
    (* The other half of the proof is much easier. *)
    intros f.
    apply funext_dep.
    intro x.
    unfold ac, acinv; destruct (f x).
    apply idpath.
  Defined.
End AxiomOfChoiceEquiv.
