Require Export Fibrations Contractible Equivalences.
Require Export UsefulEquivalences FiberEquivalences.

(** In type theory [f] and [g] are extensionally equal if they give equal values.
   In HoTT such an equality might be called "pointwise homotopy" or just "homotopy". *)

Definition ext_dep_eq {X} {P : X -> Type} (f g : forall x, P x) := forall x : X, f x ~~> g x.

(** A notation for extensional equality. *)

Notation "f === g" := (ext_dep_eq f g) (at level 50).

(** The simplest notion we call "naive functional extensionality".
   This is what a type theorist would probably write down when
   thinking of types as sets and identity types as equalities: it says
   that if two functions are equal pointwise, then they are equal.  It
   comes in both ordinary and dependent versions. *)

Definition funext_statement (X Y : Type) :=
  forall (f g : X -> Y), f === g -> f ~~> g.

Definition funext_dep_statement {X : Type} (P : fibration X) :=
  forall (f g : section P), f === g -> (f ~~> g).

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
  f ~~> g <~> f === g.
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
  (X Y : Type) (f g : X -> Y) (p : f === g) (x : X) :
  happly (strong_to_naive_funext strong_funext X Y f g p) x ~~> p x.
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
  (f g : section P) (p : f === g) (x : X) :
  happly_dep (strong_to_naive_funext_dep P strong_funext_dep f g p) x ~~> p x.
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
  forall (f : A -> B), eta f ~~> f.

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
  forall (f : section P), eta_dep f ~~> f.

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

Lemma eta_dep_is_equiv {A : Type} (P : fibration A) :
  eta_dep_statement P -> (section P <~> section P).
Proof.
  intro H.
  apply equiv_pointwise_idmap with (f := @eta_dep A P).
  apply H.
Defined.

Section WeakToStrongFunextDep.
   (** Less trivial is the fact that weak functional extensionality
      implies *strong* (dependent) functional extensionality, at least in
      the presence of the dependent eta rule. *)

  (** Assume a fibration which satisfies the dependent eta rule. *)
  Variable X : Type.
  Variable P : fibration X.

  Hypothesis Heta : eta_dep_statement P.

  (** We want to show that [weak_funext_statement P] implies
     [strong_funext_dep_statement P], which states that [happly_dep]
     is an equivalence. *)
(*
  Definition paths_from (f : section P) := {g : section P & f ~~> g}.

  Definition homotopies_from (f : section P) := {g : section P & f === g}.

  (* A first observation is that [paths_from f] and [homotopies_from g] are
     both contractible. *)
  
  Lemma paths_from_is_contr (f : section P) : is_contr (paths_from f).
  Proof.
    apply pathspace_contr'.
  Defined.

  Hypothesis H : forall X (P : fibration X), weak_funext_statement P. 

  Lemma homotopies_from_is_contr (f : section P) : is_contr (homotopies_from f).
  Proof.
    unfold homotopies_from.
    unfold is_contr, homotopies_from.
    pose (p := fun x => idpath (f x)).
    exists (f; p).
    intros [g q].
    apply opposite.


*)

  Variable f : section P.
  
  Let Q := (fun h => f ~~> h) : fibration (section P).
  Let R := (fun h => f === h) : fibration (section P).
  
  Hypothesis H : forall X (P : fibration X), weak_funext_statement P.
  
  Lemma foo g : Q g <~> R g.
  Proof.
    set (fibhap := (@happly_dep X P f) : forall h, Q h -> R h).
    apply fiber_equiv with (g := fibhap).
    apply contr_contr_is_equiv.
    (* This one is easy. *)
    apply pathspace_contr'.
    (* The other one is harder. *)
    set (altAR := forall x, { y : P x & f x ~~> y }).
    apply contr_equiv_contr with (A := altAR).
    (* It is easy to see that [altAR] is contractible. *)
    2: apply H; intro; apply pathspace_contr'.
    (* The map between these spaces is obvious. *)
    pose (k := (fun d => existT R (fun x => pr1 (d x)) (fun x => pr2 (d x))) : altAR -> total R).
    pose (kinv := (fun (e : total R)  => (fun x => (pr1 e x ; pr2 e x))) : total R -> altAR).
    apply (equiv_from_hiso k kinv).
    intros [h p].
    unfold k, kinv; simpl.
    unfold eta_dep_statement, eta_dep in Heta.
    apply @total_path with (p := Heta h).
    apply contr_path; simpl.
    exists p.
    intro q.
    apply contr_path.

  Theorem weak_to_strong_funext_dep : 
    (forall X (P : fibration X), weak_funext_statement P) -> strong_funext_dep_statement P.
  Proof.
    intros H f g.
    (* The idea is that [happly_dep] is one fiber map in a map of
       fibrations, whose total spaces are contractible and hence
       equivalent.  *)
    pose (Q := (fun h => f ~~> h) : fibration (section P)).
    pose (R := (fun h => f === h) : fibration (section P)).
    set (fibhap := (@happly_dep X P f) : forall h, Q h -> R h).
    apply (fiber_is_equiv fibhap).
    apply @contr_contr_equiv with (A := total Q) (B := total R).
    (* Contractibility of this space is easy. *)
    apply pathspace_contr'.
    (* This one is trickier; we show it is contractible by showing it
       equivalent to the total space of a different fibration. *)
    set (altAR := forall x, { y : P x & f x ~~> y }).
    apply contr_equiv_contr with (A := altAR).
    (* It is easy to see that [altAR] is contractible. *)
    2: apply H; intro; apply pathspace_contr'.
    (* The map between these spaces is obvious. *)
    pose (k := (fun d => existT R (fun x => pr1 (d x)) (fun x => pr2 (d x))) : altAR -> total R).
    pose (kinv := (fun (e : total R)  => (fun x => (pr1 e x ; pr2 e x))) : total R -> altAR).
    apply (equiv_from_hiso k kinv).
  eapply hequiv_is_equiv.
  (* as is its inverse. *)
  instantiate (1 := fun e => (fun x => (pr1 e x ; pr2 e x))).
  unfold k. intro y.
  simpl.
  (* Now we have to be a bit clever.  The LHS here is the image of [z]
     under the following endofunction. *)
  set (W := fun z:sigT R => existT R (fun x:X => pr1 z x) (fun x:X => pr2 z x)).
  path_via (W y).
  (* So if we can show that [W] is homotopic to the identity, we'll be
     done.  We do this by showing that it is (1) idempotent and (2) an
     equivalence. *)
  assert (W_idempotent : forall z, W (W z) ~~> W z); auto.
  assert (W_equiv : is_equiv W).
  (* We show that [W] is an equivalence by showing it is homotopic to
     the following slightly different map. *)
  set (W' := fun z:sigT R => let (h,q) := z in existT R (fun x => h x) q).
  apply @equiv_homotopic with (g := W').
  intro z. destruct z.
  unfold W, W'.
  apply @total_path with (p := idpath (fun x0 => x x0)).
  simpl.
  apply Heta.
  (* But [W'] is an equivalence because it is the pullback of the
     equivalence [eta_dep] along a fibration. *)
  change (is_equiv (pullback_total_equiv R (eta_dep_equiv Heta X P))).
  apply pullback_total_is_equiv.
  (* Now any idempotent equivalence is homotopic to the identity. *)
  set (We := (W ; W_equiv) : (sigT R <~> sigT R)).
  path_via (We^-1 (W (W y))).
  apply opposite, inverse_is_retraction.
  path_via' (We^-1 (W y)).
  apply map. apply W_idempotent.
  apply inverse_is_retraction.
  (* This looks like it would be difficult, except that it is a path
     in a contractible space! *)
  intro x.
  apply contr_path.
  assumption. assumption.
Defined.

(** Of course, naive dependent functional extensionality implies the
   eta rule. *)

Theorem funext_dep_to_eta_dep : funext_dep_statement -> eta_dep_statement.
Proof.
  intros H A P f.
  apply H.
  intro x.
  unfold eta_dep.
  auto.
Defined.

(** Therefore, strong dependent functional extensionality is
   equivalent to (weak functional extensionality + dependent eta). *)
