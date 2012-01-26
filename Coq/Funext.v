Require Export Fibrations Contractible Equivalences.
Require Export UsefulEquivalences FiberEquivalences.

(** For compatibility with Coq 8.2. *)
Unset Automatic Introduction.

Definition ext_dep_eq {X} {P : X -> Type} (f g : forall x, P x) := forall x : X, f x == g x.

Notation "f === g" := (ext_dep_eq f g) (at level 50).

(** The simplest notion we call "naive functional extensionality".
   This is what a type theorist would probably write down when
   thinking of types as sets and identity types as equalities: it says
   that if two functions are equal pointwise, then they are equal.  It
   comes in both ordinary and dependent versions. *)

Definition funext_statement : Type :=
  forall (X Y : Type) (f g: X -> Y), f === g -> f == g.

Definition funext_dep_statement : Type :=
  forall (X : Type) (P : X -> Type) (f g : section P), f === g -> (f == g).

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

Definition strong_funext_statement : Type :=
  forall (X Y : Type) (f g : X -> Y), is_equiv (@happly X Y f g).

Definition strong_funext_dep_statement : Type :=
  forall (X : Type) (P : X -> Type) (f g : section P),
    is_equiv (@happly_dep X P f g).

(** Of course, strong functional extensionality implies naive
   functional extensionality, along with a computation rule. *)

Theorem strong_to_naive_funext :
  strong_funext_statement -> funext_statement.
Proof.
  intros H X Y f g.
  exact ((@happly X Y f g  ;  H X Y f g) ^-1).
Defined.

Theorem strong_funext_compute
  (strong_funext : strong_funext_statement)
  (X Y:Type) (f g : X -> Y) (p : f === g) (x : X) :
  happly (strong_to_naive_funext strong_funext X Y f g p) x == p x.
Proof.
  intros.
  unfold strong_to_naive_funext.
  unfold inverse.
  simpl.
  exact (happly_dep (pr2 (pr1 (strong_funext X Y f g p))) x).
Defined.

Theorem strong_to_naive_funext_dep :
  strong_funext_dep_statement -> funext_dep_statement.
Proof.
  intros H X Y f g.
  exact ((@happly_dep X Y f g ; H X Y f g) ^-1).
Defined.

Theorem strong_funext_dep_compute
  (strong_funext_dep : strong_funext_dep_statement)
  (X : Type) (P : X -> Type) (f g : section P) (p : f === g) (x : X) :
  happly_dep (strong_to_naive_funext_dep strong_funext_dep X P f g p) x == p x.
Proof.
  intros.
  unfold strong_to_naive_funext_dep.
  unfold inverse.
  simpl.
  exact (happly_dep (pr2 (pr1 (strong_funext_dep X P f g p))) x).
Defined.

(** We also observe that for both strong and naive functional
   extensionality, the dependent version implies the non-dependent
   version.  *)

Theorem strong_funext_dep_to_nondep :
  strong_funext_dep_statement -> strong_funext_statement.
Proof.
  intros H X Y f g. 
  exact (H X (fun x => Y) f g).
Defined.

Theorem funext_dep_to_nondep :
  funext_dep_statement -> funext_statement.
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

Definition weak_funext_statement := forall (X : Type) (P : X -> Type),
  (forall x : X, is_contr (P x)) -> is_contr (forall x : X, P x).

(** It is easy to see that naive dependent functional extensionality
   implies weak functional extensionality. *)

Theorem funext_dep_to_weak :
  funext_dep_statement -> weak_funext_statement.
Proof.
  intros H X P H1.
  exists (fun x => projT1 (H1 x)).
  intro f.
  assert (p : forall (x:X) (y:P x), y == ((fun x => projT1 (H1 x)) x)).
  intros. apply contr_path, H1.
  apply H. intro x. apply p.
Defined.

(** Another (very) weak type of functional extensionality is the
   (propositional) eta rule, which is implied by naive functional
   extensionality. *)

Definition eta {A B} (f : A -> B) :=
  fun x => f x.

Definition eta_statement :=
  forall (A B:Type) (f : A -> B), eta f == f.

Theorem naive_funext_implies_eta : funext_statement -> eta_statement.
Proof.
  intros funext A B f.
  apply funext.
  intro x.
  auto.
Defined.

(** Here is the dependent version. *)

Definition eta_dep {A} {P : A -> Type} (f : forall x, P x) :=
  fun x => f x.

Definition eta_dep_statement :=
  forall (A:Type) (P : A -> Type) (f : forall x, P x), eta_dep f == f.

Theorem naive_funext_dep_implies_eta : funext_dep_statement -> eta_dep_statement.
Proof.
  intros funext_dep A P f.
  apply funext_dep.
  intro x.
  auto.
Defined.

(** A "mini" form of the desired implication (naive => strong) is that
   the eta rule does implies directly that the eta map is an
   equivalence. *)

Lemma eta_is_equiv : eta_statement -> forall (A B : Type),
  is_equiv (@eta A B).
Proof.
  intros H A B.
  apply equiv_pointwise_idmap.
  intro f.
  apply H.
Defined.

Definition eta_equiv (Heta : eta_statement) (A B : Type) :
  (A -> B) <~> (A -> B) :=
  existT is_equiv (@eta A B) (eta_is_equiv Heta A B).

(** And the dependent version. *)

Lemma eta_dep_is_equiv : eta_dep_statement -> forall (A:Type) (P : A -> Type),
   is_equiv (@eta_dep A P).
Proof.
  intros H A P.
  apply equiv_pointwise_idmap.
  intro f.
  apply H.
Defined.

Definition eta_dep_equiv (Heta : eta_dep_statement) (A : Type) (P : A -> Type) :
  (forall x, P x) <~> (forall x, P x) :=
  existT is_equiv (@eta_dep A P) (eta_dep_is_equiv Heta A P).

(** Less trivial is the fact that weak functional extensionality
   implies *strong* (dependent) functional extensionality, at least in
   the presence of the dependent eta rule. *)

Theorem weak_to_strong_funext_dep :
  eta_dep_statement -> weak_funext_statement -> strong_funext_dep_statement.
Proof.
  intros Heta H X P f g.
  (* The idea is that [happly_dep] is one fiber map in a map of
     fibrations, whose total spaces are contractible and hence
     equivalent.  *)
  set (A := forall x, P x).
  set (Q := (fun h => f == h) : A -> Type).
  set (R := (fun h => forall x, f x == h x) : A -> Type).
  set (fibhap := (@happly_dep X P f) : forall h, Q h -> R h).
  apply (fiber_is_equiv _ _ fibhap).
  apply contr_contr_equiv.
  (* Contractibility of this space is easy. *)
  apply pathspace_contr'.
  (* This one is trickier; we show it is contractible by showing it
     equivalent to the total space of a different fibration. *)
  set (altAR := forall x, { y : P x & f x == y }).
  (* which is easily shown to be contractible. *)
  assert (contr_alt: is_contr altAR).
  apply H.
  intro x.
  apply pathspace_contr'.
  apply contr_equiv_contr with (A := altAR).
  (* The map between these spaces is obvious. *)
  set (k := (fun d => existT R (fun x => pr1 (d x)) (fun x => pr2 (d x)))
    : altAR -> sigT R).
  exists k.
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
  assert (W_idempotent : forall z, W (W z) == W z); auto.
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
