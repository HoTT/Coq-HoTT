Require Export Fibrations Contractible Equivalences FiberEquivalences.

(** Much of the content here is closely related to Richard Garner’s paper “On the strength of dependent products…”.  We use different terminology in places, but recall his for comparison. *)

Definition ext_dep_eq {X} {P : X -> Type} (f g : forall x, P x)
  := forall x : X, f x == g x.

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
(** This is the rule ‘Π-ext’ in Garner. *)

(** However, there are clearly going to be problems with this in the
   homotopy world, since "being equal" is not merely a property, but
   being equipped with a path is structure.  We should expect some
   sort of coherence or canonicity of the path from f to g relating it
   to the pointwise homotopy we started with.  

   There are (at least) two natural “computation principles” one might consider.  The first fits with thinking of [funext] as an _eliminator_: it tells us what happens if we apply [funext] to a term of canonical form. *)

Definition funext_comp1_statement (funext : funext_dep_statement)
  := (forall X P f, funext X P f f (fun x => idpath (f x)) == idpath f).
(** A propositional form of Garner’s ‘Π-ext-comp’. *)

(** Does this rule follow automatically?  Yes and no.  Given a witness [funext : funext_dep_statement], this does not necessarily hold for [funext] itself; but we can always find a better witness which it does hold: *)
Definition funext_correction : funext_dep_statement -> funext_dep_statement
  := (fun funext =>
        fun X P f g h => 
            (funext X P f g h)
          @ 
            ! (funext X P g g (fun x => idpath (g x)))).

Lemma funext_correction_comp1 :
  forall (funext : funext_dep_statement),
  funext_comp1_statement (funext_correction funext).
Proof.
  unfold funext_comp1_statement.
  unfold funext_correction.
  auto with path_hints.
Defined.

(** On the other hand, if we think of [funext] as more like a _1-dimensional constructor_ for Π-types,  we can be led to the following rule, telling us what happens to it under the destructor for Π-types, function application (bumped up to dimension 1 via happly): *)

Definition funext_comp2_statement (funext : funext_dep_statement)
  := (forall X P f g p x,
      happly_dep (funext X P f g p) x == p x).
(** ‘Π-ext-app’ in Garner. *)

(** Does this rule follow automatically?  *Yes*, and in fact for a given witness [funext], it’s equivalent to [funext_comp1_statement] above.  However, this seems quite non-trivial to prove; it will follow eventually from the comparision with “contractible functional extensionality”.  So we leave this for now, and will return to it later. *)

(** Alternatively, a natural way to state a "homotopically good" notion of function
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
   functional extensionality, along with both computation rules. *)

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

Theorem strong_funext_dep_comp1
  (strong_funext_dep : strong_funext_dep_statement)
: funext_comp1_statement (strong_to_naive_funext_dep strong_funext_dep).
Proof.
  unfold funext_comp1_statement.
  intros.
  unfold strong_to_naive_funext_dep.
  unfold inverse.
  simpl.
  unfold strong_funext_dep_statement in *.
  (* To show the desired equality, we first lift the points to the homotopy fiber, and then show them equal there, which is easy since it’s contractible.  *)
  apply (@base_path _ _ (pr1 (strong_funext_dep X P f f (fun x : X => idpath (f x)))) (idpath f; idpath _)).
  symmetry.
  apply (pr2 (strong_funext_dep X P f f (fun x : X => idpath (f x)))).
Defined.

Theorem strong_funext_dep_comp2
  (strong_funext_dep : strong_funext_dep_statement)
  : funext_comp2_statement (strong_to_naive_funext_dep strong_funext_dep).
Proof.
  unfold funext_comp2_statement.
  intros.
  unfold strong_to_naive_funext_dep.
  unfold inverse.
  simpl.
  exact (happly_dep (pr2 (pr1 (strong_funext_dep X P f g p))) x).
Defined.

(* Name used in older versions, retaining for backward-compatibility: *)
Definition strong_funext_dep_compute := strong_funext_dep_comp2.

(** Conversely, does naive functional extensionality imply the strong form?  Assuming _both_ computation rules, this is not hard to show: [comp1] says that [funext] gives a left inverse to [happly], [comp2] that it gives a right inverse. *)

Lemma funext_both_comps_to_strong
  (funext : funext_dep_statement)
  (funext_comp1 : funext_comp1_statement funext)
  (funext_comp2 : funext_comp2_statement funext)
: strong_funext_dep_statement.
Proof.
  intros.  unfold strong_funext_dep_statement.
  intros.  
  (* [funext] gives a two-sided inverse to [happly]: *)  
  apply (hequiv_is_equiv happly_dep (funext _ _ f g)).
  (* First, show it’s a right inverse: *)
  intro h_fg.  apply funext.  
  intro x.  apply (funext_comp2 X P).
  (* Now, show it’s a left inverse: *)
  intro p.  destruct p.  apply funext_comp1.
Defined.

(** But can we do better, getting to strong functional extensionality
   from just naive functional extensionality itself?  At first the prospects don't
   look good; naive functional extensionality gives us a map going
   backwards, but it doesn't assert anything *about* that map, so it
   seems unlikely that it would be an inverse to [happly].

   However, it turns out that we can do it; the key is to first
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

(** Some tactics for working with eta-expansion.  *)

Ltac eta_intro f :=
  match goal with
    | [ eta_rule : eta_dep_statement |- forall (f : forall x:_, _), @?Q f] =>
        intro f;
        apply (@transport _ Q _ _ (eta_rule _ _ f));
        unfold eta_dep
    | |- forall f, @?Q f =>
      let eta_rule := fresh "eta_rule" 
      in
        intro f;
        cut eta_dep_statement; 
        (* [cut] not [assert], to defer this subgoal to end *)
          [ intro eta_rule;
            apply (@transport _ Q _ _ (eta_rule _ _ f));
            unfold eta_dep 
          | try auto ]
    | |- _ => 
      idtac "Goal not quantified over a function; cannot eta-introduce."
end.

Ltac eta_expand f := 
  revert dependent f;
  eta_intro f.

(** Possible improvements to these tactics:
 
- At end of [eta_expand], reintroduce any other hypotheses generalized at the beginning of it.
- Make [eta_expand] work without reverting and re-introducing [f]?  
- In particular, it would be really nice if some form of it could work for arbitrary terms, not just variables; I tried using variations of [match goal with |- @?Q f] to do this, but couldn’t get it to work.
- Write “plural” versions of these tactics, so one can write i.e. [eta_intros f g h] to abbreviate [eta_intro f; eta_intro g; eta_intro h].
*)

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

(** Therefore, strong dependent functional extensionality is
   equivalent to (weak functional extensionality + dependent eta).

   Putting the pieces together, we can now get the strong from the naive form: *)

Theorem naive_to_strong_funext_via_weak
  : funext_dep_statement -> strong_funext_dep_statement.
Proof.
  intro funext.
  apply weak_to_strong_funext_dep.
  apply naive_funext_dep_implies_eta.  assumption.
  apply funext_dep_to_weak.  assumption.
Defined.

(** If we want, we can also now conclude that the two computation rules are equivalent, since once one knows that [happly] is an equivalence, any left inverse to it is also a right inverse, and vice versa.

Proof of this: to do, wants a couple of new lemmas in [Equivalences.v]. *)


(** * A new version of the proof of [strong_funext] from [funext_dep]. *)

(** We start by considering yet another version of functional extensionality: that given a function [f], the space of functions together with a homotopy to [f] is contractible.  For the sake of cleaner terms, we give a slightly more specific statement than juse [is_contr (…)]: *)

Definition contr_funext_statement :=
     forall {A} {B : A -> Type} (f : forall x:A, B x),
     forall (g : forall x:A, B x)  (h : f === g),
     (g ; h) == (existT (fun g => f === g) f (fun x => idpath (f x))).

(** The analogous statement with paths in place of homotopies is, of course, always true.  (In fact, I’d recalled it being in the library somewhere, but I can’t find it now.) *)

Lemma contract_cone {A} {x:A} (yp : { y:A & x == y })
  : yp == (x ; idpath x).
Proof.
  destruct yp as [y p].  path_induction.
Defined.

(** Now, by (weak or naive) extensionality, the product of all these cones is again contractible: *)

Lemma contract_product_of_cones_from_naive_funext
  {A} {B : A -> Type} {f : forall x:A, B x}
  : funext_dep_statement ->
    forall (gh : forall x:A, { y:B x & f x == y }),
    gh == (fun x:A => ( f x ; (idpath (f x))) ).
Proof.
  intros funext gh.  
  apply funext.  intro x.
  apply contract_cone.
Defined.

(** But the type of “functions homotopic to [f]” is an up-to-eta-expansion retract of this product of cones.  So, we define this retraction: *)

Lemma pair_fun_to_fun_pair 
  {A} {B : A -> Type} {f : forall x:A, B x}
  (gh : {g : forall x : A, B x & forall x : A, f x == g x})
  : forall x:A, { y:(B x) & f x == y }.
Proof.
  exact (match gh with
          (g ; h) => (fun x:A => (g x ; h x)) end ).
Defined.

Lemma fun_pair_to_pair_fun 
  {A} {B : A -> Type} {f : forall x:A, B x}
  (k : forall x:A, { y:(B x) & f x == y })
  : {g : forall x : A, B x & forall x : A, f x == g x}.
Proof.
  exists (fun x:A => match (k x) with (gx ; _) => gx end).
  intro x.  destruct (k x) as [gx hx].  exact hx.
Defined.

(** …and now we have all the ingredients for proving contractible funext from naive funext (or alternatively from weak funext + dependent eta): *)

Theorem naive_to_contr_funext
  : funext_dep_statement
    -> contr_funext_statement.
Proof.
  intros funext.
  unfold contr_funext_statement.  intros A B.
  (* WLOG, assume all function arguments are eta-expanded. *)
  eta_intro f; eta_intro g; eta_intro h.
  (* Now, replace each side with its image under the going-around-the-retraction: *)
  path_via (fun_pair_to_pair_fun (pair_fun_to_fun_pair (g ; h))).
  path_via (@fun_pair_to_pair_fun _ _ (fun x => f x) (fun x => (f x ; idpath (f x)))).
  (* Now it’s enough to show they were equal in the product of cones: *)
  apply contract_product_of_cones_from_naive_funext.  assumption.
  (* Finally, we are obliged to justify our use of [eta_intro]. *)
  apply naive_funext_dep_implies_eta; auto. 
Defined.

Lemma contr_funext_to_comp2 (funext : funext_dep_statement)
  : (funext_comp1_statement funext)
  -> contr_funext_statement
  -> (funext_comp2_statement funext).
Proof.
  intros funext_comp1 contr_funext.
  unfold funext_comp2_statement.  intros X P f g h.
  apply (@transport _ 
           (fun (g0h0 : { g : section P & f === g }) 
              => match g0h0 with (g0;h0)
              => (forall x : X, happly_dep (funext X P f g0 h0) x == h0 x) end)
            (existT (fun g => f === g) f (fun x => idpath (f x)))
            (g ; h)).
  symmetry.  apply contr_funext.
  clear g h.  intro x. 
  (* A “rewrite” tactic would be nicer here; lacking one, we explicitly expand the RHS. *)
  path_via (happly_dep (idpath f) x).
  apply_happly.  path_simplify. 
  apply funext_comp1.
Defined.

Theorem funext_comp1_to_comp2 (funext : funext_dep_statement)
  : (funext_comp1_statement funext) -> (funext_comp2_statement funext).
Proof.
  intro funext_comp1.  
  apply contr_funext_to_comp2; auto.  
  apply naive_to_contr_funext; auto.
Defined.

Lemma funext_correction_comp2 (funext : funext_dep_statement)
  : funext_comp2_statement (funext_correction funext).
Proof.
  apply funext_comp1_to_comp2. 
  apply funext_correction_comp1.
Defined.

Theorem naive_to_strong_funext_via_contr
  : funext_dep_statement -> strong_funext_dep_statement.
Proof.
  intro funext.
  apply (funext_both_comps_to_strong (funext_correction funext)).
  apply funext_correction_comp1.
  apply funext_correction_comp2.
Defined.

Theorem contr_to_strong_funext
  : funext_dep_statement -> strong_funext_dep_statement.

(** * Comparing dependent and non-dependent forms. *)

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

(** One can prove similar things for the other variants considered.  Can we go the other way, though?? *)