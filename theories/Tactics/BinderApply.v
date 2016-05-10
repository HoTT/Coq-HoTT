(* -*- mode: coq; mode: visual-line -*-  *)

(** * Apply a lemma under binders *)
Require Import Basics.Overture Tactics.EvalIn.
(** There are some cases where [apply lem] will fail, but [intros; apply lem] will succeed.  The tactic [binder apply] is like [intros; apply lem], but it cleans up after itself by [revert]ing the things it introduced.  The tactic [binder apply lem in H] is to [binder apply lem], as [apply lem in H] is to [apply lem].  Note, however, that the implementation of [binder apply lem in H] is completely different and significantly more complicated. *)

Ltac can_binder_apply apply_tac fail1_tac :=
  first [ test apply_tac
        | test (intro; can_binder_apply apply_tac fail1_tac)
        | fail1_tac ].
Ltac binder_apply apply_tac fail1_tac :=
  can_binder_apply apply_tac fail1_tac;
  first [ apply_tac
        | let H := fresh in
          intro H;
            binder_apply apply_tac fail1_tac;
            revert H
        | fail 1 "Cannot re-revert some introduced hypothesis" ].

(** The tactic [eval_under_binders tac H] is equivalent to [tac H] if [H] is not a product (lambda-abstraction), and roughly equivalent to the constr [fun x => eval_under_binders tac (H x)] if [H] is a product. *)
Ltac eval_under_binders tac H :=
  (** Bind a convenient name for the recursive call *)
  let rec_tac := eval_under_binders tac in
  (** If the hypothesis is a product ([forall]), we want to recurse under binders; if not, we're in the base case, and we simply compute the new term.  We use [match] rather than [lazymatch] so that if the tactic fails to apply under all of the binders, we try again under fewer binders.  We want to try first under as many binders as possible, in case the tactic, e.g., instantiates extra binders with evars. *)
  match type of H with
      (** Standard pattern for recursing under binders.  We zeta-expand to work around https://coq.inria.fr/bugs/show_bug.cgi?id=3248 and https://coq.inria.fr/bugs/show_bug.cgi?id=3458; we'd otherwise need globally unique name for [x].  We zeta-reduce afterwards so the user doesn't see our zeta-expansion.  We use [x] in both the pattern and the returned constructor so that we preserve the given name for the binder.  *)
    | forall x : ?T, @?P x
      => let ret := constr:(fun x : T =>
                              let Hx := H x in
                              ltac:(
                                let ret' := rec_tac Hx in
                                exact ret')) in
         let ret' := (eval cbv zeta in ret) in
         constr:(ret')
    (** Base case - simply return [tac H]  *)
    | _ => tac H
  end.

(** The tactic [make_tac_under_binders_using_in tac using_tac H] uses [tac] to transform a term [H], solving side-conditions (e.g., if [tac] uses [apply]) with [using_tac].  It returns the updated version of [H] as a constr; if [H] is a hypothesis in the context, it does not modify it.  Conceptually, [make_tac_under_binders_using_in tac idtac H] is the composition of two tactics: a [transform_under_binders : (constr -> constr) -> (constr -> constr)] that runs a tactic under the binders of the constr it's given, and what would be an [eval tac in H], except for the fact that, e.g., [eval rewrite in H] doesn't actually work because it predates tactics in terms (we use [eval_in_using tac using_tac H] instead).

    The arguments are:

    - [tac] - should take the name of a hypothesis, and modify that hypothesis in place.  It could, for example, be [fun H => rewrite lem in H] to do the [rewrite H] under binders.

    - [using_tac] - used to solve any side-conditions that [tac] generates.  Not strictly necessary, since [tac] can always solve its own side-conditions, but it's sometimes convenient to instantiate [tac] with [fun H => eapply lem in H] or something, and solve the side-conditions with [eassumption].

    - [H] - the name of the hypothesis to start from.

    N.B. We do not require [Funext] to use this tactic; [Funext] would only required to relate the term returned by this tactic and the original term.  Note also that we only rewrite under top-level binders (e.g., under the [x] in a hypothesis of type [forall x, P x], but not under the [x] in a hypothesis of type [(fun x y => x + y) = (fun x y => y + x)]). *)
Ltac make_tac_under_binders_using_in tac using_tac H :=
  eval_under_binders ltac:(fun H' => eval_in_using tac using_tac H') H.

Ltac do_tac_under_binders_using_in tac using_tac H :=
  let H' := make_tac_under_binders_using_in tac using_tac H in
  let H'' := fresh in
  pose proof H' as H'';
    clear H;
    rename H'' into H.

Tactic Notation "constrbinder" "apply" constr(lem) "in" constr(H) "using" tactic3(tac)
  := make_tac_under_binders_using_in ltac:(fun H' => apply lem in H') tac H.
Tactic Notation "constrbinder" "eapply" open_constr(lem) "in" constr(H) "using" tactic3(tac)
  := constrbinder apply lem in H using tac.

Tactic Notation "binder" "apply" constr(lem) "in" constr(H) "using" tactic3(tac)
  := do_tac_under_binders_using_in ltac:(fun H' => apply lem in H') tac H.
Tactic Notation "binder" "eapply" open_constr(lem) "in" constr(H) "using" tactic3(tac)
  := binder apply lem in H using tac.

Tactic Notation "constrbinder" "apply" constr(lem) "in" constr(H) := constrbinder apply lem in H using idtac.
Tactic Notation "constrbinder" "eapply" open_constr(lem) "in" constr(H) := constrbinder eapply lem in H using idtac.

Tactic Notation "binder" "apply" constr(lem) := binder_apply ltac:(apply lem) ltac:(fail 1 "Cannot apply" lem).
Tactic Notation "binder" "eapply" open_constr(lem) := binder_apply ltac:(eapply lem) ltac:(fail 1 "Cannot eapply" lem).

Tactic Notation "binder" "apply" constr(lem) "in" constr(H) := binder apply lem in H using idtac.
Tactic Notation "binder" "eapply" open_constr(lem) "in" constr(H) := binder eapply lem in H using idtac.

Example basic_goal {A B C} (HA : forall x : A, B x) (HB : forall x : A, B x -> C x) : forall x : A, C x.
Proof.
  (** If we try to [apply HB], wanting to replace [C] with [B], we get an error about being unable to unify [B ?] with [A]. *)
  Fail apply HB.
  (** The tactic [binder apply] fixes this shortcoming. *)
  binder apply HB.
  exact HA.
  (** We [Abort], so that we don't get an extra constant floating around. *)
Abort.

Example basic {A B C} (HA : forall x : A, B x) (HB : forall x : A, B x -> C x) : forall x : A, C x.
Proof.
  (** If we try to [apply HB in HA], wanting to replace [B] with [C], we get an error about being unable to instantiate the argument of type [A]: "Error: Unable to find an instance for the variable x." *)
  Fail apply HB in HA.
  (** The tactic [binder apply] fixes this shortcoming. *)
  binder apply HB in HA.
  exact HA.
  (** We [Abort], so that we don't get an extra constant floating around. *)
Abort.

Example ex_funext `{Funext} {A} f g
        (H' : forall x y z w : A, f x y z w = g x y z w :> A)
: f = g.
Proof.
  (** We need to apply [path_forall] under binders five times in [H'].  We use a different variant each time to demonstrate the various ways of using this tactic.  In a normal proof, you'd probably just do [do 4 binder apply (@path_forall _) in H'] or just [repeat binder apply (@path_forall _) in H']. *)
  (** If we do [binder apply path_forall in H'], we are told that Coq can't infer the argument [A] to [path_forall].  Instead, we can [binder eapply] it, to tell Coq to defer inference and use an evar for now. *)
  Fail binder apply path_forall in H'.
  binder eapply path_forall in H'.
  (** Alternatively, we can make [A] explicit.  But then we get an error about not being able to resolve the instance of [Funext].  We can either tell Coq to solve the side condition using the [assumption] tactic (or [typeclasses eauto], for that matter), or we can have typeclass inference run when we construct the lemma to apply. *)
  (** Some versions of Proof General are bad about noticing [Fail] within a tactic; see http://proofgeneral.inf.ed.ac.uk/trac/ticket/494.  So we comment this one out. *)
  (**
<<
  Fail binder apply @path_forall in H'.
>>
  Error: Tactic failure: Cannot use <tactic> to solve side-condition goal
Funext . Extended goal with context:
(Funext ->
 forall (A : Type) (f g : A -> A -> A -> A -> A)
   (H' : forall x' x'0 x'1 : A, f x' x'0 x'1 = g x' x'0 x'1),
 let H0 := H' in Funext). *)
  binder apply @path_forall in H' using assumption.
  binder apply @path_forall in H' using typeclasses eauto.
  binder apply (@path_forall _) in H'.
  (** Now we have removed all arguments to [f] and [g] in [H']. *)
  exact H'.
  (** We [Abort], so that we don't get an extra constant floating around. *)
Abort.

(** N.B. [constrbinder apply] is like [binder apply], except that it constructs a new term and returns it, rather than applying a lemma in-place to a hypothesis.  It's primarily useful as plumbing for higher-level tactics. *)
