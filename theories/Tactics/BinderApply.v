(** * Apply a lemma under binders *)
Require Import Overture.

Ltac make_tac_under_binders_using_in tac using_tac H :=
  let rec_tac := make_tac_under_binders_using_in tac using_tac in
  match type of H with
    | forall x : ?T, @?P x
      => let ret := constr:(fun x' : T =>
                              let Hx := H x' in
                              $(let ret' := rec_tac Hx in
                                exact ret')$) in
         let ret' := (eval cbv zeta in ret) in
         constr:(ret')
    | _ => let ret := constr:($(let H' := fresh in
                                pose H as H';
                                tac H';
                                [ exact H'
                                | solve [ using_tac
                                        | let G := match goal with |- ?G => constr:(G) end in
                                          repeat match goal with H : _ |- _ => revert H end;
                                          let G' := match goal with |- ?G => constr:(G) end in
                                          fail 1
                                               "Cannot use" using_tac "to solve side-condition goal" G "."
                                               "Extended goal with context:" G' ].. ])$) in
           let ret' := (eval cbv beta zeta in ret) in
           constr:(ret')
  end.

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

Tactic Notation "binder" "apply" constr(lem) "in" constr(H) := binder apply lem in H using idtac.
Tactic Notation "binder" "eapply" open_constr(lem) "in" constr(H) := binder eapply lem in H using idtac.

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
