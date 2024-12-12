Require Import Basics.Overture.

(** TODO: Clean up *)

(** * Basic tactics *)

(** This module implements various tactics used in the library. *)

(** If the goal is [x = z], [path_via y] will replace this with two goals, [x = y] and [y = z]. *)
Ltac path_via mid :=
  apply @concat with (y := mid); auto with path_hints.

(** The following tactic is designed to be more or less interchangeable with [induction n as [ | n' IH ]] whenever [n] is a [nat] or a [trunc_index].  The difference is that it produces proof terms involving [fix] explicitly rather than [nat_ind] or [trunc_index_ind], and therefore does not introduce higher universe parameters. It works if [n] is in the context or in the goal. *)
Ltac simple_induction n n' IH :=
  try generalize dependent n;
  fix IH 1;
  intros [| n'];
  [ clear IH | specialize (IH n') ].

Ltac simple_induction' n :=
  let IH := fresh "IH" in
  simple_induction n n IH.

(** Debugging tactics to show the goal during evaluation. *)

Ltac show_goal := match goal with [ |- ?T ] => idtac T end.

Ltac show_hyp id :=
  match goal with
    | [ H := ?b : ?T |- _ ] =>
      match H with
        | id => idtac id ":=" b ":" T
      end
    | [ H : ?T |- _ ] =>
      match H with
        | id => idtac id  ":"  T
      end
  end.

Ltac show_hyps :=
  try match reverse goal with
        | [ H : ?T |- _ ] => show_hyp H ; fail
      end.

(** Do something on the last hypothesis, or fail *)

Ltac on_last_hyp tac :=
  match goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

(** Revert the last hypothesis. *)

Ltac revert_last :=
  match goal with
    [ H : _ |- _ ] => revert H
  end.

(** Repeatedly reverse the last hypothesis, putting everything in the goal. *)

Ltac reverse := repeat revert_last.

(** Reverse everything up to hypothesis id (not included). *)

Ltac revert_until id :=
  on_last_hyp ltac:(fun id' =>
    match id' with
      | id => idtac
      | _ => revert id' ; revert_until id
    end).

(** Clear duplicated hypotheses *)

Ltac clear_dup :=
  match goal with
    | [ H : ?X |- _ ] =>
      match goal with
        | [ H' : ?Y |- _ ] =>
          match H with
            | H' => fail 2
            | _ => unify X Y ; (clear H' || clear H)
          end
      end
  end.

Ltac clear_dups := repeat clear_dup.

(** Try to clear everything except some hyp *)

Ltac clear_except hyp :=
  repeat match goal with [ H : _ |- _ ] =>
           match H with
             | hyp => fail 1
             | _ => clear H
           end
         end.

Ltac on_application f tac T :=
  match T with
    | context [f ?x ?y ?z ?w ?v ?u ?a ?b ?c] => tac (f x y z w v u a b c)
    | context [f ?x ?y ?z ?w ?v ?u ?a ?b] => tac (f x y z w v u a b)
    | context [f ?x ?y ?z ?w ?v ?u ?a] => tac (f x y z w v u a)
    | context [f ?x ?y ?z ?w ?v ?u] => tac (f x y z w v u)
    | context [f ?x ?y ?z ?w ?v] => tac (f x y z w v)
    | context [f ?x ?y ?z ?w] => tac (f x y z w)
    | context [f ?x ?y ?z] => tac (f x y z)
    | context [f ?x ?y] => tac (f x y)
    | context [f ?x] => tac (f x)
  end.

(** Tactical [on_call f tac] applies [tac] on any application of [f] in the hypothesis or goal. *)

Ltac on_call f tac :=
  match goal with
    | |- ?T  => on_application f tac T
    | H : ?T |- _  => on_application f tac T
  end.

(* Destructs calls to f in hypothesis or conclusion, useful if f creates a subset object. *)

Ltac destruct_call f :=
  let tac t := (destruct t) in on_call f tac.

Ltac destruct_calls f := repeat destruct_call f.

Ltac destruct_call_in f H :=
  let tac t := (destruct t) in
  let T := type of H in
    on_application f tac T.

Ltac destruct_call_as f l :=
  let tac t := (destruct t as l) in on_call f tac.

Ltac destruct_call_as_in f l H :=
  let tac t := (destruct t as l) in
  let T := type of H in
    on_application f tac T.

Tactic Notation "destruct_call" constr(f) := destruct_call f.

(** Permit to name the results of destructing the call to [f]. *)

Tactic Notation "destruct_call" constr(f) "as" simple_intropattern(l) :=
  destruct_call_as f l.

(** Specify the hypothesis in which the call occurs as well. *)

Tactic Notation "destruct_call" constr(f) "in" hyp(id) :=
  destruct_call_in f id.

Tactic Notation "destruct_call" constr(f) "as" simple_intropattern(l) "in" hyp(id) :=
  destruct_call_as_in f l id.

(** A marker for prototypes to destruct. *)

Definition fix_proto {A : Type} (a : A) := a.

Ltac destruct_rec_calls :=
  match goal with
    | [ H : fix_proto _ |- _ ] => destruct_calls H ; clear H
  end.

Ltac destruct_all_rec_calls :=
  repeat destruct_rec_calls ; unfold fix_proto in *.

(** Try to inject any potential constructor equality hypothesis. *)

Ltac inject H := progress (inversion H ; clear_dups) ; clear H.

Ltac autoinjections := repeat (clear_dups ; ltac:(inject)).

(** Destruct an hypothesis by first copying it to avoid dependencies. *)

Ltac destruct_nondep H := let H0 := fresh "H" in assert(H0 := H); destruct H0.

(** A tactic to show contradiction by first asserting an automatically provable hypothesis. *)
Tactic Notation "contradiction" "by" constr(t) :=
  let H := fresh in assert t as H by auto with * ; contradiction.

(** A tactic that adds [H:=p:typeof(p)] to the context if no hypothesis of the same type appears in the goal.
   Useful to do saturation using tactics. *)

Ltac add_hypothesis H' p :=
  match type of p with
    ?X =>
    match goal with
      | [ H : X |- _ ] => fail 1
      | _ => set (H':=p) ; try (change p with H') ; clearbody H'
    end
  end.

(** A tactic to replace an hypothesis by another term. *)

Ltac replace_hyp H c :=
  let H' := fresh "H" in
    assert(H' := c) ; clear H ; rename H' into H.

(** A tactic to refine an hypothesis by supplying some of its arguments. *)

Ltac refine_hyp c :=
  let tac H := replace_hyp H c in
    match c with
      | ?H _ => tac H
      | ?H _ _ => tac H
      | ?H _ _ _ => tac H
      | ?H _ _ _ _ => tac H
      | ?H _ _ _ _ _ => tac H
      | ?H _ _ _ _ _ _ => tac H
      | ?H _ _ _ _ _ _ _ => tac H
      | ?H _ _ _ _ _ _ _ _ => tac H
    end.

(** TODO: From here comes from Overture.v *)

(** Clear a hypothesis and also its dependencies.  Taken from Coq stdlib, with the performance-enhancing change to [lazymatch] suggested at [https://github.com/coq/coq/issues/11689]. *)
Tactic Notation "clear" "dependent" hyp(h) :=
  let rec depclear h :=
  clear h ||
  lazymatch goal with
   | H : context [ h ] |- _ => depclear H; depclear h
  end ||
  fail "hypothesis to clear is used in the conclusion (maybe indirectly)"
 in depclear h.


(** A version of [generalize dependent] that applies only to a hypothesis.  Taken from Coq stdlib. *)
Tactic Notation "revert" "dependent" hyp(h) :=
  generalize dependent h.

(** Applying a tactic to a term with increasingly many arguments *)
Tactic Notation "do_with_holes" tactic3(x) uconstr(p) :=
  x uconstr:(p) ||
  x uconstr:(p _) ||
  x uconstr:(p _ _) ||
  x uconstr:(p _ _ _) ||
  x uconstr:(p _ _ _ _) ||
  x uconstr:(p _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

(** Same thing but starting with many holes first *)
Tactic Notation "do_with_holes'" tactic3(x) uconstr(p) :=
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _ _) ||
  x uconstr:(p _ _ _ _ _) ||
  x uconstr:(p _ _ _ _) ||
  x uconstr:(p _ _ _) ||
  x uconstr:(p _ _) ||
  x uconstr:(p _) ||
  x uconstr:(p).

(** We keep a list of global axioms that we will solve automatically, even when not using typeclass search. *)
Unset Primitive Projections.
Class IsGlobalAxiom (A : Type) : Type0 := {}.
Set Primitive Projections.
Global Hint Mode IsGlobalAxiom + : typeclass_instances.

(** We add [Funext] to the list here, and will later add [Univalence]. *)
Global Instance is_global_axiom_funext : IsGlobalAxiom Funext := {}.

(** Add [PropResizing] to the list of global axioms. *)
Global Instance is_global_axiom_propresizing : IsGlobalAxiom PropResizing := {}.

Ltac is_global_axiom A := let _ := constr:(_ : IsGlobalAxiom A) in idtac.

Ltac global_axiom := try match goal with
    | |- ?G  => is_global_axiom G; exact _
end.

(** A shorter name for [simple refine]. *)
Tactic Notation "srefine" uconstr(term) := simple refine term.
(** A shorter name for [notypeclasses refine]; also handles global axioms. *)
Tactic Notation "nrefine" uconstr(term) := notypeclasses refine term; global_axiom.
(** A shorter name for [simple notypeclasses refine]; also handles global axioms. *)
Tactic Notation "snrefine" uconstr(term) := simple notypeclasses refine term; global_axiom.

(** Note that the Coq standard library has a [rapply], but it is like our [rapply'] with many-holes first.  We prefer fewer-holes first, for instance so that a theorem producing an equivalence will by preference be used to produce an equivalence rather than to apply the coercion of that equivalence to a function. *)
Tactic Notation "rapply" uconstr(term)
  := do_with_holes ltac:(fun x => refine x) term.
Tactic Notation "rapply'" uconstr(term)
  := do_with_holes' ltac:(fun x => refine x) term.

Tactic Notation "srapply" uconstr(term)
  := do_with_holes ltac:(fun x => srefine x) term.
Tactic Notation "srapply'" uconstr(term)
  := do_with_holes' ltac:(fun x => srefine x) term.

Tactic Notation "nrapply" uconstr(term)
  := do_with_holes ltac:(fun x => nrefine x) term.
Tactic Notation "nrapply'" uconstr(term)
  := do_with_holes' ltac:(fun x => nrefine x) term.

Tactic Notation "snrapply" uconstr(term)
  := do_with_holes ltac:(fun x => snrefine x) term.
Tactic Notation "snrapply'" uconstr(term)
  := do_with_holes' ltac:(fun x => snrefine x) term.

(** Apply a tactic to one side of an equation.  For example, [lhs rapply lemma].  [tac] should produce a path. *)

Tactic Notation "lhs" tactic3(tac) := nrefine (ltac:(tac) @ _).
Tactic Notation "lhs_V" tactic3(tac) := nrefine (ltac:(tac)^ @ _).
Tactic Notation "rhs" tactic3(tac) := nrefine (_ @ ltac:(tac)^).
Tactic Notation "rhs_V" tactic3(tac) := nrefine (_ @ ltac:(tac)).

(** Ssreflect tactics, adapted by Robbert Krebbers *)
Ltac done :=
  trivial; intros; solve
    [ repeat first
      [ solve [trivial]
      | solve [symmetry; trivial]
      | reflexivity
      (* Discriminate should be here, but it doesn't work yet *)
      (* | discriminate *)
      | contradiction
      | split ]
    | match goal with
      H : ~ _ |- _ => solve [destruct H; trivial]
      end ].

Tactic Notation "by" tactic(tac) :=
  tac; done.

(** Apply using the same opacity information as typeclass proof search. *)
Ltac class_apply c := autoapply c with typeclass_instances.

(** A convenient tactic for using function extensionality. *)
Ltac by_extensionality x :=
  intros;
  match goal with
  | [ |- ?f = ?g ] => eapply path_forall; intro x;
      match goal with
        | [ |- forall (_ : prod _ _), _ ] => intros [? ?]
        | [ |- forall (_ : sig _ _), _ ] => intros [? ?]
        | _ => intros
    end;
    simpl; auto with path_hints
  end.

(** [funext] apply functional extensionality ([path_forall]) to the goal and the introduce the arguments in the context. *)
(** For instance, if you have to prove [f = g] where [f] and [g] take two arguments, you can use [funext x y], and the goal become [f x y = g x y]. *)
Tactic Notation "funext" simple_intropattern(a)
  := apply path_forall; intros a.
Tactic Notation "funext" simple_intropattern(a)  simple_intropattern(b)
  := funext a; funext b.
Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c)
  := funext a; funext b; funext c.
Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d)
  := funext a; funext b; funext c; funext d.
Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d) simple_intropattern(e)
  := funext a; funext b; funext c; funext d; funext e.
Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d) simple_intropattern(e) simple_intropattern(f)
  := funext a; funext b; funext c; funext d; funext e; funext f.

(* Test whether a tactic fails or succeeds, without actually doing anything.  Taken from Coq stdlib. *)
Ltac assert_fails tac :=
  tryif (once tac) then gfail 0 tac "succeeds" else idtac.
Tactic Notation "assert_succeeds" tactic3(tac) :=
  tryif (assert_fails tac) then gfail 0 tac "fails" else idtac.
Tactic Notation "assert_succeeds" tactic3(tac) :=
  assert_succeeds tac.
Tactic Notation "assert_fails" tactic3(tac) :=
  assert_fails tac.

(** This tactic doesn't end with [auto], but you can always write "by (path_induction;auto with path_hints)" if you want.*)
Ltac path_induction :=
  intros; repeat progress (
    match goal with
      | [ p : ?x = ?y  |- _ ] => assert_fails constr_eq x y; induction p
    end
  ).

(** The tactic [f_ap] is a replacement for the previously existing standard library tactic [f_equal].  This tactic works by repeatedly applying the fact that [f = g -> x = y -> f x = g y] to turn, e.g., [f x y = f z w] first into [f x = f z] and [y = w], and then turns the first of these into [f = f] and [x = z].  The [done] tactic is used to detect the [f = f] case and finish, and the [trivial] is used to solve, e.g., [x = x] when using [f_ap] on [f y x = f z x].  This tactic only works for non-dependently-typed functions; we cannot express [y = w] in the first example if [y] and [w] have different types.  If and when Arnaud's new-tacticals branch lands, and we can have a goal which depends on the term used to discharge another goal, then this tactic should probably be generalized to deal with dependent functions. *)
Ltac f_ap :=
  idtac;
  lazymatch goal with
    | [ |- ?f ?x = ?g ?x ] => apply (@apD10 _ _ f g);
                             try (done || f_ap)
    | _ => apply ap11;
          [ done || f_ap
          | trivial ]
  end.

(** [expand] replaces both terms of an equality (either [paths] or [pointwise_paths] in the goal with their head normal forms *)
Ltac expand :=
  idtac;
  match goal with
    | [ |- ?X = ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' = Y')
    | [ |- ?X == ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' == Y')
  end; simpl.

(** [atomic x] is the same as [idtac] if [x] is a variable or hypothesis, but is [fail 0] if [x] has internal structure.  This is useful, for example, to easily destruct all variables that show up as the discriminees of [match] statements, without destructing more complicated terms whose structures might matter. *)
Ltac atomic x :=
  idtac;
  match x with
    | _ => is_evar x; fail 1 x "is not atomic (evar)"
    | ?f _ => fail 1 x "is not atomic (application)"
    | (fun _ => _) => fail 1 x "is not atomic (fun)"
    | forall _, _ => fail 1 x "is not atomic (forall)"
    | let x := _ in _ => fail 1 x "is not atomic (let in)"
    | match _ with _ => _ end => fail 1 x "is not atomic (match)"
    | _ => is_fix x; fail 1 x "is not atomic (fix)"
    | _ => is_cofix x; fail 1 x "is not atomic (cofix)"
    | context[?E] => (* catch-all *) (assert_fails constr_eq E x); fail 1 x "is not atomic (has subterm" E ")"
    | _ => idtac
  end.

(** Find the head of the given expression. *)
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

(** This tactic gets the constructor of any one-constructor inductive type. *)
Ltac get_constructor_head T :=
  let x := fresh in
  let x' := fresh in
  let h := open_constr:(_) in
  let __ := constr:(fun (x : T)
                    => let x' := x in
                       ltac:(destruct x;
                             let x' := (eval cbv delta [x'] in x') in
                             let x' := head x' in
                             unify h x';
                             exact tt)) in
  h.

(* A version of econstructor that doesn't resolve typeclasses. *)
Ltac ntc_constructor :=
  lazymatch goal with
  | [ |- ?G ] => let build := get_constructor_head G in
                 nrapply build
  end.

(** [case_path] is a HoTT replacement for [case_eq]; [case_path x] is like [destruct x], but it remembers the original value of [x] in an equation to be introduced. *)
Ltac case_path x :=
  let x' := fresh "x" in
  set (x' := x);
    generalize (idpath : x' = x);
    clearbody x';
    destruct x'.

(** [revert_opaque x] is like [revert x], except that it fails if [x] is not an opaque variable (i.e. if it has a [:=] definition rather than just a type). *)
Ltac revert_opaque x :=
  revert x;
  match goal with
    | [ |- forall _, _ ] => idtac
    | _ => fail 1 "Reverted constant is not an opaque variable"
  end.

(** [transparent assert (H : T)] is like [assert (H : T)], but leaves the body transparent. *)
(** Since binders don't respect [fresh], we use a name unlikely to be reused. *)
Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" :=
  simple refine (let __transparent_assert_hypothesis := (_ : type) in _);
  [
  | ((* We cannot use the name [__transparent_assert_hypothesis], due to some infelicities in the naming of bound variables.  So instead we pull the bottommost hypothesis. *)
    let H := match goal with H := _ |- _ => constr:(H) end in
    rename H into name) ].

(** [transparent eassert] is like [transparent assert], but allows holes in the type, which will be turned into evars. *)
Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" "by" tactic3(tac) := let name := fresh "H" in transparent assert (name : type); [ solve [ tac ] | ].
Tactic Notation "transparent" "eassert" "(" ident(name) ":" open_constr(type) ")" := transparent assert (name : type).
Tactic Notation "transparent" "eassert" "(" ident(name) ":" open_constr(type) ")" "by" tactic3(tac) := transparent assert (name : type) by tac.

(** A version of Coq's [remember] that uses our equality. *)
Ltac remember_as term name eqname :=
  set (name := term) in *;
  pose (eqname := idpath : term = name);
  clearbody eqname name.

Tactic Notation "remember" constr(term) "as" ident(name) "eqn:" ident(eqname) :=
  remember_as term name eqname.

(** A variant that doesn't substitute in the goal and hypotheses. *)
Ltac recall_as term name eqname :=
  pose (name := term);
  pose (eqname := idpath : term = name);
  clearbody eqname name.

Tactic Notation "recall" constr(term) "as" ident(name) "eqn:" ident(eqname) :=
  recall_as term name eqname.

(** [rel_hnf], when given a goal of the form [R x y] for any relation [R], puts [x] and [y] in head normal form. *)
Ltac rel_hnf :=
  idtac;
  match goal with
    | [ |- ?R ?x ?y ] => let x' := (eval hnf in x) in
                         let y' := (eval hnf in y) in
                         change (R x' y')
  end.

(** This tactic is a version of [tryif require () then if_yes () else if_no ()] which is suitable for use in constructing constrs by virtue of being evaluated during the Ltac expression evaluation phase rather than during the tactic running phase.
All three arguments are expected to be tactic thunks which will be passed a dummy unit argument.*)
Ltac tryif_cps require if_yes if_no :=
  let res := match constr:(Set) with
             | _ => let __ := match constr:(Set) with _ => require () end in
                    ltac:(if_yes)
             | _ => ltac:(if_no)
             end in res ().

(** The following tactic [issig] proves automatically that a record type is equivalent to a nested Sigma-type. Specifically, it proves a goal that looks like

<<
   { x : A & B x } <~> Some_Record
>>

In fact you don't even have to write down the sigma type. Though it is good practice to write it out anyway, this tactic can work out the sigma type and tell you what it should look like.

The following should generate the desired equivalence. You can check the definition to see what type it has and therefore what the sigma type should be.

<<
  Definition issig_myrecord
    : _ <~> MyRecord := ltac:(issig).

  Check issig_myrecord.
>>

In order to define this tactic we have many helper tactics.

*)


Local Ltac peel_evars term :=
  lazymatch term with
  | ?f ?x
    => tryif_cps
         ltac:(fun _ => has_evar x)
         ltac:(fun _ => peel_evars f)
         ltac:(fun _ => term)
  | _ => term
  end.

Local Ltac pi_to_sig ty :=
  lazymatch (eval cbv beta in ty) with
  | forall (x : ?T) (y : @?A x), @?P x y
    => let x' := fresh in
       constr:(@sig T (fun x' : T =>
        ltac:(let res := pi_to_sig
          (forall y : A x', P x' y) in exact res)))
  | ?T -> _ => T
  end.

Local Ltac ctor_to_sig ctor :=
  let ctor := peel_evars ctor in
  let t := type of ctor in
  pi_to_sig t.

Local Ltac unify_first_evar_with term u :=
  lazymatch term with
  | ?f ?x
    => tryif has_evar f
    then unify_first_evar_with f u
    else unify x u
  end.

Local Ltac unify_with_projections term u :=
  (unify_first_evar_with term u.1; unify_with_projections term u.2) +
  (unify_first_evar_with term u;
   tryif has_evar term then fail 0 term "has evars remaining" else idtac).

(* Completely destroys v into its pieces and trys to put pieces in sigma. *)
Local Ltac refine_with_exist_as_much_as_needed_then_destruct v :=
  ((destruct v; shelve) +
   (snrefine (_ ; _);
    [ destruct v; shelve
    | refine_with_exist_as_much_as_needed_then_destruct v ])).


(* Finally we can define our issig tactic: *)
Ltac issig :=
  hnf; (* First we make sure things are normalised. *)
  (* We get the types either side of the equivalence. *)
  let A := match goal with |- ?sigma <~> ?record => constr:(sigma) end in
  let B := match goal with |- ?sigma <~> ?record => constr:(record) end in
  let u := fresh "u" in
  let v := fresh "v" in
  (** We build an equivalence with 5 holes. *)
  snrefine  (* We don't want typeclass search running. *)
    (Build_Equiv A B _ (Build_IsEquiv A B (fun u => _) (fun v => _)
      (fun v => _) (fun u => _) (fun _ => _)));
  (** Going from a sigma type to a record *)
  [ (* let built be the constructor of T *)
    let T := match goal with |- ?T => T end in
    (* We want to get the constructor of the record. Note that we use [ntc_constructor] instead of [econstructor] since we don't want to resolve typeclasses. If we used [econstructor] then the constructor would be wrong for many records whose fields are classes. [ntc_constructor] is defined in Overture.v. *)
    let built := open_constr:(ltac:(ntc_constructor) : T) in
    let A' := ctor_to_sig built in
    unify A A';
    unify_with_projections built u;
    refine built
  (** Going from a record to a sigma type *)
  | refine_with_exist_as_much_as_needed_then_destruct v
  (** Proving eissect *)
  | destruct v; cbn [pr1 pr2]; reflexivity
  (** Proving eisretr *)
  | reflexivity
  (** Proving eisadj *)
  | reflexivity ].

(** We show how the tactic works in a couple of examples. *)

Definition issig_equiv (A B : Type)
  : {f : A -> B & IsEquiv f} <~> Equiv A B.
Proof.
  issig.
Defined.

Definition issig_isequiv {A B : Type} (f : A -> B)
  : {g : B -> A & {r : f o g == idmap & { s : g o f == idmap
    & forall x : A, r (f x) = ap f (s x)}}}
  <~> IsEquiv f.
Proof.
  issig.
Defined.

(** The general reasoning behind the issig tactic is: if we know the type of the record, econstructor will give us the constructor applied to evars for each field. If we assume that there are no evars in the type, we can unify the first evar with u.1, the next evar with u.2.1, the next with u.2.2.1, etc, and if we run out of evars or projections, we backtrack and instead fill the final evar with u.2.2....2. (Note that if we strip the trailing evars from the constructor before unifying them, we get a term with a Pi type, and if we drop the final codomain and turn the Pi type into a Sigma, this lets us autogenerate the Sigma type we should be using; this is how the versions that don't need a hand-crafted Sigma type work: they unify the generated type with the term in the goal that should be the Sigma type.)

Generating the function the other way is a bit trickier, because there's no easy way to get our hands on all the projections of the record, and moreover we don't even know how many pairings we'll need. The thing we want to do is introduce the right number of pairings, destruct the variable of record type in the goal for each component, and then magically use the right projection. I'll get back to the magic in a moment; first we need to take care of the "right number" of pairings. We could pull a trick where we infer the number by looking at the term we get from econstructor in a goal whose type is the record. Instead, I chose the more concise route of coding a tactic that introduces the minimum number of pairings needed to make the magic work. How does it know the minimum number? It doesn't need to! The wonder of (recursive) multisuccess tactics is that you can say "try no pairings, and if that makes any future tactic fail, backtrack and try one pairing, and if that doesn't work, backtrack and try two pairings, etc". (The downside is that the error messages you get when you set things up wrong are truly incomprehensible, because if you make a typo in any of the fields of the Sigma type the error message you end up getting is something like "(_; _) is a Sigma type but it was expected to have the type of the final field" (and it's always about the final field, regardless of which field you made a typo in). So plausibly it's worth it to still do the small issig tactics by hand, and only use this tactic for >= 5 fields or something.)

Okay, now onto the magic. How do we know which field is the right one? Well, there's only one answer that lets us prove the section and retraction by destruct+reflexivity, so we can let unification solve this problem for us. It's important to have destructed the record variable in each of the pair-component evars, because unification is not (yet) smart enough to invert records for us; this is what the destruct before shelve in the inverse function generation tactic is. We cbn pr1 and pr2 to make the unification problem be completely syntactic (no need to unfold anything during unification). This is probably not strictly necessary, but seems like good form to me.

Finally, we can prove the other one of the section/retraction pair (I can never recall which is which), and the adjoint, by reflexivity. (Perhaps it would be better to use exact idpath, if we want to not have to unfold reflexivity when using equivalences generated by these tactics.) *)
