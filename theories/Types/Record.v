Require Import Basics.Overture.
Local Open Scope path_scope.

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
       constr:(@sigT T (fun x' : T =>
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

(* Completely destroys v into it's pieces and trys to put pieces in sigma. *)
Local Ltac refine_with_existT_as_much_as_needed_then_destruct v :=
  ((destruct v; shelve) +
   (simple notypeclasses refine (_ ; _);
    [ destruct v; shelve
    | refine_with_existT_as_much_as_needed_then_destruct v ])).


(* Finally we can define our issig tactic: *)
Ltac issig :=
  hnf; (* First we make sure things are normalised. *)
  (* We get the types either side of the equivalence. *)
  let A := match goal with |- ?sigma <~> ?record => constr:(sigma) end in
  let B := match goal with |- ?sigma <~> ?record => constr:(record) end in
  let u := fresh "u" in
  let v := fresh "v" in
  (** We build an equivalence with 5 holes. *)
  simple notypeclasses refine  (* We don't want typeclass search running. *)
    (BuildEquiv A B _ (BuildIsEquiv A B (fun u => _) (fun v => _)
      (fun v => _) (fun u => _) (fun _ => _)));
  (** Going from a sigma type to a record *)
  [ (* let built be the constructor of T *)
    let T := match goal with |- ?T => T end in
    (* We want to get the constructor of the record. Note that we use [ntceconstructor] instead of [econstructor] since we don't want to resolve typeclasses. If we used [econstructor] then the constructor would be wrong for many records whose fields are classes. [ntceconstructor] is defined in Overture.v. *)
    let built := open_constr:(ltac:(ntceconstructor) : T) in
    let A' := ctor_to_sig built in
    unify A A';
    unify_with_projections built u;
    refine built
  (** Going from a record to a sigma type *)
  | refine_with_existT_as_much_as_needed_then_destruct v
  (** Proving eissect *)
  | destruct v; cbn [pr1 pr2]; reflexivity
  (** Proving eisretr *)
  | reflexivity
  (** Proving eisadj *)
  | reflexivity ].

(** The general reasoning behind the new issig tactics is: if we know the type of the record, econstructor will give us the constructor applied to evars for each field. If we assume that there are no evars in the type, we can unify the first evar with u.1, the next evar with u.2.1, the next with u.2.2.1, etc, and if we run out of evars or projections, we backtrack and instead fill the final evar with u.2.2....2. (Note that if we strip the trailing evars from the constructor before unifying them, we get a term with a Pi type, and if we drop the final codomain and turn the Pi type into a Sigma, this lets us autogenerate the Sigma type we should be using; this is how the versions that don't need a hand-crafted Sigma type work: they unify the generated type with the term in the goal that should be the Sigma type.)

Generating the function the other way is a bit trickier, because there's no easy way to get our hands on all the projections of the record, and moreover we don't even know how many pairings we'll need. The thing we want to do is introduce the right number of pairings, destruct the variable of record type in the goal for each component, and then magically use the right projection. I'll get back to the magic in a moment; first we need to take care of the "right number" of pairings. We could pull a trick where we infer the number by looking at the term we get from econstructor in a goal whose type is the record. Instead, I chose the more concise route of coding a tactic that introduces the minimum number of pairings needed to make the magic work. How does it know the minimum number? It doesn't need to! The wonder of (recursive) multisuccess tactics is that you can say "try no pairings, and if that makes any future tactic fail, backtrack and try one pairing, and if that doesn't work, backtrack and try two pairings, etc". (The downside is that the error messages you get when you set things up wrong are truly incomprehensible, because if you make a typo in any of the fields of the Sigma type the error message you end up getting is something like "(_; _) is a Sigma type but it was expected to have the type of the final field" (and it's always about the final field, regardless of which field you made a typo in). So plausibly it's worth it to still do the small issig tactics by hand, and only use this tactic for >= 5 fields or something.)

Okay, now onto the magic. How do we know which field is the right one? Well, there's only one answer that lets us prove the section and retraction by destruct+reflexivity, so we can let unification solve this problem for us. It's important to have destructed the record variable in each of the pair-component evars, because unification is not (yet) smart enough to invert records for us; this is what the destruct before shelve in the inverse function generation tactic is. We cbn pr1 and pr2 to make the unification problem be completely syntactic (no need to unfold anything during unification). This is probably not strictly necessary, but seems like good form to me.

Finally, we can prove the other one of the section/retraction pair (I can never recall which is which), and the adjoint, by reflexively. (Perhaps it would be better to use exact idpath, if we want to not have to unfold reflexivity when using equivalences generated by these tactics.) *)

(** We show how the tactic works in a couple of examples. *)

Definition issig_contr (A : Type)
  : {x : A & forall y, x = y} <~> Contr A.
Proof.
  issig.
Defined.

Definition issig_equiv (A B : Type)
  : {f : A -> B & IsEquiv f} <~> Equiv A B.
Proof.
  issig.
Defined.

Definition issig_isequiv {A B : Type} (f : A -> B)
  : {g : B -> A & {r : Sect g f & { s : Sect f g
    & forall x : A, r (f x) = ap f (s x)}}}
  <~> IsEquiv f.
Proof.
  issig.
Defined.
