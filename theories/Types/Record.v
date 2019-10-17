(* -*- mode: coq; mode: visual-line -*- *)
(** * Techniques for applying theorems from [Sigma.v] to record types. *)

Require Import HoTT.Basics.
Require Import Types.Sigma Types.Forall.
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

Local Ltac require_as_test_cps require if_yes if_no :=
  let res := match constr:(Set) with
             | _ => let __ := match constr:(Set) with _ => require () end in
                    ltac:(if_yes)
             | _ => ltac:(if_no)
             end in res ().

Local Ltac peel_evars term :=
  lazymatch term with
  | ?f ?x
    => require_as_test_cps ltac:(fun _ => has_evar x)
                                  ltac:(fun _ => peel_evars f)
                                         ltac:(fun _ => term)
  | _ => term
  end.

Local Ltac pi_to_sig ty :=
  lazymatch (eval cbv beta in ty) with
  | forall (x : ?T) (y : @?A x), @?P x y
    => let x' := fresh in
       constr:(@sigT T (fun x' : T => ltac:(let res := pi_to_sig (forall y : A x', P x' y) in exact res)))
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

(* Notation for notypeclasses refine *)
Local Tactic Notation "ntcrefine" uconstr(term) := notypeclasses refine term.

(* TODO: consider adding this and the above into Overture.v? *)
(* Analogue of rapply, erapply or serapply for notypeclasses refine *)
Local Ltac ntcrapply p :=
  ntcrefine p ||
  ntcrefine (p _) ||
  ntcrefine (p _ _) ||
  ntcrefine (p _ _ _) ||
  ntcrefine (p _ _ _ _) ||
  ntcrefine (p _ _ _ _ _) ||
  ntcrefine (p _ _ _ _ _ _) ||
  ntcrefine (p _ _ _ _ _ _ _) ||
  ntcrefine (p _ _ _ _ _ _ _ _) ||
  ntcrefine (p _ _ _ _ _ _ _ _ _) ||
  ntcrefine (p _ _ _ _ _ _ _ _ _ _) ||
  ntcrefine (p _ _ _ _ _ _ _ _ _ _ _) ||
  ntcrefine (p _ _ _ _ _ _ _ _ _ _ _ _) ||
  ntcrefine (p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  ntcrefine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  ntcrefine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

(* This can be found in Tactics.v but we reproduce it here since it is simple. *)
Local Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

Local Ltac get_builder T :=
  let x := fresh in
  let x' := fresh in
  let h := open_constr:(_) in
  let __ := constr:(fun (x : T)
                    => let x' := x in
                       ltac:(destruct x;
                             let x' := (eval cbv delta [x'] in x') in
                             let x' := head x' in
                             unify h x';
                             exact I)) in
  h.

(* A version of econstructor that doesn't resolve typeclasses. *)
Local Ltac ntceconstructor :=
  lazymatch goal with
  | [ |- ?G ] => let build := get_builder G in
                 ntcrapply build
  end.

(* Finally we can define our issig tactic: *)
Ltac issig :=
  (* First we make sure things are normalised. *)
  hnf;
  (* We get the types either side of the equivalence. *)
  let A := match goal with |- ?A <~> ?B => constr:(A) end in
  let B := match goal with |- ?A <~> ?B => constr:(B) end in
  let u := fresh "u" in
  let v := fresh "v" in
  (** We build an equivalence with 5 holes. *)
  simple notypeclasses refine  (* We don't want typeclass search running. *)
         (BuildEquiv A B _
                     (BuildIsEquiv
                        A B
                        (fun u => _)
                        (fun v => _)
                        (fun v => _)
                        (fun u => _)
                        (fun _ => _)));
  (** Going from a sigma type to a record *)
  [ let T := match goal with |- ?T => T end in
    (* let built be the constructor of T *)
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
