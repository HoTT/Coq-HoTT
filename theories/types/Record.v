(* -*- mode: coq; mode: visual-line -*- *)
(** * Techniques for applying theorems from [Sigma.v] to record types. *)

Require Import Overture Contractible Equivalences types.Sigma types.Forall.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** The following tactic proves automatically that a two-component record type is equivalent to a Sigma-type.  Specifically, it proves a goal that looks like
<<
   { x : A & B x } <~> Some_Record
>>
   You have to give it the record constructor and the two record projections as arguments (it has no way to guess what those might be). *)

Ltac issig1 build pr1 pr2 :=
  (** What follows is is a bit of Ltac black magic.  We want to give the explicit proof term except for the coherence cell and define that cell afterwards with tactics.  We could do this by calling the tactic [refine] and leaving a placeholder [_] in the term.  However, the following trick seems to be noticably faster, at least when we move on to the 3- and 4-variable versions below. *)
  let T := fresh in
  let t := fresh in
  (** We introduce a new existential variable [T:Type], assert an element [t:T], and substitute away the definition of [T] in the context. *)
  evar (T : Type); assert (t : T); subst T;
  (** At this point we have two subgoals.  The first is to construct [t] whose type is utterly unknown (an existential variable), and the second is to prove our desired equivalence under the additional assumption of [t] (with its unknown type).  We proceed to ignore the first subgoal and supply a term proving the second one, with [t] standing in for the coherence cell.  This enables Coq to infer what the type of [t] must be.  Since existential variables are the only way that Coq can communicate typing information between subgoals, this information then propagates over to the first subgoal. *)
  [ |
  (** Just in case the user supplied a goal which only *reduces* to one of the desired form. *)
  hnf;
  (** Extract the fibration of which our Sigma-type is the total space, as well as the record type. We pull the terms out of a [match], rather than leaving everything inside the [match] because this gives us better error messages. *)
  let fibration := match goal with |- sigT ?fibration <~> ?record => constr:(fibration) end in
  let record := match goal with |- sigT ?fibration <~> ?record => constr:(record) end in
  exact (BuildEquiv (sigT fibration) record (fun u => build u.1 u.2)
    (BuildIsEquiv (sigT fibration) record (fun u => build u.1 u.2)
      (fun v => existT fibration (pr1 v) (pr2 v))
      (fun v =>
        let (v1,v2) as v' return (build (pr1 v') (pr2 v') = v')
          := v in 1)
      (fun u =>
        match u return
          (existT fibration
            (pr1 (build (u.1) (u.2)))
            (pr2 (build (u.1) (u.2))))
          = u with
          existT x y => 1
        end)
      (** We *could* actually give an explicit proof term for the coherence cell.  Here it is:
<<
      (fun u => match u return
                  ((let (v1,v2) as v' return (build (pr1 v') (pr2 v') = v')
                      := (build u.1 u.2) in 1) =
                  ap (fun u => build u.1 u.2)
                    (match u return
                       (existT fibration
                         (pr1 (build (u.1) (u.2)))
                         (pr2 (build (u.1) (u.2))))
                       = u with
                       existT x y => 1
                     end)) with
                  existT x y => 1
                end)
>>
      However, for the 3- and 4-variable versions, giving the explicit proof term seems to actually *slow down* the tactic.  Perhaps it is because Coq has to infer more implicit arguments, or perhaps this is because there is no oppertunity to run [simpl]  Thus, we proceed instead by supplying the term [t] whose type is an existential variable. *)
      t)) ];
  (** Now we are left only with the one subgoal to prove [t], and at this point we know its type.  The proof basically amounts to destructing a pair.  First, though, we instruct Coq to incorporate learned values of all unification variables.  This speeds things up significantly (although again, the difference is really only noticable for the 3- and 4-variable versions below). *)
  instantiate;
  simpl;
  let x := fresh in intro x;
  destruct x as [? ?];
  exact 1.

(** This allows us to use the same notation for the tactics with varying numbers of variables. *)
Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) :=
  issig1 build pr1 pr2.

(** We show how the tactic works in a couple of examples. *)

Definition issig_contr (A : Type)
  : { x : A & forall y:A, x = y } <~> Contr A.
Proof.
  issig (BuildContr A) (@center A) (@contr A).
Defined.

Definition issig_equiv (A B : Type)
  : { f : A -> B & IsEquiv f } <~> Equiv A B.
Proof.
  issig (BuildEquiv A B) (equiv_fun A B) (equiv_isequiv A B).
Defined.

(** Here is a version of the [issig] tactic for three-component records, which proves goals that look like
<<
   { x : A & { y : B x & C x y } } <~> Some_Record.
>>
   It takes the record constructor and its three projections as arguments, as before. *)

(** First we build a version that doesn't go through adjointification.  By applying [symmetry] first, we can speed up the coherence proof by about two orders of magnitude (in the case of [issig3], from around 24 seconds to around 0.3 seconds, plus a reduction from 16 seconds to 0.8 seconds in the [Defined].  However, this still is too slow, so we will eventually adjointify first.  The speed boost comes from the fact that we are [destruct]ing a record rather than a sigma type; when primitive projections land in Coq, hopefully this won't make so much of a difference. *)

(** The harness takes a tactical to make the [IsEquiv] proof; when proving [A <~> B], the tactical is given [A] and [B], and should return a function that takes the coherence proof [eisadj] and gives back an [IsEquiv]. *)
Ltac issig_harness make_is_equiv_tac :=
  let T := fresh in
  let t := fresh in
  evar (T : Type); assert (t : T); subst T;
  [
  | hnf;
    apply symmetry;
    let A := match goal with |- ?A <~> ?B => constr:(A) end in
    let B := match goal with |- ?A <~> ?B => constr:(B) end in
    let isequiv_proof := make_is_equiv_tac A B in
    exact (@BuildEquiv
             _ _ _
             (isequiv_proof t)) ];
  instantiate;
  simpl;
  let x := fresh in
  intro x;
    destruct x;
    exact 1.

(** Now we actually build the non-adjointified version.  We use some notations to provide a cleaner-looking tactic.  We name it [_exact] because the section and retraction are not adjusted, as they are in adjointification. *)
Ltac issig2_transparent build pr1 pr2 pr3 :=
  issig_harness
    ltac:(fun A B =>
            constr:(@BuildIsEquiv
                      A B
                      (fun v => (pr1 v; (pr2 v; pr3 v)))
                      (fun u => build u.1 u.2.1 u.2.2)
                      eta2_sigma
                      (fun v =>
                         let (v1,v2,v3) as v' return (build (pr1 v') (pr2 v') (pr3 v') = v')
                             := v in 1))).

(** Now we build the adjointified version. *)
Ltac issig2 build pr1 pr2 pr3 :=
  exact (equiv_adjointify
           (fun u => build u.1 u.2.1 u.2.2)
           (fun v => (pr1 v; (pr2 v; pr3 v)))
           (fun v =>
              let (v1,v2,v3) as v' return (build (pr1 v') (pr2 v') (pr3 v') = v')
                  := v in 1)
           eta2_sigma).

Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) :=
  issig2 build pr1 pr2 pr3.

(** And a similar version for four-component records.  It should be clear how to extend the pattern indefinitely. *)
Ltac issig3_transparent build pr1 pr2 pr3 pr4 :=
  issig_harness
    ltac:(fun A B =>
            constr:(@BuildIsEquiv
                      A B
                      (fun v => (pr1 v; (pr2 v; (pr3 v; pr4 v))))
                      (fun u => build u.1 u.2.1 u.2.2.1 u.2.2.2)
                      eta3_sigma
                      (fun v =>
                         let (v1,v2,v3,v4) as v' return (build (pr1 v') (pr2 v') (pr3 v') (pr4 v') = v')
                             := v in 1))).

Ltac issig3 build pr1 pr2 pr3 pr4 :=
  exact (equiv_adjointify
           (fun u => build u.1 u.2.1 u.2.2.1 u.2.2.2)
           (fun v => (pr1 v; (pr2 v; (pr3 v; pr4 v))))
           (fun v =>
              let (v1,v2,v3,v4) as v' return (build (pr1 v') (pr2 v') (pr3 v') (pr4 v') = v')
                  := v in 1)
           eta3_sigma).

Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) constr(pr4) :=
  issig3 build pr1 pr2 pr3 pr4.


(** The record [IsEquiv] has four components, so [issig3] can prove that it is equivalent to an iterated Sigma-type. *)

Definition issig_isequiv_transparent {A B : Type} (f : A -> B) :
  { g:B->A & { r:Sect g f & { s:Sect f g & forall x : A, r (f x) = ap f (s x) }}}
  <~> IsEquiv f.
Proof.
  issig3_transparent (BuildIsEquiv A B f) (@equiv_inv A B f) (@eisretr A B f)
    (@eissect A B f) (@eisadj A B f).
Defined.

Definition issig_isequiv {A B : Type} (f : A -> B) :
  { g:B->A & { r:Sect g f & { s:Sect f g & forall x : A, r (f x) = ap f (s x) }}}
  <~> IsEquiv f.
Proof.
  issig (BuildIsEquiv A B f) (@equiv_inv A B f) (@eisretr A B f)
    (@eissect A B f) (@eisadj A B f).
Defined.
