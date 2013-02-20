(* -*- mode: coq; mode: visual-line -*- *)
(** Techniques for applying theorems from Sigma.v to record types. *)

Require Import Overture Contractible Equivalences Sigma Forall.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** The following tactic proves automatically that a two-component record type is equivalent to a Sigma-type.  Specifically, it proves a goal that looks like

   { x : A & B x } <~> Some_Record

   You have to give it the record constructor and the two record projections as arguments (it has no way to guess what those might be). *)

Ltac issig1 build pr1 pr2 :=
  (* What follows is is a bit of Ltac black magic.  We want to give the explicit proof term except for the coherence cell and define that cell afterwards with tactics.  We could do this by calling the tactic [refine] and leaving a placeholder [_] in the term.  However, the following trick seems to be noticably faster, at least when we move on to the 3- and 4-variable versions below. *)
  let T := fresh in
  let t := fresh in
  (* We introduce a new existential variable [T:Type], assert an element [t:T], and substitute away the definition of [T] in the context. *)
  evar (T : Type); assert (t : T); subst T;
  (* At this point we have two subgoals.  The first is to construct [t] whose type is utterly unknown (an existential variable), and the second is to prove our desired equivalence under the additional assumption of [t] (with its unknown type).  We proceed to ignore the first subgoal and supply a term proving the second one, with [t] standing in for the coherence cell.  This enables Coq to infer what the type of [t] must be.  Since existential variables are the only way that Coq can communicate typing information between subgoals, this information then propagates over to the first subgoal. *)
  [ |
  (* Just in case the user supplied a goal which only *reduces* to one of the desired form. *)
  hnf;
  (* Extract the fibration of which our Sigma-type is the total space, as well as the record type. *)
  match goal with | [ |- sigT ?fibration <~> ?record ] =>
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
      (* We *could* actually give an explicit proof term for the coherence cell.  Here it is:

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

      However, for the 3- and 4-variable versions, giving the explicit proof term seems to actually *slow down* the tactic.  Perhaps it is because Coq has to infer more implicit arguments.  Thus, we proceed instead by supplying the term [t] whose type is an existential variable. *)
      t))
  end ];
  (* Now we are left only with the one subgoal to prove [t], and at this point we know its type.  The proof basically amounts to destructing a pair.  First, though, we instruct Coq to incorporate learned values of all unification variables.  This speeds things up significantly (although again, the difference is really only noticable for the 3- and 4-variable versions below). *)
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

   { x : A & { y : B x & C x y } } <~> Some_Record.

   It takes the record constructor and its three projections as arguments, as before. *)

Ltac issig2 build pr1 pr2 pr3 :=
  let T := fresh in
  let t := fresh in
  evar (T : Type); assert (t : T); subst T;
  [ | 
  hnf; match goal with
         | [ |- sigT (fun u1 => sigT (@?fibration u1)) <~> ?record ] =>
  exact (BuildEquiv (sigT (fun u1 => sigT (fibration u1))) record
                    (fun u => build u.1 u.2.1 u.2.2)
    (BuildIsEquiv (sigT (fun u1 => sigT (fibration u1))) record
      (fun u => build u.1 u.2.1 u.2.2)
      (fun v =>
        (existT (fun x => sigT (fibration x)) (pr1 v)
          (existT (fibration (pr1 v)) (pr2 v) (pr3 v))))
      (fun v =>
        let (v1,v2,v3) as v' return (build (pr1 v') (pr2 v') (pr3 v') = v')
          := v in 1)
      (fun u =>
        match u return
          (existT (fun u2 => sigT (fibration u.1 u2))
            (pr1 (build u.1 u.2.1 u.2.2))
            (existT (fibration u.1)
              (pr2 (build u.1 u.2.1 u.2.2))
              (pr3 (build u.1 u.2.1 u.2.2))))
          = u with
          existT x (existT y z) => 1
        end)
      t))
  end ];
  instantiate;
  simpl;
  let x := fresh in intro x;
  destruct x as [? [? ?]];
  exact 1.

Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) :=
  issig2 build pr1 pr2 pr3.

(** And a similar version for four-component records.  It should be clear how to extend the pattern indefinitely. *)

Ltac issig3 build pr1 pr2 pr3 pr4 :=
  let T := fresh in
  let t := fresh in
  evar (T : Type); assert (t : T); subst T;
  [ | 
  hnf; match goal with
         | [ |- sigT (fun u1 => sigT (fun u2 => sigT (@?fibration u1 u2)))
                <~> ?record ] =>
  exact (BuildEquiv (sigT (fun u1 => sigT (fun u2 => sigT (fibration u1 u2))))
                    record
                    (fun u => (build u.1 u.2.1 u.2.2.1 u.2.2.2))
    (BuildIsEquiv (sigT (fun u1 => sigT (fun u2 => sigT (fibration u1 u2)))) record
      (fun u => (build u.1 u.2.1 u.2.2.1 u.2.2.2))
      (fun v =>
        (existT (fun x => sigT (fun y => sigT (fibration x y))) (pr1 v)
          (existT (fun y => sigT (fibration (pr1 v) y)) (pr2 v)
            (existT (fibration (pr1 v) (pr2 v)) (pr3 v) (pr4 v)))))
      (fun v =>
        let (v1,v2,v3,v4) as v'
          return (build (pr1 v') (pr2 v') (pr3 v') (pr4 v') = v')
          := v in 1)
      (fun u =>
        match u return
          (existT (fun u1 => sigT (fun u2 => sigT (fibration u1 u2)))
            (pr1 (build u.1 u.2.1 u.2.2.1 u.2.2.2))
            (existT (fun u2 => sigT (fibration u.1 u2))
              (pr2 (build u.1 u.2.1 u.2.2.1 u.2.2.2))
              (existT (fibration u.1 u.2.1)
                (pr3 (build u.1 u.2.1 u.2.2.1 u.2.2.2))
                (pr4 (build u.1 u.2.1 u.2.2.1 u.2.2.2)))))
          = u with
          existT x (existT y (existT z w)) => 1
        end)
      t))
  end ];
  instantiate;
  simpl;
  let x := fresh in intro x;
  destruct x as [? [? [? ?]]];
  exact 1.

Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) constr(pr4) :=
  issig3 build pr1 pr2 pr3 pr4.

(** The record [IsEquiv] has four components, so [issig3] can prove that it is equivalent to an iterated Sigma-type. *)

Definition issig_isequiv {A B : Type} (f : A -> B) :
  { g:B->A & { r:Sect g f & { s:Sect f g & forall x : A, r (f x) = ap f (s x) }}}
  <~> IsEquiv f.
Proof.
  issig (BuildIsEquiv A B f) (@equiv_inv A B f) (@eisretr A B f)
    (@eissect A B f) (@eisadj A B f).
Defined.
