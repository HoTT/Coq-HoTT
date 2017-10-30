(* -*- mode: coq; mode: visual-line -*- *)
(** * Techniques for applying theorems from [Sigma.v] to record types. *)

Require Import HoTT.Basics.
Require Import Types.Sigma Types.Forall.
Local Open Scope path_scope.


(** The following tactic proves automatically that a two-component record type is equivalent to a Sigma-type.  Specifically, it proves a goal that looks like
<<
   { x : A & B x } <~> Some_Record
>>
   You have to give it the record constructor and the two record projections as arguments (it has no way to guess what those might be). *)

Ltac issig2 build pr1 pr2 :=
  (** Just in case the user supplied a goal which only *reduces* to one of the desired form. *)
  hnf;
  (** Extract the fibration of which our Sigma-type is the total space, as well as the record type. We pull the terms out of a [match], rather than leaving everything inside the [match] because this gives us better error messages. *)
  let fibration := match goal with |- sigT ?fibration <~> ?record => constr:(fibration) end in
  let record := match goal with |- sigT ?fibration <~> ?record => constr:(record) end in
  exact (BuildEquiv _ _ _
                    (BuildIsEquiv
                       (sigT fibration) record
                       (fun u => build u.1 u.2)
                       (fun v => existT fibration (pr1 v) (pr2 v))
                       (fun v => let (v1,v2) as v' return (build (pr1 v') (pr2 v') = v') := v in 1)
                       eta_sigma
                       (** Since [sigT] is primitve, we get judgmental η, and so we can just use the identity here *)
                       (fun _ => 1))).

(** This allows us to use the same notation for the tactics with varying numbers of variables. *)
Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) :=
  issig2 build pr1 pr2.

(** We show how the tactic works in a couple of examples. *)

Definition issig_contr (A : Type)
  : { x : A & forall y:A, x = y } <~> Contr A.
Proof.
  issig (BuildContr A) (@center A) (@contr A).
Defined.

Definition issig_equiv (A B : Type)
  : { f : A -> B & IsEquiv f } <~> Equiv A B.
Proof.
  issig (BuildEquiv A B) (@equiv_fun A B) (@equiv_isequiv A B).
Defined.

(** Here is a version of the [issig] tactic for three-component records, which proves goals that look like
<<
   { x : A & { y : B x & C x y } } <~> Some_Record.
>>
   It takes the record constructor and its three projections as arguments, as before. *)

Ltac issig3 build pr1 pr2 pr3 :=
  hnf;
  let A := match goal with |- ?A <~> ?B => constr:(A) end in
  let B := match goal with |- ?A <~> ?B => constr:(B) end in
  exact (BuildEquiv _ _ _
                    (BuildIsEquiv
                       A B
                       (fun u => build u.1 u.2.1 u.2.2)
                       (fun v => (pr1 v; pr2 v; pr3 v))
                       (fun v => let (v1, v2, v3) as v' return (build (pr1 v') (pr2 v') (pr3 v') = v') := v in 1)
                       eta2_sigma
                       (fun _ => 1))).

Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) :=
  issig3 build pr1 pr2 pr3.

(** And a similar version for four-component records.  It should be clear how to extend the pattern indefinitely. *)
Ltac issig4 build pr1 pr2 pr3 pr4 :=
  hnf;
  let A := match goal with |- ?A <~> ?B => constr:(A) end in
  let B := match goal with |- ?A <~> ?B => constr:(B) end in
  exact (BuildEquiv _ _ _
                    (BuildIsEquiv
                       A B
                       (fun u => build u.1 u.2.1 u.2.2.1 u.2.2.2)
                       (fun v => (pr1 v; pr2 v; pr3 v; pr4 v))
                       (fun v => let (v1, v2, v3, v4) as v' return (build (pr1 v') (pr2 v') (pr3 v') (pr4 v') = v') := v in 1)
                       eta3_sigma
                       (fun _ => 1))).

Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) constr(pr4) :=
  issig4 build pr1 pr2 pr3 pr4.


Ltac issig5 build pr1 pr2 pr3 pr4 pr5 :=
  hnf;
  let A := match goal with |- ?A <~> ?B => constr:(A) end in
  let B := match goal with |- ?A <~> ?B => constr:(B) end in
  exact (BuildEquiv _ _ _
                    (BuildIsEquiv
                       A B
                       (fun u => build u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2)
                       (fun v => (pr1 v; pr2 v; pr3 v; pr4 v ; pr5 v))
                       (fun v => let (v1, v2, v3, v4, v5) as v' return (build (pr1 v') (pr2 v') (pr3 v') (pr4 v') (pr5 v') = v') := v in 1)
                       (fun u => 1)
                       (fun _ => 1))).

Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) constr(pr4) constr(pr5) :=
  issig5 build pr1 pr2 pr3 pr4 pr5.

Ltac issig6 build pr1 pr2 pr3 pr4 pr5 pr6 :=
  hnf;
  let A := match goal with |- ?A <~> ?B => constr:(A) end in
  let B := match goal with |- ?A <~> ?B => constr:(B) end in
  exact (BuildEquiv _ _ _
                    (BuildIsEquiv
                       A B
                       (fun u => build u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2.1 u.2.2.2.2.2)
                       (fun v => (pr1 v; pr2 v; pr3 v; pr4 v ; pr5 v ; pr6 v))
                       (fun v => let (v1, v2, v3, v4, v5, v6) as v' return (build (pr1 v') (pr2 v') (pr3 v') (pr4 v') (pr5 v') (pr6 v') = v') := v in 1)
                       (fun u => 1)
                       (fun _ => 1))).

Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) constr(pr4) constr(pr5) constr(pr6) :=
  issig6 build pr1 pr2 pr3 pr4 pr5 pr6.

(** The record [IsEquiv] has four components, so [issig4] can prove that it is equivalent to an iterated Sigma-type. *)

Definition issig_isequiv {A B : Type} (f : A -> B) :
  { g:B->A & { r:Sect g f & { s:Sect f g & forall x : A, r (f x) = ap f (s x) }}}
  <~> IsEquiv f.
Proof.
  issig (BuildIsEquiv A B f) (@equiv_inv A B f) (@eisretr A B f)
        (@eissect A B f) (@eisadj A B f).
Defined.
