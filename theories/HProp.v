(** * HPropositions *)

Require Import Overture Contractible Equivalences Trunc.
Require Import types.Forall types.Sigma types.Prod types.Record.

Local Open Scope equiv_scope.
Local Open Scope path_scope.

(** ** Facts about [IsHProp] *)

(** Maybe this should go to a separate file? *)

Generalizable Variables A B.

(** An inhabited proposition is contractible.
   This is not an [Instance] because it causes infinite loops.
   *)
Lemma contr_inhabited_hprop (A : Type) `{H : IsHProp A} (x : A)
  : Contr A.
Proof.
  exists x.
  intro y.
  apply center, H.
Defined.

(** If inhabitation implies contractibility, then we have an h-proposition.  We probably won't often have a hypothesis of the form [A -> Contr A], so we make sure we give priority to other instances. *)
Instance hprop_inhabited_contr (A : Type) : (A -> Contr A) -> IsHProp A | 10000.
Proof.
  intros H x y.
  pose (C := H x).
  apply contr_paths_contr.
Defined.

(** If a type is contractible, then so is its type of contractions.
    Using [issig_contr] and the [equiv_intro] tactic, we can transfer this to the equivalent problem of contractibility of a certain Sigma-type, in which case we can apply the general path-construction functions. *)
Instance contr_contr `{Funext} (A : Type)
  : Contr A -> Contr (Contr A) | 100.
Proof.
  intros c; exists c; generalize c.
  equiv_intro (issig_contr A) c'.
  equiv_intro (issig_contr A) d'.
  refine (ap _ _).
  refine (path_sigma _ _ _ ((contr (c'.1))^ @ contr (d'.1)) _).
  refine (path_forall _ _ _); intros x.
  apply path2_contr.
Qed.

(** This provides the base case in a proof that truncatedness is a proposition. *)
Instance hprop_trunc `{Funext} (n : trunc_index) (A : Type)
  : IsHProp (IsTrunc n A) | 0.
Proof.
  apply hprop_inhabited_contr.
  revert A.
  induction n as [| n I]; unfold IsTrunc; simpl.
  - intros A ?.
    exact _.
  - intros A AH1.
    exists AH1.
    intro AH2.
    apply path_forall; intro x.
    apply path_forall; intro y.
    apply @path_contr.
    apply I, AH1.
Qed.

(** Chracterization of [IsHProp] in terms of all points being connected by paths. *)

Theorem allpath_hprop `{H : IsHProp A} : forall x y : A, x = y.
Proof.
  apply H.
Defined.

Theorem hprop_allpath (A : Type) : (forall (x y : A), x = y) -> IsHProp A.
  intros H x y.
  pose (C := BuildContr A x (H x)).
  apply contr_paths_contr.
Defined.

Theorem equiv_hprop_allpath `{Funext} (A : Type)
  : IsHProp A <~> (forall (x y : A), x = y).
Proof.
  apply (equiv_adjointify (@allpath_hprop A) (@hprop_allpath A));
  (* The proofs of the two homotopies making up this equivalence are almost identical.  First we start with a thing [f]. *)
    intro f;
  (* Then we apply funext a couple of times *)
    apply path_forall; intro x;
    apply path_forall; intro y;
  (* Now we conclude that [A] is contractible *)
    try pose (C := BuildContr A x (f x));
    try pose (D := contr_inhabited_hprop A x);
  (* And conclude because we have a path in a contractible space. *)
    apply path_contr.
Defined.

(** Two propositions are equivalent as soon as there are maps in both
   directions. *)

Definition equiv_iff_hprop `{IsHProp A} `{IsHProp B}
  : (A -> B) -> (B -> A) -> (A <~> B).
Proof.
  intros f g.
  apply (equiv_adjointify f g);
    intros ?; apply allpath_hprop.
Defined.


(** Being a contractible space is a proposition. *)

Instance hprop_contr `{Funext} (A : Type) : IsHProp (Contr A) | 0.
Proof.
  apply hprop_inhabited_contr.
  intro cA.
  exact _.
Defined.

(** Here is an alternate characterization of propositions. *)

Instance HProp_HProp `{Funext} A : IsHProp (IsHProp A) | 0
  := hprop_trunc minus_one A.

Theorem equiv_hprop_inhabited_contr `{Funext} {A}
  : IsHProp A <~> (A -> Contr A).
Proof.
  apply (equiv_adjointify (@contr_inhabited_hprop A) (@hprop_inhabited_contr A)).
  - intro ic. by_extensionality x.
    apply @path_contr. apply contr_contr. exact (ic x).
  - intro hp. by_extensionality x. by_extensionality y.
    apply @path_contr. apply contr_contr. exact (hp x y).
Defined.

(** Here are some alternate characterizations of contractibility. *)
Theorem equiv_contr_inhabited_hprop `{Funext} {A}
  : Contr A <~> A * IsHProp A.
Proof.
  assert (f : Contr A -> A * IsHProp A).
    intro P. split. exact (@center _ P). apply @trunc_succ. exact P.
  assert (g : A * IsHProp A -> Contr A).
    intros [a P]. apply (@contr_inhabited_hprop _ P a).
  refine (@equiv_iff_hprop _ _ _ _ f g).
  apply hprop_inhabited_contr; intro p.
  apply @contr_prod.
  exact (g p). apply (@contr_inhabited_hprop _ _ (snd p)).
Defined.

Theorem equiv_contr_inhabited_allpath `{Funext} {A}
  : Contr A <~> A * forall (x y : A), x = y.
Proof.
  apply transitivity with (y := A * IsHProp A).
  apply equiv_contr_inhabited_hprop.
  apply equiv_functor_prod'. apply equiv_idmap. apply equiv_hprop_allpath.
Defined.

(** The type of Propositions *)
(** We use both the Sigma type of propositions and the record type of propositions.
The latter allows us to automatically find a proof that a type is a proposition.

At first, we may just want to look at the record type hProp and (sigT IsHProp).
However, the generalization with total2 will allow us to define two coercions.
So, a theorem about one type can be applied to the other. It's not magic, but it is convenient.

We make total2 a Class so that sig_to_total2 can be an instance.
Also, this seems to be convenient to make tp1 and tp2 into coercions.

We should explore this some more and then apply this to other record types.

For now, it allows us to finish the proofs in epi.v which explicitly use the type 
hProp of all propositions, as opposed to just individual propositions.

More experiments with Canonical Structures (for Equivs) can be found in the deprecated
ssreflect branch.
*)

Class total2 {T} (P: T -> Type) := tpair2 { tp1 :> T ; tp2 :> P tp1 }.
Implicit Arguments tpair2 [T P] .
Lemma total2_to_sig {T} (P: T -> Type): total2 P -> sigT P.
intros [p1 p2]. exact (p1;p2).
Defined.

(** sigT will be accepted as a total2 *)
Instance sig_to_total2 {T} (P: T -> Type): sigT P -> total2 P.
intros [p1 p2]. exact {| tp1 := p1; tp2 := p2 |}.
Defined.

(** This is similar to sig_to_sigT in the stdlib *)
Coercion total2_to_sig: total2 >-> sigT.
Coercion sig_to_total2: sigT >-> total2.

Definition hProp := total2 IsHProp.
Definition hProp2Type: hProp -> Type.
intros [p3 _]. exact p3.
Defined.
(** Now we can write P-> Q for propositions *)
Coercion hProp2Type: hProp >-> Sortclass.

(* Here is a simple example.
Variable P:Type.
Variable p:(IsHProp P).
Goal hProp.
exact (P;_).*)

(** We want to find side conditions automatically. *)
Instance hProp2IsHProp (P: hProp): IsHProp P.
apply tp2.
Defined.

Hint Resolve hProp2IsHProp.

(** It is important to give the type :hProp explicitly to avoid universe inconsistencies in epi.v *)
Canonical Structure default_HProp (T:Type)(P:IsHProp T) :hProp:= (@tpair2 Type IsHProp T P).
(** In this way we can write e.g.
<<
(default_HProp Unit _)
>>
For the Unit proposition. Coq will automatically find a proof that it is a proposition.)
*)

Definition equiv_issig_total {T} {P:T->Type}
: (sigT P) <~> total2 P.
Proof.
  issig (@tpair2 T P) (@tp1 T P) (@tp2 T P).
Defined.

Definition issig_hProp:=(@equiv_issig_total Type IsHProp).