(* -*- mode: coq; mode: visual-line -*- *)
(** Techniques for applying theorems from Sigma.v to record types. *)

Require Import Overture Contractible Equivalences Sigma Forall.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** The following tactic proves automatically that a two-component record type is equivalent to a Sigma-type.  You have to give it the fibration that the Sigma-type is the total space of, the record constructor, and the two record projections as arguments. *)

Ltac issig fibration record pr1 pr2 :=
  refine (BuildEquiv _ _ (fun u => record u.1 u.2)
    (BuildIsEquiv _ _ _
      (fun v => existT fibration (pr1 v) (pr2 v))
      (fun v =>
        let (v1,v2) as v' return (record (pr1 v') (pr2 v') = v')
          := v in 1)
      (fun u =>
        match u return
          (existT fibration
            (pr1 (record (u.1) (u.2)))
            (pr2 (record (u.1) (u.2))))
          = u with
          existT x y => 1
        end)
      _));
  let v := fresh "v" in
    intros v; destruct v; exact 1.

(** We show how it works in a couple of examples. *)

Definition issig_contr (A : Type)
  : { x : A & forall y:A, x = y } <~> Contr A.
Proof.
  issig (fun x:A => forall y, x=y) (BuildContr A) (@center A) (@contr A).
Defined.

Definition issig_equiv (A B : Type)
  : { f : A -> B & IsEquiv f } <~> Equiv A B.
Proof.
  issig (@IsEquiv A B) (BuildEquiv A B) (equiv_fun A B) (equiv_isequiv A B).
Defined.

(** The function [equiv_rect] says that if [f : A -> B] is an equivalence, and we have a fibration over [B] which has a section once pulled back to [A], then it has a section over all of [B].  *)

Generalizable Variables A B f.

Definition equiv_rect `{IsEquiv A B f} (P : B -> Type)
  : (forall x:A, P (f x)) -> forall y:B, P y
  := fun g y => transport P (eisretr f y) (g (f^-1 y)).

Arguments equiv_rect {A B} f {_} P _ _.

(** Using [equiv_rect], we define a little tactic which introduces a variable and simultaneously substitutes it along an equivalence. *)

Ltac equiv_intro E x :=
  match goal with
    | |- forall y, @?Q y =>
      refine (equiv_rect E Q _); intros x
  end.

(** Combining [issig_contr] and [equiv_intro], we can transfer the problem of showing contractibility of [Contr A] to the equivalent problem of contractibility of a certain Sigma-type, in which case we can apply the general path-construction functions. *)

Instance contr_contr `{Funext} (A : Type)
  : Contr A -> Contr (Contr A).
Proof.
  intros c; exists c; generalize c.
  equiv_intro (issig_contr A) c'.
  equiv_intro (issig_contr A) d'.
  refine (ap _ _).
  refine (path_sigma _ _ _ ((contr (c'.1))^ @ contr (d'.1)) _).
  refine (path_forall _ _ _); intros x.
  apply path2_contr.
Qed.

(** Here is a version of the [issig] tactic for three-component records.  In this case, the first argument is a doubly dependent type of the form [forall (x:A) (y:B x), C x y].  Next comes the record constructor and the three projections, as before. *)

Ltac issig2 fibration record pr1 pr2 pr3 :=
  refine (BuildEquiv _ _ (fun u => record u.1 u.2.1 u.2.2)
    (BuildIsEquiv _ _ _
      (fun v =>
        (existT (fun x => sigT (fibration x)) (pr1 v)
          (existT (fibration (pr1 v)) (pr2 v) (pr3 v))))
      (fun v =>
        let (v1,v2,v3) as v' return (record (pr1 v') (pr2 v') (pr3 v') = v')
          := v in 1)
      (fun u =>
        match u return
          (existT _
            (pr1 (record u.1 u.2.1 u.2.2))
            (existT (fibration u.1)
              (pr2 (record u.1 u.2.1 u.2.2))
              (pr3 (record u.1 u.2.1 u.2.2))))
          = u with
          existT x (existT y z) => 1
        end)
      _));
  let v := fresh "v" in
    intros v; destruct v; exact 1.

(** And a similar version for four-component records.  The pattern should be clear. *)

Ltac issig3 fibration record pr1 pr2 pr3 pr4 :=
  refine (BuildEquiv _ _ (fun u => (record u.1 u.2.1 u.2.2.1 u.2.2.2))
    (BuildIsEquiv _ _ _
      (fun v =>
        (existT (fun x => sigT (fun y => sigT (fibration x y))) (pr1 v)
          (existT (fun y => sigT (fibration (pr1 v) y)) (pr2 v)
            (existT (fibration (pr1 v) (pr2 v)) (pr3 v) (pr4 v)))))
      (fun v =>
        let (v1,v2,v3,v4) as v'
          return (record (pr1 v') (pr2 v') (pr3 v') (pr4 v') = v')
          := v in 1)
      (fun u =>
        match u return
          (existT _
            (pr1 (record u.1 u.2.1 u.2.2.1 u.2.2.2))
            (existT _
              (pr2 (record u.1 u.2.1 u.2.2.1 u.2.2.2))
              (existT (fibration u.1 u.2.1)
                (pr3 (record u.1 u.2.1 u.2.2.1 u.2.2.2))
                (pr4 (record u.1 u.2.1 u.2.2.1 u.2.2.2)))))
          = u with
          existT x (existT y (existT z w)) => 1
        end)
      _));
  let v := fresh "v" in
    intros v; destruct v; exact 1.

(** The record [IsEquiv] has four components, so [issig3] can prove that it is equivalent to an iterated Sigma-type. *)

Definition issig3_isequiv {A B : Type} (f : A -> B) :
  { g:B->A & { r:Sect g f & { s:Sect f g & forall x : A, r (f x) = ap f (s x) }}}
  <~> IsEquiv f.
Proof.
  (* I'm not sure why this takes so long to complete.  Is it having a hard time inferring the type of the placeholder? *)
  issig3 (fun (g:B->A) (r:Sect g f) (s:Sect f g) => forall x : A, r (f x) = ap f (s x))
    (BuildIsEquiv A B f) (@equiv_inv A B f) (@eisretr A B f) (@eissect A B f) (@eisadj A B f).
Defined.

(** Here are the beginnings of a proof that [IsEquiv f] is an h-proposition, demonstrating again how [issig3_isequiv] and [equiv_intro] reduce the problem from one involving records to one involving Sigma-types. *)

Definition prop_isequiv `{Funext} {A B : Type} (f : A -> B) (e1 e2 : IsEquiv f)
  : e1 = e2.
Proof.
  revert e2; generalize e1.
  equiv_intro (issig3_isequiv f) h1.
  equiv_intro (issig3_isequiv f) h2.
  refine (ap _ _).
  destruct h1 as [g1 [r1 [s1 a1]]].
  destruct h2 as [g2 [r2 [s2 a2]]].
  refine (path_sigma' _
    ((path_forall _ _ (fun b => ap g1 (r2 b)))^
      @ (path_forall _ _ (fun b => s1 (g2 b)))) _).
  rewrite transport_sigma; simpl.
  (* Getting pretty nasty. *)
Abort.
