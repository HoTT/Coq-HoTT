(** * H-Set *)

Require Import Overture Contractible Equivalences Trunc HProp types.Paths types.Empty PathGroupoids.
Local Open Scope equiv_scope.
Local Open Scope path_scope.
(* Should be defined in terms of whisker and moved to PathGroupoids
Should remove the notation cancelL from PathGroupoids*)
Lemma cancel_L {A} {x y z : A} (p : x = y) (q r : y = z) : (p @ q = p @ r) -> (q = r).
Proof.
  intro a.
  induction p.
  induction r.
  path_via (idpath x @ q).
Defined.
(* Should be renamed and moved *)
Lemma ap_transport {A} {P Q : A -> Type} {x y : A} (p : x = y) (f : forall x, P x -> Q x) (z : P x) :
  f y (p # z) = (p # (f x z)).
Proof.
  by induction p.
Defined.

(** ** Facts about [HSet] *)

(** A type is a set if and only if it satisfies Axiom K. *)

Definition axiomK A := forall (x : A) (p : x = x), p = idpath x.

Definition isset_implies_axiomK {A} : HSet A -> axiomK A.
Proof.
  intros H x p.
  apply (H x x p (idpath x)).
Defined.

Instance axiomK_implies_isset {A} `{(axiomK A)}: HSet A.
Proof.
  intros x y H.
  apply @HProp_allpath.
  intros p q.
  by induction p.
Defined.

Context `{funext_dep:Funext}.

(* A convenient tactic for using extensionality. *)
Ltac by_extensionality :=
  intros; unfold compose;
  match goal with 
  | [ |- ?f = ?g ] => eapply path_forall; intro;
      match goal with
        | [ |- forall (_ : prod _ _), _ ] => intros [? ?]
        | [ |- forall (_ : sigT _ _), _ ] => intros [? ?]
        | _ => intros
    end;
    simpl;
    auto
  end.

(*
Theorem isset_equiv_axiomK {A} :
  (is_trunc 0 A) <~> (forall (x : A) (p : x = x), p = idpath x).
Proof.
  apply (equiv_adjointify (@isset_implies_axiomK A) (@axiomK_implies_isset A)).
   intro H. by_extensionality. by_extensionality. eapply path_contr.
(*  eapply (axiomK_implies_isset A H).*)
  intro H. by_extensionality.
  by_extensionality.
  eapply allpath_HProp. (* apply prop_path.*)
  apply isprop_isprop. (* should follow from a general lemma on truncations *)
Defined.
*)

(*
Instance axiomK_isprop A : HProp (axiomK A).
Proof.
  exists. apply @hlevel_equiv with (A := is_hset A).
  apply isset_equiv_axiomK.
  apply hlevel_isprop.
Defined.
*)
(*
Theorem set_path2 {A} `{HSet A} {x y : A} (p q : x = y):
  p = q.
Proof.
  set (@Contr_path _ p q).
  cbv in H.
  assert (P:=(p=q)).  Locate Contr_path.

  apply prop_inhabited_contr.
  cbv. cbv in H.
  apply H.
  assumption.
Defined.
*)

(** Recall that axiom K says that any self-path is homotopic to the
   identity path.  In particular, the identity path is homotopic to
   itself.  The following lemma says that the endo-homotopy of the
   identity path thus specified is in fact (homotopic to) its identity
   homotopy (whew!).  *)
Local Open Scope path_scope.

(* This proof is still broken 
Lemma axiomK_idpath {A} (x : A) (K : axiomK A) :
  K x (idpath x) = idpath (idpath x).
Proof. 
  set (qq := apD (K x) (K x (idpath x))).
  set (q2 := (trans_is_concat_opp (K x (idpath x)) (K x (idpath x)) @ qq)).
  !
  path_via (!! K x (idpath x)).
  path_via (! idpath (idpath x)).
  apply concat_cancel_right with (r := K x (idpath x)).
  cancel_units.
Defined.*)

(** Any type with "decidable equality" is a set. *)

Definition decidable_paths (A : Type) :=
  forall (x y : A), (x = y) + ((x = y) -> Empty).

(* Usually this lemma would be proved with [discriminate], but
   unfortunately that tactic is hardcoded to work only with Coq's
   [Prop]-valued equality. *)
Definition inl_injective {A B : Type} {x y : A} (p : inl B x = inl B y) : x = y :=
  (@transport _ (fun (s : A + B) => x = (match s with inl a => a | inr b => x end)) _ _ p (idpath x)).

Theorem decidable_implies_axiomK {A : Type} : @decidable_paths A -> @axiomK A.
Proof.
  intro d.
  intros x p.
  set (qp := apD (d x) p).
  set (q := d x x) in *.
  clearbody qp; revert qp.
  destruct q as [q | q'].
    intro qp0; apply (cancel_L q). path_via (transport _ p q).
      symmetry; apply transport_paths_r.
      path_via q. apply @inl_injective with (B := (x = x -> Empty)).
      exact ((ap_transport p (fun y => @inl (x = y) (x = y -> Empty)) q) @ qp0).
  induction (q' p).
Defined.

Corollary decidable_isset {A : Type} : @decidable_paths A -> @is_trunc 0 A.
Proof.
  intro.
  by apply @axiomK_implies_isset, @decidable_implies_axiomK.
Defined.