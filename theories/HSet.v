(** * H-Set *)
Require Import Overture Contractible Equivalences Trunc HProp types.Paths types.Empty PathGroupoids.
Local Open Scope equiv_scope.
Local Open Scope path_scope.
(* Only  axiomK_idpath below is unfinished, the cancel_units tactic is missing *)
(* Should be defined in terms of whisker and moved *)

Require Import  types.Record FunextVarieties.
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

Lemma ap_transport {A} {P Q : A -> Type} {x y : A} (p : x = y) (f : forall x, P x -> Q x) (z : P x) :
  f y (p # z) = (p # (f x z)).
Proof.
  by induction p.
Defined.

Lemma trans_is_concat_opp {A} {x y z : A} (p : x = y) (q : x = z) :
  (transport (fun x' => (x' = z)) p q) = p^ @ q.
Proof.
  induction p. by induction q.
Defined.

Definition Funext_implies_WeakFunext:Funext -> WeakFunext:=
  (fun E=> (NaiveFunext_implies_WeakFunext (Funext_implies_NaiveFunext E))).

Theorem hlevel_inhabited_contr `{E : Funext} {n X} : Trunc n X -> Contr (Trunc n X).
Proof.
  revert X. induction n.
    intros X H. apply (@contr_Contr _ _ H).
  simpl.
  intros X H. set (wfunext:=(Funext_implies_WeakFunext E)).
  do 2 (apply wfunext; intro).
  by apply IHn.
Defined.

Instance inhabited_contr_isprop {A} : (A -> Contr A) -> HProp A.
Proof.
  intros H x.
  apply (@contr_paths_contr _ (H x)).
Defined.

Instance Trunc_isprop `{E : Funext} {n A} : HProp (Trunc n A).
Proof.
  intros. Check contr_contr.
  apply inhabited_contr_isprop.
  apply hlevel_inhabited_contr.
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

Theorem isset_equiv_axiomK {A} :
  (is_trunc 0 A) <~> (forall (x : A) (p : x = x), p = idpath x).
Proof.
  apply (equiv_adjointify (@isset_implies_axiomK A) (@axiomK_implies_isset A)).
   intro H. by_extensionality. by_extensionality. 
    cut (Contr (x=x)). intro. eapply path_contr.
     exists 1. intros. symmetry. apply H.
  intro H. by_extensionality.
  by_extensionality.
  eapply allpath_HProp.
Defined.

Instance axiomK_isprop A : HProp (axiomK A).
Proof.
  apply (trunc_equiv _ _ isset_equiv_axiomK). 
Defined.


Theorem set_path2 {A} `{HSet A} {x y : A} (p q : x = y):
  p = q.
Proof.
  induction q.
  apply (isset_implies_axiomK HSet0).
Defined.

(** Recall that axiom K says that any self-path is homotopic to the
   identity path.  In particular, the identity path is homotopic to
   itself.  The following lemma says that the endo-homotopy of the
   identity path thus specified is in fact (homotopic to) its identity
   homotopy (whew!).  *)
Local Open Scope path_scope.


(* Unfinished
Lemma axiomK_idpath {A} (x : A) (K : axiomK A) :
  K x (idpath x) = idpath (idpath x).
Proof.
  set (qq := apD (K x) (K x (idpath x))).
  set (q2 := (@trans_is_concat_opp _ (K x (idpath x))) (K x (idpath x))^).  
    (* this should be concatination with @ qq).*)
  
  path_via ((K x (idpath x))^^).
  path_via (idpath (idpath x))^.
  apply cancelR with (r := K x (idpath x)).
  cancel_units.
Defined.
*)

(** Any type with "decidable equality" is a set. *)
(* just to be sure that we have the right notation *)
Notation "~ X":=(types.Empty.not X).
Definition decidable_paths (A : Type) :=
  forall (x y : A), (x = y) + (~ (x = y)).

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
    intro qp0; apply (cancelL q). path_via (transport _ p q).
      symmetry; apply transport_paths_r.
      path_via q. apply @inl_injective with (B := (~ x = x)).
      exact ((ap_transport p (fun y => @inl (x = y) (~x = y)) q) @ qp0).
  induction (q' p).
Defined.

Corollary decidable_isset {A : Type} : @decidable_paths A -> @is_trunc 0 A.
Proof.
  intro.
  by apply @axiomK_implies_isset, @decidable_implies_axiomK.
Defined.