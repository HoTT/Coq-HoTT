(** * H-Levels *)

(* The H-levels measure how complicated a type is in terms of higher path spaces.
   H-level 0 are the contractible spaces, whose homotopy is completely
   trivial. H-level [(n+1)] are spaces whose path spaces are of level [n].

   Thus, H-level 1 means "the space of paths between any two points is
   contactible". Such a space is necessarily a sub-singleton: any two points are
   connected by a path which is unique up to homotopy. In other words, H-level 1
   spaces are truth values (we call them "propositions").
  
   Next, H-level 2 means "the space of paths between any two points is a
   sub-singleton". Thus, two points might not have any paths between them, or
   they have a unique path. Such a space may have many points but it is discrete
   in the sense that all paths are trivial. We call such spaces "sets".
*)

Require Import Overture Contractible Equivalences Funext types.Paths.
Local Open Scope equiv_scope.

Generalizable Variable A.

(** The space of contractions of a contractible space is contractible. *)
Instance contr_Contr `{Funext} `{Contr A} : Contr (Contr A).
  exists {| center := center A ; contr := contr |}.
  intros [c h].
  apply (Contr_path (contr c)).
  apply path_forall.
  intro; apply path2_contr.
Qed.

(** ** H-levels and general facts about them. *)

Fixpoint is_hlevel (n : nat) (A : Type) : Type :=
  match n with
    | 0 => Contr A
    | S n' => forall (x y : A), is_hlevel n' (x = y)
  end.

(** A contractible space has h-level zero, of course. *)
Instance Contr_hlevel_0 (A : Type) : is_hlevel 0 A -> Contr A
  := idmap.
  
(** H-levels are cummulative. *)
Lemma hlevel_succ (n : nat) :
  forall A : Type, is_hlevel n A -> is_hlevel (S n) A.
Proof.
  induction n as [| n I].
  - intros A H x y.
    unfold is_hlevel in H.
    apply contr_paths_contr.
  - intros A H x y p q.
    apply I.
    apply H.
Qed.

(** ** Facts about [HProp] *)

(** Maybe this should go to a separate file? *)

Class HProp (A : Type) :=
  { is_hprop : is_hlevel 1 A }.

(** An inhabited proposition is contractible. *)
Lemma Contr_inhabited_HProp `{H : HProp A} (x : A) : Contr A.
Proof.
  exists x.
  intro y.
  apply H.
Defined.

(** If inhabitation implies contractibility, then we have an h-proposition. *)
Instance HProp_inhabited_contr (A : Type) : (A -> Contr A) -> HProp A.
Proof.
  intro H.
  exists.
  intros x y.
  pose (C := H x).
  apply contr_paths_contr.
Defined.

(** [is_hlevel] is a proposition. *)
Instance HProp_is_hlevel `{E : Funext} (n  : nat) (A : Type) : HProp (is_hlevel n A).
Proof.
  apply HProp_inhabited_contr.
  generalize A; clear A.
  induction n as [| n I].
  - intros A H.
    unfold is_hlevel in * |- *.
    apply contr_Contr.
  - intros A H.
    exists H.
    intro G.
    apply path_forall; intro x.
    apply path_forall; intro y.
    simpl in G, H.
    apply @path_contr.
    apply I, H.
Qed.

(** Equivalence preserves h-levels (this is, of course, trivial with univalence). *)
Theorem hlevel_equiv (n : nat) : forall (A B : Type), (A <~> B) -> is_hlevel n A -> is_hlevel n B.
Proof.
  induction n as [| n I].
  - apply Contr_equiv_contr.
  - intros A B e H x y.
    fold is_hlevel.
    apply I with (A := (e^-1 x = e^-1 y)).
    + apply equiv_inverse.
      apply @equiv_ap.
      apply @isequiv_inverse.
    + apply H.
Defined.

(** ** Facts about [HSet] *)

Class HSet (A : Type) :=
  { _ : is_hlevel 2 A }.


(* COMMENTED OUT FOR NOW

(** H-level is preserved under equivalence.
   (This is, of course, trivial with univalence.) *)


(** And by products *)

Definition prod_hlevel:
  forall n A B, is_hlevel n A -> is_hlevel n B -> is_hlevel n (A * B).
Proof.
  induction n; intros A B.
  intros [a ac] [b bc].
  exists (a,b).
  intros [a' b'].
  apply prod_path. apply ac. apply bc.
  intros Ah Bh [a1 b1] [a2 b2].
  apply @hlevel_equiv with (A := ((a1 = a2) * (b1 = b2))%type).
  apply equiv_inverse, prod_path_equiv.
  apply IHn. apply Ah. apply Bh.
Defined.

(** And by dependent sums *)

Definition total_hlevel: forall n A (P : A -> Type),
  is_hlevel n A -> (forall a, is_hlevel n (P a)) ->
  is_hlevel n (sigT P).
Proof.
  intros n; induction n.
  intros A P [a ac] Pc.
  exists (a; pr1 (Pc a)).
  intros [a' p'].
  apply @total_path with (ac a').
  apply contr_path; apply (Pc a).
  intros A P Ah Ph [a1 p1] [a2 p2].
  apply @hlevel_equiv with
    (A := {p : a1 = a2 & transport p p1 = p2}).
  apply equiv_inverse, total_paths_equiv.
  apply IHn.
  apply Ah.
  intros p; apply (Ph a2).
Defined.

(** Propositions are of h-level 1. *)

Definition is_prop := is_hlevel 1.

(** Here is an alternate characterization of propositions. *)

Definition isprop_isprop A : is_prop (is_prop A) := hlevel_isprop 1 A.

Definition iscontr_isprop A : is_prop (is_contr A).
Proof.
  apply inhabited_contr_isprop.
  apply contr_contr.
Defined.

Theorem prop_equiv_inhabited_contr {A} : is_prop A <~> (A -> is_contr A).
Proof.
  apply (equiv_from_hequiv (prop_inhabited_contr A) (inhabited_contr_isprop A)).
  intro H.
  unfold prop_inhabited_contr, inhabited_contr_isprop.
  simpl.
  apply funext.
  intro x.
  apply contr_path.
  apply contr_contr.
  exact (H x).
  intro H.
  unfold prop_inhabited_contr, inhabited_contr_isprop.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro y.
  apply contr_path.
  apply contr_contr.
  exact (H x y).
Defined.

(** And another one. *)

Theorem prop_path {A} : is_prop A -> forall (x y : A), x = y.
Proof.
  unfold is_prop. simpl.
  intros H x y.
  exact (pr1 (H x y)).
Defined.

Theorem allpath_prop {A} : (forall (x y : A), x = y) -> is_prop A.
  intros H x y.
  assert (K : is_contr A).
  exists x. intro y'. apply H.
  apply contr_pathcontr. assumption.
Defined.

Theorem prop_equiv_allpath {A} : is_prop A <~> (forall (x y : A), x = y).
Proof.
  apply (equiv_from_hequiv prop_path allpath_prop).
  intro H.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro y.
  apply contr_path.
  apply (allpath_prop  H).
  intro H.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro y.
  apply contr_path.
  apply contr_contr.
  apply H.
Defined.
  
(** Two propositions are equivalent as soon as there are maps in both
   directions. *)

Definition prop_iff_equiv A B : is_prop A -> is_prop B ->
  (A -> B) -> (B -> A) -> (A <~> B).
Proof.
  intros Ap Bp f g.
  apply (equiv_from_hequiv f g); 
  intros; apply prop_path; auto.
Defined.

(** Props are closed under sums (with prop base) and arbitrary
   dependent products. *)

Definition sum_isprop X (P : X -> Type) :
  is_prop X -> (forall x, is_prop (P x)) -> is_prop (sigT P).
Proof.
  intros Xp Pp.
  apply allpath_prop.
  intros [x p] [y q].
  apply @total_path with (prop_path Xp x y).
  apply prop_path, Pp.
Defined.

Definition forall_isprop {X} (P : X -> Type) :
  (forall x, is_prop (P x)) -> is_prop (forall x, P x).
Proof.
  intros H.
  apply allpath_prop.
  intros f g.
  apply funext_dep. intros x.
  apply prop_path.
  apply H.
Defined.

(** Being an equivalence is a prop. *)

Definition is_equiv_is_prop {X Y} (f: X -> Y) : is_prop (is_equiv f).
Proof.
  apply forall_isprop. intros y.
  apply iscontr_isprop.
Defined.

(** Sets are of h-level 2. *)

Definition is_set := is_hlevel 2.

(** A type is a set if and only if it satisfies Axiom K. *)

Definition axiomK A := forall (x : A) (p : x = x), p = idpath x.

Definition isset_implies_axiomK A : is_set A -> axiomK A.
Proof.
  intros H x p.
  apply (H x x p (idpath x)).
Defined.

Definition axiomK_implies_isset A : axiomK A -> is_set A.
Proof.
  intros H x y.
  apply allpath_prop.
  intros p q.
  induction q.
  apply H.
Defined.

Theorem isset_equiv_axiomK {A} :
  is_set A <~> (forall (x : A) (p : x = x), p = idpath x).
Proof.
  apply (equiv_from_hequiv (isset_implies_axiomK A) (axiomK_implies_isset A)).
  intro H.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro p.
  apply contr_path.
  apply (axiomK_implies_isset A H).
  intro H.
  apply funext_dep.
  intro x.
  apply funext_dep.
  intro y.
  apply prop_path.
  apply isprop_isprop.
Defined.

Definition isset_isprop A : is_prop (is_set A) := hlevel_isprop 2 A.

Theorem axiomK_isprop A : is_prop (axiomK A).
Proof.
  apply @hlevel_equiv with (A := is_set A).
  apply isset_equiv_axiomK.
  apply hlevel_isprop.
Defined.

Theorem set_path2 (A : Type) (x y : A) (p q : x = y) :
  is_set A -> (p = q).
Proof.
  intro H.
  apply contr_path.
  apply prop_inhabited_contr.
  cbv. cbv in H.
  apply H.
  assumption.
Defined.

(** Recall that axiom K says that any self-path is homotopic to the
   identity path.  In particular, the identity path is homotopic to
   itself.  The following lemma says that the endo-homotopy of the
   identity path thus specified is in fact (homotopic to) its identity
   homotopy (whew!).  *)

Lemma axiomK_idpath (A : Type) (x : A) (K : axiomK A) :
  K x (idpath x) = idpath (idpath x).
Proof.
  intros.
  set (qq := map_dep (K x) (K x (idpath x))).
  set (q2 := !trans_is_concat_opp (K x (idpath x)) (K x (idpath x)) @ qq).
  path_via (!! K x (idpath x)).
  path_via (! idpath (idpath x)).
  apply concat_cancel_right with (r := K x (idpath x)).
  cancel_units.
Defined.

(** Any type with "decidable equality" is a set. *)

Definition decidable_paths (A : Type) :=
  forall (x y : A), (x = y) + ((x = y) -> Empty_set).

(* Usually this lemma would be proved with [discriminate], but
   unfortunately that tactic is hardcoded to work only with Coq's
   [Prop]-valued equality. *)
Definition inl_injective {A B : Type} {x y : A} (p : inl B x = inl B y) : x = y :=
  transport (P := fun (s : A + B) => x = (match s with inl a => a | inr b => x end)) p (idpath x).

Theorem decidable_implies_axiomK {A : Type} : decidable_paths A -> axiomK A.
Proof.
  intro d.
  intros x p.
  set (qp := map_dep (d x) p).
  set (q := d x x) in *.
  clearbody qp; revert qp.
  destruct q as [q | q'].
  intro qp0. 
  apply (concat_cancel_left q).
  path_via (transport p q).
  apply opposite, trans_is_concat.
  path_via q.
  set (qp1 := trans_map p (fun y => @inl (x = y) (x = y -> Empty_set)) q).
  simpl in qp1.
  apply @inl_injective with (B := (x = x -> Empty_set)).
  exact (qp1 @ qp0).
  induction (q' p).
Defined.

Corollary decidable_isset (A : Type) : decidable_paths A -> is_set A.
Proof.
  intro.
  apply axiomK_implies_isset, decidable_implies_axiomK.
  assumption.
Defined.


*)