(* -*- mode: coq; mode: visual-line -*- *)
(** * Comparing definitions of equivalence *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp.

Local Open Scope nat_scope.
Local Open Scope path_scope.

Generalizable Variables A B f.

Section AssumeFunext.
Context `{Funext}.

(** In this file we show that several different definitions of "equivalence" are all equivalent to the one we have chosen.  We already observed in [Types/Equiv.v] that a map is an equivalence iff all of its homotopy fibers are contractible.  This was Voevodsky's first definition of equivalences in homotopy type theory.  *)


(** ** Bi-invertible maps *)

(** A map is "bi-invertible" if it has both a section and a retraction, not necessarily the same.  This definition of equivalence was proposed by Andre Joyal. *)

Definition BiInv `(f : A -> B) : Type
  := {g : B -> A & Sect f g} * {h : B -> A & Sect h f}.

(** It seems that the easiest way to show that bi-invertibility is equivalent to being an equivalence is also to show that both are h-props and that they are logically equivalent. *)

Definition isequiv_biinv `(f : A -> B)
  : BiInv f -> IsEquiv f.
Proof.
  intros [[g s] [h r]].
  exact (isequiv_adjointify f g
    (fun x => ap f (ap g (r x)^ @ s (h x))  @ r x)
    s).
Defined.

Global Instance isprop_biinv `(f : A -> B) : IsHProp (BiInv f) | 0.
Proof.
  apply hprop_inhabited_contr.
  intros bif; pose (fe := isequiv_biinv f bif).
  apply @contr_prod.
  (* For this, we've done all the work already. *)
  - by apply contr_retr_equiv.
  - by apply contr_sect_equiv.
Defined.

Definition equiv_biinv_isequiv `(f : A -> B)
  : BiInv f <~> IsEquiv f.
Proof.
  apply equiv_iff_hprop.
  - by apply isequiv_biinv.
  - intros ?.  split.
    + by exists (f^-1); apply eissect.
    + by exists (f^-1); apply eisretr.
Defined.

(** ** n-Path-split maps.

A map is n-path-split if its induced maps on the first n iterated path-spaces are split surjections.  Thus every map is 0-path-split, the 1-path-split maps are the split surjections, and so on.  It turns out that for n>1, being n-path-split is the same as being an equivalence. *)

Fixpoint PathSplit (n : nat) `(f : A -> B) : Type
  := match n with
       | 0 => Unit
       | S n => (forall a, hfiber f a) *
                forall (x y : A), PathSplit n (@ap _ _ f x y)
     end.

Definition isequiv_pathsplit (n : nat) `{f : A -> B}
: PathSplit n.+2 f -> IsEquiv f.
Proof.
  intros [g k].
  pose (h := fun x y p => (fst (k x y) p).1).
  pose (hs := fun x y => (fun p => (fst (k x y) p).2)
                         : Sect (h x y) (ap f)).
  clearbody hs; clearbody h; clear k.
  apply isequiv_contr_map; intros b.
  apply contr_inhabited_hprop.
  2:exact (g b).
  apply hprop_allpath; intros [a p] [a' p'].
  refine (path_sigma' _ (h a a' (p @ p'^)) _).
  refine (transport_paths_Fl _ _ @ _).
  refine ((inverse2 (hs a a' (p @ p'^)) @@ 1) @ _).
  refine ((inv_pp p p'^ @@ 1) @ _).
  refine (concat_pp_p _ _ _ @ _).
  refine ((1 @@ concat_Vp _) @ _).
  exact ((inv_V p' @@ 1) @ concat_p1 _).
Defined.

Global Instance contr_pathsplit_isequiv
           (n : nat) `(f : A -> B) `{IsEquiv _ _ f}
: Contr (PathSplit n f).
Proof.
  generalize dependent B; revert A.
  simple_induction n n IHn; intros A B f ?.
  - exact _.
  - apply contr_prod.
Defined.

Global Instance ishprop_pathsplit (n : nat) `(f : A -> B)
: IsHProp (PathSplit n.+2 f).
Proof.
  apply hprop_inhabited_contr; intros ps.
  pose (isequiv_pathsplit n ps).
  exact _.
Defined.

Definition equiv_pathsplit_isequiv (n : nat) `(f : A -> B)
: PathSplit n.+2 f <~> IsEquiv f.
Proof.
  refine (equiv_iff_hprop _ _).
  - apply isequiv_pathsplit.
  - intros ?; refine (center _).
Defined.

(** Path-splitness transfers across commutative squares of equivalences. *)
Lemma equiv_functor_pathsplit (n : nat) {A B C D}
      (f : A -> B) (g : C -> D) (h : A <~> C) (k : B <~> D)
      (p : g o h == k o f)
: PathSplit n f <~> PathSplit n g.
Proof.
  destruct n as [|n].
  1:apply equiv_idmap.
  destruct n as [|n].
  - simpl.
    refine (_ *E equiv_contr_contr).
    refine (equiv_functor_forall' k^-1 _); intros d.
    unfold hfiber.
    refine (equiv_functor_sigma' h _); intros a.
    refine (equiv_concat_l (p a) d oE _).
    simpl; apply equiv_moveR_equiv_M.
  - refine (_ oE equiv_pathsplit_isequiv n f).
    refine ((equiv_pathsplit_isequiv n g)^-1 oE _).
    apply equiv_iff_hprop; intros e.
    + refine (isequiv_commsq f g h k (fun a => (p a)^)).
    + refine (isequiv_commsq' f g h k p).
Defined.

(** A map is oo-path-split if it is n-path-split for all n.  This is also equivalent to being an equivalence. *)

Definition ooPathSplit `(f : A -> B) : Type
  := forall n, PathSplit n f.

Definition isequiv_oopathsplit `{f : A -> B}
: ooPathSplit f -> IsEquiv f
  := fun ps => isequiv_pathsplit 0 (ps 2).

Global Instance contr_oopathsplit_isequiv
           `(f : A -> B) `{IsEquiv _ _ f}
: Contr (ooPathSplit f).
Proof.
  apply contr_forall.
Defined.

Global Instance ishprop_oopathsplit `(f : A -> B)
: IsHProp (ooPathSplit f).
Proof.
  apply hprop_inhabited_contr; intros ps.
  pose (isequiv_oopathsplit ps).
  exact _.
Defined.

Definition equiv_oopathsplit_isequiv `(f : A -> B)
: ooPathSplit f <~> IsEquiv f.
Proof.
  refine (equiv_iff_hprop _ _).
  - apply isequiv_oopathsplit.
  - intros ?; refine (center _).
Defined.

End AssumeFunext.

(** ** Relational equivalences *)
(** This definition is due to Peter LeFanu Lumsdaine on the HoTT mailing list.  This definition gives more judgmental properties, though has the downside of jumping universe levels. *)
Section relational.
  Record RelEquiv A B :=
    { equiv_rel : A -> B -> Type;
      relequiv_contr_f : forall a, Contr { b : B & equiv_rel a b };
      relequiv_contr_g : forall b, Contr { a : A & equiv_rel a b } }.

  Arguments equiv_rel {A B} _ _ _.
  Global Existing Instance relequiv_contr_f.
  Global Existing Instance relequiv_contr_g.

  Definition issig_relequiv {A B}
  : { equiv_rel : A -> B -> Type
    | { f : forall a, Contr { b : B & equiv_rel a b }
      | forall b, Contr { a : A & equiv_rel a b } } }
      <~> RelEquiv A B.
  Proof.
    issig.
  Defined.

  Definition relequiv_of_equiv {A B} (e : A <~> B) : RelEquiv A B.
  Proof.
    refine {| equiv_rel a b := e a = b |}.
    (** The rest is found by typeclass inference! *)
  Defined.

  Definition equiv_of_relequiv {A B} (e : RelEquiv A B) : A <~> B.
  Proof.
    refine (equiv_adjointify
              (fun a => (center { b : B & equiv_rel e a b}).1)
              (fun b => (center { a : A & equiv_rel e a b}).1)
              _ _);
    intro x; cbn.
    { refine (ap pr1 (contr _) : _.1 = (x; _).1).
      exact (center {a : A & equiv_rel e a x}).2. }
    { refine (ap pr1 (contr _) : _.1 = (x; _).1).
      exact (center {b : B & equiv_rel e x b}).2. }
  Defined.

  Definition RelIsEquiv {A B} (f : A -> B)
    := { r : RelEquiv A B | forall x, (center { b : B & equiv_rel r x b }).1 = f x }.

  (** TODO: Prove [ishprop_relisequiv `{Funext} {A B} f : IsHProp (@RelIsEquiv A B f)] *)

  (** * Judgmental property *)
  Definition inverse_relequiv {A B} (e : RelEquiv A B) : RelEquiv B A
    := {| equiv_rel a b := equiv_rel e b a |}.

  Definition reinv_V {A B} (e : RelEquiv A B)
  : inverse_relequiv (inverse_relequiv e) = e
    := 1.

  (** TODO: Is there a definition of this that makes [inverse_relequiv (relequiv_idmap A)] be [relequiv_idmap A], judgmentally? *)
  Definition relequiv_idmap A : RelEquiv A A
    := {| equiv_rel a b := a = b |}.

  (** TODO: Define composition; we probably need truncation to do this? *)
End relational.
