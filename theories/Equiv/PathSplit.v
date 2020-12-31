(* -*- mode: coq; mode: visual-line -*- *)

Require Import HoTT.Basics HoTT.Types.

Local Open Scope nat_scope.
Local Open Scope path_scope.

Generalizable Variables A B f.

Section AssumeFunext.
Context `{Funext}.

(** * n-Path-split maps.

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
                         : (ap f) o (h x y) == idmap).
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
