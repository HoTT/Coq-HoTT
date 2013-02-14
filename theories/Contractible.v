(* -*- mode: coq; mode: visual-line -*- *)
(** Contractibility *)

Require Import Overture PathGroupoids.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** Naming convention: we consistently abbreviate "contractible" as "contr".  A theorem about a space [X] being contractible (which will usually be an instance of the typeclass [Contr]) is called [contr_X]. *)

(** Allow ourselves to implicitly generalize over types [A] and [B], and a function [f]. *)
Generalizable Variables A B f.

(** If a space is contractible, then any two points in it are connected by a path in a canonical way. *)
Definition path_contr `{Contr A} (x y : A) : x = y
  := (contr x)^ @ (contr y).

(** Similarly, any two parallel paths in a contractible space are homotopic, which is just the principle UIP. *)
Definition path2_contr `{Contr A} {x y : A} (p q : x = y) : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
    intro r; destruct r; apply symmetry; now apply concat_Vp.
  path_via (path_contr x y).
Defined.

(** It follows that any space of paths in a contractible space is contractible. *)
Instance contr_paths_contr `{Contr A} (x y : A) : Contr (x = y) := {
  center := (contr x)^ @ contr y;
  contr := path2_contr ((contr x)^ @ contr y)
}.

(** Also, the total space of any based path space is contractible. *)
Instance contr_basedpaths {X : Type} (x : X) : Contr {y : X & x = y}.
  exists (x ; 1).
  intros [y []]; reflexivity.
Defined.

Instance contr_basedpaths' {X : Type} (x : X) : Contr {y : X & y = x}.
  exists (existT (fun y => y = x) x 1).
  intros [y []]; reflexivity.
Defined.

(** If [f] is an equivalence, then its homotopy fibers are contractible.  That is, it is a Voevodsky equivalence, or a homotopy bijection.  Probably the following two proofs should really be using some standard facts about paths in Sigma types.  *)

Instance contr_hfiber_equiv `(IsEquiv A B f) (b : B)
  : Contr {a:A & f a = b}.
Proof.
  assert (fp : forall (x x':A) (p:f x = b) (p':f x' = b)
      (q : x = x') (r : ap f q @ p' = p), (x;p) = (x';p') :> {x:A & f x = b}).
    intros x x' p p' q r; destruct q. exact (ap _ (r^ @ concat_1p _)).
  refine (BuildContr _ (f^-1 b; eisretr f b) _).
  intros [a p].
  refine (fp (f^-1 b) a (eisretr f b) p ((ap f^-1 p)^ @ eissect f a) _).
  rewrite ap_pp, ap_V, <- ap_compose, concat_pp_p, <- eisadj.
  apply moveR_Vp.
  exact ((concat_A1p (eisretr f) p)^).
Qed.

(* This should not be an Instance, as it causes infinite loops. *)
Definition isequiv_contr_hfibers `(f : A -> B)
  (hfc : forall y:B, Contr {x:A & f x = y})
  : IsEquiv f.
Proof.
  pose (g b := projT1 (@center _ (hfc b))).
  pose (isretr b := projT2 (@center _ (hfc b))).
  assert (sa : forall a, { issect : g (f a) = a & isretr (f a) = ap f issect }).
    intros a.
    assert (fp : forall (x x' : {x:A & f x = f a}) (q : x = x'),
        { p : projT1 x = projT1 x' & projT2 x = ap f p @ projT2 x' }).
      intros x _ []. exists 1; exact ((concat_1p _)^).
    set (r := fp (@center _ (hfc (f a))) (a;1) (@contr _ (hfc (f a)) (a;1))).
    exact (projT1 r ; projT2 r @ concat_p1 _).
  exact (BuildIsEquiv _ _ f g isretr
    (fun a => projT1 (sa a)) (fun a => projT2 (sa a))).
Defined.

Definition equiv_contr_hfibers `(f : A -> B)
  (hfc : forall y:B, Contr {x:A & f x = y})
  : (A <~> B)
  := BuildEquiv _ _ f (isequiv_contr_hfibers f hfc).
