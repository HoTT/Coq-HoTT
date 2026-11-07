From HoTT Require Import Basics.Overture Basics.Equivalences.

(** * The registered rewriting schemes have the expected universe variables and make proofs produced by [rewrite] unfold to [transport]. *)

Definition rewrite_left {A : Type} {x y : A} (P : A -> Type)
  (u : P x) (p : x = y)
  : P y.
Proof.
  rewrite <- p.
  exact u.
Defined.

Definition rewrite_right {A : Type} {x y : A} (P : A -> Type)
  (u : P y) (p : x = y)
  : P x.
Proof.
  rewrite -> p.
  exact u.
Defined.

Definition rewrite_left_is_transport {A : Type} {x y : A}
  (P : A -> Type) (u : P x) (p : x = y)
  : rewrite_left P u p = transport P p u
  := idpath.

Definition rewrite_right_is_transport {A : Type} {x y : A}
  (P : A -> Type) (u : P y) (p : x = y)
  : rewrite_right P u p = transport P p^ u
  := idpath.

(** Check that [simpl] and [cbn] automatically unfold [paths_rew] and [paths_rew_r]. *)

Definition rewrite_left_simpl {A : Type} {x y : A}
  (P : A -> Type) (u : P x) (p : x = y)
  : rewrite_left P u p = transport P p u.
Proof.
  unfold rewrite_left.
  Fail match goal with |- transport _ p u = transport _ p u => idtac end.
  simpl.
  match goal with |- transport _ p u = transport _ p u => idtac end.
  reflexivity.
Defined.

Definition rewrite_right_cbn {A : Type} {x y : A}
  (P : A -> Type) (u : P y) (p : x = y)
  : rewrite_right P u p = transport P p^ u.
Proof.
  unfold rewrite_right.
  Fail match goal with |- transport _ p^ u = transport _ p^ u => idtac end.
  cbn.
  match goal with |- transport _ p^ u = transport _ p^ u => idtac end.
  reflexivity.
Defined.

(** Check that [transport'] and [transport_V'] are transparent to typeclass search and have the correct universe variables. *)

Definition isequiv_transport' {A : Type@{u1}} {x y : A}
  (P : A -> Type@{u2}) (p : x = y)
  : IsEquiv (fun u => transport'@{u1 u2} P u p).
Proof.
  exact _.
Defined.

Definition isequiv_transport'_check {A : Type} {x y : A}
  (P : A -> Type) (p : x = y)
  : isequiv_transport' P p = isequiv_transport P p
  := idpath.

Definition isequiv_transport_V' {A : Type@{u1}} {x y : A}
  (P : A -> Type@{u2}) (p : x = y)
  : IsEquiv (fun u => transport_V'@{u1 u2} P u p).
Proof.
  exact _.
Defined.
