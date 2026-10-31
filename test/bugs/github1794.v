From HoTT Require Import Basics.Overture Basics.Equivalences.

(** The registered rewriting schemes have the expected universe variables and make proofs produced by [rewrite] unfold to [transport]. *)
Check paths_rew@{u1 u2}.
Check paths_rew_r@{u1 u2}.

Definition rewrite_paths_rew {A : Type} {x y : A} (P : A -> Type)
  (u : P x) (p : x = y)
  : P y.
Proof.
  rewrite <- p.
  exact u.
Defined.

Definition rewrite_paths_rew_r {A : Type} {x y : A} (P : A -> Type)
  (u : P y) (p : x = y)
  : P x.
Proof.
  rewrite -> p.
  exact u.
Defined.

Definition rewrite_paths_rew_is_transport {A : Type} {x y : A}
  (P : A -> Type) (u : P x) (p : x = y)
  : rewrite_paths_rew P u p = transport P p u
  := idpath.

Definition rewrite_paths_rew_r_is_transport {A : Type} {x y : A}
  (P : A -> Type) (u : P y) (p : x = y)
  : rewrite_paths_rew_r P u p = transport P p^ u
  := idpath.

(** Check that [simpl] and [cbn] automatically unfold [paths_rew] and [paths_rew_r]. *)

Definition paths_rew_simpl {A : Type} {x y : A}
  (P : A -> Type) (u : P x) (p : x = y)
  : rewrite_paths_rew P u p = transport P p u.
Proof.
  unfold rewrite_paths_rew.
  Fail match goal with |- transport _ p u = transport _ p u => idtac end.
  simpl.
  match goal with |- transport _ p u = transport _ p u => idtac end.
  reflexivity.
Defined.

Definition paths_rew_r_cbn {A : Type} {x y : A}
  (P : A -> Type) (u : P y) (p : x = y)
  : rewrite_paths_rew_r P u p = transport P p^ u.
Proof.
  unfold rewrite_paths_rew_r.
  Fail match goal with |- transport _ p^ u = transport _ p^ u => idtac end.
  cbn.
  match goal with |- transport _ p^ u = transport _ p^ u => idtac end.
  reflexivity.
Defined.

(** Check that [paths_rew] and [paths_rew_r] are transparent to typeclass search. *)

Definition isequiv_paths_rew {A : Type} {x y : A}
  (P : A -> Type) (p : x = y)
  : IsEquiv (fun u => paths_rew P u p).
Proof.
  exact _.
Defined.

Definition isequiv_paths_rew_check {A : Type} {x y : A}
  (P : A -> Type) (p : x = y)
  : isequiv_paths_rew P p = isequiv_transport P p
  := idpath.
