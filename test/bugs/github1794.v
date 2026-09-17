From HoTT Require Import Basics.Overture.

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
