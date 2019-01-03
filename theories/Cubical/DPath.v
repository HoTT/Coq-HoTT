Require Import HoTT.Basics HoTT.Types.

(* Dependent paths *)

Definition dpath {A} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) : Type.
Proof.
  destruct p; exact (u=v).
Defined.

Definition dpath_compose {A B} (f : A -> B) (P : B -> Type) {x y : A}
           (p : x = y) (u : P (f x)) (v : P (f y))
  : dpath P (ap f p) u v <~> dpath (fun x => P (f x)) p u v.
Proof.
  destruct p; apply equiv_idmap.
Defined.

(* Prod *)

Definition dpath_prod {A} (P Q : A -> Type)
           {x y : A} (p : x = y)
           (u : P x) (v : P y) (r : Q x) (s : Q y)
           (h : dpath P p u v) (k : dpath Q p r s)
  : dpath (fun x => P x * Q x) p (u,r) (v,s).
Proof.
  destruct p; apply path_prod; assumption.
Defined.

(* Forall *)

Definition dpath_forall_const `{Funext} {A B} (P : A -> B -> Type)
           {x y : A} (p : x = y)
           (u : forall b, P x b) (v : forall b, P y b)
           (h : forall b, dpath (fun a => P a b) p (u b) (v b))
  : dpath (fun a => forall b, P a b) p u v.
Proof.
  destruct p; cbn in *.
  apply path_forall; assumption.
Defined.

(* Sigma *)

Definition path_sig_uncurried {A : Type} (P : A -> Type) (u v : sig P)
           (pq : {p : pr1 u = pr1 v &
                      dpath P p (pr2 u) (pr2 v)})
: u = v.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; destruct pq as [p q].
  cbn in *; destruct p; cbn in *; destruct q; reflexivity.
Defined.  

Definition path_sig {A : Type} (P : A -> Type) (u v : sig P)
           (p : pr1 u = pr1 v) (q : dpath P p (pr2 u) (pr2 v))
: u = v
  := path_sig_uncurried P u v (exist _ p q).

Definition ap_pr1_path_sig {A : Type} (P : A -> Type) (u v : sig P)
           (p : pr1 u = pr1 v) (q : dpath P p (pr2 u) (pr2 v))
: ap pr1 (path_sig P u v p q) = p.
Proof.
  destruct u, v; cbn in *; destruct p; cbn in *; destruct q; reflexivity.
Defined.

Definition ap_pr1_pr1_path_sig {A : Type} (B : A -> Type) (P : sig B -> Type)
           (u v : sig P)
           (p : pr1 (pr1 u) = pr1 (pr1 v))
           (q : dpath B p (pr2 (pr1 u)) (pr2 (pr1 v)))
           (r : dpath P (path_sig B (pr1 u) (pr1 v) p q) (pr2 u) (pr2 v))
  : ap (fun w => pr1 (pr1 w)) (path_sig P u v (path_sig B (pr1 u) (pr1 v) p q) r)
    = p.
Proof.
  destruct u as [[u11 u12] u2]; destruct v as [[v11 v12] v2].
  cbn in *; destruct p; cbn in *; destruct q; cbn in *; destruct r; reflexivity.
Defined.
