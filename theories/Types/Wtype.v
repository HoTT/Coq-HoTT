(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about W-types (well-founded trees) *)

Require Import HoTT.Basics.
Require Import Types.Forall Types.Sigma Types.Paths Types.Unit.
Local Open Scope path_scope.

Generalizable Variables X A B C f g n.

(** Primitive projections do not work for recursive records; see bug #4648 - https://coq.inria.fr/bugs/show_bug.cgi?id=4648. *)
Local Unset Primitive Projections.
Inductive W (A : Type) (B : A -> Type) : Type :=
  sup { w_label : A ; w_arg : B w_label -> W A B }.
Local Set Primitive Projections.

Arguments w_label {A B} _.
Arguments w_arg {A B} _ _.

(** ** Paths *)

Definition path_wtype {A B} (u v : W A B)
  (pq : (w_label u;w_arg u) = (w_label v;w_arg v) :> {a : _ & B a -> W A B})
: u = v.
Proof.
  destruct u,v; apply (path_sigma_uncurried _ _ _)^-1 in pq.
  destruct pq as [p q]; cbn in p; destruct p; cbn in q; destruct q.
  exact idpath.
Defined.

Definition path_wtype_inv {A B} {u v : W A B} (pq : u = v)
: (w_label u;w_arg u) = (w_label v;w_arg v) :> {a : _ & B a -> W A B}
  := match pq with
       | 1 => match u with
                | sup _ _ => 1
              end
     end.

(** This lets us identify the path space of a W-type, up to equivalence. *)

Definition eisretr_path_wtype {A B} {z z' : W A B}
: Sect (@path_wtype_inv _ _ z z') (path_wtype z z')
  := fun p => match p as p in (_ = z') return
                    path_wtype z z' (path_wtype_inv p) = p
              with
                | 1 => match z as z return
                             path_wtype z z (path_wtype_inv 1) = 1
                       with
                         | sup _ _ => 1
                       end
              end.

Definition eissect_path_wtype {A B} {z z' : W A B}
: Sect (path_wtype z z') (@path_wtype_inv _ _ z z').
Proof.
  intro r; destruct z, z'; set (pq := (path_sigma_uncurried _ _ _)^-1 r).
  rewrite (eisretr _ _ : path_sigma_uncurried _ _ _ pq = r)^.
  destruct pq as [p q]; cbn in p; destruct p; cbn in q; destruct q.
  exact idpath.
Defined.

Global Instance isequiv_path_wtype {A B} {z z' : W A B}
: IsEquiv (path_wtype z z') | 0.
Proof.
  refine (isequiv_adjointify (path_wtype z z')
                       (@path_wtype_inv _ _ z z')
                       (@eisretr_path_wtype A B z z')
                       (@eissect_path_wtype A B z z')).
Defined.

Definition equiv_path_wtype {A B} (z z' : W A B)
  := BuildEquiv _ _ _ (@isequiv_path_wtype A B z z').

(** ** W-types preserve truncation *)

Global Instance trunc_wtype `{Funext} `{B : A -> Type}
         `{IsTrunc n.+1 A}
: IsTrunc n.+1 (W A B) | 100.
Proof.
  generalize dependent A; intros A B ac; intros z; induction z as [a w].
  intro y; destruct y as [a0 w0]; refine (trunc_equiv _ (equiv_path_wtype _ _)).
  apply (trunc_equiv' {p : a = a0 & forall b, w b = w0 (p # b)}).
  { transitivity {p : a = a0 & transport (fun a => B a -> W A B) p w = w0}.
    { apply equiv_functor_sigma_id; intro p; induction p.
      by apply equiv_path_forall. }
    by erapply (equiv_path_sigma _ (a;w) (a0;w0)). }
  apply (@trunc_sigma _ _ _ (ac a a0)); intro p; rapply @trunc_forall.
Defined.
