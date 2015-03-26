(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about W-types (well-founded trees) *)

Require Import HoTT.Basics.
Require Import Types.Forall Types.Sigma Types.Paths Types.Unit.
Local Open Scope path_scope.

Generalizable Variables X A B C f g n.

Inductive W (A : Type) (B : A -> Type) : Type :=
  sup : forall a, (B a -> W A B) -> W A B.

(** ** Paths *)


Definition path_wtype {A B} (z z' : W A B)
           (pq : match z, z' with
                   | sup a1 t1, sup a2 t2 =>
                       (a1;t1) = (a2;t2) :> {a : _ & B a -> W A B}
                 end)
: z = z'.
Proof.
  destruct z, z'; apply (path_sigma_uncurried _ _ _)^-1 in pq.
  destruct pq as [p q]; cbn in p; destruct p; cbn in q; destruct q.
  exact idpath.
Defined.

Definition path_wtype_inv {A B} {z z' : W A B}
           (pq : z = z')
: match z, z' with
    | sup a1 t1, sup a2 t2 =>
         (existT (fun a => B a -> W A B) a1 t1) = (a2;t2)
  end
  := match pq with
       | 1 => match z with
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
  generalize dependent A; intros A B ac; intros z; induction z; intro y.
  destruct y; refine (trunc_equiv _ (equiv_path_wtype _ _)).
  apply (trunc_equiv' {p : a = a0 & forall b, w b = w0 (p # b)}).
  { transitivity {p : a = a0 & transport (fun a => B a -> W A B) p w = w0}.
    { apply equiv_functor_sigma_id; intro p; induction p.
      by apply equiv_path_forall. }
    by erapply (equiv_path_sigma _ (a;w) (a0;w0)). }
  apply (@trunc_sigma _ _ _ (ac a a0)); intro p; rapply @trunc_forall.
Defined.