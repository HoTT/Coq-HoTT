(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Export ooCat.Cat0.  (* ooCat.Laxity. *)

Generalizable Variables m n p A B C.

(** * Fibrations *)

(** TODO: Do general fibrations with Laxity. *)


(** ** Isofibrations *)

(** An isofibration is a displayed category with isomorphism-lifting in all dimensions. *)
CoInductive IsIsoFib {m A} n B `{DHasEquivs m A n B} :=
{
  lift_obj : forall {a b : A} (f : a $<~> b) (u : B a), B b ;
  lift_cate : forall {a b : A} (f : a $<~> b) (u : B a),
      DCatEquiv f u (lift_obj f u) ;
  isisofib_dhom : forall {a b : A} {u : B a} {v : B b},
      @IsIsoFib (pred m) (a $-> b) (pred n) (fun f => DHom f u v)
                _ _ _ _ _ _ ;
}.

Existing Class IsIsoFib.
Global Existing Instance isisofib_dhom.
