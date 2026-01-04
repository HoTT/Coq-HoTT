From HoTT Require Import WildCat.SetoidRewrite WildCat.Core WildCat.AbEnriched.
From HoTT Require Import Basics.Overture.

Local Open Scope mc_add_scope.

(** Test that setoid rewriting works with the additive structure. *)

Definition test1 (A : Type) `{IsAbGroup_0gpd A}
  {a b c d : A} (p : b $== c) (q : c $== d)
  : b + a $== d + a.
Proof.
  rewrite p.
  rewrite <- q.
  reflexivity.
Defined.

Definition test2 (A : Type) `{IsAbGroup_0gpd A}
  {a b c d : A} (p : b $== c) (q : c $== d)
  : a + b $== a + d.
Proof.
  rewrite p.
  rewrite <- q.
  reflexivity.
Defined.

Definition test3 (A : Type) `{IsAbGroup_0gpd A}
  {a b c d : A} (p : a $== c) (q : b $== d)
  : a - b $== c - d.
Proof.
  rewrite p.
  rewrite <- q.
  reflexivity.
Defined.

Definition test4 (A : Type) `{IsAbGroup_0gpd A}
  {a b : A} (p : a $== b)
  : - a $== - b.
Proof.
  rewrite p.
  reflexivity.
Defined.

(** Test rewriting just on LHS of a sum. *)
Definition test5 (A : Type) `{IsAbGroup_0gpd A}
  {a b c : A} (p : a $== b)
  : a + c $== b + c.
Proof.
  rewrite p.
  reflexivity.
Defined.

(** Test rewriting just on RHS of a sum. *)
Definition test6 (A : Type) `{IsAbGroup_0gpd A}
  {a b c : A} (p : a $== b)
  : c + a $== c + b.
Proof.
  rewrite p.
  reflexivity.
Defined.

(** Test rewriting simultaneously on both sides of a sum. *)
Definition test7 (A : Type) `{IsAbGroup_0gpd A}
  {a b : A} (p : a $== b)
  : a + a $== b + b.
Proof.
  rewrite p.
  reflexivity.
Defined.
