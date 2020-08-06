Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import HIT.Coeq.
Require Import Algebra.Groups.FreeProduct.

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

(** Coequalizers of group homomorphisms *)


Definition GroupCoeq {A B : Group} (f g : GroupHomomorphism A B) : Group
  := AmalgamatedFreeProduct A B B f g.


