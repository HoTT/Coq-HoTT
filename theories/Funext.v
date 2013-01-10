(** * Function extensionalty *)

(** We formulate function extensionality in a separate file, even though it properly belongs to [types.Forall], because it is used in many places.  *)

Require Import Overture.
Local Open Scope equiv_scope.

(** The function extensionality axiom is formulated as a class. To use it in a theorem, just assume it with [`{Funext}], and then you can use [path_forall], defined below.  If you need function extensionality for a whole development, you can assume it for an entire Section with [Context `{Funext}].  *)
Class Funext := 
  { isequiv_apD10 :> forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g) }.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  (forall x, f x = g x) -> f = g
  :=
  (@apD10 A P f g)^-1.

Definition path_forall2 `{Funext} {A B : Type} {P : A -> B -> Type} (f g : forall x y, P x y) :
  (forall x y, f x y = g x y) -> f = g
  := 
  (fun E => path_forall f g (fun x => path_forall (f x) (g x) (E x))).
