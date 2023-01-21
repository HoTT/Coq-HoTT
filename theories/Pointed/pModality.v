Require Import Basics Types ReflectiveSubuniverse Pointed.Core.

Local Open Scope pointed_scope.

(** * Modalities and pointed types *)

Global Instance ispointed_O `{O : ReflectiveSubuniverse} (X : Type)
  `{IsPointed X} : IsPointed (O X) := to O _ (point X).

Definition pto (O : ReflectiveSubuniverse@{u}) (X : pType@{u})
  : X ->* [O X, _]
  := Build_pMap X [O X, _] (to O X) idpath.

(** If [A] is already [O]-local, then Coq knows that [pto] is an equivalence, so we can simply define: *)
Definition pequiv_pto `{O : ReflectiveSubuniverse} {X : pType} `{In O X}
  : X <~>* [O X, _] := Build_pEquiv _ _ (pto O X) _.

(** Applying [O_rec] to a pointed map yields a pointed map. *)
Definition pO_rec `{O : ReflectiveSubuniverse} {X Y : pType}
  `{In O Y} (f : X ->* Y) : [O X, _] ->* Y
  := Build_pMap [O X, _] _ (O_rec f) (O_rec_beta _ _ @ point_eq f).
