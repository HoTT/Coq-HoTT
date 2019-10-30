Require Import HoTT.Basics Types.Universe TruncType UnivalenceImpliesFunext.

Local Open Scope path_scope.

Section Functorish.
Context `{Univalence}.
(* We do not need composition to be preserved. *)
Class Functorish (F : Type -> Type) := {
  fmap {A B} (f : A -> B) : F A -> F B ;
  fmap_idmap (A:Type) : fmap (idmap : A -> A) = idmap
}.

Global Arguments fmap F {FF} {A B} f _ : rename.
Global Arguments fmap_idmap F {FF A} : rename.

Context (F : Type -> Type).
Context {FF : Functorish F}.

Proposition isequiv_fmap {A B} (f : A -> B) `{IsEquiv _ _ f}
  : IsEquiv (fmap F f).
Proof.
  refine (equiv_induction (fun A' e => IsEquiv (fmap F e)) _ _ (Build_Equiv _ _ f _)).
  refine (transport _ (fmap_idmap F)^ _);
    try apply isequiv_idmap. (* This line may not be needed in a new enough coq. *)
Defined.

Proposition fmap_agrees_with_univalence {A B} (f : A -> B) `{IsEquiv _ _ f}
  : fmap F f = equiv_path _ _ (ap F (path_universe f)).
Proof.
  refine (equiv_induction
    (fun A' e => fmap F e = equiv_path _ _ (ap F (path_universe e)))
    _ _ (Build_Equiv _ _ f _)).
  transitivity (idmap : F A -> F A).
  - apply fmap_idmap.
  - change (equiv_idmap A) with (equiv_path A A 1).
    rewrite (@eta_path_universe _ A A 1). exact 1.
Defined.

End Functorish.
