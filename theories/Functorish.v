Require Import HoTT TruncType.
Open Scope equiv.
Open Scope path.

Section AssumeUnivalence.
Context `{Univalence}.
Section AssumeFunext.
Context `{Funext}.

Lemma equiv_rect {A0 : Type} (P : forall A1 : Type, (A0 <~> A1) -> Type)
  (d0 : P A0 (equiv_idmap A0))
: forall (A1 : Type) (e : A0 <~> A1), P A1 e.
Proof.
  assert (H1 : forall (A1 : Type) (p : A0 = A1), P A1 (equiv_path _ _ p))
   by (by destruct p).
  intros A1 e.
  assert (H2 := H1 A1 (path_universe e)).
  refine (transport _ _ H2).
  destruct e as [e_fun e_isequiv]. apply eisretr.
Defined.

(** Surely should be able to simplify this!? *)
Lemma equiv_comp {A0 : Type} (P : forall A1 : Type, (A0 <~> A1) -> Type)
  (d0 : P A0 (equiv_idmap A0))
: equiv_rect P d0 A0 (equiv_idmap A0) = d0.
Proof.
  assert (lem : forall (q : A0 = A0) (r : 1 = q),
    @transport _ (P A0) _ _ (ap (equiv_path _ _) r^)
     (match q as p in (_ = y) return (P y (equiv_path A0 y p))
        with 1 => d0 end) = d0) by (by destruct r).
  unfold equiv_rect; simpl.
  rewrite (eisadj (equiv_path A0 A0) 1).
  rewrite <- (inv_V (eissect (equiv_path A0 A0) 1)).
  apply lem.
Defined.

Section Functorish.
(* We do not need composition to be preserved. *)
Global Class Functorish (F : Type -> Type) := {
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
  refine (equiv_rect (fun A' e => IsEquiv (fmap F e)) _ _ (BuildEquiv _ _ f _)).
  refine (transport _ (fmap_idmap F)^ _).
Defined.

Proposition fmap_agrees_with_univalence {A B} (f : A -> B) `{IsEquiv _ _ f}
  : fmap F f = equiv_path _ _ (ap F (path_universe f)).
Proof.
  refine (equiv_rect
    (fun A' e => fmap F e = equiv_path _ _ (ap F (path_universe e)))
    _ _ (BuildEquiv _ _ f _)).
  path_via (idmap : F A -> F A).
    apply fmap_idmap.
  change (equiv_idmap A) with (equiv_path A A 1).
  rewrite (@eta_path_universe _ A A 1). exact 1.
Defined.

End Functorish.
End AssumeFunext.
End AssumeUnivalence.
