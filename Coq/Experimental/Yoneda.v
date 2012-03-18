(* The Yoneda lemma, first proved by Egbert Rijke. *)

Add LoadPath "..".
Require Import Paths Fibrations Equivalences Funext.

Definition hom {A : Type} (P Q : A -> Type) := forall x, P x -> Q x.

Definition Y {A : Type} (a : A) := (fun x => x ~~> a).

Axiom extensionality : funext_dep_statement.

Lemma Yoneda {A : Type} (P : A -> Type) (a : A) : P a <~> hom (Y a) P.
Proof.
  exists (fun (u : P a) x (p : x ~~> a) => transport (!p) u).
  apply @hequiv_is_equiv with (g := (fun (eta : hom (Y a) P) => eta a (idpath a))); auto.
  intro eta.
  apply extensionality; intro x.
  apply extensionality; intro p. 
  unfold Y in p.
  path_induction.
Defined.

Lemma Y_full_and_faithful {A : Type} (P : A -> Type) (x y : A) : (x ~~> y) <~> hom (Y x) (Y y).
Proof.
  apply @Yoneda with (P := (fun z => z ~~> y)).
Defined.

Lemma total_equivalence {A : Type} (P Q : A -> Type) :
  (forall x, P x <~> Q x) -> sigT P <~> sigT Q.
Proof.
  intro tau.
  exists (fun (u : sigT P) => existT Q (projT1 u) (tau (projT1 u) (projT2 u))).
  apply @hequiv_is_equiv with
    (g := (fun (v : sigT Q) => existT P (projT1 v) ((tau (projT1 v))^-1 (projT2 v)))).
  intros [x ?].
  simpl.
  apply total_path with (p := idpath x).
  simpl.
  apply inverse_is_section.
  intros [x ?].
  simpl.
  apply total_path with (p := idpath x).
  simpl.
  apply inverse_is_retraction.
Defined.


