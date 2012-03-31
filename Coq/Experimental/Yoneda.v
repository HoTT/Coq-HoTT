(* The Yoneda lemma, first proved by Egbert Rijke. *)

Add LoadPath "..".
Require Import Paths Fibrations Equivalences Funext Univalence UnivalenceImpliesFunext.

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

Section Equivalence_of_equivalences.
  (* Here is a nice little observation about equivalences, for which we need univalence,
     it seeems.*)

  Hypothesis univalence : univalence_statement.

  Hypothesis eta : eta_statement.

  Let funext : 

  Variable A B : Type.
  Variable f : A <~> B.

  Let g : (A <~> B) -> (A <~> A).
  Proof.
    intro e.
    exists (fun x => f^-1 (e x)).
    apply @hequiv_is_equiv with (g := (fun y => e^-1 (f y))).
    intro x; path_via (f^-1 (f x)); auto using @inverse_is_section, @inverse_is_retraction.
    intro x; path_via (e^-1 (e x)); auto using @inverse_is_section, @inverse_is_retraction.
  Defined.

  Let h : (A <~> A) -> (A <~> B).
  Proof.
    intro e.
    exists (fun x => f (e^-1 x)).
    apply @hequiv_is_equiv with (g := (fun y => e (f^-1 y))).
    intro y; path_via (f (f^-1 y)); auto using @inverse_is_section, @inverse_is_retraction.
    intro y; path_via (e (e^-1 y)); auto using @inverse_is_section, @inverse_is_retraction.
  Defined.

  Lemma equiv_equiv_equiv : (A <~> B) <~> (A <~> A).
  Proof.
    exists g.
    apply @hequiv_is_equiv with (g := h).
    intro e.
    apply funext.



Section YonedaSpace.

  Variable A : Type.
  Variable P : A -> Type.

  Definition YonedaSpace := forall a, P a <~> hom (Y a) P.

  Let F : YonedaSpace -> forall a, P a <~> P a.
  Proof.
    intros f a.
    exists (fun x => (Yoneda P a)^-1 (f a x)).
    apply @hequiv_is_equiv with (g := (fun x => (f a)^-1 (Yoneda P a x))).
    intro x.
    path_via ((Yoneda P a)^-1 ((Yoneda P a) x)).
    apply inverse_is_section.
    intro x.
    path_via ((f a)^-1 (f a x)).
    apply inverse_is_section.
    apply inverse_is_retraction.
  Defined.

  Let G : (forall a, P a <~> P a) -> YonedaSpace.
  Proof.
    clear F.
    intros g a.
    exists (fun x => Yoneda P a (g a x)).
    apply @hequiv_is_equiv with (g := fun x => (g a)^-1 ((Yoneda P a)^-1 x)).
    intro h.
    path_via ((Yoneda P a) ((Yoneda P a)^-1 h)).
    apply inverse_is_section.
    apply inverse_is_section.
    intro x.
    path_via ((g a)^-1 (g a x)).
    apply inverse_is_retraction.
  Defined.
    
  Lemma YonedaSpace_equiv:
    YonedaSpace <~> forall a, P a <~> P a.
  Proof.
    exists F.
    apply @hequiv_is_equiv with (g := G).
  Admitted.
End YonedaSpace.
  

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


