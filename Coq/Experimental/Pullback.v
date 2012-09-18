(**** WORK IN PROGRESS WITH Egbert Rijke ***)

Add LoadPath "..".

Require Import Paths Fibrations.
(* Contractible Funext HLevel  Equivalences FiberEquivalences FunextEquivalences Univalence. *)
Require Import ExtensionalityAxiom.

(** Fiber-wise products work as expected. *)
Section FiberwiseProduct.
  Variable A : Type.
  Variable U V : fibration A.
  
  Definition P (a : A) := (U a * V a)%type.

  Variable W : fibration A.
  Variable h : forall a : A, W a -> U a.
  Variable k : forall a : A, W a -> V a.
  
  Lemma factor : forall a : A, W a -> P a.
  Proof.
    intros a w.
    exact (h a w, k a w).
  Defined.

  Lemma triangle1 : forall a w, fst (factor a w) == h a w.
  Proof.
    auto.
  Defined.

  Lemma triangle2 : forall a w, snd (factor a w) == k a w.
  Proof.
    auto.
  Defined.

  Lemma factor_unique (s : forall a, W a -> P a) :
    (forall a w, fst (s a w) == h a w) ->
    (forall a w, snd (s a w) == k a w) ->
    (forall a w, s a w == factor a w).
  Proof.
    intros e1 e2 a w.
    path_via (fst (s a w), snd (s a w)).
    apply opposite, prod_eta.
    apply prod_path; auto.
  Defined.
End FiberwiseProduct.

Section FiberReplacement.
  (* We show that the fiber replacement of a map is fiber-wise equivalent to it. *)

  Variable A B : Set.
  Variable f : A -> B.

  Definition fiber_replacement f := {y : B & @hfiber A B f y}.

  Lemma fiber_replacement_equiv : A <~> fiber_replacement f.
  Proof.
    apply (equiv_from_hequiv
      (fun x => (f x ; (x ; idpath (f x))) : fiber_replacement f)
      (fun (u : fiber_replacement f) => pr1 (pr2 u))).
    intros [y [x p]].
    simpl.
    apply @total_path with p.
    simpl.
    path_via (x ; p # (idpath (f x))).
    apply trans_sum.

    Focus 2.
    intro; apply idpath.



(** Is it really the case that pullbacks work out, as Steve Awodey suggests? *)

Section Pullback.
  Variable A B C : Type.
  Variable f : A -> C.
  Variable g : B -> C.

  Definition P := { ab : A * B & f (fst ab) == g (snd ab) }.
  Definition p1 (u : P) := fst (pr1 u).
  Definition p2 (u : P) := snd (pr1 u).

  Section UniversalProperty.
    Variable Q : Type.
    Variable h : Q -> A.
    Variable k : Q -> B.
    Hypothesis e : forall z : Q, f (h z) == g (k z).

    Definition factor (z : Q) : P := ((h z, k z) ; e z).

    (** Upper triangle commutes. *)
    Theorem triangle_up (z : Q) : p1 (factor z) == h z.
    Proof.
      auto.
    Defined.

    Theorem triangle_down (z : Q) : p2 (factor z) == k z.
    Proof.
      auto.
    Defined.

    Let uniqueness_elem (u : P) (a : A) (b : B) :
      p1 u == a ->
      p2 u == b ->
      pr1 u == (a, b).
    Proof.
      intros e1 e2.
      path_via (p1 u, p2 u).
      apply opposite, prod_eta.
      apply prod_path; assumption.
    Defined.

    Lemma uniqueness (factor' : Q -> P) :
      (forall z : Q, p1 (factor' z) == h z) ->
      (forall z : Q, p2 (factor' z) == k z) ->
      forall z : Q, factor' z == factor z.
    Proof.
      intros e1 e2 z.
      unfold factor.      
      apply @total_path with (p := uniqueness_elem (factor' z) (h z) (k z) (e1 _) (e2 _)).
      simpl; unfold uniqueness_elem.
      hott_simpl.

      


    
     


End Pullback.




Parameter X Y A : Type.
Parameter f : X -> A.
Parameter g : Y -> A.

Structure Cone (C : Type) := {
  p1 : C -> X ;
  p2 : C -> Y ;
  gamma : forall (c : C), f (p1 c) == g (p2 c)
}.

Implicit Arguments p1 [C].
Implicit Arguments p2 [C].
Implicit Arguments gamma [C].

Definition equal_cone {C : Type} (P Q : Cone C) :=
  forall (alpha : forall (c : C), p1 P c == p1 Q c)
         (beta :  forall (c : C), p2 P c == p2 Q c),
           forall (c : C), gamma P c @ map g (beta c) == map f (alpha c) @ gamma Q c.

Definition r {C : Type} (P : Cone C) {B : Type} (h : B -> C) : Cone B.
Proof.
  refine
    {| 
       p1 := fun (b : B) => p1 P (h b) ;
       p2 := fun (b : B) => p2 P (h b)
    |}.
  intro u.
  apply gamma.
Defined.

Definition is_pullback {C : Type} (P : Cone C) :=
  forall B, is_equiv (@r C P B).

(* We now try to define the pullback. *)

Definition C := { xy : X * Y & f (fst xy) == g (snd xy) }. (* This won't work. *)

Definition P : Cone C.
Proof.
  refine
    {|
      p1 := fun (u : C) => fst (pr1 u) ;
      p2 := fun (u : C) => snd (pr1 u)
    |}.
  intros [[x y] p].
  exact p.
Defined.

(* We define the inverse of r P. *)
Definition rPinv {B : Type} (Q : Cone B) : B -> C.
Proof.
  intro b.
  destruct Q as [h k alpha].
  exists (h b, k b).
  apply alpha.
Defined.

(* Is rinv really the inverse? *)
Lemma r_rPinv {B : Type} (Q : Cone B) : equal_cone (r P (rPinv Q)) Q.
Proof.
Admitted.

Lemma rPinv_r {B : Type} (h : B -> C): forall b : B, rPinv (r P h) b == h b.
Proof.
  intro b.
  destruct (r P h) as [q1 q2 delta].
  unfold rPinv; simpl.
  destruct (h b) as [[x y] p]; simpl in * |- *.
Admitted.
