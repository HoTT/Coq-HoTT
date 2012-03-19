Require Import Paths Equivalences UsefulEquivalences Funext UnivalenceAxiom HLevel.

(** This file defines some useful equivalences that require functional
   extensionality, usually involving equivalences between function
   spaces. *)

(** Currying and uncurrying are equivalences. *)

Definition curry_equiv A B C : (A * B -> C) <~> (A -> B -> C).
Proof.
  exists (fun f => fun a b => f (a,b)).
  apply hequiv_is_equiv with (fun g => fun x => g (fst x) (snd x)).
  intro f; apply funext; intro a; apply funext; intro b; auto.
  intro g; apply funext; intros [a b]; auto.
Defined.

(** Flipping the arguments of a two-variable function is an equivalence. *)

Definition flip_equiv A B C : (A -> B -> C) <~> (B -> A -> C).
Proof.
  exists (fun f => fun b a => f a b).
  apply hequiv_is_equiv with (fun g => fun a b => g b a).
  intro g; apply funext; intro a; apply funext; intro b; auto.
  intro f; apply funext; intro b; apply funext; intro a; auto.
Defined.

(** Pre- and post-composing by an equivalence is an equivalence. *)

Lemma precomp_equiv A B C (g : A <~> B) : (B -> C) <~> (A -> C).
Proof.
  exists (fun h => h o g).
  apply @hequiv_is_equiv with (g := fun k => k o (g ^-1));
    intros k; apply funext; intros a; unfold compose; simpl; apply map.
  apply inverse_is_retraction.
  apply inverse_is_section.
Defined.

Lemma postcomp_equiv A B C (g : B <~> C) : (A -> B) <~> (A -> C).
Proof.
  exists (fun h => g o h).
  apply @hequiv_is_equiv with (g := fun k => (g ^-1) o k);
    intros k; apply funext; intros a; unfold compose; simpl.
  apply inverse_is_section.
  apply inverse_is_retraction.
Defined.

Lemma postcomp_equiv_dep A P Q (g : forall a:A, P a <~> Q a) :
  (forall a, P a) <~> (forall a, Q a).
Proof.
  exists (fun f a => g a (f a)).
  apply @hequiv_is_equiv with (g := fun k a => (g a ^-1) (k a));
    intros k; apply funext_dep; intros a; unfold compose; simpl.
  apply inverse_is_section.
  apply inverse_is_retraction.
Defined.

(** The space of factorizations through an equivalence is contractible. *)

Lemma equiv_postfactor_contr A B C (g : B <~> C) (h : A -> C) :
  is_contr { f : A -> B &  g o f ~~>= h }.
Proof.
  apply contr_equiv_contr with ({f : A -> B & g o f ~~> h}).
  apply total_equiv with (fun f => happly).
  intros f; apply strong_funext.
  refine (pr2 (postcomp_equiv _ _ _ g) h).
Defined.

Lemma equiv_prefactor_contr A B C (f : A <~> B) (h : A -> C) :
  is_contr { g : B -> C &  g o f ~~>= h }.
Proof.
  apply contr_equiv_contr with ({g : B -> C & g o f ~~> h}).
  apply total_equiv with (fun g => happly).
  intros g; apply strong_funext.
  refine (pr2 (precomp_equiv _ _ _ f) h).
Defined.

(** It follows that [is_hiso] is a prop, and hence equivalent to [is_equiv].  *)

Theorem is_hiso_is_prop A B (f : A -> B) : is_prop (is_hiso f).
Proof.
  apply allpath_prop.
  intros [g1 h1] [g2 h2].
  set (feq := (f ; hiso_to_equiv f (g1,h1)) : A <~> B).
  apply prod_path; apply contr_path.
  refine (equiv_prefactor_contr _ _ _ feq (idmap A)).
  refine (equiv_postfactor_contr _ _ _ feq (idmap B)).
Defined.

Theorem is_equiv_is_hiso_equiv A B (f : A -> B) : is_equiv f <~> is_hiso f.
Proof.
  apply prop_iff_equiv.
  apply is_equiv_is_prop.
  apply is_hiso_is_prop.
  intros fiseq; exact (equiv_to_hiso (f; fiseq)).
  apply hiso_to_equiv.
Defined.

(** Cartesian products have the correct universal property. *)

Lemma prod_equiv A B T :
  (T -> A) * (T -> B) <~> (T -> A * B).
Proof.
  exists (fun fg => fun t => (fst fg t, snd fg t)).
  apply @hequiv_is_equiv with
    (fun h => (fun t => fst (h t), fun t => snd (h t))).
  intros h; apply funext; intros t; simpl.
  destruct (h t) as [a b]; auto.
  intros [f g]; apply prod_path; apply funext; intros t; auto.
Defined.

(** Given an iterated fibration, to give a section of the composite
   fibration is equivalent to giving a section of the first fibration and
   a section over that of the second.  *)

Lemma section_total_equiv A (P : A -> Type) (Q : forall a, P a -> Type) :
  (forall a, sigT (Q a)) <~> {s : forall a, P a & forall a, Q a (s a) }.
Proof.
  exists (fun f => (existT (fun s => forall a, Q a (s a))
    (fun a => pr1 (f a)) (fun a => pr2 (f a)))).
  apply hequiv_is_equiv with
    (g := fun sr:{s : forall a, P a & forall a, Q a (s a) } =>
      let (s,r) := sr in (fun a => existT (Q a) (s a) (r a))).
  intros [s r].
  set (p := funext_dep (f := eta_dep s) (g := s) (fun a => idpath (s a))).
  apply total_path with p; simpl.
  apply funext_dep; intros a.
  apply (concat (trans_map p
    (fun s' (r': forall a, Q a (s' a)) => r' a) (eta_dep r))).
  path_via (transport (happly_dep p a) (eta_dep r a)).
  unfold happly_dep.
  apply @map_trans with (f := fun h : forall a' : A, P a' => h a).
  path_via (transport (idpath (s a)) (eta_dep r a)).
  apply happly, map.
  apply funext_dep_compute with
    (f := eta_dep s) (g := s) (p := fun a' : A => idpath (s a')).
  intros f.
  apply funext_dep; intros a.
  destruct (f a); auto.
Defined.

(** The space of sections of fibrations is "associative". *)

Section SectionAssoc.

  Hypotheses (A:Type) (P : A -> Type) (Q : forall x, P x -> Type).

  Let sa1 : (forall (x:A) (p:P x), Q x p)
    -> forall xp:sigT P, Q (pr1 xp) (pr2 xp).
  Proof.
    intros f [x p]; exact (f x p).
  Defined.

  Let sa2 : (forall xp:sigT P, Q (pr1 xp) (pr2 xp))
    -> forall (x:A) (p:P x), Q x p.
  Proof.
    intros f x p; exact (f (x;p)).
  Defined.
    
  Definition section_assoc :
    (forall (x:A) (p:P x), Q x p) <~> (forall xp:sigT P, Q (pr1 xp) (pr2 xp)).
  Proof.
    exists sa1.
    apply hequiv_is_equiv with sa2.
    intros f; apply funext_dep; intros [x p]; auto.
    intros f; apply funext_dep; intros p; apply funext_dep; intros x; auto.
  Defined.

End SectionAssoc.

Section SectionAssocSum.

  Hypotheses (A:Type) (P : A -> Type) (Q : sigT P -> Type).

  Let sa1 : (forall (x:A) (p:P x), Q (x;p))
    -> forall xp:sigT P, Q xp.
  Proof.
    intros f [x p]; exact (f x p).
  Defined.

  Let sa2 : (forall xp:sigT P, Q xp)
    -> forall (x:A) (p:P x), Q (x;p).
  Proof.
    intros f x p; exact (f (x;p)).
  Defined.
    
  Definition section_assoc_sum :
    (forall (x:A) (p:P x), Q (x;p)) <~> (forall xp:sigT P, Q xp).
  Proof.
    exists sa1.
    apply hequiv_is_equiv with sa2.
    intros f; apply funext_dep; intros [x p]; auto.
    intros f; apply funext_dep; intros p; apply funext_dep; intros x; auto.
  Defined.

End SectionAssocSum.

(* And "commutative". *)

Definition section_comm (A:Type) (B:Type) (P : A -> B -> Type) :
  (forall a b, P a b) <~> (forall b a, P a b).
Proof.
  exists (fun f b a => f a b).
  apply hequiv_is_equiv with (fun f a b => f b a).
  intros f; apply funext_dep; intros y; apply funext_dep; intros x; auto.
  intros f; apply funext_dep; intros x; apply funext_dep; intros y; auto.
Defined.

(* The space of sections of a type dependent on paths with one end
   free is equivalent, by the eliminator, to the fiber over the
   identity path. *)

Program Definition section_paths_equiv A (x:A)
  (P : forall (b:A), x~~>b -> Type) :
  (forall (y:A) (p: x ~~> y), P y p) <~> P x (idpath x)
  := (_ ; hequiv_is_equiv _ _ _ _).
Next Obligation.
  intros A x P Z.
  exact (Z x (idpath x)).
Defined.
Next Obligation.
  intros A x P z y p.
  induction p. exact z.
Defined.
Next Obligation.
  intros A x P z;
    unfold section_paths_equiv_obligation_1, section_paths_equiv_obligation_2.
  auto.
Defined.
Next Obligation.
  unfold section_paths_equiv_obligation_1, section_paths_equiv_obligation_2.
  intros A x P Z; apply funext_dep; intros y; apply funext_dep; intros p.
  induction p. auto.
Defined.

(* Finally, we can prove that [is_adjoint_equiv] is equivalent to [is_equiv]. *)

Theorem is_adjoint_equiv_equiv A B (f : A -> B) :
  is_equiv f <~> is_adjoint_equiv f.
Proof.
  unfold is_equiv, is_contr.
  apply @equiv_compose with
    (B := {g: forall y:B, hfiber f y & forall y y0, y0 ~~> g y}).
  apply section_total_equiv.
  unfold hfiber.
  set (X := {g : B -> A & forall y:B, f (g y) ~~> y}).
  set (Y := forall y : B, {x : A & f x ~~> y}).
  set (k := equiv_inverse
    (section_total_equiv B (fun _ => A) (fun y x => f x ~~> y)) : X <~> Y).
  apply @equiv_compose with
    (B := {gs : X & forall y y0, y0 ~~> k gs y}).
  apply equiv_inverse.
  exists (total_map k (fun gs => idmap
    (forall (y : B) (y0 : {x : A & f x ~~> y}), y0 ~~> k gs y))).
  apply pullback_total_is_equiv with (f := k)
    (Q := fun g => forall (y : B) (y0 : {x : A & f x ~~> y}), y0 ~~> g y).
  unfold X.
  apply @equiv_compose with
    (B := {g : B -> A & { s : forall y, f (g y) ~~> y &
      forall (y : B) (y0 : {x : A & f x ~~> y}), y0 ~~> k (g;s) y}}).
  apply equiv_inverse.
  apply total_assoc_sum with
    (Q := fun gs => forall (y : B) (y0 : {x : A & f x ~~> y}), y0 ~~> k gs y).
  unfold is_adjoint_equiv.
  cut (forall g,
    {s : forall y : B, f (g y) ~~> y &
      forall (y : B) (y0 : {x : A & f x ~~> y}), y0 ~~> k (g ; s) y}
    <~>
    {is_section : forall y : B, f (g y) ~~> y &
      {is_retraction : forall x : A, g (f x) ~~> x &
        forall x : A, map f (is_retraction x) ~~> is_section (f x)}}).
  intros H. apply total_equiv with (g := H). intros g; apply (pr2 (H g)).
  intros g.
  cut (forall s,
    (forall (y : B) (y0 : {x : A & f x ~~> y}), y0 ~~> k (g ; s) y)
    <~>
    {is_retraction : forall x : A, g (f x) ~~> x &
      forall x : A, map f (is_retraction x) ~~> s (f x)}).
  intros H. apply total_equiv with H.  intros s; apply (pr2 (H s)).
  intros s.
  apply @equiv_compose with
    (B := forall (y : B) (x : A) (p : f x ~~> y), (x;p) ~~> k (g;s) y).
  apply postcomp_equiv_dep. intros y.
  apply equiv_inverse.
  apply section_assoc_sum with (Q := fun y0 => y0 ~~> k (g;s) y).
  apply @equiv_compose with
    (B := forall (y : B) (x : A) (p : f x ~~> y),
      { q : x ~~> pr1 (k (g;s) y) &
        transport q p ~~> pr2 (k (g;s) y)}).
  apply postcomp_equiv_dep; intros y.
  apply postcomp_equiv_dep; intros x.
  apply postcomp_equiv_dep; intros p.
  apply total_paths_equiv.
  unfold k; simpl. clear X Y k.
  apply @equiv_compose with
    (B := forall (x : A) (y : B) (p : f x ~~> y),
      {q : x ~~> g y & transport (P := fun x0 : A => f x0 ~~> y) q p ~~> s y}).
  apply section_comm.
  apply @equiv_compose with
    (B := forall x:A, { r : g (f x) ~~> x & map f r ~~> s (f x)}).
  2:apply section_total_equiv.
  apply postcomp_equiv_dep; intros x.
  apply @equiv_compose with
    (B := forall (y : B) (p : f x ~~> y),
      {q : x ~~> g y & !map f q @ p ~~> s y}).
  apply postcomp_equiv_dep; intros y.
  apply postcomp_equiv_dep; intros p.
  apply equiv_inverse.
  apply @equiv_compose with
    (B := {q : x ~~> g y &
      transport (P := fun y0 => y0 ~~> y) (map f q) p ~~> s y}).
  apply total_equiv with
    (g := fun q:x ~~> g y => concat (trans_is_concat_opp (map f q) p)).
  intros q; apply concat_is_equiv_left.
  apply total_equiv with
    (g := fun q:x ~~> g y => concat (map_trans (fun y0 => y0 ~~> y) f q p)).
  intros q; apply concat_is_equiv_left.
  apply @equiv_compose with
    (B := {r : x ~~> g (f x) & !map f r @ idpath (f x) ~~> s (f x)}).
  Focus 2.
  apply @equiv_compose with
    (B := {r : x ~~> g (f x) & map f (!r) ~~> s (f x)}).
  apply @equiv_compose with
    (B := {r : x ~~> g (f x) & !map f r ~~> s (f x)}).
  apply total_equiv with (fun r:x ~~> g (f x) =>
    concat (!idpath_right_unit _ _ _ (!map f r))).
  intros r; apply concat_is_equiv_left.
  apply total_equiv with (fun r:x ~~> g (f x) =>
    concat (opposite_map _ _ f _ _ r)).
  intros r; apply concat_is_equiv_left.
  exists (total_map
    (P := fun r => map f (!r) ~~> s (f x))
    (Q := fun r => map f r ~~> s (f x))
    (opposite_equiv x (g (f x)))
    (fun r => idmap (map f (!r) ~~> s (f x)))).
  refine (pullback_total_is_equiv
    (fun r => map f r ~~> s (f x)) (opposite_equiv x (g (f x)))).
  refine (section_paths_equiv B (f x)
    (fun y p => {q : x ~~> g y & !map f q @ p ~~> s y})).
Defined.

(** And therefore it is a prop. *)

Theorem is_adjoint_equiv_is_prop A B (f : A -> B) :
  is_prop (is_adjoint_equiv f).
Proof.
  apply allpath_prop; intros e1 e2.
  apply equiv_injective with
    (V := is_equiv f)
    (w := equiv_inverse (is_adjoint_equiv_equiv A B f)).
  apply is_equiv_is_prop.
Defined.
