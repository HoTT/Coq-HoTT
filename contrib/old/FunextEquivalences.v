Require Import Paths Equivalences UsefulEquivalences Funext HLevel.
Require Import ExtensionalityAxiom.

(** This file defines some useful equivalences that require functional
   extensionality, usually involving equivalences between function
   spaces. *)

(** Currying and uncurrying are equivalences. *)

Definition curry_equiv A B C : (A * B -> C) <~> (A -> B -> C).
Proof.
  apply (equiv_from_hequiv (fun f => fun a b => f (a,b)) (fun g => fun x => g (fst x) (snd x)));
  now repeat by_extensionality.
Defined.

(** Flipping the arguments of a two-variable function is an equivalence. *)

Definition flip_equiv A B C : (A -> B -> C) <~> (B -> A -> C).
Proof.
  apply (equiv_from_hequiv (fun f => fun b a => f a b) (fun g => fun a b => g b a));
  now repeat by_extensionality.
Defined.

(** Pre- and post-composing by an equivalence is an equivalence. *)

Lemma precomp_equiv A B C (g : A <~> B) : (B -> C) <~> (A -> C).
Proof.
  apply (equiv_from_hequiv (fun h => h o g) (fun k => k o (g ^-1))) ;
    by_extensionality.
  now apply map; hott_simpl.
  now apply map; hott_simpl.
Defined.

Lemma postcomp_equiv A B C (g : B <~> C) : (A -> B) <~> (A -> C).
Proof.
  apply (equiv_from_hequiv (fun h => g o h) (fun k => (g ^-1) o k)) ;
    by_extensionality.
  now apply inverse_is_section.
  now apply inverse_is_retraction.
Defined.

Lemma postcomp_equiv_dep A P Q (g : forall a:A, P a <~> Q a) :
  (forall a, P a) <~> (forall a, Q a).
Proof.
  apply (equiv_from_hequiv (fun f a => g a (f a)) (fun k a => (g a ^-1) (k a)));
    by_extensionality.
  now apply inverse_is_section.
  now apply inverse_is_retraction.
Defined.

(** The space of factorizations through an equivalence is contractible. *)

Lemma equiv_postfactor_contr A B C (g : B <~> C) (h : A -> C) :
  is_contr { f : A -> B &  g o f == h }.
Proof.
  apply contr_equiv_contr with ({f : A -> B & g o f = h}).
  apply total_equiv.
  now intros; apply strong_funext_equiv.
  apply (equiv_is_equiv (postcomp_equiv _ _ _ g) h).
Defined.

Lemma equiv_prefactor_contr A B C (f : A <~> B) (h : A -> C) :
  is_contr { g : B -> C &  g o f == h }.
Proof.
  apply contr_equiv_contr with ({g : B -> C & g o f = h}).
  apply total_equiv.
  intros g; apply strong_funext_equiv.
  apply (equiv_is_equiv (precomp_equiv _ _ _ f) h).
Defined.

Section IsHisoIsProp.
  (** We show that [is_hiso] is a prop, and hence equivalent to [is_equiv].  *)

  (** How can we avoid wasting time on lemmas such as the one below? *)

  Definition is_hiso' {A B : Type} (f : A -> B) :=
    ({g : B -> A & forall y, f (g y) = y} * {h : B -> A & forall x, h (f x) = x})%type.

  Lemma is_hiso'_equiv_is_hiso {A B} (f : A -> B) : is_hiso' f <~> is_hiso f.
  Proof.
    pose (e := fun (q : is_hiso' f) =>
      {| hiso_section := pr1 (fst q) ;
         hiso_is_section := pr2 (fst q) ;
         hiso_retraction := pr1 (snd q) ;
         hiso_is_retraction := pr2 (snd q) |}).
    pose (einv := fun (p : is_hiso f) =>
      ((hiso_section p; hiso_is_section p), (hiso_retraction p; hiso_is_retraction p)) : is_hiso' f).
    apply (equiv_from_hequiv e einv).
    now intros [g G h H]; unfold e, einv; apply idpath.
    now intros [[g G] [h H]]; unfold e, einv; apply idpath.
  Defined.

  Theorem is_hiso'_is_prop A B (f : A -> B) : is_prop (is_hiso' f).
  Proof.
    apply allpath_prop.
    intros [gG hH] [jJ kK].
    set (e := equiv_from_hiso {| hiso_map := f ; hiso_is_hiso := is_hiso'_equiv_is_hiso f (gG, hH) |}).
    apply prod_path; apply contr_path.
    apply (equiv_postfactor_contr _ _ _ e (idmap B)).
    apply (equiv_prefactor_contr _ _ _ e (idmap A)).
  Defined.

  Theorem is_hiso_is_prop A B (f : A -> B) : is_prop (is_hiso f).
  Proof.
    apply @hlevel_equiv with (A := is_hiso' f).
    apply is_hiso'_equiv_is_hiso.
    apply is_hiso'_is_prop.
  Defined.
    
  Theorem is_equiv_is_hiso_equiv A B (f : A -> B) : is_equiv f <~> is_hiso f.
  Proof.
    apply prop_iff_equiv.
    apply is_equiv_is_prop.
    apply is_hiso_is_prop.
    apply is_hiso_from_is_equiv.
    apply is_equiv_from_is_hiso.
  Defined.
End IsHisoIsProp.

(** Cartesian products have the correct universal property. *)

Lemma prod_equiv A B T :
  (T -> A) * (T -> B) <~> (T -> A * B).
Proof.
  apply (equiv_from_hequiv
    (fun fg => fun t => (fst fg t, snd fg t))
    (fun h => (fun t => fst (h t), fun t => snd (h t)))).
  intros h; apply funext; intros t; simpl.
  destruct (h t) as [a b]; auto.
  intros [f g]; apply prod_path; apply funext; intros t; auto.
Defined.

(** Given an iterated fibration, to give a section of the composite fibration is
   equivalent to giving a section of the first fibration and a section over that
   of the second.

   Did you recognize this as the axiom of choice? I did, eventually...
 *)

Lemma section_total_equiv A (P : fibration A) (Q : forall a, fibration (P a)) :
  (forall a, {b : P a & Q a b}) <~> {s : section P & forall a, Q a (s a) }.
Proof.
  apply (ac_equiv eta_dep_rule weak_funext).
Defined.

Section SectionAssoc.
  (** The space of sections of fibrations is "associative". *)

  Hypotheses (A : Type) (P : fibration A) (Q : forall x, fibration (P x)).

  Let sa : (forall x (u : P x), Q x u) -> forall xp : total P, Q (pr1 xp) (pr2 xp) :=
    (fun f xu => f (pr1 xu) (pr2 xu)).

  Let sainv : (forall xp : total P, Q (pr1 xp) (pr2 xp)) -> forall x (u : P x), Q x u :=
    (fun f x u => f (x; u)).
    
  Definition section_assoc :
    (forall x (u : P x), Q x u) <~> (forall xu : total P, Q (pr1 xu) (pr2 xu)).
  Proof.
    apply (equiv_from_hequiv sa sainv); unfold sa, sainv;
      now repeat by_extensionality.
  Defined.
End SectionAssoc.

Section SectionAssocSum.
  (** And similarly for sums. *)

  Hypotheses (A : Type) (P : fibration A) (Q : fibration (total P)).

  Let sa : (forall x (u : P x), Q (x;u)) -> section Q.
  Proof.
    intros f [x p]; exact (f x p).
  Defined.

  Let sainv : section Q -> (forall x (u : P x), Q (x;u)) :=
    fun f x p => f (x; p).
    
  Definition section_assoc_sum :
    (forall x (u : P x), Q (x;u)) <~> section Q.
  Proof.
    apply (equiv_from_hequiv sa sainv); unfold sa, sainv;
    repeat by_extensionality.
  Defined.

End SectionAssocSum.

(* And "commutative". *)

Definition section_comm (A : Type) (B : Type) (P : A -> B -> Type) :
  (forall a b, P a b) <~> (forall b a, P a b).
Proof.
  apply (equiv_from_hequiv (fun f b a => f a b) (fun f a b => f b a)); 
  repeat by_extensionality.
Defined.

Section SectionPathsEquiv.

  (* The space of sections of a type dependent on paths with one end
     free is equivalent, by the eliminator, to the fiber over the
     identity path. *)

  Variable A : Type.
  Variable x : A.
  Variable P : forall y, fibration (x = y).

  Let sa : (forall y (p: x = y), P y p) -> P x (idpath x) :=
    fun Z => Z x (idpath x).

  Let sainv : P x (idpath x) -> forall y (p: x = y), P y p.
  Proof.
    intros u y p.
    induction p.
    exact u.
  Defined.

  Definition section_paths_equiv :
    (forall y (p: x = y), P y p) <~> P x (idpath x).
  Proof.
    apply (equiv_from_hequiv sa sainv); unfold sa, sainv; simpl.
    now auto.
    now repeat by_extensionality; path_induction.
  Defined.
End SectionPathsEquiv.

(* Finally, we can prove that [is_adjoint_equiv] is equivalent to [is_equiv]. *)


(*** UNFINISHED DOWN HERE


Theorem is_adjoint_equiv_equiv A B (f : A -> B) :
  is_equiv f <~> is_adjoint_equiv f.
Proof.
  unfold is_equiv, is_contr.
  apply @equiv_compose with
    (B := {g: forall y:B, hfiber f y & forall y y0, y0 = g y}).
  apply section_total_equiv.
  unfold hfiber.
  set (X := {g : B -> A & forall y:B, f (g y) = y}).
  set (Y := forall y : B, {x : A & f x = y}).
  set (k := equiv_inverse
    (section_total_equiv B (fun _ => A) (fun y x => f x = y)) : X <~> Y).
  apply @equiv_compose with
    (B := {gs : X & forall y y0, y0 = k gs y}).
  apply equiv_inverse.
  exists (total_map k (fun gs => idmap
    (forall (y : B) (y0 : {x : A & f x = y}), y0 = k gs y))).
  apply pullback_total_is_equiv with (f := k)
    (Q := fun g => forall (y : B) (y0 : {x : A & f x = y}), y0 = g y).
  unfold X.
  apply @equiv_compose with
    (B := {g : B -> A & { s : forall y, f (g y) = y &
      forall (y : B) (y0 : {x : A & f x = y}), y0 = k (g;s) y}}).
  apply equiv_inverse.
  apply total_assoc_sum with
    (Q := fun gs => forall (y : B) (y0 : {x : A & f x = y}), y0 = k gs y).
  unfold is_adjoint_equiv.
  cut (forall g,
    {s : forall y : B, f (g y) = y &
      forall (y : B) (y0 : {x : A & f x = y}), y0 = k (g ; s) y}
    <~>
    {is_section : forall y : B, f (g y) = y &
      {is_retraction : forall x : A, g (f x) = x &
        forall x : A, map f (is_retraction x) = is_section (f x)}}).
  intros H. apply total_equiv with (g := H). intros g; apply (pr2 (H g)).
  intros g.
  cut (forall s,
    (forall (y : B) (y0 : {x : A & f x = y}), y0 = k (g ; s) y)
    <~>
    {is_retraction : forall x : A, g (f x) = x &
      forall x : A, map f (is_retraction x) = s (f x)}).
  intros H. apply total_equiv with H.  intros s; apply (pr2 (H s)).
  intros s.
  apply @equiv_compose with
    (B := forall (y : B) (x : A) (p : f x = y), (x;p) = k (g;s) y).
  apply postcomp_equiv_dep. intros y.
  apply equiv_inverse.
  apply section_assoc_sum with (Q := fun y0 => y0 = k (g;s) y).
  apply @equiv_compose with
    (B := forall (y : B) (x : A) (p : f x = y),
      { q : x = pr1 (k (g;s) y) &
        transport q p = pr2 (k (g;s) y)}).
  apply postcomp_equiv_dep; intros y.
  apply postcomp_equiv_dep; intros x.
  apply postcomp_equiv_dep; intros p.
  apply total_paths_equiv.
  unfold k; simpl. clear X Y k.
  apply @equiv_compose with
    (B := forall (x : A) (y : B) (p : f x = y),
      {q : x = g y & transport (P := fun x0 : A => f x0 = y) q p = s y}).
  apply section_comm.
  apply @equiv_compose with
    (B := forall x:A, { r : g (f x) = x & map f r = s (f x)}).
  2:apply section_total_equiv.
  apply postcomp_equiv_dep; intros x.
  apply @equiv_compose with
    (B := forall (y : B) (p : f x = y),
      {q : x = g y & !map f q @ p = s y}).
  apply postcomp_equiv_dep; intros y.
  apply postcomp_equiv_dep; intros p.
  apply equiv_inverse.
  apply @equiv_compose with
    (B := {q : x = g y &
      transport (P := fun y0 => y0 = y) (map f q) p = s y}).
  apply total_equiv with
    (g := fun q:x = g y => concat (trans_is_concat_opp (map f q) p)).
  intros q; apply concat_is_equiv_left.
  apply total_equiv with
    (g := fun q:x = g y => concat (map_trans (fun y0 => y0 = y) f q p)).
  intros q; apply concat_is_equiv_left.
  apply @equiv_compose with
    (B := {r : x = g (f x) & !map f r @ idpath (f x) = s (f x)}).
  Focus 2.
  apply @equiv_compose with
    (B := {r : x = g (f x) & map f (!r) = s (f x)}).
  apply @equiv_compose with
    (B := {r : x = g (f x) & !map f r = s (f x)}).
  apply total_equiv with (fun r:x = g (f x) =>
    concat (!idpath_right_unit _ _ _ (!map f r))).
  intros r; apply concat_is_equiv_left.
  apply total_equiv with (fun r:x = g (f x) =>
    concat (opposite_map _ _ f _ _ r)).
  intros r; apply concat_is_equiv_left.
  exists (total_map
    (P := fun r => map f (!r) = s (f x))
    (Q := fun r => map f r = s (f x))
    (opposite_equiv x (g (f x)))
    (fun r => idmap (map f (!r) = s (f x)))).
  refine (pullback_total_is_equiv
    (fun r => map f r = s (f x)) (opposite_equiv x (g (f x)))).
  refine (section_paths_equiv B (f x)
    (fun y p => {q : x = g y & !map f q @ p = s y})).
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

****)
