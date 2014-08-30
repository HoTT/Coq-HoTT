(* -*- mode: coq; mode: visual-line -*- *)

(** ** The cumulative hierarchy [V]. *)

Require Import Overture PathGroupoids HProp Trunc Fibrations Equivalences EquivalenceVarieties UnivalenceImpliesFunext.
Require Import types.Unit types.Bool types.Universe types.Sigma types.Arrow types.Forall.
Require Import hit.minus1Trunc hit.quotient.
Local Open Scope path_scope.
Local Open Scope equiv_scope.


(** ** Pushout with respect to a relation *)

(** This could be implemented using the pushouts in /hit/Pushout.v, where f and g are (fst o pr1) and (snd o pr1), with domain {(a,b) : A * B & R a b}. However, these pushouts weren't implemented when I started this work, and doing it this way is closer to exercise 10.11 of the HoTT book *)

Module Export RPushout.

Private Inductive RPushout {A B : Type} (R : A -> B -> hProp) : Type :=
| inL : A -> RPushout R
| inR : B -> RPushout R.

Axiom glue : forall {A B : Type} (R : A -> B -> hProp)
  (a : A) (b : B) (r : R a b), (inL R a) = (inR R b).

Definition RPushout_rect {A B : Type} {R : A -> B -> hProp}
  (P : RPushout R -> Type)
  (i : forall a : A, P (inL R a)) (j : forall b : B, P (inR R b)) 
  (gl : forall (a : A) (b : B) (r : R a b), (glue R a b r) # (i a) = (j b))
: forall (x : RPushout R), P x
:= fun x => (match x with inL a => (fun _ => i a)
                        | inR b => (fun _ => j b) end) gl.

Axiom RPushout_comp_glue : forall {A B : Type} {R : A -> B -> hProp}
  (P : RPushout R -> Type)
  (i : forall a : A, P (inL R a)) (j : forall b : B, P (inR R b)) 
  (gl : forall (a : A) (b : B) (r : R a b), (glue R a b r) # (i a) = (j b))
  (a : A) (b : B) (r : R a b),
apD (RPushout_rect P i j gl) (glue R a b r) = gl a b r.

End RPushout.

(* The non-depentent eliminator *)

Definition RPushout_rect_nd {A B : Type} (R : A -> B -> hProp)
  (P : Type) (i : A -> P) (j : B -> P)
  (gl : forall (a : A) (b : B) (r : R a b), (i a) = (j b))
: RPushout R -> P
:= RPushout_rect (fun _ => P) i j (fun a b r => transport_const _ _ @ gl a b r).

Definition RPushout_comp_nd_glue {A B : Type} (R : A -> B -> hProp) 
  (P : Type) (i : A -> P) (j : B -> P)
  (gl : forall (a : A) (b : B) (r : R a b), (i a) = (j b))
  (a : A) (b : B) (r : R a b)
: ap (RPushout_rect_nd R P i j gl) (glue R a b r) = gl a b r.
Proof.
  apply (cancelL (transport_const (glue R a b r) (i a))).
  path_via (apD (RPushout_rect_nd R P i j gl) (glue R a b r)).
  apply (apD_const (RPushout_rect_nd R P i j gl) (glue R a b r))^.
  refine (RPushout_comp_glue (fun _ => P) _ _ _ _ _ _).
Defined.


(** Bitotal relation *)

Definition bitotal {A B : Type} (R : A -> B -> hProp) :=
   (forall a : A, hexists (fun (b : B) => R a b))
 * (forall b : B, hexists (fun (a : A) => R a b)).

(** ** The cumulative hierarchy V *)

Module Export CumulativeHierarchy.

Private Inductive V : Type@{U'} :=
| set {A : Type@{U}} (f : A -> V) : V.

Axiom setext : forall {A B : Type} (R : A -> B -> hProp)
  (bitot_R : bitotal R) (h : RPushout R -> V),
set (h o (inL R)) = set (h o (inR R)).

Axiom is0trunc_V : IsTrunc 0 V.

Definition V_rect (P : V -> Type)
  (H_0trunc : forall v : V, IsTrunc 0 (P v))
  (H_set : forall (A : Type) (f : A -> V) (H_f : forall a : A, P (f a)), P (set f))
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : bitotal R)
    (h : RPushout R -> V) (H_h : forall x : RPushout R, P (h x)),
    (setext R bitot_R h) # (H_set A (h o inL R) (H_h oD inL R))
      = H_set B (h o inR R) (H_h oD inR R) )
: forall v : V, P v
:= fix F (v : V) :=
     (match v with
      | set A f => fun _ _ => H_set A f (fun a => F (f a))
     end) H_setext H_0trunc.

Axiom V_comp_setext : forall (P : V -> Type)
  (H_0trunc : forall v : V, IsTrunc 0 (P v))
  (H_set : forall (A : Type) (f : A -> V) (H_f : forall a : A, P (f a)), P (set f))
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : bitotal R)
    (h : RPushout R -> V) (H_h : forall x : RPushout R, P (h x)),
    (setext R bitot_R h) # (H_set A (h o inL R) (H_h oD inL R))
      = H_set B (h o inR R) (H_h oD inR R) )
  (A B : Type) (R : A -> B -> hProp) (bitot_R : bitotal R) (h : RPushout R -> V),
apD (V_rect P H_0trunc H_set H_setext) (setext R bitot_R h)
= H_setext A B R bitot_R h ((V_rect P H_0trunc H_set H_setext) oD h).

End CumulativeHierarchy.

(* The non-dependent eliminator *)

Definition V_rect_nd (P : Type)
  (H_0trunc : IsTrunc 0 P)
  (H_set : forall (A : Type), (A -> V) -> (A -> P) -> P)
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : bitotal R)
    (h : RPushout R -> V) (H_h : RPushout R -> P),
    H_set A (h o inL R) (H_h o inL R) = H_set B (h o inR R) (H_h o inR R) )
: V -> P.
Proof.
  refine (V_rect _ _ H_set _).
  intros. exact (transport_const _ _ @ H_setext A B R bitot_R h H_h).
Defined.

Definition V_comp_nd_setext (P : Type)
  (H_0trunc : IsTrunc 0 P)
  (H_set : forall (A : Type), (A -> V) -> (A -> P) -> P)
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : bitotal R)
    (h : RPushout R -> V) (H_h : RPushout R -> P),
    H_set A (h o inL R) (H_h o inL R) = H_set B (h o inR R) (H_h o inR R) )
  (A B : Type) (R : A -> B -> hProp) (bitot_R : bitotal R) (h : RPushout R -> V)
: ap (V_rect_nd P H_0trunc H_set H_setext) (setext R bitot_R h)
  = H_setext A B R bitot_R h ((V_rect_nd P H_0trunc H_set H_setext) o h).
Proof.
  apply (cancelL (transport_const (setext R bitot_R h) _)).
  path_via (apD (V_rect_nd P H_0trunc H_set H_setext) (setext R bitot_R h)).
  symmetry; apply (apD_const (V_rect_nd P H_0trunc H_set H_setext)).
  apply (V_comp_setext (fun _ => P)).
Defined.


(** ** Alternative induction principle (This is close to the one from the book) *)

Definition equal_img {A B C : Type} (f : A -> C) (g : B -> C) :=
   (forall a : A, hexists (fun (b : B) => f a = g b))
 * (forall b : B, hexists (fun (a : A) => f a = g b)).

Let setext' {A B : Type} (f : A -> V) (g : B -> V) (eq_img : equal_img f g)
: set f = set g.
Proof.
  pose (R := fun a b => hp (f a = g b) _).
  pose (h := RPushout_rect_nd R V f g (fun _ _ r => r)).
  exact (setext R eq_img h).
Defined.

Definition V_rect'_nd (P : Type)
  (H_0trunc : IsTrunc 0 P)
  (H_set : forall (A : Type), (A -> V) -> (A -> P) -> P)
  (H_setext' : forall (A B : Type) (f : A -> V) (g : B -> V), (equal_img f g) ->
    forall (H_f : A -> P) (H_g : B -> P), (equal_img H_f H_g) ->
    (H_set A f H_f) = (H_set B g H_g) )
: V -> P.
Proof.
  refine (V_rect_nd _ _ H_set _).
  intros A B R bitot_R h H_h.
  apply H_setext'.
  - split.
    + intro a. generalize (fst bitot_R a). apply minus1Trunc_map.
      intros [b r]. exists b. exact (ap h (glue R _ _ r)).
    + intro b. generalize (snd bitot_R b). apply minus1Trunc_map.
      intros [a r]. exists a. exact (ap h (glue R _ _ r)).
  - split.
    + intro a. generalize (fst bitot_R a). apply minus1Trunc_map.
      intros [b r]. exists b. exact (ap H_h (glue R _ _ r)).
    + intro b. generalize (snd bitot_R b). apply minus1Trunc_map.
      intros [a r]. exists a. exact (ap H_h (glue R _ _ r)).
Defined.

(* We might also want to prove the associated computation rules *)
(** Note that the hypothesis H_setext' differs from the one given in section 10.5 of the HoTT book. *)
Definition V_rect' (P : V -> Type)
  (H_0trunc : forall v : V, IsTrunc 0 (P v))
  (H_set : forall (A : Type) (f : A -> V) (H_f : forall a : A, P (f a)), P (set f))
  (H_setext' : forall (A B : Type) (f : A -> V) (g : B -> V)
    (eq_img: equal_img f g)
    (H_f : forall a : A, P (f a)) (H_g : forall b : B, P (g b))
    (H_eqimg : (forall a : A, hexists (fun (b : B) =>
                  hexists (fun (p:f a = g b) => p # (H_f a) = H_g b)))
             * (forall b : B, hexists (fun (a : A) =>
                  hexists (fun (p:f a = g b) => p # (H_f a) = H_g b))) ),
    (setext' f g eq_img) # (H_set A f H_f) = (H_set B g H_g)
  )
: forall v : V, P v.
Proof.
  apply V_rect with H_set; try assumption.
  intros A B R bitot_R h H_h.
  pose (f := h o inL R : A -> V ).
  pose (g := h o inR R : B -> V ).
  pose (H_f := H_h oD inL R : forall a : A, P (f a)).
  pose (H_g := H_h oD inR R : forall b : B, P (g b)).
  assert (eq_img : equal_img f g).
  { split.
    - intro a. generalize (fst bitot_R a). apply minus1Trunc_map.
      intros [b r]. exists b. exact (ap h (glue R _ _ r)).
    - intro b. generalize (snd bitot_R b). apply minus1Trunc_map.
      intros [a r]. exists a. exact (ap h (glue R _ _ r)). }
  path_via (transport P (setext' (h o inL R) (h o inR R) eq_img)
      (H_set A (h o inL R) (H_h oD inL R))).
  { apply (ap (fun p => transport P p (H_set A (h o inL R) (H_h oD inL R)))).
    apply allpath_hprop. }
  apply (H_setext' A B f g eq_img H_f H_g).  split.
  - intro a.
    set (truncb := fst bitot_R a). generalize truncb.
    apply minus1Trunc_map.
    intros [b Rab]. exists b.
    apply min1.
    exists (ap h (glue R _ _ Rab)).
    apply (concatR (apD H_h (glue R _ _ Rab))).
    apply inverse. unfold f, g, compose. apply transport_compose.
  - intros b.
    set (trunca := snd bitot_R b). generalize trunca.
    apply minus1Trunc_map.
    intros [a Rab]. exists a.
    apply min1.
    exists (ap h (glue R _ _ Rab)).
    apply (concatR (apD H_h (glue R _ _ Rab))).
    apply inverse. unfold f, g, compose. apply transport_compose.
Defined.


(** Simpler induction principle when the goal is an hprop *)

Definition V_rect_hprop (P : V -> Type)
  (H_set : forall (A : Type) (f : A -> V) (H_f : forall a : A, P (f a)), P (set f))
  (isHProp_P : forall v : V, IsHProp (P v))
  : forall v : V, P v.
Proof.
  refine (V_rect _ _ H_set _).
  intros. apply allpath_hprop.
Defined.


Section AssumingUA.
Context `{ua : Univalence}.

(** ** Membership relation *)

Definition mem (x : V) : V -> hProp.
Proof.
  refine (V_rect'_nd _ _ _ _). intros A f _.
  exact (hp (hexists (fun a : A => f a = x)) _). simpl.
  intros A B f g eqimg _ _ _. apply path_iff_hProp_uncurried; split; simpl.
  - intro H. refine (minus1Trunc_ind _ H).
    intros [a p]. generalize (fst eqimg a). apply minus1Trunc_map.
    intros [b p']. exists b. path_via (f a).
  - intro H. refine (minus1Trunc_ind _ H).
    intros [b p]. generalize (snd eqimg b). apply minus1Trunc_map.
    intros [a p']. exists a. path_via (g b).
Defined.

Notation "x ∈ v" := (mem x v)
  (at level 30) : set_scope.
Open Scope set_scope.

(** ** Subset relation *)

Definition subset (x : V) (y : V) : hProp
:= hp (forall z : V, z ∈ x -> z ∈ y) _.

Notation "x ⊆ y" := (subset x y)
  (at level 30) : set_scope.


(** ** Bisimulation relation *)
(** The equality in V lives in Type@{U'}. We define the bisimulation relation which is a U-small resizing of the equality in V: it must live in hProp_U : Type{U'}, hence the codomain is hProp@{U'}. We then prove that bisimulation is equality (bisim_equals_id), then use it to prove the key lemma monic_set_present. *)

(* We define bisimulation by double induction on V. We first fix the first argument as set(A,f) and define bisim_aux : V -> hProp, by induction. This is the inner of the two inductions. *)
Let bisim_aux (A : Type) (f : A -> V) (H_f : A -> V -> hProp) : V -> hProp.
Proof.
  apply V_rect'_nd with
    (fun B g _ => hp ( (forall a, hexists (fun b => H_f a (g b)))
                      * forall b, hexists (fun a => H_f a (g b)) ) _
    ).
  exact _.
  intros B B' g g' eq_img H_g H_g' H_img; simpl.
  apply path_iff_hProp_uncurried; split; simpl.
  - intros [H1 H2]; split.
    + intro a. refine (minus1Trunc_ind _ (H1 a)).
      intros [b H3]. generalize (fst eq_img b). apply minus1Trunc_map.
      intros [b' p]. exists b'. exact (transport (fun x => H_f a x) p H3).
    + intro b'. refine (minus1Trunc_ind _ (snd eq_img b')).
      intros [b p]. generalize (H2 b). apply minus1Trunc_map.
      intros [a H3]. exists a. exact (transport (fun x => H_f a x) p H3).
  - intros [H1 H2]; split.
    + intro a. refine (minus1Trunc_ind _ (H1 a)).
      intros [b' H3]. generalize (snd eq_img b'). apply minus1Trunc_map.
      intros [b p]. exists b. exact (transport (fun x => H_f a x) p^ H3).
    + intro b. refine (minus1Trunc_ind _ (fst eq_img b)).
      intros [b' p]. generalize (H2 b'). apply minus1Trunc_map.
      intros [a H3]. exists a. exact (transport (fun x => H_f a x) p^ H3).
Defined.

(* Then we define bisim : V -> (V -> hProp) by induction again *)
Definition bisimulation : V@{U' U} -> V@{U' U} -> hProp@{U'}.
Proof.
  refine (V_rect'_nd (V -> hProp) _ bisim_aux _).
  intros A B f g eq_img H_f H_g H_img.
  apply path_forall.
  refine (V_rect_hprop _ _ _).
  intros C h _; simpl.
  apply path_iff_hProp_uncurried; split; simpl.
  - intros [H1 H2]; split.
    + intro b. refine (minus1Trunc_ind _ (snd H_img b)).
      intros [a p]. generalize (H1 a). apply minus1Trunc_map.
      intros [c H3]. exists c. exact ((ap10 p (h c)) # H3).
    + intro c. refine (minus1Trunc_ind _ (H2 c)).
      intros [a H3]. generalize (fst H_img a). apply minus1Trunc_map.
      intros [b p]. exists b. exact ((ap10 p (h c)) # H3).
  - intros [H1 H2]; split.
    + intro a. refine (minus1Trunc_ind _ (fst H_img a)).
      intros [b p]. generalize (H1 b). apply minus1Trunc_map.
      intros [c H3]. exists c. exact ((ap10 p^ (h c)) # H3).
    + intro c. refine (minus1Trunc_ind _ (H2 c)).
      intros [b H3]. generalize (snd H_img b). apply minus1Trunc_map.
      intros [a p]. exists a. exact ((ap10 p^ (h c)) # H3).
Defined.

Notation "u ~~ v" := (bisimulation u v)
  (at level 30) : set_scope.

Instance reflexive_bisimulation : Reflexive bisimulation.
Proof.
  refine (V_rect_hprop _ _ _).
  intros A f H_f; simpl. split.
  - intro a; apply min1; exists a; auto.
  - intro a; apply min1; exists a; auto.
Defined.

Lemma bisimulation_equals_id : forall u v : V, (u = v) = (u ~~ v).
Proof.
  intros u v.
  apply path_iff_hprop_uncurried; split.
  intro p; exact (transport (fun x => u ~~ x) p (reflexive_bisimulation u)).
  generalize u v.
  refine (V_rect_hprop _ _ _); intros A f H_f.
  refine (V_rect_hprop _ _ _); intros B g _.
  simpl; intros [H1 H2].
  apply setext'. split.
  - intro a. generalize (H1 a). apply minus1Trunc_map.
    intros [b h]. exists b; exact (H_f a (g b) h).
  - intro b. generalize (H2 b). apply minus1Trunc_map.
    intros [a h]. exists a; exact (H_f a (g b) h).
Defined.


(** ** Canonical presentation of V-sets (Lemma 10.5.6) *)

(** Using the regular kernel (with = instead of ~~) also works, but this seems to be a Coq bug, it should lead to a universe inconsistency in the monic_set_present lemma later. This version is the right way to do it. *)
Definition ker_bisim {A} (f : A -> V) (x y : A) := (f x ~~ f y).
Lemma setrel_ker_bisim {A} (f : A -> V) : setrel (ker_bisim f).
Proof.
  intros x y. apply _.
Defined.

Lemma inj_surj_factor_V {A : Type} (f : A -> V)
: exists (C : Type) (e : A -> C) (m : C -> V), IsHSet C * is_epi e * is_mono m * (f = m o e).
Proof.
  pose (C := quotient (setrel_ker_bisim f)).
  assert (IsHSet C) by (unfold C; apply _).
  exists C.
  pose (e := class_of (setrel_ker_bisim f)).
  exists e.
  transparent assert (m : (C -> V)).
  { apply quotient_rect with f.
    intros x y H. path_via (f x). apply transport_const.
    exact (transport (fun X => X) (bisimulation_equals_id (f x) (f y))^ H). }
  exists m.
  split. split. split.
  - assumption.
  - unfold is_epi. refine (quotient_rect _ _ _).
    intro a; apply min1; exists a. exact 1.
    intros x y H. apply allpath_hprop.
  - unfold is_mono. intro u.
    apply hprop_allpath.
    assert (H : forall (x y : C) (p : m x = u) (p' : m y = u), x = y).
    { refine (quotient_rect _ _ _). intro a.
      refine (quotient_rect _ _ _). intros a' p p'.
      + apply related_classes_eq.
        refine (transport (fun X => X) (bisimulation_equals_id _ _) _).
        path_via (m (e a)). path_via (m (e a')).
        exact (p @ p'^).
      + intros; apply allpath_hprop.
      + intros; apply allpath_hprop. }
    intros [x p] [y p'].
    apply path_sigma_hprop; simpl.
    exact (H x y p p').
  - apply path_forall. intro a. reflexivity.
Defined.


Section MonicSetPresent_Uniqueness.
(** Given u : V, we want to show that the representation u = @set Au mu, where Au is an hSet and mu is monic, is unique. *)

Context {u : V} {Au Au': Type} {h : IsHSet Au} {h' : IsHSet Au'} {mu : Au -> V} {mono : is_mono mu}
  {mu' : Au' -> V} {mono' : is_mono mu'} {p : u = set mu} {p' : u = set mu'}.

Lemma eq_img_untrunc : (forall a : Au, {a' : Au' & mu' a' = mu a})
                     * (forall a' : Au', {a : Au & mu a = mu' a'}).
Proof.
  split.
  intro a. exact (untrunc_hprop (mono' (mu a)) (transport (fun x => mu a ∈ x) (p^ @ p') (min1 (a; 1)))).
  intro a'. exact (untrunc_hprop (mono (mu' a')) (transport (fun x => mu' a' ∈ x) (p'^ @ p) (min1 (a'; 1)))).
Defined.

Let e : Au -> Au' := fun a => pr1 (fst eq_img_untrunc a).
Let inv_e : Au' -> Au := fun a' => pr1 (snd eq_img_untrunc a').

Let hom1 : Sect inv_e e.
Proof.
  intro a'.
  apply (is_mono_isinj mu' mono').
  path_via (mu (inv_e a')).
  exact (pr2 (fst eq_img_untrunc (inv_e a'))).
  exact (pr2 (snd eq_img_untrunc a')).
Defined.

Let hom2 : Sect e inv_e.
Proof.
  intro a.
  apply (is_mono_isinj mu mono).
  path_via (mu' (e a)).
  exact (pr2 (snd eq_img_untrunc (e a))).
  exact (pr2 (fst eq_img_untrunc a)).
Defined.

Let path : Au' = Au.
Proof.
  apply path_universe_uncurried.
  apply (equiv_adjointify inv_e e hom2 hom1).
Defined.

Lemma mu_eq_mu' : transport (fun A : Type => A -> V) path^ mu = mu'.
Proof.
  apply path_forall. intro a'.
  path_via (transport (fun X => V) path^ (mu (transport (fun X : Type => X) path^^ a'))).
  apply (@transport_arrow Type (fun X : Type => X) (fun X => V) Au Au' path^ mu a').
  path_via (mu (transport idmap path^^ a')).
  apply transport_const.
  path_via (mu (inv_e a')).
  2: apply (pr2 (snd eq_img_untrunc a')).
  refine (ap mu _).
  path_via (transport idmap path a').
  exact (ap (fun x => transport idmap x a') (inv_V path)).
  apply transport_path_universe.
Defined.

Lemma monic_set_present_uniqueness : (Au; (mu; (h, mono, p))) = (Au'; (mu'; (h', mono', p'))) :> {A : Type & {m : A -> V & IsHSet A * is_mono m * (u = set m)}}.
Proof.
  apply path_sigma_uncurried; simpl.
  exists path^.
  path_via (path^ # mu; transportD (fun A => A -> V) (fun A m => IsHSet A * is_mono m * (u = set m)) path^ mu (h, mono, p)).
  apply (@transport_sigma Type (fun A => A -> V) (fun A m => IsHSet A * is_mono m * (u = set m)) Au Au' path^ (mu; (h, mono, p))).
  apply path_sigma_hprop; simpl.
  exact mu_eq_mu'.
Defined.

End MonicSetPresent_Uniqueness.

(** This lemma actually says a little more than 10.5.6, i.e., that Au is a hSet *)
Lemma monic_set_present : forall u : V, exists (Au : Type) (m : Au -> V),
  (IsHSet Au) * (is_mono m) * (u = set m).
Proof.
  apply V_rect_hprop.
  - intros A f _.
    destruct (inj_surj_factor_V f) as [Au [eu [mu (((hset_Au, epi_eu), mono_mu), factor)]]].
    exists Au, mu. split. exact (hset_Au, mono_mu).
    apply setext'; split.
    + intro a. apply min1; exists (eu a). exact (ap10 factor a).
    + intro a'. generalize (epi_eu a'). apply minus1Trunc_map.
      intros [a p]. exists a. path_via (mu (eu a)).
      exact (ap10 factor a). exact (ap mu p). 
  - intro v. apply hprop_allpath.
    intros [Au [mu ((hset, mono), p)]].
    intros [Au' [mu' ((hset', mono'), p')]].
    apply monic_set_present_uniqueness.
Defined.

Definition type_of_members (u : V) : Type := pr1 (monic_set_present u).

Notation "[ u ]" := (type_of_members u)
  (at level 20) : set_scope.

Definition func_of_members {u : V} : [u] -> V := pr1 (pr2 (monic_set_present u)) : [u] -> V.

Definition is_hset_typeofmembers {u : V} : IsHSet ([u]) := fst (fst (pr2 (pr2 (monic_set_present u)))).

Definition is_mono_funcofmembers {u : V} : is_mono func_of_members := snd (fst (pr2 (pr2 (monic_set_present u)))).

Definition is_valid_presentation (u : V) : u = set func_of_members := snd (pr2 (pr2 (monic_set_present u))).


(** ** Lemmas 10.5.8 (i) & (vii), we put them here because they are useful later *)
Lemma extensionality : forall {x y : V}, (x ⊆ y * y ⊆ x) <-> x = y.
Proof.
  refine (V_rect_hprop _ _ _). intros A f _.
  refine (V_rect_hprop _ _ _). intros B g _.
  split.
  - intros [H1 H2]. apply setext'. split.
    + intro. refine (minus1Trunc_ind _ (H1 (f a) (min1 (a;1)))).
      intros [b p]. apply min1. exists b. exact p^.
    + intro. apply (H2 (g b)). apply min1; exists b; reflexivity.
  - intro p; split.
    + intros z Hz. apply (transport (fun x => z ∈ x) p Hz).
    + intros z Hz. apply (transport (fun x => z ∈ x) p^ Hz).
Qed.

Lemma mem_induction (C : V -> hProp)
: (forall v, (forall x, x ∈ v -> C x) -> C v) -> forall v, C v.
Proof.
  intro H.
  refine (V_rect_hprop _ _ _).
  intros A f H_f. apply H. intros x Hx.
  generalize Hx; apply minus1Trunc_ind.
  intros [a p]. exact (transport C p (H_f a)).
Defined.

(** ** Two useful lemmas *)

Instance irreflexive_mem : Irreflexive mem.
Proof.
  refine (mem_induction (fun x => hp (~ x ∈ x) _) _); simpl in *.
  intros v H. intro Hv.
  exact (H v Hv Hv).
Defined.

Lemma path_V_eqimg {A B} {f : A -> V} {g : B -> V} : set f = set g -> equal_img f g.
Proof.
  intro p. split.
  - intro a.
    assert (H : f a ∈ set g).
    { apply (snd extensionality p).
      apply min1; exists a; reflexivity. }
    generalize H; apply minus1Trunc_map. intros [b p']. exists b; exact p'^.
  - intro b.
    assert (H : g b ∈ set f).
    { apply (snd extensionality p^).
      apply min1; exists b; reflexivity. }
    generalize H; apply minus1Trunc_map. intros [a p']. exists a; exact p'.
Defined.


(** ** Definitions of particular sets in V *)

(** The empty set *)
Definition V_empty : V := set (Empty_rect (fun _ => V)).

(** The singleton {u} *)
Definition V_singleton (u : V) : V@{U' U} := set (Unit_rect u).

Lemma path_singleton {u v : V} : V_singleton u = V_singleton v <-> u = v.
Proof.
  split.
  - intro H. specialize (path_V_eqimg H). intros (H1, H2).
    refine (minus1Trunc_ind _ (H1 tt)). intros [t p]. destruct t; exact p.
  - intro p. apply setext'; split.
    intro t; destruct t; apply min1; exists tt; exact p.
    intro t; destruct t; apply min1; exists tt; exact p.
Defined.

(** The pair {u,v} *)
Definition V_pair (u : V) (v : V) : V@{U' U} := set (fun b : Bool => if b then u else v).

Lemma path_pair {u v u' v' : V@{U' U}} : (u = u') * (v = v') -> V_pair u v = V_pair u' v'.
Proof.
  intros (H1, H2). apply setext'. split.
  + apply Bool_rect. apply min1; exists true. assumption.
    apply min1; exists false; assumption.
  + apply Bool_rect. apply min1; exists true; assumption.
    apply min1; exists false; assumption.
Defined.

Lemma pair_eq_singleton {u v w : V} : V_pair u v = V_singleton w <-> (u = w) * (v = w).
Proof.
  split.
  + intro H. destruct (path_V_eqimg H) as (H1, H2).
    refine (minus1Trunc_ind _ (H1 true)). intros [t p]; destruct t.
    refine (minus1Trunc_ind _ (H1 false)). intros [t p']; destruct t.
    split; [exact p| exact p'].
  + intros (p1, p2). apply setext'; split.
    intro a; apply min1; exists tt. destruct a; [exact p1 | exact p2].
    intro t; apply min1; exists true. destruct t; exact p1.
Defined.

(** The ordered pair (u,v) *)
Definition V_pair_ord (u : V) (v : V) : V := V_pair (V_singleton u) (V_pair u v).

Notation " [ u , v ] " := (V_pair_ord u v)
  (at level 20) : set_scope.

Lemma path_pair_ord {a b c d : V} : [a, b] = [c, d] <-> (a = c) * (b = d).
Proof.
  split.
  - intro p. assert (p1 : a = c).
    + assert (H : V_singleton a ∈ [c, d]).
      { apply (snd extensionality p). simpl.
        apply min1; exists true; reflexivity. }
      refine (minus1Trunc_ind _ H). intros [t p']; destruct t.
      apply (fst path_singleton p'^).
      symmetry; apply (fst pair_eq_singleton p').
    + split. exact p1.
      assert (H : hor (b = c) (b = d)).
      { assert (H' : V_pair a b ∈ [c, d]).
        { apply (snd extensionality p).
          apply min1; exists false; reflexivity. }
        refine (minus1Trunc_ind _ H'). intros [t p']; destruct t.
        * apply min1; left. apply (fst pair_eq_singleton p'^).
        * destruct (path_V_eqimg p') as (H1, H2).
          generalize (H2 false); apply minus1Trunc_map.
          intros [t p'']; destruct t.
          left; exact p''^. right; exact p''^. }
      refine (minus1Trunc_ind _ H). intro case; destruct case as [p'| p'].
      2: assumption.
      assert (H' : [a, b] = V_singleton (V_singleton b)).
      { apply (snd pair_eq_singleton).
        split. apply path_singleton; exact (p1 @ p'^).
        apply (snd pair_eq_singleton).
        split; [exact (p1 @ p'^) | reflexivity]. }
      assert (H'' : V_pair c d = V_singleton b)
        by apply (fst pair_eq_singleton (p^ @ H')).
      symmetry; apply (fst pair_eq_singleton H'').
- intros (p, p').
  apply path_pair. split. apply path_singleton; exact p.
  apply path_pair. split; assumption; assumption.
Defined.

(** The cartesian product a × b *)
Definition V_cart_prod (a : V) (b : V) : V
:= set (fun x : [a] * [b] => [func_of_members (fst x), func_of_members (snd x)]).

Notation " a × b " := (V_cart_prod a b)
  (at level 25) : set_scope.

(** f is a function with domain a and codomain b *)
Definition V_is_func (a : V) (b : V) (f : V) := f ⊆ a × b
 * (forall x, x ∈ a -> hexists (fun y => y ∈ b * [x,y] ∈ f))
 * (forall x y y', [x,y] ∈ f * [x,y'] ∈ f -> y = y').

(** The set of functions from a to b *)
Definition V_func (a : V) (b : V) : V
:= @set ([a] -> [b]) (fun f => set (fun x => [func_of_members x, func_of_members (f x)] )).

(** The union of a set Uv *)
Definition V_union (v : V) := 
  @set ({x : [v] & [func_of_members x]}) (fun z => func_of_members (pr2 z)).

(** The ordinal successor x ∪ {x} *)
Definition V_succ : V -> V.
Proof.
  refine (V_rect'_nd _ _ _ _). intros A f _.
  exact (set (fun (x : A + Unit) => match x with inl a => f a
                                          | inr tt => set f end)).
  simpl; intros A B f g eq_img _ _ _. apply setext'. split.
  - intro. destruct a.
    + generalize (fst eq_img a). apply minus1Trunc_map.
      intros [b p]. exists (inl b); exact p.
    + apply min1; exists (inr tt). destruct u. apply setext'; auto.
  - intro. destruct b.
    + generalize (snd eq_img b). apply minus1Trunc_map.
      intros [a p]. exists (inl a); exact p.
    + apply min1; exists (inr tt). destruct u. apply setext'; auto.
Defined.

(** The set of finite ordinals *) 
Definition V_omega : V
:= set (fix I n := match n with 0   => V_empty
                              | S n => V_succ (I n) end).


(** ** Axioms of set theory (theorem 10.5.8) *)

Lemma not_mem_Vempty : forall x, ~ (x ∈ V_empty).
Proof.
  intros x Hx. generalize Hx; apply minus1Trunc_ind.
  intros [ff _]. exact ff.
Qed.

Lemma pairing : forall u v, hexists (fun w => forall x, x ∈ w <-> hor (x = u) (x = v)).
Proof.
  intros u v. apply min1. exists (V_pair u v).
  intro; split; apply minus1Trunc_map.
  - intros [[|] p]; [left|right]; exact p^.
  - intros [p | p]; [exists true | exists false]; exact p^.
Qed.

Lemma infinity : (V_empty ∈ V_omega) * (forall x, x ∈ V_omega -> V_succ x ∈ V_omega).
Proof.
  split. apply min1; exists 0; auto.
  intro. apply minus1Trunc_map.
  intros [n p]. exists (S n). rewrite p; auto.
Qed.

Lemma union : forall v, hexists (fun w => forall x, x ∈ w <-> hexists (fun u => x ∈ u * u ∈ v)).
Proof.
  intro v. apply min1; exists (V_union v).
  intro x; split.
  - intro H. simpl in H. generalize H; apply minus1Trunc_map.
    intros [[u' x'] p]; simpl in p.
    exists (func_of_members u'); split.
    + refine (transport (fun z => x ∈ z) (is_valid_presentation (func_of_members u'))^ _).
      simpl. apply min1; exists x'. exact p.
    + refine (transport (fun z => func_of_members u' ∈ z) (is_valid_presentation v)^ _).
      simpl. apply min1; exists u'; reflexivity.
  - apply minus1Trunc_ind. intros [u (Hx, Hu)].
    generalize (transport (fun z => u ∈ z) (is_valid_presentation v) Hu).
    apply minus1Trunc_ind. intros [u' pu].
    generalize (transport (fun z => x ∈ z) (is_valid_presentation (func_of_members u')) (transport (fun z => x ∈ z) pu^ Hx)).
    apply minus1Trunc_ind. intros [x' px].
    apply min1. exists (u'; x'). exact px.
Qed.

Lemma function : forall u v, hexists (fun w => forall x, x ∈ w <-> V_is_func u v x).
Proof.
  intros u v. apply min1; exists (V_func u v).
  assert (memb_u : u = set (@func_of_members u)) by exact (is_valid_presentation u).
  assert (memb_v : v = set (@func_of_members v)) by exact (is_valid_presentation v).
  intro phi; split.
  - intro H. split. split.
    + intros z Hz. simpl in *. generalize H. apply minus1Trunc_ind.
      intros [h p_phi]. generalize (transport (fun x => z ∈ x) p_phi^ Hz). apply minus1Trunc_map.
      intros [a p]. exists (a, h a). assumption.
    + intros x Hx. generalize (transport (fun y => x ∈ y) memb_u Hx).
      apply minus1Trunc_ind. intros [a p]. generalize H; apply minus1Trunc_map.
      intros [h p_phi]. exists (func_of_members (h a)). split.
      exact (transport (fun z => func_of_members (h a) ∈ z) memb_v^ (min1 (h a; 1))).
      apply (transport (fun y => [x, func_of_members (h a)] ∈ y) p_phi).
      apply min1; exists a. rewrite p; reflexivity.
    + intros x y y' (Hy, Hy'). generalize H; apply minus1Trunc_ind. intros [h p_phi].
      generalize (transport (fun z => [x, y] ∈ z) p_phi^ Hy). apply minus1Trunc_ind. intros [a p].
      generalize (transport (fun z => [x, y'] ∈ z) p_phi^ Hy'). apply minus1Trunc_ind. intros [a' p'].
      destruct (fst path_pair_ord p) as (px, py). destruct (fst path_pair_ord p') as (px', py').
      path_via (func_of_members (h a)). path_via (func_of_members (h a')).
      refine (ap func_of_members _). refine (ap h _).
      apply (is_mono_isinj func_of_members is_mono_funcofmembers a a' (px @ px'^)).
  - intros ((H1, H2), H3). simpl.
    assert (h : forall a : [u], {b : [v] & [func_of_members a, func_of_members b] ∈ phi}).
    { intro a. pose (x := func_of_members a).
      refine (let H := untrunc_hprop _ (H2 x (transport (fun z => x ∈ z) memb_u^ (min1 (a; 1)))) in _).
      { apply hprop_allpath. intros [y (H1_y, H2_y)] [y' (H1_y', H2_y')].
        apply path_sigma_uncurried; simpl.
        exists (H3 x y y' (H2_y, H2_y')).
        apply allpath_hprop. }
      destruct H as [y (H1_y, H2_y)].
      destruct (untrunc_hprop (is_mono_funcofmembers y) (transport (fun z => y ∈ z) memb_v H1_y)) as [b Hb].
      exists b. exact (transport (fun z => [x, z] ∈ phi) Hb^ H2_y). }
    apply min1; exists (fun a => pr1 (h a)). apply extensionality. split.
    + intros z Hz. generalize Hz; apply minus1Trunc_ind. intros [a Ha].
      exact (transport (fun w => w ∈ phi) Ha (pr2 (h a))).
    + intros z Hz. simpl.
      generalize (H1 z Hz). apply minus1Trunc_map. intros [(a,b) p]. simpl in p.
      exists a. path_via ([func_of_members a, func_of_members b]).
      apply path_pair_ord. split. reflexivity.
      apply H3 with (func_of_members a). split.
      exact (pr2 (h a)).
      exact (transport (fun w => w ∈ phi) p^ Hz).
Qed.

Lemma replacement : forall (r : V -> V) (x : V),
  hexists (fun w => forall y, y ∈ w <-> hexists (fun z => z ∈ x * (r z = y))).
Proof.
  intro r. refine (V_rect_hprop _ _ _).
  intros A f _. apply min1. exists (set (r o f)). split.
  - apply minus1Trunc_map.
    intros [a p]. exists (f a). split. apply min1; exists a; auto. assumption.
  - apply minus1Trunc_ind.
    intros [z [h p]]. generalize h. apply minus1Trunc_map.
    intros [a p']. exists a. path_via (r z). exact (ap r p').
Qed.

Lemma separation (C : V -> hProp) : forall a : V,
  hexists (fun w => forall x, x ∈ w <-> x ∈ a * (C x)).
Proof.
  refine (V_rect_hprop _ _ _).
  intros A f _. apply min1. exists (set (fun z : {a : A & C (f a)} => f (pr1 z))). split.
  - apply minus1Trunc_ind.
    intros [[a h] p]. split. apply min1; exists a; assumption. exact (transport C p h).
  - intros [H1 H2]. generalize H1. apply minus1Trunc_map.
    intros [a p]. exists (a; transport C p^ H2). exact p.
Qed.

End AssumingUA.