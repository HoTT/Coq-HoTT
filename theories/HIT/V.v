(* -*- mode: coq; mode: visual-line -*- *)

(** * The cumulative hierarchy [V]. *)

Require Import HoTT.Basics HoTT.Basics.Notations HoTT.Basics.Utf8.
Require Import Types.Unit Types.Bool Types.Universe Types.Sigma Types.Arrow Types.Forall.
Require Import HProp HSet UnivalenceImpliesFunext TruncType.
Require Import HIT.Truncations HIT.quotient.
Local Open Scope nat_scope.
Local Open Scope path_scope.



(** ** Pushout with respect to a relation *)

(** This could be implemented using the pushouts in /HIT/Pushout.v, where [f] and [g] are [(fst o pr1)] and [(snd o pr1)], with domain {(a,b) : A * B & R a b}. However, these pushouts weren't implemented when I started this work, and doing it this way is closer to exercise 10.11 of the HoTT book *)

Module Export RPushout.

Private Inductive RPushout {A B : Type} (R : A -> B -> hProp) : Type :=
| inL : A -> RPushout R
| inR : B -> RPushout R.

Axiom glue : forall {A B : Type} (R : A -> B -> hProp)
  (a : A) (b : B) (r : R a b), (inL R a) = (inR R b).

Definition RPushout_ind {A B : Type} {R : A -> B -> hProp}
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
apD (RPushout_ind P i j gl) (glue R a b r) = gl a b r.

End RPushout.

(** The non-depentent eliminator *)

Definition RPushout_rec {A B : Type} (R : A -> B -> hProp)
  (P : Type) (i : A -> P) (j : B -> P)
  (gl : forall (a : A) (b : B) (r : R a b), (i a) = (j b))
: RPushout R -> P
:= RPushout_ind (fun _ => P) i j (fun a b r => transport_const _ _ @ gl a b r).

Definition RPushout_comp_nd_glue {A B : Type} (R : A -> B -> hProp)
  (P : Type) (i : A -> P) (j : B -> P)
  (gl : forall (a : A) (b : B) (r : R a b), (i a) = (j b))
  (a : A) (b : B) (r : R a b)
: ap (RPushout_rec R P i j gl) (glue R a b r) = gl a b r.
Proof.
  apply (cancelL (transport_const (glue R a b r) (i a))).
  transitivity (apD (RPushout_rec R P i j gl) (glue R a b r)).
  apply (apD_const (RPushout_rec R P i j gl) (glue R a b r))^.
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
Existing Instance is0trunc_V.

Fixpoint V_ind (P : V -> Type)
  (H_0trunc : forall v : V, IsTrunc 0 (P v))
  (H_set : forall (A : Type) (f : A -> V) (H_f : forall a : A, P (f a)), P (set f))
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : bitotal R)
    (h : RPushout R -> V) (H_h : forall x : RPushout R, P (h x)),
    (setext R bitot_R h) # (H_set A (h o inL R) (H_h oD inL R))
      = H_set B (h o inR R) (H_h oD inR R) )
  (v : V)
: P v
:= (match v with
     | set A f => fun _ _ => H_set A f (fun a => V_ind P H_0trunc H_set H_setext (f a))
    end) H_setext H_0trunc.

(** We don't need to axiomatize the computation rule because we get it for free thanks to 0-truncation *)

End CumulativeHierarchy.

Definition V_comp_setext (P : V -> Type)
  (H_0trunc : forall v : V, IsTrunc 0 (P v))
  (H_set : forall (A : Type) (f : A -> V) (H_f : forall a : A, P (f a)), P (set f))
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : bitotal R)
    (h : RPushout R -> V) (H_h : forall x : RPushout R, P (h x)),
    (setext R bitot_R h) # (H_set A (h o inL R) (H_h oD inL R))
      = H_set B (h o inR R) (H_h oD inR R) )
  (A B : Type) (R : A -> B -> hProp) (bitot_R : bitotal R) (h : RPushout R -> V)
: apD (V_ind P H_0trunc H_set H_setext) (setext R bitot_R h)
  = H_setext A B R bitot_R h ((V_ind P H_0trunc H_set H_setext) oD h).
Proof.
  apply path_ishprop.
Defined.

(** The non-dependent eliminator *)

Definition V_rec (P : Type)
  (H_0trunc : IsTrunc 0 P)
  (H_set : forall (A : Type), (A -> V) -> (A -> P) -> P)
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : bitotal R)
    (h : RPushout R -> V) (H_h : RPushout R -> P),
    H_set A (h o inL R) (H_h o inL R) = H_set B (h o inR R) (H_h o inR R) )
: V -> P.
Proof.
  refine (V_ind _ _ H_set _).
  intros. exact (transport_const _ _ @ H_setext A B R bitot_R h H_h).
Defined.

Definition V_comp_nd_setext (P : Type)
  (H_0trunc : IsTrunc 0 P)
  (H_set : forall (A : Type), (A -> V) -> (A -> P) -> P)
  (H_setext : forall (A B : Type) (R : A -> B -> hProp) (bitot_R : bitotal R)
    (h : RPushout R -> V) (H_h : RPushout R -> P),
    H_set A (h o inL R) (H_h o inL R) = H_set B (h o inR R) (H_h o inR R) )
  (A B : Type) (R : A -> B -> hProp) (bitot_R : bitotal R) (h : RPushout R -> V)
: ap (V_rec P H_0trunc H_set H_setext) (setext R bitot_R h)
  = H_setext A B R bitot_R h ((V_rec P H_0trunc H_set H_setext) o h).
Proof.
  apply path_ishprop.
Defined.


(** ** Alternative induction principle (This is close to the one from the book) *)

Definition equal_img {A B C : Type} (f : A -> C) (g : B -> C) :=
   (forall a : A, hexists (fun (b : B) => f a = g b))
 * (forall b : B, hexists (fun (a : A) => f a = g b)).

Definition setext' {A B : Type} (f : A -> V) (g : B -> V) (eq_img : equal_img f g)
: set f = set g.
Proof.
  pose (R := fun a b => BuildhProp (f a = g b)).
  pose (h := RPushout_rec R V f g (fun _ _ r => r)).
  exact (setext R eq_img h).
Defined.

Definition V_rec' (P : Type)
  (H_0trunc : IsTrunc 0 P)
  (H_set : forall (A : Type), (A -> V) -> (A -> P) -> P)
  (H_setext' : forall (A B : Type) (f : A -> V) (g : B -> V), (equal_img f g) ->
    forall (H_f : A -> P) (H_g : B -> P), (equal_img H_f H_g) ->
    (H_set A f H_f) = (H_set B g H_g) )
: V -> P.
Proof.
  refine (V_rec _ _ H_set _).
  intros A B R bitot_R h H_h.
  apply H_setext'.
  - split.
    + intro a. generalize (fst bitot_R a). apply (Trunc_functor -1).
      intros [b r]. exists b. exact (ap h (glue R _ _ r)).
    + intro b. generalize (snd bitot_R b). apply (Trunc_functor -1).
      intros [a r]. exists a. exact (ap h (glue R _ _ r)).
  - split.
    + intro a. generalize (fst bitot_R a). apply (Trunc_functor -1).
      intros [b r]. exists b. exact (ap H_h (glue R _ _ r)).
    + intro b. generalize (snd bitot_R b). apply (Trunc_functor -1).
      intros [a r]. exists a. exact (ap H_h (glue R _ _ r)).
Defined.

(** Note that the hypothesis H_setext' differs from the one given in section 10.5 of the HoTT book. *)
Definition V_ind' (P : V -> Type)
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
  apply V_ind with H_set; try assumption.
  intros A B R bitot_R h H_h.
  pose (f := h o inL R : A -> V ).
  pose (g := h o inR R : B -> V ).
  pose (H_f := H_h oD inL R : forall a : A, P (f a)).
  pose (H_g := H_h oD inR R : forall b : B, P (g b)).
  assert (eq_img : equal_img f g).
  { split.
    - intro a. generalize (fst bitot_R a). apply (Trunc_functor -1).
      intros [b r]. exists b. exact (ap h (glue R _ _ r)).
    - intro b. generalize (snd bitot_R b). apply (Trunc_functor -1).
      intros [a r]. exists a. exact (ap h (glue R _ _ r)). }
  transitivity (transport P (setext' (h o inL R) (h o inR R) eq_img)
      (H_set A (h o inL R) (H_h oD inL R))).
  { apply (ap (fun p => transport P p (H_set A (h o inL R) (H_h oD inL R)))).
    apply path_ishprop. }
  apply (H_setext' A B f g eq_img H_f H_g).  split.
  - intro a.
    set (truncb := fst bitot_R a). generalize truncb.
    apply (Trunc_functor -1).
    intros [b Rab]. exists b.
    apply tr.
    exists (ap h (glue R _ _ Rab)).
    apply (concatR (apD H_h (glue R _ _ Rab))).
    apply inverse. unfold f, g. apply transport_compose.
  - intros b.
    set (trunca := snd bitot_R b). generalize trunca.
    apply (Trunc_functor -1).
    intros [a Rab]. exists a.
    apply tr.
    exists (ap h (glue R _ _ Rab)).
    apply (concatR (apD H_h (glue R _ _ Rab))).
    apply inverse. unfold f, g. apply transport_compose.
Defined.


(** Simpler induction principle when the goal is an hprop *)

Definition V_ind_hprop (P : V -> Type)
  (H_set : forall (A : Type) (f : A -> V) (H_f : forall a : A, P (f a)), P (set f))
  (isHProp_P : forall v : V, IsHProp (P v))
  : forall v : V, P v.
Proof.
  refine (V_ind _ _ H_set _).
  intros. apply path_ishprop.
Defined.


Section AssumingUA.
Context `{ua : Univalence}.

(** ** Membership relation *)

Definition mem (x : V) : V -> hProp.
Proof.
  simple refine (V_rec' _ _ _ _). intros A f _.
  exact (hexists (fun a : A => f a = x)). simpl.
  intros A B f g eqimg _ _ _.
  apply path_iff_hprop; simpl.
  - intro H. refine (Trunc_rec _ H).
    intros [a p]. generalize (fst eqimg a). apply (Trunc_functor -1).
    intros [b p']. exists b. transitivity (f a); auto with path_hints.
  - intro H. refine (Trunc_rec _ H).
    intros [b p]. generalize (snd eqimg b). apply (Trunc_functor -1).
    intros [a p']. exists a. transitivity (g b); auto with path_hints.
Defined.

Declare Scope set_scope.
Notation "x ∈ v" := (mem x v) : set_scope.
Open Scope set_scope.

(** ** Subset relation *)

Definition subset (x : V) (y : V) : hProp
:= BuildhProp (forall z : V, z ∈ x -> z ∈ y).

Notation "x ⊆ y" := (subset x y) : set_scope.


(** ** Bisimulation relation *)
(** The equality in V lives in Type@{U'}. We define the bisimulation relation which is a U-small resizing of the equality in V: it must live in hProp_U : Type{U'}, hence the codomain is hProp@{U'}. We then prove that bisimulation is equality (bisim_equals_id), then use it to prove the key lemma monic_set_present. *)

(* We define bisimulation by double induction on V. We first fix the first argument as set(A,f) and define bisim_aux : V -> hProp, by induction. This is the inner of the two inductions. *)
Local Definition bisim_aux (A : Type) (f : A -> V) (H_f : A -> V -> hProp) : V -> hProp.
Proof.
  apply V_rec' with
    (fun B g _ => BuildhProp ( (forall a, hexists (fun b => H_f a (g b)))
                               * forall b, hexists (fun a => H_f a (g b)) )
    ).
  exact _.
  intros B B' g g' eq_img H_g H_g' H_img; simpl.
  apply path_iff_hprop; simpl.
  - intros [H1 H2]; split.
    + intro a. refine (Trunc_rec _ (H1 a)).
      intros [b H3]. generalize (fst eq_img b).
      unfold hexists. refine (@Trunc_functor -1 {b0 : B' & g b = g' b0} {b0 : B' & H_f a (g' b0)} _).
      intros [b' p]. exists b'. exact (transport (fun x => H_f a x) p H3).
    + intro b'. refine (Trunc_rec _ (snd eq_img b')).
      intros [b p]. generalize (H2 b). apply (Trunc_functor -1).
      intros [a H3]. exists a. exact (transport (fun x => H_f a x) p H3).
  - intros [H1 H2]; split.
    + intro a. refine (Trunc_rec _ (H1 a)).
      intros [b' H3]. generalize (snd eq_img b'). apply (Trunc_functor -1).
      intros [b p]. exists b. exact (transport (fun x => H_f a x) p^ H3).
    + intro b. refine (Trunc_rec _ (fst eq_img b)).
      intros [b' p]. generalize (H2 b'). apply (Trunc_functor -1).
      intros [a H3]. exists a. exact (transport (fun x => H_f a x) p^ H3).
Defined.

(* Then we define bisim : V -> (V -> hProp) by induction again *)
Definition bisimulation : V@{U' U} -> V@{U' U} -> hProp@{U'}.
Proof.
  refine (V_rec' (V -> hProp) _ bisim_aux _).
  intros A B f g eq_img H_f H_g H_img.
  apply path_forall.
  refine (V_ind_hprop _ _ _).
  intros C h _; simpl.
  apply path_iff_hprop; simpl.
  - intros [H1 H2]; split.
    + intro b. refine (Trunc_rec _ (snd H_img b)).
      intros [a p]. generalize (H1 a). apply (Trunc_functor -1).
      intros [c H3]. exists c. exact ((ap10 p (h c)) # H3).
    + intro c. refine (Trunc_rec _ (H2 c)).
      intros [a H3]. generalize (fst H_img a). apply (Trunc_functor -1).
      intros [b p]. exists b. exact ((ap10 p (h c)) # H3).
  - intros [H1 H2]; split.
    + intro a. refine (Trunc_rec _ (fst H_img a)).
      intros [b p]. generalize (H1 b). apply (Trunc_functor -1).
      intros [c H3]. exists c. exact ((ap10 p^ (h c)) # H3).
    + intro c. refine (Trunc_rec _ (H2 c)).
      intros [b H3]. generalize (snd H_img b). apply (Trunc_functor -1).
      intros [a p]. exists a. exact ((ap10 p^ (h c)) # H3).
Defined.

Notation "u ~~ v" := (bisimulation u v) : set_scope.

Global Instance reflexive_bisimulation : Reflexive bisimulation.
Proof.
  refine (V_ind_hprop _ _ _).
  intros A f H_f; simpl. split.
  - intro a; apply tr; exists a; auto.
  - intro a; apply tr; exists a; auto.
Defined.

Lemma bisimulation_equiv_id : forall u v : V, (u = v) <~> (u ~~ v).
Proof.
  intros u v.
  apply equiv_iff_hprop.
  intro p; exact (transport (fun x => u ~~ x) p (reflexive_bisimulation u)).
  generalize u v.
  refine (V_ind_hprop _ _ _); intros A f H_f.
  refine (V_ind_hprop _ _ _); intros B g _.
  simpl; intros [H1 H2].
  apply setext'. split.
  - intro a. generalize (H1 a). apply (Trunc_functor -1).
    intros [b h]. exists b; exact (H_f a (g b) h).
  - intro b. generalize (H2 b). apply (Trunc_functor -1).
    intros [a h]. exists a; exact (H_f a (g b) h).
Defined.


(** ** Canonical presentation of V-sets (Lemma 10.5.6) *)

(** Using the regular kernel (with = instead of ~~) also works, but this seems to be a Coq bug, it should lead to a universe inconsistency in the monic_set_present lemma later. This version is the right way to do it. *)
Definition ker_bisim {A} (f : A -> V) (x y : A) := (f x ~~ f y).

Definition ker_bisim_is_ker {A} (f : A -> V)
  : forall (x y : A), f x = f y <~> ker_bisim f x y.
Proof.
  intros; apply bisimulation_equiv_id.
Defined.

Section MonicSetPresent_Uniqueness.
(** Given u : V, we want to show that the representation u = @set Au mu, where Au is an hSet and mu is monic, is unique. *)

Context {u : V} {Au Au': Type} {h : IsHSet Au} {h' : IsHSet Au'} {mu : Au -> V} {mono : IsEmbedding mu}
  {mu' : Au' -> V} {mono' : IsEmbedding mu'} {p : u = set mu} {p' : u = set mu'}.

Lemma eq_img_untrunc : (forall a : Au, {a' : Au' & mu' a' = mu a})
                     * (forall a' : Au', {a : Au & mu a = mu' a'}).
Proof.
  split.
  intro a. exact (@untrunc_istrunc -1 _ (mono' (mu a)) (transport (fun x => mu a ∈ x) (p^ @ p') (tr (a; 1)))).
  intro a'. exact (@untrunc_istrunc -1 _ (mono (mu' a')) (transport (fun x => mu' a' ∈ x) (p'^ @ p) (tr (a'; 1)))).
Defined.

Let e : Au -> Au' := fun a => pr1 (fst eq_img_untrunc a).
Let inv_e : Au' -> Au := fun a' => pr1 (snd eq_img_untrunc a').

Let hom1 : Sect inv_e e.
Proof.
  intro a'.
  apply (isinj_embedding mu' mono').
  transitivity (mu (inv_e a')).
  exact (pr2 (fst eq_img_untrunc (inv_e a'))).
  exact (pr2 (snd eq_img_untrunc a')).
Defined.

Let hom2 : Sect e inv_e.
Proof.
  intro a.
  apply (isinj_embedding mu mono).
  transitivity (mu' (e a)).
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
  transitivity (transport (fun X => V) path^ (mu (transport (fun X : Type => X) path^^ a'))).
  apply (@transport_arrow Type (fun X : Type => X) (fun X => V) Au Au' path^ mu a').
  transitivity (mu (transport idmap path^^ a')).
  apply transport_const.
  transitivity (mu (inv_e a')).
  2: apply (pr2 (snd eq_img_untrunc a')).
  refine (ap mu _).
  transitivity (transport idmap path a').
  exact (ap (fun x => transport idmap x a') (inv_V path)).
  apply transport_path_universe.
Defined.

Lemma monic_set_present_uniqueness : (Au; (mu; (h, mono, p))) = (Au'; (mu'; (h', mono', p'))) :> {A : Type & {m : A -> V & IsHSet A * IsEmbedding m * (u = set m)}}.
Proof.
  apply path_sigma_uncurried; simpl.
  exists path^.
  transitivity (path^ # mu; transportD (fun A => A -> V) (fun A m => IsHSet A * IsEmbedding m * (u = set m)) path^ mu (h, mono, p)).
  apply (@transport_sigma Type (fun A => A -> V) (fun A m => IsHSet A * IsEmbedding m * (u = set m)) Au Au' path^ (mu; (h, mono, p))).
  apply path_sigma_hprop; simpl.
  exact mu_eq_mu'.
Defined.

End MonicSetPresent_Uniqueness.

(** This lemma actually says a little more than 10.5.6, i.e., that Au is a hSet *)
Lemma monic_set_present : forall u : V, exists (Au : Type) (m : Au -> V),
  (IsHSet Au) * (IsEmbedding m) * (u = set m).
Proof.
  apply V_ind_hprop.
  - intros A f _.
    destruct (quotient_kernel_factor f (ker_bisim f) (ker_bisim_is_ker f))
      as [Au [eu [mu (((hset_Au, epi_eu), mono_mu), factor)]]].
    exists Au, mu. split. exact (hset_Au, mono_mu).
    apply setext'; split.
    + intro a. apply tr; exists (eu a). exact (ap10 factor a).
    + intro a'. generalize (epi_eu a').
      intros ?; refine (Trunc_functor -1 _ (center _)).
      intros [a p]. exists a. transitivity (mu (eu a)).
      exact (ap10 factor a). exact (ap mu p).
  - intro v. apply hprop_allpath.
    intros [Au [mu ((hset, mono), p)]].
    intros [Au' [mu' ((hset', mono'), p')]].
    apply monic_set_present_uniqueness.
Defined.

Definition type_of_members (u : V) : Type := pr1 (monic_set_present u).

Notation "[ u ]" := (type_of_members u) : set_scope.

Definition func_of_members {u : V} : [u] -> V := pr1 (pr2 (monic_set_present u)) : [u] -> V.

Definition is_hset_typeofmembers {u : V} : IsHSet ([u]) := fst (fst (pr2 (pr2 (monic_set_present u)))).

Definition IsEmbedding_funcofmembers {u : V} : IsEmbedding func_of_members := snd (fst (pr2 (pr2 (monic_set_present u)))).

Definition is_valid_presentation (u : V) : u = set func_of_members := snd (pr2 (pr2 (monic_set_present u))).


(** ** Lemmas 10.5.8 (i) & (vii), we put them here because they are useful later *)
Lemma extensionality : forall {x y : V}, (x ⊆ y * y ⊆ x) <-> x = y.
Proof.
  refine (V_ind_hprop _ _ _). intros A f _.
  refine (V_ind_hprop _ _ _). intros B g _.
  split.
  - intros [H1 H2]. apply setext'. split.
    + intro. refine (Trunc_rec _ (H1 (f a) (tr (a;1)))).
      intros [b p]. apply tr. exists b. exact p^.
    + intro. apply (H2 (g b)). apply tr; exists b; reflexivity.
  - intro p; split.
    + intros z Hz. apply (transport (fun x => z ∈ x) p Hz).
    + intros z Hz. apply (transport (fun x => z ∈ x) p^ Hz).
Qed.

Lemma mem_induction (C : V -> hProp)
: (forall v, (forall x, x ∈ v -> C x) -> C v) -> forall v, C v.
Proof.
  intro H.
  refine (V_ind_hprop _ _ _).
  intros A f H_f. apply H. intros x Hx.
  generalize Hx; apply Trunc_rec.
  intros [a p]. exact (transport C p (H_f a)).
Defined.

(** ** Two useful lemmas *)

Global Instance irreflexive_mem : Irreflexive mem.
Proof.
  assert (forall v, IsHProp (complement (fun x x0 : V => x ∈ x0) v v)). (* https://coq.inria.fr/bugs/show_bug.cgi?id=3854 *)
  { intro.
    unfold complement.
    exact _. }
  refine (mem_induction (fun x => BuildhProp (~ x ∈ x)) _); simpl in *.
  intros v H. intro Hv.
  exact (H v Hv Hv).
Defined.

Lemma path_V_eqimg {A B} {f : A -> V} {g : B -> V} : set f = set g -> equal_img f g.
Proof.
  intro p. split.
  - intro a.
    assert (H : f a ∈ set g).
    { apply (snd extensionality p).
      apply tr; exists a; reflexivity. }
    generalize H; apply (Trunc_functor -1). intros [b p']. exists b; exact p'^.
  - intro b.
    assert (H : g b ∈ set f).
    { apply (snd extensionality p^).
      apply tr; exists b; reflexivity. }
    generalize H; apply (Trunc_functor -1). intros [a p']. exists a; exact p'.
Defined.


(** ** Definitions of particular sets in V *)

(** The empty set *)
Definition V_empty : V := set (Empty_ind (fun _ => V)).

(** The singleton {u} *)
Definition V_singleton (u : V) : V@{U' U} := set (Unit_ind u).

Global Instance isequiv_ap_V_singleton {u v : V}
: IsEquiv (@ap _ _ V_singleton u v).
Proof.
  simple refine (BuildIsEquiv _ _ _ _ _ _ _); try solve [ intro; apply path_ishprop ].
  { intro H. specialize (path_V_eqimg H). intros (H1, H2).
    refine (Trunc_rec _ (H1 tt)). intros [t p]. destruct t; exact p. }
Defined.

(** The pair {u,v} *)
Definition V_pair (u : V) (v : V) : V@{U' U} := set (fun b : Bool => if b then u else v).

Lemma path_pair {u v u' v' : V@{U' U}} : (u = u') * (v = v') -> V_pair u v = V_pair u' v'.
Proof.
  intros (H1, H2). apply setext'. split.
  + apply Bool_ind. apply tr; exists true. assumption.
    apply tr; exists false; assumption.
  + apply Bool_ind. apply tr; exists true; assumption.
    apply tr; exists false; assumption.
Defined.

Lemma pair_eq_singleton {u v w : V} : V_pair u v = V_singleton w <-> (u = w) * (v = w).
Proof.
  split.
  + intro H. destruct (path_V_eqimg H) as (H1, H2).
    refine (Trunc_rec _ (H1 true)). intros [t p]; destruct t.
    refine (Trunc_rec _ (H1 false)). intros [t p']; destruct t.
    split; [exact p| exact p'].
  + intros (p1, p2). apply setext'; split.
    intro a; apply tr; exists tt. destruct a; [exact p1 | exact p2].
    intro t; apply tr; exists true. destruct t; exact p1.
Defined.

(** The ordered pair (u,v) *)
Definition V_pair_ord (u : V) (v : V) : V := V_pair (V_singleton u) (V_pair u v).

Notation " [ u , v ] " := (V_pair_ord u v) : set_scope.

Lemma path_pair_ord {a b c d : V} : [a, b] = [c, d] <-> (a = c) * (b = d).
Proof.
  split.
  - intro p. assert (p1 : a = c).
    + assert (H : V_singleton a ∈ [c, d]).
      { apply (snd extensionality p). simpl.
        apply tr; exists true; reflexivity. }
      refine (Trunc_rec _ H). intros [t p']; destruct t.
      apply ((ap V_singleton)^-1 p'^).
      symmetry; apply (fst pair_eq_singleton p').
    + split. exact p1.
      assert (H : hor (b = c) (b = d)).
      { assert (H' : V_pair a b ∈ [c, d]).
        { apply (snd extensionality p).
          apply tr; exists false; reflexivity. }
        refine (Trunc_rec _ H'). intros [t p']; destruct t.
        * apply tr; left. apply (fst pair_eq_singleton p'^).
        * destruct (path_V_eqimg p') as (H1, H2).
          generalize (H2 false); apply (Trunc_functor -1).
          intros [t p'']; destruct t.
          left; exact p''^. right; exact p''^. }
      refine (Trunc_rec _ H). intro case; destruct case as [p'| p'].
      2: assumption.
      assert (H' : [a, b] = V_singleton (V_singleton b)).
      { apply (snd pair_eq_singleton).
        split. apply ap; exact (p1 @ p'^).
        apply (snd pair_eq_singleton).
        split; [exact (p1 @ p'^) | reflexivity]. }
      assert (H'' : V_pair c d = V_singleton b)
        by apply (fst pair_eq_singleton (p^ @ H')).
      symmetry; apply (fst pair_eq_singleton H'').
- intros (p, p').
  apply path_pair. split. apply ap; exact p.
  apply path_pair. split; assumption; assumption.
Defined.

(** The cartesian product a × b *)
Definition V_cart_prod (a : V) (b : V) : V
:= set (fun x : [a] * [b] => [func_of_members (fst x), func_of_members (snd x)]).

Notation " a × b " := (V_cart_prod a b) : set_scope.

(** f is a function with domain a and codomain b *)
Definition V_is_func (a : V) (b : V) (f : V) := f ⊆ (a × b)
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
  simple refine (V_rec' _ _ _ _). intros A f _.
  exact (set (fun (x : A + Unit) => match x with inl a => f a
                                          | inr tt => set f end)).
  simpl; intros A B f g eq_img _ _ _. apply setext'. split.
  - intro. destruct a.
    + generalize (fst eq_img a). apply (Trunc_functor -1).
      intros [b p]. exists (inl b); exact p.
    + apply tr; exists (inr tt). destruct u. apply setext'; auto.
  - intro. destruct b.
    + generalize (snd eq_img b). apply (Trunc_functor -1).
      intros [a p]. exists (inl a); exact p.
    + apply tr; exists (inr tt). destruct u. apply setext'; auto.
Defined.

(** The set of finite ordinals *)
Definition V_omega : V
:= set (fix I n := match n with 0   => V_empty
                              | S n => V_succ (I n) end).


(** ** Axioms of set theory (theorem 10.5.8) *)

Lemma not_mem_Vempty : forall x, ~ (x ∈ V_empty).
Proof.
  intros x Hx. generalize Hx; apply Trunc_rec.
  intros [ff _]. exact ff.
Qed.

Lemma pairing : forall u v, hexists (fun w => forall x, x ∈ w <-> hor (x = u) (x = v)).
Proof.
  intros u v. apply tr. exists (V_pair u v).
  intro; split; apply (Trunc_functor -1).
  - intros [[|] p]; [left|right]; exact p^.
  - intros [p | p]; [exists true | exists false]; exact p^.
Qed.

Lemma infinity : (V_empty ∈ V_omega) * (forall x, x ∈ V_omega -> V_succ x ∈ V_omega).
Proof.
  split. apply tr; exists 0; auto.
  intro. apply (Trunc_functor -1).
  intros [n p]. exists (S n). rewrite p; auto.
Qed.

Lemma union : forall v, hexists (fun w => forall x, x ∈ w <-> hexists (fun u => x ∈ u * u ∈ v)).
Proof.
  intro v. apply tr; exists (V_union v).
  intro x; split.
  - intro H. simpl in H. generalize H; apply (Trunc_functor -1).
    intros [[u' x'] p]; simpl in p.
    exists (func_of_members u'); split.
    + refine (transport (fun z => x ∈ z) (is_valid_presentation (func_of_members u'))^ _).
      simpl. apply tr; exists x'. exact p.
    + refine (transport (fun z => func_of_members u' ∈ z) (is_valid_presentation v)^ _).
      simpl. apply tr; exists u'; reflexivity.
  - apply Trunc_rec. intros [u (Hx, Hu)].
    generalize (transport (fun z => u ∈ z) (is_valid_presentation v) Hu).
    apply Trunc_rec. intros [u' pu].
    generalize (transport (fun z => x ∈ z) (is_valid_presentation (func_of_members u')) (transport (fun z => x ∈ z) pu^ Hx)).
    apply Trunc_rec. intros [x' px].
    apply tr. exists (u'; x'). exact px.
Qed.

Lemma function : forall u v, hexists (fun w => forall x, x ∈ w <-> V_is_func u v x).
Proof.
  intros u v. apply tr; exists (V_func u v).
  assert (memb_u : u = set (@func_of_members u)) by exact (is_valid_presentation u).
  assert (memb_v : v = set (@func_of_members v)) by exact (is_valid_presentation v).
  intro phi; split.
  - intro H. split. split.
    + intros z Hz. simpl in *. generalize H. apply Trunc_rec.
      intros [h p_phi]. generalize (transport (fun x => z ∈ x) p_phi^ Hz). apply (Trunc_functor -1).
      intros [a p]. exists (a, h a). assumption.
    + intros x Hx. generalize (transport (fun y => x ∈ y) memb_u Hx).
      apply Trunc_rec. intros [a p]. generalize H; apply (Trunc_functor -1).
      intros [h p_phi]. exists (func_of_members (h a)). split.
      exact (transport (fun z => func_of_members (h a) ∈ z) memb_v^ (tr (h a; 1))).
      apply (transport (fun y => [x, func_of_members (h a)] ∈ y) p_phi).
      apply tr; exists a. rewrite p; reflexivity.
    + intros x y y' (Hy, Hy'). generalize H; apply Trunc_rec. intros [h p_phi].
      generalize (transport (fun z => [x, y] ∈ z) p_phi^ Hy). apply Trunc_rec. intros [a p].
      generalize (transport (fun z => [x, y'] ∈ z) p_phi^ Hy'). apply Trunc_rec. intros [a' p'].
      destruct (fst path_pair_ord p) as (px, py). destruct (fst path_pair_ord p') as (px', py').
      transitivity (func_of_members (h a)); auto with path_hints. transitivity (func_of_members (h a'));auto with path_hints.
      refine (ap func_of_members _). refine (ap h _).
      apply (isinj_embedding func_of_members IsEmbedding_funcofmembers a a' (px @ px'^)).
  - intros ((H1, H2), H3). simpl.
    assert (h : forall a : [u], {b : [v] & [func_of_members a, func_of_members b] ∈ phi}).
    { intro a. pose (x := func_of_members a).
      transparent assert (H : {y : V & y ∈ v * [x, y] ∈ phi}).
      refine (@untrunc_istrunc -1 {y : V & y ∈ v * [x, y] ∈ phi} _
                                 (H2 x (transport (fun z => x ∈ z) memb_u^ (tr (a; 1))))).
      { apply hprop_allpath. intros [y (H1_y, H2_y)] [y' (H1_y', H2_y')].
        apply path_sigma_uncurried; simpl.
        exists (H3 x y y' (H2_y, H2_y')).
        apply path_ishprop. }
      destruct H as [y (H1_y, H2_y)].
      destruct (@untrunc_istrunc -1 _ (IsEmbedding_funcofmembers y) (transport (fun z => y ∈ z) memb_v H1_y)) as [b Hb].
      exists b. exact (transport (fun z => [x, z] ∈ phi) Hb^ H2_y). }
    apply tr; exists (fun a => pr1 (h a)). apply extensionality. split.
    + intros z Hz. generalize Hz; apply Trunc_rec. intros [a Ha].
      exact (transport (fun w => w ∈ phi) Ha (pr2 (h a))).
    + intros z Hz. simpl.
      generalize (H1 z Hz). apply (Trunc_functor -1). intros [(a,b) p]. simpl in p.
      exists a. transitivity ([func_of_members a, func_of_members b]); auto with path_hints.
      apply ap.
      apply H3 with (func_of_members a). split.
      exact (pr2 (h a)).
      exact (transport (fun w => w ∈ phi) p^ Hz).
Qed.

Lemma replacement : forall (r : V -> V) (x : V),
  hexists (fun w => forall y, y ∈ w <-> hexists (fun z => z ∈ x * (r z = y))).
Proof.
  intro r. refine (V_ind_hprop _ _ _).
  intros A f _. apply tr. exists (set (r o f)). split.
  - apply (Trunc_functor -1).
    intros [a p]. exists (f a). split. apply tr; exists a; auto. assumption.
  - apply Trunc_rec.
    intros [z [h p]]. generalize h. apply (Trunc_functor -1).
    intros [a p']. exists a. transitivity (r z); auto with path_hints. exact (ap r p').
Qed.

Lemma separation (C : V -> hProp) : forall a : V,
  hexists (fun w => forall x, x ∈ w <-> x ∈ a * (C x)).
Proof.
  refine (V_ind_hprop _ _ _).
  intros A f _. apply tr. exists (set (fun z : {a : A & C (f a)} => f (pr1 z))). split.
  - apply Trunc_rec.
    intros [[a h] p]. split. apply tr; exists a; assumption. exact (transport C p h).
  - intros [H1 H2]. generalize H1. apply (Trunc_functor -1).
    intros [a p]. exists (a; transport C p^ H2). exact p.
Qed.

End AssumingUA.
