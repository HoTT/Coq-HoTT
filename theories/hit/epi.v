Require Import Overture hit.minus1Trunc HProp Misc TruncType types.Universe Equivalences Trunc HSet types.Unit UnivalenceImpliesFunext.
Require Import TruncType hit.Pushout hit.Truncations types.Forall types.Sigma Contractible PathGroupoids types.Paths.

Open Local Scope path_scope.
Open Local Scope equiv_scope.

Section AssumingUA.
(** The univalence axiom for HProp (Voevodsky's uahp) *)
(** We need fs to be able to find hprop_trunc *)
Context `{ua:Univalence}.
Lemma path_biimp : forall P P': sigT IsHProp, (P.1<->P'.1) -> P = P'.
intros ? ? X. apply (equiv_path_sigma_hprop P P'). apply path_universe_uncurried.
destruct P, P'. destruct X.
by apply equiv_iff_hprop.
Defined.

Lemma biimp_path : forall P P': sigT IsHProp, P = P' -> (P.1<->P'.1).
intros ?? p. by destruct p.
Defined.

Lemma path_equiv_biimp :
 forall P P': sigT IsHProp, (P.1<->P'.1) <~> (P = P').
intros.
apply equiv_adjointify with (path_biimp P P') (biimp_path P P').
- intro x. destruct x. eapply allpath_hprop.
- intros x. cut (IsHProp (P .1 <-> P' .1)). intro H. apply allpath_hprop.
  cut (Contr(P .1 <-> P' .1)). intro. apply trunc_succ.
  exists x. intro y. destruct y as [y1 y2]. destruct x as [x1 x2].
f_ap; apply path_forall; intro x; [apply P'.2| apply P.2].
Defined.

(** The variant of [uahp] for record types. *)
Lemma path_equiv_biimp_rec {P P':hProp}: (P->P') -> (P'->P) -> P = P'.
set (p:=issig_hProp^-1 P).
set (p':=issig_hProp^-1 P').
intros X X0.
assert (p=p') by (by apply path_equiv_biimp).
clear X X0.
transitivity (issig_hProp (issig_hProp ^-1 P)); destruct P. reflexivity.
transitivity (issig_hProp (issig_hProp ^-1 P')); destruct P';[f_ap|reflexivity].
Defined.

(** We will now prove that for sets epis and surjections are biequivalent.*)
Definition isepi {X Y} `(f:X->Y) := forall Z: hSet,
  forall g h: Y -> Z, g o f = h o f -> g = h.

Definition isepi' {X Y} `(f : X -> Y) :=
  forall (Z : hSet) (g : Y -> Z), Contr { h : Y -> Z | g o f = h o f }.

Lemma equiv_isepi_isepi' {X Y} f : @isepi X Y f <~> @isepi' X Y f.
Proof.
  unfold isepi, isepi'.
  apply (@equiv_functor_forall' _ _ _ _ _ (equiv_idmap _)); intro Z.
  apply (@equiv_functor_forall' _ _ _ _ _ (equiv_idmap _)); intro g.
  unfold equiv_idmap; simpl.
  refine (transitivity _ _ _ (@equiv_sigT_rect _ _ (fun h : Y -> Z => g o f = h o f) (fun h => g = h.1)) _).
  (** TODO(JasonGross): Can we do this entirely by chaining equivalences? *)
  apply equiv_iff_hprop.
  { intro hepi.
    refine {| center := (g; idpath) |}.
    intro xy; specialize (hepi xy).
    apply path_sigma_uncurried.
    exists hepi.
    apply allpath_hprop. }
  { intros hepi xy.
    exact (ap pr1 ((contr (g; 1))^ @ contr xy)). }
Defined.

Definition issurj {X Y} (f:X->Y) := forall y:Y , hexists (fun x => (f x) = y).

Section cones.
  Lemma isepi'_contr_cone `{Funext} {A B : hSet} (f : A -> B) : isepi' f -> Contr (cone f).
  Proof.
    intros hepi.
    exists (cone_point _).
    pose (alpha1 := @pp A B Unit f !).
    pose (tot:= { h : B -> cone f & truncation_incl o push o inl o f = h o f }).
    pose (l := (truncation_incl o push o inl; idpath) : tot).
    pose (r := (@const B (cone f) (cone_point _); (ap (fun f => @truncation_incl 0 _ o f) (path_forall _ _ alpha1))) : tot).
    subst tot.
    assert (X : l = r) by (pose (hepi {| setT := cone f |} (truncation_incl o push o inl)); apply path_contr).
    subst l r.

    pose (I0 b := apD10 (X ..1) b).
    refine (Truncation_rect _ _).
    pose (fun a : B + Unit => (match a as a return cone_point _ = truncation_incl (push a) with
                                 | inl a' => (I0 a')^
                                 | inr tt => idpath
                               end)) as I0f.
    refine (pushout_rect _ _ _ I0f _).

    simpl. subst alpha1. intros.
    unfold cone_point.
    subst I0. simpl.
    pose (X..2) as p. simpl in p. rewrite transport_precompose in p.
    assert (H':=concat (ap (fun x => apD10 x a) p) (apD10_ap_postcompose truncation_incl _ _ (path_forall pushl pushr pp) _)).
    rewrite (apD10_path_forall _ _ _ a) in H'.
    clear p.
    (** Apparently [pose; clearbody] is only ~.8 seconds, while [pose proof] is ~4 seconds? *)
    pose (concat (apD10_ap_precompose f _ _ (X ..1) a)^ H') as p.
    clearbody p.
    simpl in p.
    rewrite p.
    rewrite transport_paths_Fr.
    apply concat_Vp.
  Qed.
End cones.

Lemma issurj_isepi {X Y} (f:X->Y): issurj f -> isepi f.
intros sur ? ? ? ep. apply path_forall. intro y.
specialize (sur y).
apply (minus1Trunc_rect_nondep (A:=(sigT (fun x : X => f x = y))));
  try assumption.
 intros [x p]. set (p0:=apD10 ep x).
 transitivity (g (f x)). by apply ap.
 transitivity (h (f x)); auto with path_hints. by apply ap.
intros. by apply @set_path2.
Qed.

(** Old-style proof using polymorphic Omega. Needs resizing for the isepi proof to live in the
 same universe as X and Y (the Z quantifier is instantiated with an hSet at a level higher)
<<
Lemma isepi_issurj {X Y} (f:X->Y): isepi f -> issurj f.
Proof.
  intros epif y.
  set (g :=fun _:Y => Unit_hp).
  set (h:=(fun y:Y => (hp (hexists (fun _ : Unit => {x:X & y = (f x)})) _ ))).
  assert (X1: g o f = h o f ).
  - apply path_forall. intro x. apply path_equiv_biimp_rec;[|done].
    intros _ . apply min1. exists tt. by (exists x).
  - specialize (epif _ g h).
    specialize (epif X1). clear X1.
    set (p:=apD10 epif y).
    apply (@minus1Trunc_map (sigT (fun _ : Unit => sigT (fun x : X => y = f x)))).
    + intros [ _ [x eq]].
      exists x.
        by symmetry.
    + apply (transport hproptype p tt).
Defined.
>> *)

Section isepi_issurj.
  Context {X Y : hSet} (f : X -> Y) (Hisepi : isepi f).
  Definition epif := equiv_isepi_isepi' _ Hisepi.
  Definition fam (c : cone f) : hProp.
  Proof.
    pose (fib y := hp (hexists (fun x : X => f x = y)) _).
    apply (fun f => @Truncation_rect_nondep _ _ hProp _ f c).
    refine (pushout_rectnd hProp
                           (fun x : Y + Unit =>
                              match x with
                                | inl y => fib y
                                | inr x => Unit_hp
                              end)
                           (fun x => _)).
    (** Prove that the truncated sigma is equivalent to Unit *)
    pose (contr_inhabited_hprop (fib (f x)) (min1 (x; idpath))) as i.
    apply path_hprop. simpl. simpl in i.
    refine (path_universe_uncurried _).
    apply (equiv_contr_unit).
  Defined.

  Lemma isepi_issurj : issurj f.
  Proof.
    intros y.
    pose (i := isepi'_contr_cone _ epif).

    assert (X0 : forall x : cone f, fam x = fam (cone_point f)).
    { intros. apply contr_dom_equiv. apply i. }
    specialize (X0 (truncation_incl (push (inl y)))). simpl in X0.
    exact (transport idmap (ap hproptype X0)^ tt).
  Defined.
End isepi_issurj.

Lemma isepi_isequiv X Y (f : X -> Y) `{IsEquiv _ _ f}
: isepi f.
Proof.
  intros ? g h H'.
  apply ap10 in H'.
  apply path_forall.
  intro x.
  transitivity (g (f (f^-1 x))).
  - by rewrite eisretr.
  - transitivity (h (f (f^-1 x))).
    * apply H'.
    * by rewrite eisretr.
Qed.
End AssumingUA.
