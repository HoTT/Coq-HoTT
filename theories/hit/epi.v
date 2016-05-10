Require Import HoTT.Basics.
Require Import Types.Universe Types.Unit Types.Forall Types.Arrow Types.Sigma Types.Paths.
Require Import HProp HSet TruncType UnivalenceImpliesFunext.
Require Import hit.Pushout hit.Truncations hit.Connectedness.

Local Open Scope path_scope.

Section AssumingUA.
Context `{ua:Univalence}.

(** We will now prove that for sets, epis and surjections are equivalent.*)
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
  refine (transitivity (@equiv_sigT_ind _ (fun h : Y -> Z => g o f = h o f) (fun h => g = h.1)) _).
  (** TODO(JasonGross): Can we do this entirely by chaining equivalences? *)
  apply equiv_iff_hprop.
  { intro hepi.
    refine {| center := (g; idpath) |}.
    intro xy; specialize (hepi xy).
    apply path_sigma_uncurried.
    exists hepi.
    apply path_ishprop. }
  { intros hepi xy.
    exact (ap pr1 ((contr (g; 1))^ @ contr xy)). }
Defined.

Section cones.
  Lemma isepi'_contr_cone `{Funext} {A B : hSet} (f : A -> B) : isepi' f -> Contr (setcone f).
  Proof.
    intros hepi.
    exists (setcone_point _).
    pose (alpha1 := @pp A B Unit f (const tt)).
    pose (tot:= { h : B -> setcone f & tr o push o inl o f = h o f }).
    transparent assert (l : tot).
    { simple refine (tr o _ o inl; _).
      { refine push. }
      { refine idpath. } }
    pose (r := (@const B (setcone f) (setcone_point _); (ap (fun f => @tr 0 _ o f) (path_forall _ _ alpha1))) : tot).
    subst tot.
    assert (X : l = r).
      { let lem := constr:(fun X push' => hepi (BuildhSet (setcone f)) (tr o push' o @inl _ X)) in
        pose (lem _ push).
        refine (path_contr l r). }
    subst l r.

    pose (I0 b := ap10 (X ..1) b).
    refine (Trunc_ind _ _).
    pose (fun a : B + Unit => (match a as a return setcone_point _ = tr (push a) with
                                 | inl a' => (I0 a')^
                                 | inr tt => idpath
                               end)) as I0f.
    refine (pushout_ind _ _ _ I0f _).

    simpl. subst alpha1. intros.
    unfold setcone_point.
    subst I0. simpl.
    pose (X..2) as p. simpl in p.
    rewrite (transport_precompose f _ _ X..1) in p.
    assert (H':=concat (ap (fun x => ap10 x a) p) (ap10_ap_postcompose tr (path_arrow pushl pushr pp) _)).
    rewrite ap10_path_arrow in H'.
    clear p.
    (** Apparently [pose; clearbody] is only ~.8 seconds, while [pose proof] is ~4 seconds? *)
    pose (concat (ap10_ap_precompose f (X ..1) a)^ H') as p.
    clearbody p.
    simpl in p.
    rewrite p.
    rewrite transport_paths_Fr.
    apply concat_Vp.
  Qed.
End cones.

Lemma issurj_isepi {X Y} (f:X->Y): IsSurjection f -> isepi f.
intros sur ? ? ? ep. apply path_forall. intro y.
specialize (sur y). pose (center (merely (hfiber f y))).
apply (Trunc_rec (n:=-1) (A:=(sigT (fun x : X => f x = y))));
  try assumption.
 intros [x p]. set (p0:=apD10 ep x).
 transitivity (g (f x)). by apply ap.
 transitivity (h (f x));auto with path_hints. by apply ap.
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
  Definition fam (c : setcone f) : hProp.
  Proof.
    pose (fib y := hexists (fun x : X => f x = y)).
    apply (fun f => @Trunc_rec _ _ hProp _ f c).
    refine (pushout_rec hProp
                           (fun x : Y + Unit =>
                              match x with
                                | inl y => fib y
                                | inr x => Unit_hp
                              end)
                           (fun x => _)).
    (** Prove that the truncated sigma is equivalent to Unit *)
    pose (contr_inhabited_hprop (fib (f x)) (tr (x; idpath))) as i.
    apply path_hprop. simpl. simpl in i.
    apply (equiv_contr_unit).
  Defined.

  Lemma isepi_issurj : IsSurjection f.
  Proof.
    intros y.
    pose (i := isepi'_contr_cone _ epif).

    assert (X0 : forall x : setcone f, fam x = fam (setcone_point f)).
    { intros. apply contr_dom_equiv. apply i. }
    specialize (X0 (tr (push (inl y)))). simpl in X0.
    exact (transport Contr (ap trunctype_type X0)^ _).
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
