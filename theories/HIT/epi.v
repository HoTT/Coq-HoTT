From HoTT Require Import Basics.
Require Import Types.
Require Import TruncType.
Require Import ReflectiveSubuniverse.
Require Import Colimits.Pushout Truncations.Core HIT.SetCone.

Local Open Scope path_scope.

Section AssumingUA.
Context `{ua:Univalence}.

(** We will now prove that for sets, epis and surjections are equivalent.*)
Definition isepi {X Y} `(f:X->Y) := forall Z: HSet,
  forall g h: Y -> Z, g o f = h o f -> g = h.

Definition isepi_funext {X Y : Type} (f : X -> Y)
  := forall Z : HSet, forall g0 g1 : Y -> Z, g0 o f == g1 o f -> g0 == g1.

Definition isepi' {X Y} `(f : X -> Y) :=
  forall (Z : HSet) (g : Y -> Z), Contr { h : Y -> Z | g o f = h o f }.

Lemma equiv_isepi_isepi' {X Y} f : @isepi X Y f <~> @isepi' X Y f.
Proof.
  unfold isepi, isepi'.
  apply (@equiv_functor_forall' _ _ _ _ _ (equiv_idmap _)); intro Z.
  apply (@equiv_functor_forall' _ _ _ _ _ (equiv_idmap _)); intro g.
  unfold equiv_idmap; simpl.
  refine (transitivity (@equiv_sig_ind _ (fun h : Y -> Z => g o f = h o f) (fun h => g = h.1)) _).
  (** TODO(JasonGross): Can we do this entirely by chaining equivalences? *)
  apply equiv_iff_hprop.
  { intro hepi.
    napply (Build_Contr _ (g; idpath)).
    intro xy; specialize (hepi xy).
    apply path_sigma_uncurried.
    exists hepi.
    apply path_ishprop. }
  { intros hepi xy.
    exact (ap pr1 ((contr (g; 1))^ @ contr xy)). }
Defined.

Definition equiv_isepi_isepi_funext {X Y : Type} (f : X -> Y)
  : isepi f <~> isepi_funext f.
Proof.
  apply equiv_iff_hprop.
  - intros e ? g0 g1 h.
    apply equiv_path_arrow.
    apply e.
    by apply path_arrow.
  - intros e ? g0 g1 p.
    apply path_arrow.
    apply e.
    by apply equiv_path_arrow.
Defined.

Section cones.
  Lemma isepi'_contr_cone `{Funext} {A B : HSet} (f : A -> B) : isepi' f -> Contr (setcone f).
  Proof.
    intros hepi.
    apply (Build_Contr _ (setcone_point _)).
    pose (alpha1 := @pglue A B Unit f (const_tt _)).
    pose (tot:= { h : B -> setcone f & tr o push o inl o f = h o f }).
    transparent assert (l : tot).
    { simple refine (tr o _ o inl; _).
      { exact push. }
      { exact idpath. } }
    pose (r := (@const B (setcone f) (setcone_point _); (ap (fun f => @tr 0 _ o f) (path_forall _ _ alpha1))) : tot).
    subst tot.
    assert (X : l = r).
      { let lem := constr:(fun X push' => hepi (Build_HSet (setcone f)) (tr o push' o @inl _ X)) in
        pose (lem _ push).
        exact (path_contr l r). }
    subst l r.

    pose (I0 b := ap10 (X ..1) b).
    refine (Trunc_ind _ _).
    pose (fun a : B + Unit => (match a as a return setcone_point _ = tr (push a) with
                                 | inl a' => (I0 a')^
                                 | inr tt => idpath
                               end)) as I0f.
    refine (Pushout_ind _ (fun a' => I0f (inl a')) (fun u => (I0f (inr u))) _).

    simpl. subst alpha1. intros.
    unfold setcone_point.
    subst I0. simpl.
    pose (X..2) as p. simpl in p.
    rewrite (transport_precompose f _ _ X..1) in p.
    assert (H':=concat (ap (fun x => ap10 x a) p) (ap10_ap_postcompose tr (path_arrow (pushl o f) (pushr o const_tt _) pglue) _)).
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
Proof.
intros sur ? ? ? ep. apply path_forall. intro y.
specialize (sur y). pose (center (merely (hfiber f y))).
apply (Trunc_rec (n:=-1) (A:=(sig (fun x : X => f x = y))));
  try assumption.
intros [x p]. set (p0:=apD10 ep x).
transitivity (g (f x)).
- by apply ap.
- transitivity (h (f x));auto with path_hints. by apply ap.
Qed.

Corollary issurj_isepi_funext {X Y} (f:X->Y) : IsSurjection f -> isepi_funext f.
Proof.
  intro s.
  apply equiv_isepi_isepi_funext.
  by apply issurj_isepi.
Defined.

(** Old-style proof using polymorphic Omega. Needs resizing for the [isepi] proof to live in the
 same universe as X and Y (the Z quantifier is instantiated with an HSet at a level higher)
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
    apply (@minus1Trunc_map (sig (fun _ : Unit => sig (fun x : X => y = f x)))).
    + intros [ _ [x eq]].
      exists x.
        by symmetry.
    + apply (transport hproptype p tt).
Defined.
>>
*)

Section isepi_issurj.
  Context {X Y : HSet} (f : X -> Y) (Hisepi : isepi f).
  Definition epif := equiv_isepi_isepi' _ Hisepi.
  Definition fam (c : setcone f) : HProp.
  Proof.
    pose (fib y := hexists (fun x : X => f x = y)).
    apply (fun f => @Trunc_rec _ _ HProp _ f c).
    refine (Pushout_rec HProp fib (fun _ => Unit_hp) (fun x => _)).
    (** Prove that the truncated sigma is equivalent to Unit *)
    pose (contr_inhabited_hprop (fib (f x)) (tr (x; idpath))) as i.
    apply path_hprop. simpl. simpl in i.
    exact (equiv_contr_unit).
  Defined.

  Lemma isepi_issurj : IsSurjection f.
  Proof.
    intros y.
    pose (i := isepi'_contr_cone _ epif).

    assert (X0 : forall x : setcone f, fam x = fam (setcone_point f)).
    { intros. apply contr_dom_equiv. exact i. }
    specialize (X0 (tr (push (inl y)))). simpl in X0.
    unfold IsConnected.
    refine (transport (fun A => Contr A) (ap trunctype_type X0)^ _); exact _.
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
