From HoTT Require Import Basics Types.
Require Import HoTT.Truncations.
Require Import Universes.BAut Universes.Rigid.
Require Import ExcludedMiddle.

Local Open Scope trunc_scope.
Local Open Scope path_scope.

(** * The universe *)

(** ** Automorphisms of the universe *)

(** See "Parametricity, automorphisms of the universe, and excluded middle" by Booij, Escardó, Lumsdaine, Shulman. *)

(** If two inequivalent types have equivalent automorphism oo-groups, then assuming LEM we can swap them and leave the rest of the universe untouched. *)
Section SwapTypes.
  (** Amusingly, this does not actually require univalence!  But of course, to verify [BAut A <~> BAut B] in any particular example does require univalence. *)
  Context `{Funext} `{ExcludedMiddle}.
  Context (A B : Type) (ne : ~(A <~> B)) (e : BAut A <~> BAut B).

  Definition equiv_swap_types : Type <~> Type.
  Proof.
    refine (((equiv_decidable_sum (fun X:Type => merely (X=A)))^-1)
              oE _ oE
              (equiv_decidable_sum (fun X:Type => merely (X=A)))).
    refine ((equiv_functor_sum_l
               (equiv_decidable_sum (fun X => merely (X.1=B)))^-1)
              oE _ oE
              (equiv_functor_sum_l
                 (equiv_decidable_sum (fun X => merely (X.1=B))))).
    refine ((equiv_sum_assoc _ _ _)
              oE _ oE
              (equiv_sum_assoc _ _ _)^-1).
    apply equiv_functor_sum_r.
    assert (q : BAut B <~> {x : {x : Type & ~ merely (x = A)} &
                                merely (x.1 = B)}).
    { refine (equiv_sigma_assoc _ _ oE _).
      apply equiv_functor_sigma_id; intros X.
      apply equiv_iff_hprop.
      - intros p.
        refine (fun q => _ ; p).
        strip_truncations.
        destruct q.
        exact (ne (equiv_path X B p)).
      - exact pr2. }
    refine (_ oE equiv_sum_symm _ _).
    apply equiv_functor_sum'.
    - exact (e^-1 oE q^-1).
    - exact (q oE e).
  Defined.

  Definition equiv_swap_types_swaps : merely (equiv_swap_types A = B).
  Proof.
    assert (ea := (e (point _)).2). cbn in ea.
    strip_truncations; apply tr.
    unfold equiv_swap_types.
    apply moveR_equiv_V.
    rewrite (equiv_decidable_sum_l
               (fun X => merely (X=A)) A (tr 1)).
    assert (ne' : ~ merely (B=A))
      by (intros p; strip_truncations; exact (ne (equiv_path A B p^))).
    rewrite (equiv_decidable_sum_r
               (fun X => merely (X=A)) B ne').
    cbn.
    apply ap, path_sigma_hprop; cbn.
    exact ea.
  Defined.

  Definition equiv_swap_types_not_id
    : equiv_swap_types <> equiv_idmap.
  Proof.
    intros p.
    assert (q := equiv_swap_types_swaps).
    strip_truncations.
    apply ne.
    apply equiv_path.
    rewrite p in q; exact q.
  Qed.

End SwapTypes.

(** In particular, we can swap any two distinct rigid types. *)

Definition equiv_swap_rigid `{Univalence} `{ExcludedMiddle}
           (A B : Type) `{IsRigid A} `{IsRigid B} (ne : ~(A <~> B))
  : Type <~> Type.
Proof.
  refine (equiv_swap_types A B ne _).
  exact equiv_contr_contr.
Defined.

(** Such as [Empty] and [Unit]. *)

Definition equiv_swap_empty_unit `{Univalence} `{ExcludedMiddle}
  : Type <~> Type
  := equiv_swap_rigid Empty Unit (fun e => e^-1 tt).

(** In this case we get an untruncated witness of the swapping. *)

Definition equiv_swap_rigid_swaps `{Univalence} `{ExcludedMiddle}
           (A B : Type) `{IsRigid A} `{IsRigid B} (ne : ~(A <~> B))
  : equiv_swap_rigid A B ne A = B.
Proof.
  unfold equiv_swap_rigid, equiv_swap_types.
  apply moveR_equiv_V.
  rewrite (equiv_decidable_sum_l
             (fun X => merely (X=A)) A (tr 1)).
  assert (ne' : ~ merely (B=A))
    by (intros p; strip_truncations; exact (ne (equiv_path A B p^))).
  rewrite (equiv_decidable_sum_r
             (fun X => merely (X=A)) B ne').
  cbn.
  apply ap, path_sigma_hprop; cbn.
  exact ((path_contr (center (BAut B)) (point (BAut B)))..1).
Defined.

(** We can also swap the products of two rigid types with another type [X], under a connectedness/truncatedness assumption. *)

Definition equiv_swap_prod_rigid  `{Univalence} `{ExcludedMiddle}
           (X A B : Type) (n : trunc_index) (ne : ~(X*A <~> X*B))
           `{IsRigid A} `{IsConnected n.+1 A}
           `{IsRigid B} `{IsConnected n.+1 B}
           `{IsTrunc n.+1 X}
  : Type <~> Type.
Proof.
  refine (equiv_swap_types (X*A) (X*B) ne _).
  transitivity (BAut X).
  - symmetry; exact (baut_prod_rigid_equiv X A n).
  - exact (baut_prod_rigid_equiv X B n).
Defined.

(** Conversely, from some nontrivial automorphisms of the universe we can deduce nonconstructive consequences. *)

Definition lem_from_aut_type_unit_empty `{Univalence}
           (f : Type <~> Type) (eu : f Unit = Empty)
  : ExcludedMiddle_type.
Proof.
  apply DNE_to_LEM, DNE_from_allneg; intros P ?.
  exists (f P); split.
  - intros p.
    assert (Contr P) by (apply contr_inhabited_hprop; assumption).
    assert (q : Unit = P)
      by (apply path_universe_uncurried, equiv_contr_contr).
    destruct q.
    rewrite eu.
    auto.
  - intros nfp.
    assert (q : f P = Empty)
      by (apply path_universe_uncurried, equiv_to_empty, nfp).
    rewrite <- eu in q.
    apply ((ap f)^-1) in q.
    rewrite q; exact tt.
Defined.

Lemma equiv_hprop_idprod `{Univalence}
      (A : Type) (P : Type) (a : merely A) `{IsHProp P}
  : P <-> (P * A = A).
Proof.
  split.
  - intros p; apply path_universe with snd.
    apply isequiv_adjointify with (fun a => (p,a)).
    + intros x; reflexivity.
    + intros [p' x].
      apply path_prod; [ apply path_ishprop | reflexivity ].
  - intros q.
    strip_truncations.
    apply equiv_path in q.
    exact (fst (q^-1 a)).
Defined.

Definition lem_from_aut_type_inhabited_empty `{Univalence}
           (f : Type <~> Type)
           (A : Type) (a : merely A) (eu : f A = Empty)
  : ExcludedMiddle_type.
Proof.
  apply DNE_to_LEM, DNE_from_allneg; intros P ?.
  exists (f (P * A)); split.
  - intros p.
    assert (q := fst (equiv_hprop_idprod A P a) p).
    apply (ap f) in q.
    rewrite eu in q.
    rewrite q; auto.
  - intros q.
    apply equiv_to_empty in q.
    apply path_universe_uncurried in q.
    rewrite <- eu in q.
    apply ((ap f)^-1) in q.
    exact (snd (equiv_hprop_idprod A P a) q).
Defined.

(** If you can derive a constructive taboo from an automorphism of the universe such that [g X <> X], then you get [X]-many beers; see <https://groups.google.com/d/msg/homotopytypetheory/8CV0S2DuOI8/blCo7x-B7aoJ>. *)

Definition zero_beers `{Univalence}
           (g : Type <~> Type) (ge : g Empty <> Empty)
  : ~~ExcludedMiddle_type.
Proof.
  pose (f := equiv_inverse g).
  intros nlem.
  apply ge.
  apply path_universe_uncurried, equiv_to_empty; intros gz.
  apply nlem.
  apply (lem_from_aut_type_inhabited_empty f (g Empty) (tr gz)).
  unfold f; apply eissect.
Defined.

Definition lem_beers `{Univalence}
           (g : Type <~> Type) (ge : g ExcludedMiddle_type <> ExcludedMiddle_type)
  : ~~ExcludedMiddle_type.
Proof.
  intros nlem.
  pose (nlem' := equiv_to_empty nlem).
  apply path_universe_uncurried in nlem'.
  rewrite nlem' in ge.
  apply (zero_beers g) in ge.
  exact (ge nlem).
Defined.
