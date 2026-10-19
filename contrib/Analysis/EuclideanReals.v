(** * The Euclidean reals *)

(** Assuming propositional resizing, the Euclidean reals of Escardó and Simpson ("A universal characterization of the closed Euclidean interval", LICS 2001) are the least Cauchy complete subset containing the rationals of a Cauchy complete Archimedean ordered field [F], such as the Dedekind reals: the meet of all such subsets. They coincide with the HoTT book reals when those exist, and they are homotopy-initial among Cauchy structures on sets. The proof of initiality follows the strategy of Escardó and Simpson: the subsets [Y] containing the rationals and contained in the Euclidean reals, with a unique morphism restricted to [Y], form a subdcpo of the subsets of [F] which is closed under adding limits, so that a fixed point of adding limits in it, which exists by the fixed point theorem for subdcpos, is Cauchy complete and hence the Euclidean reals. *)

From HoTT Require Import Basics Types.Sigma Types.Forall Types.Universe Truncations.Core
  Truncations.Constant.
From HoTT.Universes Require Import HSet HProp TruncType.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.rationals
  interfaces.archimedean
  interfaces.cauchy
  interfaces.round
  theory.rings
  theory.rationals
  orders.orders
  orders.rings
  orders.rationals.
From HoTT.DomainTheory Require Import Dcpo Constructions FixedPoints.
From HoTT_Contrib.Analysis Require Import
  MetricSpace CauchyCompleteness CauchyStructure HoTTBookReals RealsInclusions.

Section euclidean.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}
    `{!RoundUpStrict Q}.
  Context {F : Type} `{OrderedField F} {Farch : ArchimedeanProperty Q F} `{!IsComplete Q F}.
  Let qinc : Cast Q F := rationals_to_field Q F.
  Existing Instance qinc.

  (** ** The Euclidean reals *)

  Universe i.

  (** The Cauchy complete subsets of [F] containing the rationals. *)
  Definition CompleteSubset
    := {R : F -> HProp@{i} & prod (ContainsRationals Q R) (IsCauchyCompleteSubset Q R)}.

  Context `{Funext} `{PropResizing}.

  (** With propositional resizing, the Euclidean reals are the meet of the Cauchy complete subsets containing the rationals, a subset in the same universe. *)
  Definition euclidean_reals (x : F) : HProp@{i}
    := hprop_meet (fun R : CompleteSubset => R.1 x).

  Definition euclidean_reals_in (x : F)
    : (forall R : CompleteSubset, R.1 x) -> euclidean_reals x
    := hprop_meet_in _.

  Definition euclidean_reals_out (x : F) (r : euclidean_reals x) (R : CompleteSubset)
    : R.1 x
    := hprop_meet_out _ R r.

  Definition containsrationals_euclidean_reals : ContainsRationals Q euclidean_reals
    := fun q => euclidean_reals_in _ (fun R => fst R.2 q).

  Definition iscauchycompletesubset_euclidean_reals : IsCauchyCompleteSubset Q euclidean_reals
    := fun x h => euclidean_reals_in _
         (fun R => snd R.2 x (fun e => euclidean_reals_out _ (h e) R)).

  (** The Euclidean reals are the least Cauchy complete subset containing the rationals. *)
  Definition euclidean_reals_least (R : F -> HProp@{i})
    (Rq : ContainsRationals Q R) (Rc : IsCauchyCompleteSubset Q R) (x : F)
    : euclidean_reals x -> R x
    := fun r => euclidean_reals_out x r (R; (Rq, Rc)).

  (** The Euclidean reals with their Cauchy structure. *)
  Definition euclidean_reals_cauchy_structure : CauchyStructure Q
    := subset_cauchy_structure Q euclidean_reals containsrationals_euclidean_reals
         iscauchycompletesubset_euclidean_reals.

  (** ** The Euclidean reals and the HoTT book reals *)

  Section hottbookreals.
    Context (RH : CauchyStructure Q) `{!IsHoTTBookReals Q RH}.
    Local Notation i := (hottbookreals_to_field Q RH (F:=F)).

    Definition containsrationals_hottbookreals : ContainsRationals Q (subset_hottbookreals Q RH)
      := fun q => (cs_rat Q RH q; cshom_rat Q _ _ i q).

    (** As subsets of [F], the Euclidean reals and the HoTT book reals coincide. *)
    Lemma euclidean_reals_iff_hottbookreals (x : F)
      : euclidean_reals x <-> subset_hottbookreals Q RH x.
    Proof.
      split.
      - apply euclidean_reals_least.
        + exact containsrationals_hottbookreals.
        + exact (iscauchycompletesubset_hottbookreals Q RH).
      - intros [u p]; rewrite <- p.
        exact (hottbookreals_to_field_subset Q euclidean_reals containsrationals_euclidean_reals
                 iscauchycompletesubset_euclidean_reals RH u).
    Qed.
  End hottbookreals.

  (** ** Morphisms on subsets *)

  Section subhom.
    Context (S : CauchyStructure Q) `{!IsHSet S}.
    Local Notation closeS := (cs_close Q S).
    Local Notation FC := (CauchyApproximation Q (field_close Q (F:=F))).

    (** A morphism of Cauchy structures restricted to a subset [Y]: a map preserving closeness, the rationals in [Y] and the limits in [Y] of Cauchy approximations in [Y]. *)
    Record SubHom (Y : F -> HProp) := {
      subhom_fun :> sig Y -> S;
      subhom_close : forall e (u v : sig Y), field_close Q e u.1 v.1
        -> closeS e (subhom_fun u) (subhom_fun v);
      subhom_rat : forall q (h : Y (' q)), subhom_fun (exist Y (' q) h) = cs_rat Q S q;
      subhom_lim : forall (x : FC) (hx : forall e, Y (x e)) (h : Y (field_lim Q x)),
        subhom_fun (exist Y (field_lim Q x) h)
        = cs_lim Q S (Build_CauchyApproximation Q closeS (fun e => subhom_fun (exist Y (x e) (hx e)))
                        (fun d e => subhom_close (d + e) (exist Y (x d) (hx d))
                                      (exist Y (x e) (hx e))
                                      (iscauchyapproximation_approximation Q _ x d e)))
    }.

    Arguments subhom_fun {Y} a u : rename.
    Arguments subhom_close {Y} a e u v c : rename.
    Arguments subhom_rat {Y} a q h : rename.
    Arguments subhom_lim {Y} a x hx h : rename.

    Definition subhom_approximation {Y : F -> HProp} (a : SubHom Y) (x : FC)
      (hx : forall e, Y (x e))
      : CauchyApproximation Q closeS
      := Build_CauchyApproximation Q closeS (fun e => a (exist Y (x e) (hx e)))
           (fun d e => subhom_close a (d + e) (exist Y (x d) (hx d)) (exist Y (x e) (hx e))
                         (iscauchyapproximation_approximation Q _ x d e)).

    Definition issig_subhom (Y : F -> HProp) : _ <~> SubHom Y := ltac:(issig).

    Lemma path_subhom {Y : F -> HProp} (a b : SubHom Y) (p : a == b) : a = b.
    Proof.
      apply (equiv_ap' (issig_subhom Y)^-1 _ _).
      apply path_sigma_hprop; funext u; exact (p u).
    Defined.

    Definition contr_subhom_iff (Y : F -> HProp)
      : Contr (SubHom Y) <-> SubHom Y * (forall a b : SubHom Y, a == b).
    Proof.
      split.
      - intros c; split; [exact (center _)|].
        intros a b; exact (ap10 (ap (subhom_fun (Y:=Y)) (path_contr a b))).
      - intros [a h]; apply (Build_Contr _ a); intro b; exact (path_subhom a b (h a b)).
    Defined.

    (** A restricted morphism on [Y] restricts to every subset of [Y]. *)
    Definition subhom_restrict {X Y : F -> HProp} (inc : forall y, X y -> Y y) (a : SubHom Y)
      : SubHom X.
    Proof.
      snapply Build_SubHom.
      - exact (fun u => a (u.1; inc _ u.2)).
      - exact (fun e u v c => subhom_close a e (u.1; inc _ u.2) (v.1; inc _ v.2) c).
      - exact (fun q h => subhom_rat a q (inc _ h)).
      - exact (fun x hx h => subhom_lim a x (fun e => inc _ (hx e)) (inc _ h)).
    Defined.

    (** The value at a point is the limit of the constant approximation. *)
    Lemma subhom_const {X : F -> HProp} (a : SubHom X) (y : F) (h : X y)
      : a (exist X y h) = cs_lim Q S (subhom_approximation a (const_approximation Q y) (fun _ => h)).
    Proof.
      rhs_V exact (subhom_lim a (const_approximation Q y) (fun _ => h)
                     (transport X (field_lim_const Q y)^ h)).
      apply ap; exact (path_sigma_hprop (y; h) (_; _) (field_lim_const Q y)^).
    Qed.

    (** Approximations with the same limit have images with the same limit. *)
    Lemma subhom_lim_path {X : F -> HProp} (a : SubHom X) (x x' : FC)
      (hx : forall e, X (x e)) (hx' : forall e, X (x' e)) (p : field_lim Q x = field_lim Q x')
      : cs_lim Q S (subhom_approximation a x hx) = cs_lim Q S (subhom_approximation a x' hx').
    Proof.
      rapply cs_lim_path; intros e d n; apply subhom_close.
      apply (field_close_lim_lim Q x x' e); rewrite p; apply (field_close_refl Q).
    Qed.

    (** The subsets [Y] containing the rationals and contained in the Euclidean reals on which there is a unique restricted morphism. *)
    Definition unique_subhom_subset (Y : F -> HProp@{i}) : HProp
      := Build_HProp (ContainsRationals Q Y * (forall y, Y y -> euclidean_reals y)
                      * Contr (SubHom Y)).

    (** ** The rationals *)

    Definition rationals_subset (y : F) : HProp@{i}
      := Build_HProp (hfiber (cast Q F) y).

    Definition containsrationals_rationals : ContainsRationals Q rationals_subset
      := fun q => (q; idpath).

    Definition subhom_rationals : SubHom rationals_subset.
    Proof.
      snapply Build_SubHom.
      - exact (fun u => cs_rat Q S (u.2).1).
      - intros e [y [q p]] [y' [r p']] c; cbn in c |- *; destruct p, p'.
        exact (cs_close_rat_rat Q S q r e (rational_close_field_close Q e q r c)).
      - intros q h; cbn.
        exact (ap (cs_rat Q S) (ap pr1 (path_ishprop h (q; idpath)))).
      - intros x hx [s p]; cbn.
        apply cs_eq; intro e; rewrite (pos_split3 e).
        apply cs_close_rat_lim; cbn.
        destruct (hx (e / 3)) as [q p']; cbn.
        apply (cs_close_rat_rat Q S), (rational_close_field_close Q (F:=F)).
        rewrite p, p'.
        exact (field_close_symmetric Q _ _ _
                 (isapproximationlimit_field_lim Q x (e / 3) (e / 3))).
    Defined.

    Lemma subhom_rationals_unique (a : SubHom rationals_subset) (u : sig rationals_subset)
      : a u = cs_rat Q S (u.2).1.
    Proof.
      destruct u as [y [q p]]; destruct p; exact (subhom_rat a q _).
    Qed.

    Definition unique_subhom_rationals : unique_subhom_subset rationals_subset.
    Proof.
      refine ((containsrationals_rationals, _), _).
      - intros y [q p]; destruct p; exact (containsrationals_euclidean_reals q).
      - apply (snd (contr_subhom_iff _)); split.
        + exact subhom_rationals.
        + intros a b u; exact (subhom_rationals_unique a u @ (subhom_rationals_unique b u)^).
    Defined.

    (** ** Limits of approximations in a subset *)

    Definition limits_subset (X : F -> HProp@{i}) (y : F) : HProp@{i}
      := Build_HProp (hexists (fun x : FC => prod (forall e, X (x e)) (field_lim Q x = y))).

    Definition limits_subset_incl (X : F -> HProp@{i}) (y : F) (h : X y) : limits_subset X y
      := tr (const_approximation Q y; (fun _ => h, field_lim_const Q y)).

    Section limits_closed.
      Context (X : F -> HProp@{i}) (hX : unique_subhom_subset X).
      Local Notation fX := (@center (SubHom X) (snd hX)).
      Local Notation PX := (limits_subset X).

      (** The value of the restricted morphism at the limit of an approximation in [X] is the limit in [S] of its images. It does not depend on the approximation, so it factors through the truncation in [PX]. *)
      Local Definition limits_fun (u : sig PX) : S.
      Proof.
        srapply (merely_rec_hset (fun w : {x : FC & prod (forall e, X (x e)) (field_lim Q x = u.1)}
                                  => cs_lim Q S (subhom_approximation fX w.1 (fst w.2))) u.2).
        intros [x [hx p]] [x' [hx' p']]; exact (subhom_lim_path fX x x' hx hx' (p @ p'^)).
      Defined.

      Arguments limits_fun : simpl never.

      Local Lemma limits_fun_beta (x : FC) (hx : forall e, X (x e)) (y : F)
        (p : field_lim Q x = y) (h : PX y)
        : limits_fun (y; h) = cs_lim Q S (subhom_approximation fX x hx).
      Proof.
        exact (ap (limits_fun o exist PX y) (path_ishprop h (tr (x; (hx, p))))).
      Qed.

      Local Lemma limits_fun_incl (y : F) (h : X y)
        : limits_fun (y; limits_subset_incl X y h) = fX (y; h).
      Proof.
        rewrite (limits_fun_beta (const_approximation Q y) (fun _ => h) y (field_lim_const Q y)).
        exact (subhom_const fX y h)^.
      Qed.

      Local Lemma limits_fun_close (e : Qpos Q) (u v : sig PX) (c : field_close Q e u.1 v.1)
        : closeS e (limits_fun u) (limits_fun v).
      Proof.
        destruct u as [y h], v as [y' h']; cbn in c.
        pose proof h as h0; pose proof h' as h0'; revert h h'.
        strip_truncations; destruct h0 as [x [hx p]], h0' as [x' [hx' p']]; intros h h'.
        rewrite (limits_fun_beta x hx y p), (limits_fun_beta x' hx' y' p').
        destruct p, p'.
        assert (r := field_close_rounded Q e _ _ c); strip_truncations.
        destruct r as [d [d' [q c']]]; rewrite q.
        rapply cs_close_lim_lim_split; intros n m; apply subhom_close.
        exact (field_close_lim_lim Q x x' d c' n m).
      Qed.

      Local Definition subhom_limits : SubHom PX.
      Proof.
        snapply Build_SubHom.
        - exact limits_fun.
        - exact limits_fun_close.
        - intros q h.
          rewrite (limits_fun_beta (const_approximation Q (' q)) (fun _ => fst (fst hX) q) (' q)
                     (field_lim_const Q _)).
          exact ((subhom_const fX _ _)^ @ subhom_rat fX q _).
        - intros x hx h.
          pose proof h as h0; revert h; strip_truncations; destruct h0 as [x' [hx' p]]; intro h.
          rewrite (limits_fun_beta x' hx' _ p).
          rapply cs_lim_path; intros e d n; cbn.
          rewrite <- limits_fun_incl.
          apply limits_fun_close; cbn.
          apply (field_close_lim_lim Q x' x e); rewrite p; apply (field_close_refl Q).
      Defined.

      Local Lemma subhom_limits_unique (a : SubHom PX) (u : sig PX)
        : a u = limits_fun u.
      Proof.
        destruct u as [y h]; pose proof h as h0; revert h.
        strip_truncations; destruct h0 as [x [hx p]]; intro h.
        rewrite (limits_fun_beta x hx y p); destruct p.
        lhs exact (subhom_lim a x (fun e => limits_subset_incl X _ (hx e)) h).
        exact (ap (fun b => cs_lim Q S (subhom_approximation b x hx))
                 (@path_contr _ (snd hX) (subhom_restrict (limits_subset_incl X) a) fX)).
      Qed.

      Definition unique_subhom_limits : unique_subhom_subset PX.
      Proof.
        refine ((_, _), _).
        - intro q; exact (limits_subset_incl X _ (fst (fst hX) q)).
        - intros y h; strip_truncations; destruct h as [x [hx p]]; destruct p.
          exact (iscauchycompletesubset_euclidean_reals x (fun e => snd (fst hX) _ (hx e))).
        - apply (snd (contr_subhom_iff _)); split.
          + exact subhom_limits.
          + intros a b u; exact (subhom_limits_unique a u @ (subhom_limits_unique b u)^).
      Defined.
    End limits_closed.

    (** ** Directed suprema *)

    Local Notation le := (relation_pointwise (fun _ : F => le_hprop@{i _})).

    Section directed.
      Context {I : Type} (D : I -> F -> HProp@{i}) (d : IsDirected (Ale:=le) D)
        (Y : F -> HProp@{i}) (sY : IsSup (Ale:=le) D Y)
        (hD : forall k, unique_subhom_subset (D k)).
      Local Notation fk k := (@center (SubHom (D k)) (snd (hD k))).

      Local Definition sup_in (k : I) (y : F) : D k y -> Y y := issup_upper sY k y.

      Local Lemma sup_out (y : F) : Y y -> merely {k : I & D k y}.
      Proof.
        intro h.
        assert (le' : le Y (fun y => hprop_join (fun k => D k y))).
        { apply (issup_least sY); intros k y' h'; exact (hprop_join_in _ k h'). }
        exact (equiv_smalltype _ (le' y h)).
      Qed.

      Local Lemma sup_compat (k m : I) (le_km : forall y, D k y -> D m y) (u : sig (D k))
        : fk k u = fk m (u.1; le_km _ u.2).
      Proof.
        exact (ap10 (ap (subhom_fun (Y:=D k))
                       (@path_contr _ (snd (hD k)) (fk k) (subhom_restrict le_km (fk m)))) u).
      Qed.

      (** The value at [y] is that of the morphism on any [D k] containing [y]. It does not depend on [k], since the family is directed, so it factors through the truncation. *)
      Local Definition sup_fun (u : sig Y) : S.
      Proof.
        srapply (merely_rec_hset (fun w : {k : I & D k u.1} => fk w.1 (u.1; w.2)) (sup_out _ u.2)).
        intros [k hk] [k' hk'].
        assert (m := snd d k k'); strip_truncations; destruct m as [m [lk lk']].
        rewrite (sup_compat k m lk), (sup_compat k' m lk').
        apply ap, path_sigma_hprop; reflexivity.
      Defined.

      Arguments sup_fun : simpl never.

      Local Lemma sup_fun_beta (k : I) (y : F) (hk : D k y) (h : Y y)
        : sup_fun (y; h) = fk k (y; hk).
      Proof.
        exact (ap (merely_rec_hset _) (path_ishprop (sup_out y h) (tr (k; hk)))).
      Qed.

      Local Lemma sup_fun_close (e : Qpos Q) (u v : sig Y) (c : field_close Q e u.1 v.1)
        : closeS e (sup_fun u) (sup_fun v).
      Proof.
        destruct u as [y h], v as [y' h']; cbn in c.
        assert (w := sup_out y h); assert (w' := sup_out y' h'); strip_truncations.
        destruct w as [k hk], w' as [k' hk'].
        assert (m := snd d k k'); strip_truncations; destruct m as [m [lk lk']].
        rewrite (sup_fun_beta m y (lk _ hk)), (sup_fun_beta m y' (lk' _ hk')).
        exact (subhom_close (fk m) e (y; lk _ hk) (y'; lk' _ hk') c).
      Qed.

      Local Definition subhom_sup : SubHom Y.
      Proof.
        snapply Build_SubHom.
        - exact sup_fun.
        - exact sup_fun_close.
        - intros q h.
          assert (k := fst d); strip_truncations.
          rewrite (sup_fun_beta k _ (fst (fst (hD k)) q)).
          exact (subhom_rat (fk k) q _).
        - intros x hx h.
          assert (w := sup_out _ h); strip_truncations; destruct w as [k hk].
          rewrite (sup_fun_beta k _ hk), (subhom_const (fk k)).
          rapply cs_lim_path; intros e d' n; cbn.
          rewrite <- (sup_fun_beta k _ hk h).
          apply sup_fun_close; cbn.
          apply (field_close_lim_lim Q (const_approximation Q _) x e).
          rewrite (field_lim_const Q); apply (field_close_refl Q).
      Defined.

      Local Lemma subhom_sup_unique (a : SubHom Y) (u : sig Y) : a u = sup_fun u.
      Proof.
        destruct u as [y h].
        assert (w := sup_out _ h); strip_truncations; destruct w as [k hk].
        rewrite (sup_fun_beta k _ hk).
        lhs exact (ap a (path_sigma_hprop (y; h) (y; sup_in k y hk) idpath)).
        exact (ap10 (ap (subhom_fun (Y:=D k))
                       (@path_contr _ (snd (hD k)) (subhom_restrict (sup_in k) a) (fk k))) (y; hk)).
      Qed.

      Definition unique_subhom_sup : unique_subhom_subset Y.
      Proof.
        refine ((_, _), _).
        - intro q; assert (k := fst d); strip_truncations.
          exact (sup_in k _ (fst (fst (hD k)) q)).
        - intros y h; assert (w := sup_out _ h); strip_truncations; destruct w as [k hk].
          exact (snd (fst (hD k)) y hk).
        - apply (snd (contr_subhom_iff _)); split.
          + exact subhom_sup.
          + intros a b u; exact (subhom_sup_unique a u @ (subhom_sup_unique b u)^).
      Defined.
    End directed.

    (** ** The fixed point *)

    Context `{Univalence}.

    Local Instance issubdcpo_unique_subhom : IsSubdcpo le unique_subhom_subset.
    Proof.
      intros I D d hD; exact (unique_subhom_sup D d _ (issup_dcpo_sup D d) hD).
    Defined.

    Local Instance orderpreserving_limits_subset
      : OrderPreserving (Ale:=le) (Ble:=le) limits_subset.
    Proof.
      intros X X' le_XX' y; exact (Trunc_functor _ (fun w => (w.1; (fun e => le_XX' _ (fst w.2 e), snd w.2)))).
    Defined.

    (** The least fixed point of [limits_subset] above the rationals, in the subdcpo of subsets with a unique restricted morphism, is the Euclidean reals. *)
    Lemma contr_subhom_euclidean_reals : Contr (SubHom euclidean_reals).
    Proof.
      destruct (fixed_point_subdcpo (Ale:=le) limits_subset unique_subhom_subset
                  unique_subhom_limits (fun X _ => limits_subset_incl X)
                  rationals_subset unique_subhom_rationals) as [R [hR p]].
      assert (Rc : IsCauchyCompleteSubset Q R).
      { intros x hx; exact (transport (fun Z : F -> HProp => Z (field_lim Q x)) p (tr (x; (hx, idpath)))). }
      assert (q : R = euclidean_reals).
      { funext y; apply path_iff_hprop.
        - exact (snd (fst hR) y).
        - exact (euclidean_reals_least R (fst (fst hR)) Rc y). }
      exact (transport (fun Z => Contr (SubHom Z)) q (snd hR)).
    Qed.

    (** On the Euclidean reals, restricted morphisms are the morphisms of Cauchy structures. *)
    Definition cshom_subhom_euclidean_reals (a : SubHom euclidean_reals)
      : CauchyStructureHom Q euclidean_reals_cauchy_structure S.
    Proof.
      snapply Build_CauchyStructureHom.
      - exact a.
      - exact (subhom_close a).
      - exact (fun q => subhom_rat a q _).
      - exact (fun x => subhom_lim a (approximation_subset_pr1 Q _ x) (fun e => (x e).2) _).
      - intros; apply path_ishprop.
    Defined.

    Definition subhom_cshom_euclidean_reals
      (f : CauchyStructureHom Q euclidean_reals_cauchy_structure S)
      : SubHom euclidean_reals.
    Proof.
      snapply Build_SubHom.
      - exact f.
      - exact (cshom_close Q _ _ f).
      - intros q h.
        rhs_V exact (cshom_rat Q _ _ f q).
        exact (ap f (path_sigma_hprop (exist euclidean_reals (' q) h)
                       (cs_rat Q euclidean_reals_cauchy_structure q) idpath)).
      - intros x hx h.
        pose (x' := Build_CauchyApproximation Q (subset_close Q euclidean_reals)
                      (fun e => (x e; hx e)) (iscauchyapproximation_approximation Q _ x)).
        refine (_ @ cshom_lim Q _ _ f x' @ _).
        + exact (ap f (path_sigma_hprop (exist euclidean_reals (field_lim Q x) h)
                         (cs_lim Q euclidean_reals_cauchy_structure x') idpath)).
        + apply ap; snapply path_cauchyapproximation; [exact _|]; intro e; reflexivity.
    Defined.

    (** The Euclidean reals are homotopy-initial among Cauchy structures on sets. *)
    Theorem contr_cshom_euclidean_reals
      : Contr (CauchyStructureHom Q euclidean_reals_cauchy_structure S).
    Proof.
      apply (snd (contr_cauchystructurehom_iff Q _ _)); split.
      - exact (cshom_subhom_euclidean_reals (@center _ contr_subhom_euclidean_reals)).
      - intros f g.
        exact (ap10 (ap (subhom_fun (Y:=euclidean_reals))
                       (@path_contr _ contr_subhom_euclidean_reals
                          (subhom_cshom_euclidean_reals f) (subhom_cshom_euclidean_reals g)))).
    Qed.
  End subhom.
End euclidean.
