(** * Cauchy approximations and Cauchy structures *)

From HoTT Require Import Basics Types.Sigma Types.Forall Truncations.Core.
From HoTT.Spaces Require Import Nat.Core.
From HoTT.Classes Require Import
  interfaces.abstract_algebra
  interfaces.orders
  interfaces.rationals
  interfaces.archimedean
  interfaces.cauchy
  interfaces.naturals
  interfaces.round
  implementations.peano_naturals
  theory.rings
  theory.dec_fields
  theory.rationals
  orders.orders
  orders.rings
  orders.semirings
  orders.dec_fields
  orders.naturals
  orders.rationals.
From HoTT_Contrib.Analysis Require Import MetricSpace CauchyCompleteness.

(** Premetrics, moduli of Cauchy convergence and limits of sequences are in [MetricSpace]. *)

Section cauchy_structure.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q}.

  (** ** Cauchy approximations *)

  Section approximation.
    Context {X : Type} (close : Qpos Q -> X -> X -> Type).

    (** A Cauchy approximation is a map [x] from the positive rationals with [x d] and [x e] being [(d + e)]-close. *)
    Definition IsCauchyApproximation (x : Qpos Q -> X)
      := forall d e : Qpos Q, close (d + e) (x d) (x e).

    Record CauchyApproximation := {
      approximation :> Qpos Q -> X;
      iscauchyapproximation_approximation : IsCauchyApproximation approximation
    }.

    (** A limit of a Cauchy approximation [x] is a point [u] with [x e] and [u] being [(e + d)]-close for all [e] and [d]. *)
    Definition IsApproximationLimit (x : Qpos Q -> X) (u : X)
      := forall e d : Qpos Q, close (e + d) (x e) u.

    (** Cauchy completeness is the structure of a limit operator for Cauchy approximations. *)
    Class CauchyComplete := {
      approximation_limit : CauchyApproximation -> X;
      isapproximationlimit_approximation_limit
        : forall x : CauchyApproximation, IsApproximationLimit x (approximation_limit x)
    }.

    Definition issig_cauchyapproximation : _ <~> CauchyApproximation := ltac:(issig).

    (** Over a premetric, Cauchy approximations with the same values are equal. *)
    Lemma path_cauchyapproximation `{Funext} `{!IsPremetric Q close}
      (x y : CauchyApproximation) (p : forall e, x e = y e)
      : x = y.
    Proof.
      apply (equiv_ap' issig_cauchyapproximation^-1 _ _).
      apply path_sigma_hprop; funext e; exact (p e).
    Defined.

  End approximation.

  (** A map which preserves closeness acts on Cauchy approximations. *)
  Definition map_cauchy_approximation {X Y : Type} {closeX : Qpos Q -> X -> X -> Type}
    {closeY : Qpos Q -> Y -> Y -> Type} (f : X -> Y)
    (g : forall e u v, closeX e u v -> closeY e (f u) (f v))
    (x : CauchyApproximation closeX)
    : CauchyApproximation closeY
    := {| approximation := f o x;
          iscauchyapproximation_approximation
            := fun d e => g _ _ _ (iscauchyapproximation_approximation closeX x d e) |}.

  (** ** Cauchy structures *)

  (** A Cauchy structure is a type with a premetric, a map [rat] from the rationals, a map [lim] from Cauchy approximations, a map [eq] identifying points which are [e]-close for every [e], and four laws relating closeness to [rat] and [lim]. *)
  Record CauchyStructure := {
    cs_type :> Type;
    cs_close : Qpos Q -> cs_type -> cs_type -> Type;
    cs_ispremetric : IsPremetric Q cs_close;
    cs_rat : Q -> cs_type;
    cs_lim : CauchyApproximation cs_close -> cs_type;
    cs_eq : forall u v : cs_type, (forall e, cs_close e u v) -> u = v;
    cs_close_rat_rat : forall (q r : Q) (e : Qpos Q),
      - ' e < q - r < ' e -> cs_close e (cs_rat q) (cs_rat r);
    cs_close_rat_lim : forall (q : Q) (y : CauchyApproximation cs_close) (e d : Qpos Q),
      cs_close e (cs_rat q) (y d) -> cs_close (e + d) (cs_rat q) (cs_lim y);
    cs_close_lim_rat : forall (x : CauchyApproximation cs_close) (r : Q) (e d : Qpos Q),
      cs_close e (x d) (cs_rat r) -> cs_close (e + d) (cs_lim x) (cs_rat r);
    cs_close_lim_lim : forall (x y : CauchyApproximation cs_close) (e d n : Qpos Q),
      cs_close e (x d) (y n) -> cs_close (e + d + n) (cs_lim x) (cs_lim y)
  }.

  #[export] Existing Instance cs_ispremetric.

  (** A morphism of Cauchy structures is a map [f] which preserves closeness, [rat], [lim] and [eq]. *)
  Record CauchyStructureHom (R S : CauchyStructure) := {
    cshom_fun :> R -> S;
    cshom_close : forall e u v, cs_close R e u v -> cs_close S e (cshom_fun u) (cshom_fun v);
    cshom_rat : forall q, cshom_fun (cs_rat R q) = cs_rat S q;
    cshom_lim : forall x, cshom_fun (cs_lim R x)
                          = cs_lim S (map_cauchy_approximation cshom_fun cshom_close x);
    cshom_eq : forall u v (p : forall e, cs_close R e u v),
      ap cshom_fun (cs_eq R u v p) = cs_eq S _ _ (fun e => cshom_close e u v (p e))
  }.

  Arguments cshom_close {R S} f e u v c : rename.
  Arguments cshom_rat {R S} f q : rename.
  Arguments cshom_lim {R S} f x : rename.
  Arguments cshom_eq {R S} f u v p : rename.

  Section path_cshom.
    Context (R S : CauchyStructure) `{!IsHSet S}.

    Definition issig_cauchystructurehom : _ <~> CauchyStructureHom R S := ltac:(issig).

    (** Into a set, a morphism is determined by its underlying map, since the other components are propositions. *)
    Lemma path_cauchystructurehom `{Funext} (f g : CauchyStructureHom R S) (p : f == g)
      : f = g.
    Proof.
      apply (equiv_ap' issig_cauchystructurehom^-1 _ _).
      apply path_sigma_hprop; funext u; exact (p u).
    Defined.

    (** Hence the type of morphisms into a set is contractible exactly when there is a morphism and any two morphisms are pointwise equal. *)
    Definition contr_cauchystructurehom_iff `{Funext}
      : Contr (CauchyStructureHom R S)
        <-> CauchyStructureHom R S * (forall f g : CauchyStructureHom R S, f == g).
    Proof.
      split.
      - intros c; split; [exact (center _)|].
        intros f g; exact (ap10 (ap (cshom_fun R S) (path_contr f g))).
      - intros [f h]; apply (Build_Contr _ f); intro g.
        exact (path_cauchystructurehom f g (h f g)).
    Defined.
  End path_cshom.

  Definition cshom_idmap (R : CauchyStructure) : CauchyStructureHom R R.
  Proof.
    snapply Build_CauchyStructureHom.
    - exact idmap.
    - exact (fun e u v c => c).
    - intro q; reflexivity.
    - intro x; reflexivity.
    - intros u v p; apply ap_idmap.
  Defined.

  Definition cshom_compose {R S T : CauchyStructure}
    (g : CauchyStructureHom S T) (f : CauchyStructureHom R S)
    : CauchyStructureHom R T.
  Proof.
    snapply Build_CauchyStructureHom.
    - exact (g o f).
    - exact (fun e u v c => cshom_close g e _ _ (cshom_close f e u v c)).
    - intro q; exact (ap g (cshom_rat f q) @ cshom_rat g q).
    - intro x; exact (ap g (cshom_lim f x) @ cshom_lim g _).
    - intros u v p.
      lhs napply (ap_compose f g).
      exact (ap (ap g) (cshom_eq f u v p) @ cshom_eq g _ _ _).
  Defined.

  (** ** Comparing limits *)

  Section compare_limits.
    Context {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q} (S : CauchyStructure).


    Local Lemma qpos_split4 (e0 d : Qpos Q)
      : e0 + d = d / 2 / 2 + (e0 + d / 2 / 2) + d / 2 / 2 + d / 2 / 2.
    Proof.
      set (h := d / 2 / 2).
      rewrite (qpos_plus_comm h (e0 + h)), <- (Qpos_plus_assoc e0 h h).
      rewrite <- 2 (Qpos_plus_assoc e0).
      apply ap; rewrite <- (Qpos_plus_assoc (h + h) h h); unfold h.
      rewrite <- (pos_split2 (d / 2)); exact (pos_split2 d).
    Qed.

    (** Two Cauchy approximations whose terms are close up to [e0] and their indices have limits which are close up to [e0] and any positive rational. *)
    Lemma cs_close_lim_lim_split (a b : CauchyApproximation (cs_close S)) (e0 : Qpos Q)
      (c : forall d n, cs_close S (d + (e0 + n)) (a d) (b n)) (d : Qpos Q)
      : cs_close S (e0 + d) (cs_lim S a) (cs_lim S b).
    Proof.
      rewrite (qpos_split4 e0 d); apply cs_close_lim_lim, c.
    Qed.

    (** Hence two Cauchy approximations whose terms are close up to any positive rational and their indices have the same limit. *)
    Lemma cs_lim_path (a b : CauchyApproximation (cs_close S))
      (c : forall e d n, cs_close S (d + (e + n)) (a d) (b n))
      : cs_lim S a = cs_lim S b.
    Proof.
      apply cs_eq; intro e; rewrite (pos_split2 e).
      apply cs_close_lim_lim_split, c.
    Qed.
  End compare_limits.

  (** ** The Cauchy structure of a Cauchy complete Archimedean ordered field *)

  Section field.
    Context {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}.
    Context {F : Type} `{OrderedField F} {Farch : ArchimedeanProperty Q F}.
    Let qinc : Cast Q F := rationals_to_field Q F.
    Existing Instance qinc.

    #[export] Instance ispremetric_field_close : IsPremetric Q (field_close Q (F:=F)).
    Proof.
      intros e u v; unfold field_close; exact _.
    Defined.

    (** Closeness is reflexive. *)
    Lemma field_close_refl (e : Qpos Q) (u : F) : field_close Q e u u.
    Proof.
      unfold field_close; rewrite plus_negate_r; split.
      - apply flip_pos_negate, (pos_rationals_to_field_qpos Q).
      - apply (pos_rationals_to_field_qpos Q).
    Qed.

    (** An element of [F] below [b + e] for every positive rational [e] is at most [b]. *)
    Lemma le_lt_plus_qpos (a b : F) (lt : forall e : Qpos Q, a < b + ' (' e)) : a ≤ b.
    Proof.
      apply flip_nonpos_minus, (nonpos_lt_qpos Q); intro e.
      apply flip_lt_minus_l; rewrite plus_comm; exact (lt e).
    Qed.

    (** A limit [u] of [x] is [d]-close to [x d] in the weak sense [|x d - u| ≤ d]. *)
    Lemma isapproximationlimit_le (x : Qpos Q -> F) (u : F)
      (islim : IsApproximationLimit (field_close Q) x u) (d : Qpos Q)
      : - ' (' d) ≤ x d - u ≤ ' (' d).
    Proof.
      split.
      - rewrite <- (negate_involutive (x d - u)).
        apply (snd (flip_le_negate (- (x d - u)) (' (' d)))).
        apply le_lt_plus_qpos; intro e.
        apply flip_lt_negate_l.
        rewrite <- (preserves_plus (f:=cast Q F)).
        exact (fst (islim d e)).
      - apply le_lt_plus_qpos; intro e.
        rewrite <- (preserves_plus (f:=cast Q F)).
        exact (snd (islim d e)).
    Qed.

    (** Triangle inequalities mixing closeness with the weak closeness above. *)
    Lemma field_close_le_triangle (e d : Qpos Q) (u v w : F)
      (c : field_close Q e u v) (c' : - ' (' d) ≤ v - w ≤ ' (' d))
      : field_close Q (e + d) u w.
    Proof.
      unfold field_close.
      change (' (' (e + d))) with (' (' e + ' d) : F).
      rewrite (preserves_plus (f:=cast Q F)), <- (plus_minus_telescope u v w).
      exact (lt_le_bound_plus _ _ _ _ c c').
    Qed.

    Lemma le_field_close_triangle (e d : Qpos Q) (u v w : F)
      (c : - ' (' d) ≤ u - v ≤ ' (' d)) (c' : field_close Q e v w)
      : field_close Q (d + e) u w.
    Proof.
      unfold field_close.
      change (' (' (d + e))) with (' (' d + ' e) : F).
      rewrite (preserves_plus (f:=cast Q F)), <- (plus_minus_telescope u v w).
      exact (le_lt_bound_plus _ _ _ _ c c').
    Qed.

    Context `{!RoundUpStrict Q}.

    Local Notation nQ := (naturals_to_semiring nat Q).

    (** The positive rationals [1 / (n + 1)]. *)
    Local Definition recip_succ (n : nat) : Qpos Q := / (' (S n)).

    (** An index beyond which [1 / (n + 1) < e]. *)
    Local Definition recip_succ_index (e : Qpos Q) : nat := (round_up_strict Q (/ ' e)).1.

    Local Lemma recip_succ_lt (e : Qpos Q) (n : nat) (len : (recip_succ_index e <= n)%nat)
      : ' (recip_succ n) < ' e.
    Proof.
      change (/ nQ (S n) < ' e).
      rewrite <- (dec_recip_involutive (' e)).
      apply flip_lt_dec_recip.
      - apply pos_dec_recip_compat, pos_is_pos.
      - refine (lt_le_trans _ _ _ (round_up_strict Q (/ ' e)).2 _).
        exact (nat_to_semiring_le _ _ (leq_succ_r len)).
    Qed.

    (** A Cauchy approximation gives a sequence with a modulus of Cauchy convergence. *)
    Local Lemma cauchymodulus_approximation (x : CauchyApproximation (field_close Q (F:=F)))
      : CauchyModulus Q F (x o recip_succ) (recip_succ_index o (fun e => e / 2)).
    Proof.
      intros e m n lem len.
      apply (field_close_weaken Q (recip_succ m + recip_succ n)).
      - rewrite (pos_split2 e).
        exact (plus_lt_compat _ _ _ _ (recip_succ_lt _ m lem) (recip_succ_lt _ n len)).
      - exact (iscauchyapproximation_approximation _ x _ _).
    Qed.

    Context `{!IsComplete Q F}.

    (** The limit of a Cauchy approximation, computed as the limit of the sequence [x (1 / (n + 1))]. *)
    Definition field_lim (x : CauchyApproximation (field_close Q (F:=F))) : F
      := (is_complete Q F _ _ (cauchymodulus_approximation x)).1.

    Lemma isapproximationlimit_field_lim (x : CauchyApproximation (field_close Q (F:=F)))
      : IsApproximationLimit (field_close Q) x (field_lim x).
    Proof.
      intros e d.
      assert (c := (is_complete Q F _ _ (cauchymodulus_approximation x)).2 (d / 2)).
      strip_truncations; destruct c as [N close].
      set (n := Nat.Core.nat_max N (recip_succ_index (d / 2))).
      apply (field_close_weaken Q (e + recip_succ n + d / 2)).
      - change (' e + ' (recip_succ n) + ' (d / 2) < ' e + ' d).
        assert (p : ' d = ' (d / 2) + ' (d / 2))
          by exact (ap (cast (Qpos Q) Q) (pos_split2 d)).
        rewrite p.
        change (' e + ' (recip_succ n) + ' (d / 2) < ' e + (' (d / 2) + ' (d / 2))).
        rewrite plus_assoc.
        apply (strictly_order_preserving (+ ' (d / 2))), (strictly_order_preserving (' e +)).
        exact (recip_succ_lt _ n (le_nat_max_r _ _)).
      - apply (field_close_triangle Q _ _ _ (x (recip_succ n))).
        + exact (iscauchyapproximation_approximation _ x _ _).
        + apply field_close_symmetric; exact (close n (le_nat_max_l _ _)).
    Qed.

    (** In the other direction, [|field_lim x - x d| ≤ d]. *)
    Local Lemma field_lim_minus_le (x : CauchyApproximation (field_close Q (F:=F))) (d : Qpos Q)
      : - ' (' d) ≤ field_lim x - x d ≤ ' (' d).
    Proof.
      rewrite (negate_swap_r (field_lim x) (x d)).
      exact (le_bound_negate _ _
               (isapproximationlimit_le x _ (isapproximationlimit_field_lim x) d)).
    Qed.

    #[export] Instance cauchycomplete_field : CauchyComplete (field_close Q (F:=F))
      := {| approximation_limit := field_lim;
            isapproximationlimit_approximation_limit := isapproximationlimit_field_lim |}.

    (** A Cauchy complete Archimedean ordered field has a canonical Cauchy structure. *)
    Definition cauchy_structure_field : CauchyStructure.
    Proof.
      rapply (Build_CauchyStructure F (field_close Q) _ (cast Q F) field_lim).
      - exact (field_close_eq Q).
      - intros q r e; exact (field_close_rationals Q e q r).
      - intros q y e d c.
        exact (field_close_le_triangle e d _ _ _ c
                 (isapproximationlimit_le y _ (isapproximationlimit_field_lim y) d)).
      - intros x r e d c.
        rewrite (qpos_plus_comm e d).
        exact (le_field_close_triangle e d _ (x d) _ (field_lim_minus_le x d) c).
      - intros x y e d n c.
        rewrite (qpos_plus_comm e d).
        apply (field_close_le_triangle (d + e) n _ (y n)).
        + exact (le_field_close_triangle e d _ (x d) _ (field_lim_minus_le x d) c).
        + exact (isapproximationlimit_le y _ (isapproximationlimit_field_lim y) n).
    Defined.


    (** The constant Cauchy approximation, whose limit is its value. *)
    Definition const_approximation (y : F) : CauchyApproximation (field_close Q (F:=F))
      := Build_CauchyApproximation _ (fun _ => y) (fun d e => field_close_refl _ y).

    Lemma field_lim_const (y : F) : field_lim (const_approximation y) = y.
    Proof.
      apply (field_close_eq Q); intro e; rewrite (pos_split2 e).
      exact (field_close_symmetric Q _ _ _
               (isapproximationlimit_field_lim (const_approximation y) (e / 2) (e / 2))).
    Qed.

    (** Terms of Cauchy approximations whose limits are [e]-close are close up to [e] and their indices. *)
    Lemma field_close_lim_lim (x y : CauchyApproximation (field_close Q (F:=F))) (e : Qpos Q)
      (c : field_close Q e (field_lim x) (field_lim y)) (d n : Qpos Q)
      : field_close Q (d + (e + n)) (x d) (y n).
    Proof.
      apply (le_field_close_triangle (e + n) d _ (field_lim x)).
      1: exact (isapproximationlimit_le x _ (isapproximationlimit_field_lim x) d).
      apply (field_close_le_triangle e n _ (field_lim y)); [exact c|].
      rewrite (negate_swap_r (field_lim y) (y n)).
      exact (le_bound_negate _ _ (isapproximationlimit_le y _ (isapproximationlimit_field_lim y) n)).
    Qed.

  End field.

End cauchy_structure.
