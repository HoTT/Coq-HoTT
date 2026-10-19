(** * The HoTT book reals *)

From HoTT Require Import Basics Types.Sigma Types.Forall Truncations.Core.
From HoTT.Universes Require Import HSet.
From HoTT.Cubical Require Import DPath.
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
From HoTT_Contrib.Analysis Require Import MetricSpace CauchyCompleteness CauchyStructure.

(** The Cauchy reals of the HoTT book (Section 11.3) are a higher inductive-inductive type, which cannot be defined in Rocq. We characterize them instead by a universal property: they are a homotopy-initial Cauchy structure, that is, a Cauchy structure [R] with a contractible type of morphisms [R -> S] to every Cauchy structure [S]. A development that wants to use the HoTT book reals takes a Cauchy structure [R] together with an instance of [IsHoTTBookReals R] as a hypothesis; nothing is postulated globally.

    Design choices:

    - We take initiality as primitive, rather than the induction principle. Initiality is a single hypothesis, phrased with the existing records [CauchyStructure] and [CauchyStructureHom], and it is what the comparison of the HoTT book reals with other reals uses. We derive the dependent induction principle from it, with its computation rules for [rat] and [lim], by Sojakova's argument: initiality gives a morphism into the Cauchy structure on a total space, whose first component is the identity, again by initiality. The other direction, initiality from induction, would need a characterization of the paths between morphisms, which we never need.

    - [CauchyStructure] is not cumulative, so [IsHoTTBookReals R] quantifies over Cauchy structures at the same universe levels as [R]. This suffices for the uses below: the total space of a family [A : R -> Type] of types in the universe of the carrier of [R], and any Cauchy complete Archimedean ordered field in that universe, such as the Dedekind reals, if the carrier of [R] is large enough. A higher inductive-inductive type would be initial with respect to every universe; the hypothesis states this for one universe at a time.

    - We do not assume that [R] is a set: it follows from initiality, since closeness is reflexive. The premetric [B] over closeness in the induction principle is valued in propositions, so that the total space is again a premetric space.

    - What the HoTT book proves with the full higher inductive-inductive type, namely Cauchy completeness and the fact that [R] embeds into every Cauchy complete Archimedean ordered field (HoTT book, Section 11.3.2 and Theorem 11.3.50), follows here from initiality alone, given one Cauchy complete Archimedean ordered field [F] in the universe of the carrier of [R]: by induction, the canonical morphism [R -> F] reflects closeness. Everything else then follows from properties of [F]. *)

Section hottbook_reals.
  Universe UQ.
  Context (Q : Type@{UQ}) {Qap : Apart Q} {Qplus : Plus Q} {Qmult : Mult Q}
    {Qzero : Zero Q} {Qone : One Q} {Qneg : Negate Q} {Qrecip : DecRecip Q}
    {Qle : Le Q} {Qlt : Lt@{UQ UQ} Q} {QtoField : RationalsToField Q}
    {Qrats : Rationals Q}.

  (** ** Homotopy-initial Cauchy structures *)

  (** The HoTT book reals: a Cauchy structure with a contractible type of morphisms to every Cauchy structure. *)
  Class IsHoTTBookReals (R : CauchyStructure Q)
    := contr_cshom_hottbookreals ::
         forall S : CauchyStructure Q, Contr (CauchyStructureHom Q R S).

  (** ** Dependent Cauchy approximations *)

  Section dependent.
    Context {X : Type} (close : Qpos Q -> X -> X -> Type) `{!IsPremetric Q close}
      (A : X -> Type)
      (B : forall u v, A u -> A v -> forall e, close e u v -> Type)
      `{forall u v a b e c, IsHProp (B u v a b e c)}.

    (** A family [A] over a premetric space with a premetric [B] over closeness gives a premetric on the total space. *)
    Definition sig_close (e : Qpos Q) (w w' : sig A) : Type
      := {c : close e w.1 w'.1 & B _ _ w.2 w'.2 e c}.

    #[export] Instance ispremetric_sig_close : IsPremetric Q sig_close.
    Proof.
      intros e w w'; unfold sig_close; exact _.
    Defined.

    (** A dependent Cauchy approximation over a Cauchy approximation [x]. *)
    Definition IsDependentCauchyApproximation (x : CauchyApproximation Q close)
      (a : forall e, A (x e))
      := forall d e,
        B _ _ (a d) (a e) (d + e) (iscauchyapproximation_approximation Q close x d e).

    Record DependentCauchyApproximation (x : CauchyApproximation Q close) := {
      dependent_approximation :> forall e, A (x e);
      isdependentcauchyapproximation_dependent_approximation
        : IsDependentCauchyApproximation x dependent_approximation
    }.

    Definition issig_dependentcauchyapproximation (x : CauchyApproximation Q close)
      : _ <~> DependentCauchyApproximation x
      := ltac:(issig).

    Lemma path_dependentcauchyapproximation `{Funext} {x : CauchyApproximation Q close}
      (a b : DependentCauchyApproximation x) (p : forall e, a e = b e)
      : a = b.
    Proof.
      apply (equiv_ap' (issig_dependentcauchyapproximation x)^-1 _ _).
      apply path_sigma_hprop; funext e; exact (p e).
    Defined.

    Definition transport_dependentcauchyapproximation
      {x y : CauchyApproximation Q close} (s : x = y)
      (a : DependentCauchyApproximation x) e
      : transport DependentCauchyApproximation s a e
        = transport A (ap10 (ap (approximation Q close) s) e) (a e).
    Proof.
      destruct s; reflexivity.
    Defined.

    (** Pairing [x] with [a] gives a Cauchy approximation in the total space exactly when [a] is a dependent Cauchy approximation over [x]. *)
    Lemma iscauchyapproximation_sig_iff (x : CauchyApproximation Q close)
      (a : forall e, A (x e))
      : IsCauchyApproximation Q sig_close (fun e => (x e; a e))
        <-> IsDependentCauchyApproximation x a.
    Proof.
      split.
      - intros c d e.
        exact (transport (B _ _ _ _ _) (path_ishprop _ _) (c d e).2).
      - intros c d e; exact (_; c d e).
    Defined.

    (** Conversely, a Cauchy approximation in the total space splits into its components. *)
    Definition approximation_pr1 (y : CauchyApproximation Q sig_close)
      : CauchyApproximation Q close
      := map_cauchy_approximation Q pr1 (fun e u v c => c.1) y.

    Definition approximation_pr2 (y : CauchyApproximation Q sig_close)
      : DependentCauchyApproximation (approximation_pr1 y)
      := Build_DependentCauchyApproximation (approximation_pr1 y) (fun e => (y e).2)
           (fun d e => (iscauchyapproximation_approximation Q _ y d e).2).

  End dependent.

  (** ** Paths between morphisms *)

  (** A path between morphisms of Cauchy structures is compatible with their actions on [rat] and [lim]. *)
  Section cshom_path.
    Context {R S : CauchyStructure Q}.

    Definition cshom_path_rat {f g : CauchyStructureHom Q R S} (p : f = g) (q : Q)
      : ap10 (ap (cshom_fun Q R S) p) (cs_rat Q R q) @ cshom_rat Q R S g q
        = cshom_rat Q R S f q.
    Proof.
      destruct p; apply concat_1p.
    Defined.

    (** The path [f o x = g o x] of Cauchy approximations induced by [p]. *)
    Definition cshom_path_approximation {f g : CauchyStructureHom Q R S} (p : f = g)
      (x : CauchyApproximation Q (cs_close Q R))
      : map_cauchy_approximation Q f (cshom_close Q R S f) x
        = map_cauchy_approximation Q g (cshom_close Q R S g) x
      := ap (fun k : CauchyStructureHom Q R S =>
               map_cauchy_approximation Q k (cshom_close Q R S k) x) p.

    Definition cshom_path_lim {f g : CauchyStructureHom Q R S} (p : f = g)
      (x : CauchyApproximation Q (cs_close Q R))
      : ap10 (ap (cshom_fun Q R S) p) (cs_lim Q R x) @ cshom_lim Q R S g x
        = cshom_lim Q R S f x @ ap (cs_lim Q S) (cshom_path_approximation p x).
    Proof.
      destruct p; exact (concat_1p _ @ (concat_p1 _)^).
    Defined.

    Definition ap10_cshom_path_approximation {f g : CauchyStructureHom Q R S} (p : f = g)
      (x : CauchyApproximation Q (cs_close Q R)) e
      : ap10 (ap (approximation Q _) (cshom_path_approximation p x)) e
        = ap10 (ap (cshom_fun Q R S) p) (x e).
    Proof.
      destruct p; reflexivity.
    Defined.

  End cshom_path.

  (** ** The induction principle *)

  Section induction.
    Context (R : CauchyStructure Q).
    Local Notation close := (cs_close Q R).
    Local Notation rat := (cs_rat Q R).
    Local Notation lim := (cs_lim Q R).

    (** The data of the induction principle: a family [A] with a premetric [B] over closeness, cases for [rat], [lim] and [eq], and the four distance laws. *)
    Context (A : R -> Type)
      (B : forall u v, A u -> A v -> forall e, close e u v -> Type)
      `{forall u v a b e c, IsHProp (B u v a b e c)}.
    Local Notation D := (DependentCauchyApproximation close A B).

    Context (f_rat : forall q, A (rat q))
      (f_lim : forall x, D x -> A (lim x))
      (f_eq : forall u v a b (p : forall e, sig_close close A B e (u; a) (v; b)),
          DPath A (cs_eq Q R u v (fun e => (p e).1)) a b)
      (f_close_rat_rat : forall q r e (h : - ' e < q - r < ' e),
          B _ _ (f_rat q) (f_rat r) e (cs_close_rat_rat Q R q r e h))
      (f_close_rat_lim : forall q y (b : D y) e d (c : close e (rat q) (y d)),
          B _ _ (f_rat q) (b d) e c
          -> B _ _ (f_rat q) (f_lim y b) (e + d) (cs_close_rat_lim Q R q y e d c))
      (f_close_lim_rat : forall x (a : D x) r e d (c : close e (x d) (rat r)),
          B _ _ (a d) (f_rat r) e c
          -> B _ _ (f_lim x a) (f_rat r) (e + d) (cs_close_lim_rat Q R x r e d c))
      (f_close_lim_lim : forall x y (a : D x) (b : D y) e d n (c : close e (x d) (y n)),
          B _ _ (a d) (b n) e c
          -> B _ _ (f_lim x a) (f_lim y b) (e + d + n)
                (cs_close_lim_lim Q R x y e d n c)).

    (** The data give a Cauchy structure on the total space of [A]. *)
    Definition sig_cauchy_structure : CauchyStructure Q.
    Proof.
      snapply (Build_CauchyStructure Q (sig A) (sig_close close A B) _
                 (fun q => (rat q; f_rat q))
                 (fun y => (lim (approximation_pr1 close A B y);
                            f_lim _ (approximation_pr2 close A B y)))).
      1: exact _.
      - intros w w' p.
        exact (path_sigma A w w' _ (f_eq w.1 w'.1 w.2 w'.2 p)).
      - intros q r e h; exact (_; f_close_rat_rat q r e h).
      - intros q y e d c.
        exact (_; f_close_rat_lim q _ (approximation_pr2 close A B y) e d c.1 c.2).
      - intros x r e d c.
        exact (_; f_close_lim_rat _ (approximation_pr2 close A B x) r e d c.1 c.2).
      - intros x y e d n c.
        exact (_; f_close_lim_lim _ _ (approximation_pr2 close A B x)
                    (approximation_pr2 close A B y) e d n c.1 c.2).
    Defined.

    Definition cshom_sig_pr1 : CauchyStructureHom Q sig_cauchy_structure R.
    Proof.
      snapply (Build_CauchyStructureHom Q sig_cauchy_structure R pr1 (fun e u v c => c.1)).
      - intro q; reflexivity.
      - intro y; reflexivity.
      - intros w w' p; apply pr1_path_sigma.
    Defined.

    Context `{!IsHoTTBookReals R}.

    (** By initiality we get a morphism into the total space, and its composite with the first projection is the identity, again by initiality. *)
    Local Definition hottbookreals_sig_hom : CauchyStructureHom Q R sig_cauchy_structure
      := center _.
    Local Notation h := hottbookreals_sig_hom.

    Local Definition hottbookreals_sig_hom_pr1
      : cshom_compose Q cshom_sig_pr1 h = cshom_idmap Q R
      := path_contr _ _.

    Local Definition path_hottbookreals_sig_hom_pr1 (u : R) : (h u).1 = u
      := ap10 (ap (cshom_fun Q R R) hottbookreals_sig_hom_pr1) u.

    Definition hottbookreals_ind (u : R) : A u
      := path_hottbookreals_sig_hom_pr1 u # (h u).2.

    Local Lemma transport_premetric {u u' v v'} (p : u' = u) (p' : v' = v) a b e c c'
      : B u' v' a b e c' -> B u v (p # a) (p' # b) e c.
    Proof.
      destruct p, p'; exact (transport _ (path_ishprop _ _)).
    Defined.

    (** The induction principle also gives the premetric [B] on all close pairs. *)
    Definition hottbookreals_ind_close u v e (c : close e u v)
      : B u v (hottbookreals_ind u) (hottbookreals_ind v) e c
      := transport_premetric (path_hottbookreals_sig_hom_pr1 u)
           (path_hottbookreals_sig_hom_pr1 v) _ _ e c _ (cshom_close Q R _ h e u v c).2.

    Definition hottbookreals_ind_beta_rat (q : Q) : hottbookreals_ind (rat q) = f_rat q.
    Proof.
      unfold hottbookreals_ind.
      assert (p : path_hottbookreals_sig_hom_pr1 (rat q) = pr1_path (cshom_rat Q _ _ h q)).
      { exact ((concat_p1 _)^ @ cshom_path_rat hottbookreals_sig_hom_pr1 q @ concat_p1 _). }
      rewrite p.
      exact (pr2_path (cshom_rat Q _ _ h q)).
    Defined.

    (** The dependent Cauchy approximation [fun e => hottbookreals_ind (x e)] over [x]. *)
    Definition hottbookreals_ind_approximation (x : CauchyApproximation Q close) : D x
      := Build_DependentCauchyApproximation close A B x (fun e => hottbookreals_ind (x e))
           (fun d e => hottbookreals_ind_close _ _ _ _).

    Local Lemma transport_f_lim {y x : CauchyApproximation Q close} (s : y = x) (b : D y)
      : transport A (ap lim s) (f_lim y b) = f_lim x (transport D s b).
    Proof.
      destruct s; reflexivity.
    Defined.

    Definition hottbookreals_ind_beta_lim `{Funext} (x : CauchyApproximation Q close)
      : hottbookreals_ind (lim x) = f_lim x (hottbookreals_ind_approximation x).
    Proof.
      unfold hottbookreals_ind.
      assert (p : path_hottbookreals_sig_hom_pr1 (lim x)
                  = pr1_path (cshom_lim Q _ _ h x)
                    @ ap lim (cshom_path_approximation hottbookreals_sig_hom_pr1 x)).
      { refine ((concat_p1 _)^ @ cshom_path_lim hottbookreals_sig_hom_pr1 x @ _).
        exact (whiskerR (concat_p1 _) _). }
      rewrite p, transport_pp, (pr2_path (cshom_lim Q _ _ h x)).
      lhs napply transport_f_lim.
      apply ap; snapply path_dependentcauchyapproximation; [exact _ | intro e].
      lhs napply transport_dependentcauchyapproximation.
      apply (ap (fun r => transport A r _)).
      exact (ap10_cshom_path_approximation hottbookreals_sig_hom_pr1 x e).
    Defined.

  End induction.

  (** ** Recursion and induction into propositions *)

  Section initiality.
    Context (R : CauchyStructure Q) `{!IsHoTTBookReals R}.
    Local Notation close := (cs_close Q R).
    Local Notation rat := (cs_rat Q R).
    Local Notation lim := (cs_lim Q R).

    (** The unique morphism to a Cauchy structure. *)
    Definition hottbookreals_rec (S : CauchyStructure Q) : CauchyStructureHom Q R S
      := center _.

    Definition hottbookreals_rec_unique {S : CauchyStructure Q}
      (f g : CauchyStructureHom Q R S)
      : f == g
      := ap10 (ap (cshom_fun Q R S) (path_contr f g)).

    (** Induction into a family of propositions only needs cases for [rat] and [lim]. *)
    Definition hottbookreals_ind_hprop (A : R -> Type) `{forall u, IsHProp (A u)}
      (f_rat : forall q, A (rat q))
      (f_lim : forall x : CauchyApproximation Q close, (forall e, A (x e)) -> A (lim x))
      : forall u, A u.
    Proof.
      rapply (hottbookreals_ind R A (fun _ _ _ _ _ _ => Unit) f_rat (fun x a => f_lim x a)).
      1: intros; apply path_ishprop.
      all: intros; exact tt.
    Defined.

    (** Closeness is reflexive, so [R] is a set. *)
    Lemma hottbookreals_close_refl `{Funext} {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}
      (e : Qpos Q) (u : R)
      : close e u u.
    Proof.
      revert u e.
      snapply (hottbookreals_ind_hprop (fun u => forall e, close e u u)).
      1: exact _.
      - intros q e; exact (cs_close_rat_rat Q R q q e (rational_close_refl Q e q)).
      - intros x _ e.
        assert (p : e = e / 2 / 2 + e / 2 / 2 + e / 2 / 2 + e / 2 / 2).
        { rewrite <- (pos_split2 (e / 2)), <- Qpos_plus_assoc, <- (pos_split2 (e / 2)).
          exact (pos_split2 e). }
        rewrite p; apply cs_close_lim_lim, iscauchyapproximation_approximation.
    Qed.

    #[export] Instance ishset_hottbookreals `{Funext} {Qdec : DecidablePaths Q}
      {Qtriv : TrivialApart Q}
      : IsHSet R.
    Proof.
      snapply (ishset_hrel_subpaths (R:=fun u v => forall e, close e u v)).
      - intros u e; apply hottbookreals_close_refl.
      - exact _.
      - exact (cs_eq Q R).
    Defined.

  End initiality.

  (** ** Closeness in an Archimedean ordered field *)

  Section field.
    Context {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q}.
    Context {F : Type} `{OrderedField F} {Farch : ArchimedeanProperty Q F}.
    Let qinc : Cast Q F := rationals_to_field Q F.
    Existing Instance qinc.
    Local Instance orderpreserving_qinc : OrderPreserving (cast Q F)
      := full_pseudo_order_preserving.

    (** Closeness in [F] is rounded. *)
    Lemma field_close_rounded (e : Qpos Q) (u v : F) (c : field_close Q e u v)
      : merely {d : Qpos Q & {d' : Qpos Q & prod (e = d + d') (field_close Q d u v)}}.
    Proof.
      destruct c as [lo hi].
      assert (h1 := archimedean_property Q F _ _ hi).
      assert (h2 := archimedean_property Q F _ _ (flip_lt_negate_l _ _ lo)).
      strip_truncations; destruct h1 as [q1 [l1 l1']], h2 as [q2 [l2 l2']].
      (* A rational [m < e] above both [q1] and [q2]. *)
      assert (hm : {m : Q & (q1 ≤ m) /\ (q2 ≤ m) /\ (m < ' e)}).
      { destruct (le_or_lt q1 q2) as [le|lt].
        - exact (q2; (le, (reflexivity _, strictly_order_reflecting (cast Q F) _ _ l2'))).
        - exact (q1; (reflexivity _,
                      (lt_le _ _ lt, strictly_order_reflecting (cast Q F) _ _ l1'))). }
      destruct hm as [m [le1 [le2 lt]]].
      assert (hi' : u - v < ' m)
        by exact (lt_le_trans _ _ _ l1 (order_preserving (cast Q F) _ _ le1)).
      assert (lo' : - (u - v) < ' m)
        by exact (lt_le_trans _ _ _ l2 (order_preserving (cast Q F) _ _ le2)).
      assert (mpos : 0 < m).
      { destruct (le_or_lt m 0) as [le|gt]; [|exact gt].
        assert (le' : ' m ≤ (0 : F)).
        { rewrite <- (preserves_0 (f:=cast Q F)); exact (order_preserving _ _ _ le). }
        assert (n1 := fst (flip_neg_negate _) (lt_le_trans _ _ _ hi' le')).
        destruct (irreflexivity (<) 0 (transitivity n1 (lt_le_trans _ _ _ lo' le'))). }
      apply tr.
      exists (mkQpos m mpos), (mkQpos (' e - m) (snd (flip_pos_minus _ _) lt)).
      split.
      - apply pos_eq; cbn.
        rewrite (plus_comm m), <- plus_assoc, plus_negate_l, plus_0_r; reflexivity.
      - exact (flip_lt_negate_l _ _ lo', hi').
    Qed.

    Context `{!RoundUpStrict Q} `{!IsComplete Q F}.

    (** If the limit of [y] is [e]-close to [w], then so is some [y d], with room [d] to spare. *)
    Lemma field_lim_close_split (y : CauchyApproximation Q (field_close Q (F:=F))) (w : F)
      (e : Qpos Q) (c : field_close Q e (field_lim Q y) w)
      : merely {d : Qpos Q & {e' : Qpos Q & prod (e = e' + d) (field_close Q e' (y d) w)}}.
    Proof.
      assert (r := field_close_rounded e _ _ c); strip_truncations.
      destruct r as [d0 [d0' [p c']]].
      apply tr; exists (d0' / 2), (d0 + d0' / 2); split.
      - rewrite p, <- Qpos_plus_assoc, <- pos_split2; reflexivity.
      - rewrite (qpos_plus_comm d0).
        exact (le_field_close_triangle Q d0 (d0' / 2) _ _ _
                 (isapproximationlimit_le Q y _ (isapproximationlimit_field_lim Q y) _) c').
    Qed.

  End field.

  (** ** The canonical map into a Cauchy complete Archimedean ordered field *)

  Section to_field.
    Context (R : CauchyStructure Q) `{!IsHoTTBookReals R}.
    Local Notation close := (cs_close Q R).
    Local Notation rat := (cs_rat Q R).
    Local Notation lim := (cs_lim Q R).

    Context {Qdec : DecidablePaths Q} {Qtriv : TrivialApart Q} `{!RoundUpStrict Q}.
    Context {F : Type} `{OrderedField F} {Farch : ArchimedeanProperty Q F}
      `{!IsComplete Q F}.
    Let qinc : Cast Q F := rationals_to_field Q F.
    Existing Instance qinc.

    Definition hottbookreals_to_field
      : CauchyStructureHom Q R (cauchy_structure_field Q (F:=F))
      := hottbookreals_rec R _.

    Local Notation i := hottbookreals_to_field.

    (** The canonical map reflects closeness. *)
    Lemma hottbookreals_to_field_reflects_close `{Funext} (u v : R) (e : Qpos Q)
      : field_close Q e (i u) (i v) -> close e u v.
    Proof.
      revert u v e.
      snapply (hottbookreals_ind_hprop R
                 (fun u => forall v e, field_close Q e (i u) (i v) -> close e u v)).
      1,2: exact _.
      - intro q.
        snapply (hottbookreals_ind_hprop R
                   (fun v => forall e, field_close Q e (i (rat q)) (i v) -> close e (rat q) v)).
        1,2: exact _.
        + intros r e c.
          rewrite 2 (cshom_rat Q _ _ i) in c.
          exact (cs_close_rat_rat Q R q r e (rational_close_field_close Q e q r c)).
        + intros y IHy e c.
          rewrite (cshom_lim Q _ _ i) in c.
          assert (s := field_lim_close_split _ _ e (field_close_symmetric Q _ _ _ c)).
          strip_truncations; destruct s as [d [e' [p c']]].
          rewrite p.
          apply cs_close_rat_lim, IHy, field_close_symmetric, c'.
      - intros x IHx.
        snapply (hottbookreals_ind_hprop R
                   (fun v => forall e, field_close Q e (i (lim x)) (i v) -> close e (lim x) v)).
        1,2: exact _.
        + intros r e c.
          rewrite (cshom_lim Q _ _ i) in c.
          assert (s := field_lim_close_split _ _ e c).
          strip_truncations; destruct s as [d [e' [p c']]].
          rewrite p.
          apply cs_close_lim_rat, IHx, c'.
        + intros y _ e c.
          rewrite 2 (cshom_lim Q _ _ i) in c.
          assert (s := field_lim_close_split _ _ e c).
          strip_truncations; destruct s as [d [e' [p c']]].
          assert (s := field_lim_close_split _ _ e' (field_close_symmetric Q _ _ _ c')).
          strip_truncations; destruct s as [n [e'' [p' c'']]].
          rewrite p, p', <- Qpos_plus_assoc, (qpos_plus_comm n d), Qpos_plus_assoc.
          apply cs_close_lim_lim, IHx, field_close_symmetric, c''.
    Qed.

    (** Hence the canonical map is an embedding. *)
    #[export] Instance isinj_hottbookreals_to_field `{Funext} : IsInjective i.
    Proof.
      intros u v p; apply (cs_eq Q R); intro e.
      apply hottbookreals_to_field_reflects_close.
      rewrite p; exact (cshom_close Q _ _ i e v v (hottbookreals_close_refl R e v)).
    Qed.

    #[export] Instance isembedding_hottbookreals_to_field `{Funext} : IsEmbedding i
      := isembedding_isinj_hset i _.

    (** ** Cauchy completeness *)

    (** [lim x] is a limit of [x]. *)
    Lemma isapproximationlimit_hottbookreals `{Funext} (x : CauchyApproximation Q close)
      : IsApproximationLimit Q close x (lim x).
    Proof.
      intros e d; apply hottbookreals_to_field_reflects_close.
      rewrite (cshom_lim Q _ _ i).
      exact (isapproximationlimit_field_lim Q
               (map_cauchy_approximation Q i (cshom_close Q _ _ i) x) e d).
    Qed.

    Definition cauchycomplete_hottbookreals `{Funext} : CauchyComplete Q close
      := {| approximation_limit := lim;
            isapproximationlimit_approximation_limit := isapproximationlimit_hottbookreals |}.

  End to_field.

End hottbook_reals.
