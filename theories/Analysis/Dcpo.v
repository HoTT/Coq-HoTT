(** * Directed-complete partial orders *)

From HoTT Require Import Basics Types TruncType Truncations.Core Universes.Smallness.
From HoTT.Classes.interfaces Require Import canonical_names orders.

Local Open Scope type_scope.

(** We formalize directed-complete partial orders (dcpos) and two fixed point theorems for them: inflationary endomaps of a dcpo have a common fixed point, which needs no propositional resizing, and, assuming propositional resizing, a monotone endomap of a dcpo with a bottom element has a least fixed point (Pataraia's theorem).

Subsets of a type [A] are maps [A -> HProp]. Universe levels matter here: for a universe [i], a partial order on [A : Type@{i}] with relation in [Type@{i}] is a dcpo at level [i] when every directed subset [D : A -> HProp@{i}] has a join. Without propositional resizing these notions depend on [i], and we keep track of the universe levels throughout. *)

(** ** Upper bounds, joins and directed subsets *)

Section Directed.
  Context {A : Type} {Ale : Le A}.

  Definition IsUpperBound (D : A -> HProp) (w : A) : Type
    := forall x, D x -> x ≤ w.

  (** A join of [D] is a least upper bound. *)
  Definition IsJoin (D : A -> HProp) (w : A) : Type
    := IsUpperBound D w * (forall v, IsUpperBound D v -> w ≤ v).

  Definition IsSemidirected (D : A -> HProp) : Type
    := forall x y, D x -> D y -> hexists (fun z => D z * (x ≤ z) * (y ≤ z)).

  Definition IsDirected (D : A -> HProp) : Type
    := hexists D * IsSemidirected D.

  Context `{Funext}.

  #[export] Instance ishprop_issemidirected (D : A -> HProp)
    : IsHProp (IsSemidirected D)
    := _.

  #[export] Instance ishprop_isdirected (D : A -> HProp)
    : IsHProp (IsDirected D)
    := _.

  Context `{!is_mere_relation A Ale}.

  #[export] Instance ishprop_isupperbound (D : A -> HProp) (w : A)
    : IsHProp (IsUpperBound D w)
    := _.

  #[export] Instance ishprop_isjoin (D : A -> HProp) (w : A)
    : IsHProp (IsJoin D w)
    := _.

  (** In a partial order, a subset has at most one join, so having a join is a property. *)
  Definition path_isjoin `{!AntiSymmetric Ale} (D : A -> HProp) (w w' : A)
    (j : IsJoin D w) (j' : IsJoin D w')
    : w = w'
    := antisymmetry Ale _ _ (snd j w' (fst j')) (snd j' w (fst j)).

  #[export] Instance ishprop_join `{!AntiSymmetric Ale} (D : A -> HProp)
    : IsHProp {w : A & IsJoin D w}.
  Proof.
    apply hprop_allpath.
    intros [w j] [w' j'].
    apply path_sigma_hprop.
    exact (path_isjoin D w w' j j').
  Defined.

End Directed.

(** ** Dcpos *)

(** A partial order on [A : Type@{i}] is a dcpo if every directed subset [A -> HProp@{i}] has a join. Since joins in a partial order are unique, the joins are given as structure. *)
Class IsDcpo@{i} {A : Type@{i}} (Ale : Le@{i i} A) := {
  isdcpo_partialorder :: PartialOrder Ale ;
  dcpo_join : forall D : A -> TruncType@{i} (-1), IsDirected D -> {w : A & IsJoin D w}
}.

Arguments dcpo_join {A Ale _} D _.

Section DcpoJoin.
  Context {A : Type} {Ale : Le A} `{!IsDcpo Ale}.

  (** The join of a directed subset. *)
  Definition dcpo_sup (D : A -> HProp) (dirD : IsDirected D) : A
    := (dcpo_join D dirD).1.

  Definition dcpo_sup_upper (D : A -> HProp) (dirD : IsDirected D)
    : IsUpperBound D (dcpo_sup D dirD)
    := fst (dcpo_join D dirD).2.

  Definition dcpo_sup_least (D : A -> HProp) (dirD : IsDirected D)
    : forall v, IsUpperBound D v -> dcpo_sup D dirD ≤ v
    := snd (dcpo_join D dirD).2.

  (** A subdcpo is a subset that contains the joins of the directed subsets it contains. *)
  Class IsSubdcpo (B : A -> HProp) :=
    issubdcpo : forall (D : A -> HProp) (dirD : IsDirected D),
      (forall x, D x -> B x) -> B (dcpo_sup D dirD).

End DcpoJoin.

Arguments IsSubdcpo {A} Ale {_} B.

(** ** The dcpo of elements of a subdcpo *)

(** The order on [A] restricts to the elements of a subtype of [A]. *)
Definition le_sig {A : Type} {Ale : Le A} (B : A -> Type) : Le (sig B)
  := fun u v => u.1 ≤ v.1.

Section Subdcpo.
  Context {A : Type} {Ale : Le A} `{!IsDcpo Ale} (B : A -> HProp) `{!IsSubdcpo Ale B}.

  Local Existing Instance le_sig.

  #[export] Instance partialorder_sig : PartialOrder (le_sig B).
  Proof.
    split.
    - exact _.
    - intros u v; unfold le, le_sig; exact _.
    - split.
      + intros u; unfold le, le_sig; reflexivity.
      + intros u v w; unfold le, le_sig; apply transitivity.
    - intros u v p q.
      apply path_sigma_hprop.
      exact (antisymmetry Ale _ _ p q).
  Defined.

  (** A directed subset of the elements of [B] gives a directed subset of [A]. *)
  Definition subset_pr1 (D : sig B -> HProp) : A -> HProp
    := fun x => Build_HProp {b : B x & D (x; b)}.

  Definition isdirected_subset_pr1 (D : sig B -> HProp) (dirD : IsDirected D)
    : IsDirected (subset_pr1 D).
  Proof.
    destruct dirD as [inhD semiD].
    split.
    - strip_truncations.
      destruct inhD as [u Du].
      exact (tr (u.1; (u.2; Du))).
    - intros x y [bx Dx] [by' Dy].
      specialize (semiD (x; bx) (y; by') Dx Dy).
      strip_truncations.
      destruct semiD as [z [[Dz xz] yz]].
      exact (tr (z.1; ((z.2; Dz), xz, yz))).
  Defined.

  #[export] Instance isdcpo_sig : IsDcpo (le_sig B).
  Proof.
    split.
    1: exact _.
    intros D dirD.
    pose (dirD' := isdirected_subset_pr1 D dirD).
    exists (dcpo_sup _ dirD'; issubdcpo _ dirD' (fun x Dx => Dx.1)).
    split.
    - intros u Du.
      exact (dcpo_sup_upper _ dirD' u.1 (u.2; Du)).
    - intros v ubv.
      apply dcpo_sup_least.
      intros x [bx Dx].
      exact (ubv (x; bx) Dx).
  Defined.

End Subdcpo.
(** ** Function spaces *)

Section Pointwise.
  Context `{Funext} {A B : Type} (Ble : Le B).

  #[export] Instance partialorder_pointwise `{!PartialOrder Ble}
    : PartialOrder (relation_pointwise (fun _ : A => Ble)).
  Proof.
    split.
    - exact _.
    - intros f g; unfold relation_pointwise; exact _.
    - split.
      + intros f x; exact (reflexivity (R:=Ble) _).
      + intros f g h p q x; exact (transitivity (R:=Ble) (p x) (q x)).
    - intros f g p q.
      apply path_forall; intro x.
      exact (antisymmetry Ble _ _ (p x) (q x)).
  Defined.

  (** The values at [x] of the elements of a subset of [A -> B]. *)
  Definition subset_ev (D : (A -> B) -> HProp) (x : A) : B -> HProp
    := fun y => hexists (fun f => D f * (f x = y)).

  Definition isdirected_subset_ev (D : (A -> B) -> HProp)
    (dirD : IsDirected (Ale:=relation_pointwise (fun _ => Ble)) D) (x : A)
    : IsDirected (subset_ev D x).
  Proof.
    destruct dirD as [inhD semiD].
    split.
    - strip_truncations.
      destruct inhD as [f Df].
      exact (tr (f x; tr (f; (Df, idpath)))).
    - intros y z Dy Dz.
      strip_truncations.
      destruct Dy as [f [Df []]], Dz as [g [Dg []]].
      specialize (semiD f g Df Dg).
      strip_truncations.
      destruct semiD as [h [[Dh fh] gh]].
      exact (tr (h x; (tr (h; (Dh, idpath)), fh x, gh x))).
  Defined.

  (** Joins in [A -> B] are computed pointwise. *)
  #[export] Instance isdcpo_pointwise `{!IsDcpo Ble}
    : IsDcpo (relation_pointwise (fun _ : A => Ble)).
  Proof.
    split.
    1: exact _.
    intros D dirD.
    exists (fun x => dcpo_sup _ (isdirected_subset_ev D dirD x)).
    split.
    - intros f Df x.
      apply dcpo_sup_upper.
      exact (tr (f; (Df, idpath))).
    - intros g ubg x.
      apply dcpo_sup_least.
      intros y Dy.
      strip_truncations.
      destruct Dy as [f [Df []]].
      exact (ubg f Df x).
  Defined.

  Definition isjoin_dcpo_sup_pointwise `{!IsDcpo Ble} (D : (A -> B) -> HProp)
    (dirD : IsDirected D) (x : A)
    : IsJoin (subset_ev D x) (dcpo_sup D dirD x)
    := (dcpo_join _ (isdirected_subset_ev D dirD x)).2.

End Pointwise.

Hint Extern 2 (IsDcpo (relation_pointwise _)) =>
  exact (isdcpo_pointwise _) : typeclass_instances.

(** ** Inflationary endomaps *)

(** An endomap is inflationary if it is monotone and increasing. *)
Class IsInflationary {A : Type} {Ale : Le A} (f : A -> A) := {
  isinflationary_orderpreserving :: OrderPreserving f ;
  increasing : forall x, x ≤ f x
}.

Arguments increasing {A Ale} f {_} x.

Section Inflationary.
  Context {A : Type} `{Le A}.

  Definition issig_isinflationary (f : A -> A)
    : _ <~> IsInflationary f
    := ltac:(issig).

  #[export] Instance ishprop_isinflationary `{Funext} `{!is_mere_relation A le}
    (f : A -> A)
    : IsHProp (IsInflationary f).
  Proof.
    nrefine (istrunc_equiv_istrunc _ (issig_isinflationary f)).
    unfold OrderPreserving; exact _.
  Defined.

  #[export] Instance isinflationary_idmap `{!Reflexive (≤)}
    : IsInflationary (idmap : A -> A).
  Proof.
    split.
    - intros x y; exact idmap.
    - intro x; reflexivity.
  Defined.

  #[export] Instance isinflationary_compose `{!Transitive (≤)}
    (f g : A -> A) `{!IsInflationary f} `{!IsInflationary g}
    : IsInflationary (f o g).
  Proof.
    split.
    - intros x y p.
      by do 2 apply (order_preserving _).
    - intro x.
      transitivity (g x).
      + exact (increasing g x).
      + exact (increasing f (g x)).
  Defined.

End Inflationary.

(** ** Inflationary endomaps have a common fixed point *)

Section InflationaryFixedPoint.
  Context `{Funext} {A : Type} {Ale : Le A} `{!IsDcpo Ale}.

  Local Existing Instance le_sig.

  (** The subset of inflationary endomaps of [A]. *)
  Definition subset_inflationary : (A -> A) -> HProp
    := fun f => Build_HProp (IsInflationary f).

  #[export] Instance issubdcpo_inflationary
    : IsSubdcpo (relation_pointwise (fun _ : A => Ale)) subset_inflationary.
  Proof.
    intros D dirD DI.
    pose proof (isjoin_dcpo_sup_pointwise Ale D dirD) as J.
    split.
    - intros x y p.
      apply (snd (J x)).
      intros z Dz.
      strip_truncations.
      destruct Dz as [f [Df []]].
      pose proof (DI f Df : IsInflationary f).
      transitivity (f y).
      + exact (order_preserving f _ _ p).
      + exact (dcpo_sup_upper _ dirD f Df y).
    - intro x.
      pose proof (fst dirD) as inhD.
      strip_truncations.
      destruct inhD as [f Df].
      transitivity (f x).
      + exact (@increasing _ _ f (DI f Df) x).
      + exact (dcpo_sup_upper _ dirD f Df x).
  Defined.

  (** The inflationary endomaps form a dcpo. *)
  Local Notation Infl := (sig subset_inflationary).
  Local Notation le_infl
    := (le_sig (Ale:=relation_pointwise (fun _ : A => Ale)) subset_inflationary).

  (** All inflationary endomaps, as a subset of the inflationary endomaps. *)
  Local Definition subset_all : Infl -> HProp
    := fun _ => Build_HProp Unit.

  Definition isdirected_inflationary : IsDirected (Ale:=le_infl) subset_all.
  Proof.
    split.
    - exact (tr ((idmap; isinflationary_idmap); tt)).
    - intros [f If] [g Ig] _ _.
      change (IsInflationary f) in If; change (IsInflationary g) in Ig.
      refine (tr ((f o g; isinflationary_compose f g); (tt, _, _))).
      + intro x.
        exact (order_preserving f _ _ (increasing g x)).
      + intro x.
        exact (increasing f (g x)).
  Defined.

  (** The greatest inflationary endomap. *)
  Definition top_inflationary : A -> A
    := (dcpo_sup subset_all isdirected_inflationary).1.

  #[export] Instance isinflationary_top_inflationary
    : IsInflationary top_inflationary
    := (dcpo_sup subset_all isdirected_inflationary).2.

  Definition top_inflationary_greatest (f : A -> A) {If : IsInflationary f}
    : forall x, f x ≤ top_inflationary x
    := dcpo_sup_upper subset_all isdirected_inflationary (f; If) tt.

  (** Every value of [top_inflationary] is a fixed point of every inflationary endomap. *)
  Definition top_inflationary_fixed_point (f : A -> A) `{!IsInflationary f} (x : A)
    : f (top_inflationary x) = top_inflationary x.
  Proof.
    apply (antisymmetry Ale).
    - exact (top_inflationary_greatest (f o top_inflationary) x).
    - apply increasing; exact _.
  Defined.

End InflationaryFixedPoint.

(** ** Fixed points in subdcpos *)

Section SubdcpoFixedPoint.
  Context `{Funext} {A : Type} {Ale : Le A} `{!IsDcpo Ale}.

  (** If a subdcpo [B] is closed under a monotone map [f], and [f] is increasing on [B], then any element of [B] gives a fixed point of [f] in [B]. This needs no propositional resizing. *)
  Definition fixed_point_subdcpo (f : A -> A) `{!OrderPreserving f}
    (B : A -> HProp) `{!IsSubdcpo Ale B}
    (closed : forall x, B x -> B (f x)) (incr : forall x, B x -> x ≤ f x)
    (b : A) (Bb : B b)
    : {x : A & B x * (f x = x)}.
  Proof.
    pose (g := fun u : sig B => (f u.1; closed u.1 u.2) : sig B).
    assert (Ig : IsInflationary (Ale:=le_sig B) g).
    { split.
      - intros u v p; exact (order_preserving f _ _ p).
      - intro u; exact (incr u.1 u.2). }
    pose (t := top_inflationary (Ale:=le_sig B) (b; Bb)).
    exists t.1.
    split.
    - exact t.2.
    - exact (ap pr1 (top_inflationary_fixed_point g (b; Bb))).
  Defined.

End SubdcpoFixedPoint.

(** ** Joins and meets of propositions *)

(** With propositional resizing, every family of propositions has a join and a meet in [HProp], in any universe. *)
Section HPropLattice.
  Context `{PropResizing}.

  Definition hprop_join {I : Type} (P : I -> HProp) : HProp
    := Build_HProp (smalltype (hexists P)).

  Definition hprop_join_in {I : Type} (P : I -> HProp) (i : I)
    : P i -> hprop_join P
    := fun p => (equiv_smalltype _)^-1 (tr (i; p)).

  Definition hprop_join_rec {I : Type} (P : I -> HProp) (Q : HProp)
    (f : forall i, P i -> Q)
    : hprop_join P -> Q.
  Proof.
    intro p.
    pose proof (equiv_smalltype _ p) as p'.
    strip_truncations.
    exact (f p'.1 p'.2).
  Defined.

  Context `{Funext}.

  Definition hprop_meet {I : Type} (P : I -> HProp) : HProp
    := Build_HProp (smalltype (forall i, P i)).

  Definition hprop_meet_in {I : Type} (P : I -> HProp)
    : (forall i, P i) -> hprop_meet P
    := (equiv_smalltype _)^-1.

  Definition hprop_meet_out {I : Type} (P : I -> HProp) (i : I)
    : hprop_meet P -> P i
    := fun p => equiv_smalltype _ p i.

End HPropLattice.

(** ** The dcpo of propositions *)

(** Propositions are ordered by implication. We allow the relation to land in any universe [j] containing [HProp@{i}], since a dcpo at level [j] needs a relation in [Type@{j}]. *)
Definition le_hprop@{i j | i < j} : Le@{j j} (TruncType@{i} (-1))
  := fun P Q => P -> Q.

#[export] Instance partialorder_hprop `{Univalence} : PartialOrder le_hprop.
Proof.
  split.
  - exact _.
  - intros P Q; unfold le_hprop; exact _.
  - split.
    + intros P; exact idmap.
    + intros P Q R p q; exact (q o p).
  - intros P Q p q.
    exact (path_iff_hprop p q).
Defined.

(** With propositional resizing, [HProp] in a universe [i] is a dcpo at every universe level at which it lives, so in particular at level [i+1]. By [isdcpo_pointwise], the same holds for the subsets [A -> HProp] of a type [A] in universe [i], ordered by inclusion. *)
#[export] Instance isdcpo_hprop `{PropResizing} `{Univalence} : IsDcpo le_hprop.
Proof.
  split.
  1: exact _.
  intros D _.
  exists (hprop_join (fun P : sig D => P.1)).
  split.
  - intros P DP.
    exact (hprop_join_in (fun P : sig D => P.1) (P; DP)).
  - intros Q ubQ.
    exact (hprop_join_rec _ Q (fun P => ubQ P.1 P.2)).
Defined.

(** ** Pataraia's fixed point theorem *)

Section LeastFixedPoint.
  Context `{PropResizing} `{Funext} {A : Type} {Ale : Le A} `{!IsDcpo Ale}
    (bot : A) (isbot : forall x, bot ≤ x) (f : A -> A) `{!OrderPreserving f}.

  (** The subdcpos that contain [bot] and are closed under [f]. *)
  Local Definition IsAdmissible (B : A -> HProp) : Type
    := IsSubdcpo Ale B * B bot * (forall x, B x -> B (f x)).

  (** Their intersection, which needs propositional resizing. *)
  Local Definition least_admissible : A -> HProp
    := fun x => hprop_meet (fun B : {B : A -> HProp & IsAdmissible B} => B.1 x).

  Local Definition least_admissible_subset (B : A -> HProp) (aB : IsAdmissible B)
    (x : A)
    : least_admissible x -> B x
    := hprop_meet_out _ (B; aB).

  Local Definition isadmissible_least_admissible : IsAdmissible least_admissible.
  Proof.
    refine (_, _, _).
    - intros D dirD Dsub.
      apply hprop_meet_in.
      intros [B [[sB botB] fB]].
      apply sB.
      intros x Dx.
      exact (least_admissible_subset B (sB, botB, fB) x (Dsub x Dx)).
    - apply hprop_meet_in.
      intros [B [[sB botB] fB]].
      exact botB.
    - intros x Bx.
      apply hprop_meet_in.
      intros [B aB].
      apply (snd aB).
      exact (least_admissible_subset B aB x Bx).
  Defined.

  (** The elements below a prefixed point of [f] form an admissible subset. *)
  Local Definition isadmissible_below (y : A) (fy : f y ≤ y)
    : IsAdmissible (fun x => Build_HProp (x ≤ y)).
  Proof.
    refine (_, _, _).
    - intros D dirD Dsub.
      exact (dcpo_sup_least D dirD y Dsub).
    - exact (isbot y).
    - intros x xy.
      exact (transitivity (order_preserving f _ _ xy) fy).
  Defined.

  (** The elements below their image under [f] form an admissible subset. *)
  Local Definition isadmissible_increasing
    : IsAdmissible (fun x => Build_HProp (x ≤ f x)).
  Proof.
    refine (_, _, _).
    - intros D dirD Dsub.
      apply dcpo_sup_least.
      intros x Dx.
      transitivity (f x).
      + exact (Dsub x Dx).
      + apply (order_preserving f).
        exact (dcpo_sup_upper D dirD x Dx).
    - exact (isbot (f bot)).
    - intros x xfx.
      exact (order_preserving f _ _ xfx).
  Defined.

  (** Assuming propositional resizing, a monotone endomap of a dcpo with a bottom element has a least prefixed point, which is also its least fixed point. *)
  Definition least_fixed_point
    : {a : A & (f a = a) * (forall y, f y ≤ y -> a ≤ y)}.
  Proof.
    destruct isadmissible_least_admissible as [[sB botB] fB].
    destruct (fixed_point_subdcpo f least_admissible fB
                (least_admissible_subset _ isadmissible_increasing) bot botB)
      as [a [Ba p]].
    exists a.
    split.
    - exact p.
    - intros y fy.
      exact (least_admissible_subset _ (isadmissible_below y fy) a Ba).
  Defined.

End LeastFixedPoint.
