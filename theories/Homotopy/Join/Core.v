Require Import Basics Types.
Require Import Cubical.DPath Cubical.PathSquare.
Require Import Homotopy.NullHomotopy.
Require Import Extensions.
Require Import Colimits.Pushout.
Require Import Truncations.Core Truncations.Connectedness.
Require Import Pointed.Core.
Require Import WildCat.
Require Import Spaces.Nat.Core.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** * Joins *)

(** The join is the pushout of two types under their product. *)
Section Join.

  Definition Join (A : Type@{i}) (B : Type@{j})
    := Pushout@{k i j k} (@fst A B) (@snd A B).

  Definition joinl {A B} : A -> Join A B
    := fun a => @pushl (A*B) A B fst snd a.

  Definition joinr {A B} : B -> Join A B
    := fun b => @pushr (A*B) A B fst snd b.

  Definition jglue {A B} a b : joinl a = joinr b
    := @pglue (A*B) A B fst snd (a , b).

  Definition Join_ind {A B : Type} (P : Join A B -> Type)
    (P_A : forall a, P (joinl a)) (P_B : forall b, P (joinr b))
    (P_g : forall a b, transport P (jglue a b) (P_A a) = (P_B b))
    : forall (x : Join A B), P x.
  Proof.
    apply (Pushout_ind P P_A P_B).
    exact (fun ab => P_g (fst ab) (snd ab)).
  Defined.

  Definition Join_ind_beta_jglue {A B : Type} (P : Join A B -> Type)
    (P_A : forall a, P (joinl a)) (P_B : forall b, P (joinr b))
    (P_g : forall a b, transport P (jglue a b) (P_A a) = (P_B b)) a b
    : apD (Join_ind P P_A P_B P_g) (jglue a b) = P_g a b
    := Pushout_ind_beta_pglue _ _ _ _ _.

  (** A version of [Join_ind] specifically for proving that two functions defined on a [Join] are homotopic. *)
  Definition Join_ind_FlFr {A B P : Type} (f g : Join A B -> P)
    (Hl : forall a, f (joinl a) = g (joinl a))
    (Hr : forall b, f (joinr b) = g (joinr b))
    (Hglue : forall a b, ap f (jglue a b) @ Hr b = Hl a @ ap g (jglue a b))
    : f == g.
  Proof.
    snrapply Join_ind.
    - exact Hl.
    - exact Hr.
    - intros a b.
      nrapply transport_paths_FlFr'.
      apply Hglue.
  Defined.

  Definition Join_ind_Flr {A B : Type} (f : Join A B -> Join A B)
    (Hl : forall a, f (joinl a) = joinl a)
    (Hr : forall b, f (joinr b) = joinr b)
    (Hglue : forall a b, ap f (jglue a b) @ Hr b = Hl a @ jglue a b)
    : forall x, f x = x.
  Proof.
    snrapply (Join_ind_FlFr _ _ Hl Hr).
    intros a b.
    lhs nrapply Hglue.
    apply ap; symmetry.
    apply ap_idmap.
  Defined.

  (** And a version for showing that a composite is homotopic to the identity. *)
  Definition Join_ind_FFlr {A B P : Type} (f : Join A B -> P) (g : P -> Join A B)
    (Hl : forall a, g (f (joinl a)) = joinl a)
    (Hr : forall b, g (f (joinr b)) = joinr b)
    (Hglue : forall a b, ap g (ap f (jglue a b)) @ Hr b = Hl a @ jglue a b)
    : forall x, g (f x) = x.
  Proof.
    snrapply Join_ind.
    - exact Hl.
    - exact Hr.
    - intros a b.
      nrapply transport_paths_FFlr'.
      apply Hglue.
  Defined.

  Definition Join_rec {A B P : Type} (P_A : A -> P) (P_B : B -> P)
    (P_g : forall a b, P_A a = P_B b) : Join A B -> P.
  Proof.
    apply (Pushout_rec P P_A P_B).
    exact (fun ab => P_g (fst ab) (snd ab)).
  Defined.

  Definition Join_rec_beta_jglue {A B P : Type} (P_A : A -> P)
    (P_B : B -> P) (P_g : forall a b, P_A a = P_B b) a b
    : ap (Join_rec P_A P_B P_g) (jglue a b) = P_g a b.
  Proof.
    snrapply Pushout_rec_beta_pglue.
  Defined.

  (** If [A] is ipointed, so is [Join A B]. *)
  Definition pjoin (A : pType) (B : Type) : pType
    := [Join A B, joinl pt].

End Join.

Arguments joinl {A B}%_type_scope _ , [A] B _.
Arguments joinr {A B}%_type_scope _ , A [B] _.

(** * [Join_rec] gives an equivalence of 0-groupoids

  We now prove many things about [Join_rec], for example, that it is an equivalence of 0-groupoids from the [JoinRecData] that we define next.  The framework we use is a bit elaborate, but it parallels the framework used in TriJoin.v, where careful organization is essential. *)

Record JoinRecData {A B P : Type} := {
    jl : A -> P;
    jr : B -> P;
    jg : forall a b, jl a = jr b;
  }.

Arguments JoinRecData : clear implicits.
Arguments Build_JoinRecData {A B P}%_type_scope (jl jr jg)%_function_scope.

(** We use the name [join_rec] for the version of [Join_rec] defined on this data. *)
Definition join_rec {A B P : Type} (f : JoinRecData A B P)
  : Join A B $-> P
  := Join_rec (jl f) (jr f) (jg f).

Definition join_rec_beta_jg {A B P : Type} (f : JoinRecData A B P) (a : A) (b : B)
  : ap (join_rec f) (jglue a b) = jg f a b
  := Join_rec_beta_jglue _ _ _ a b.

(** We're next going to define a map in the other direction.  We do it via showing that [JoinRecData] is a 0-coherent 1-functor to [Type]. We'll later show that it is a 1-functor to 0-groupoids. *)
Definition joinrecdata_fun {A B P Q : Type} (g : P -> Q) (f : JoinRecData A B P)
  : JoinRecData A B Q.
Proof.
  snrapply Build_JoinRecData.
  - exact (g o jl f).
  - exact (g o jr f).
  - exact (fun a b => ap g (jg f a b)).
Defined.

(** The join itself has canonical [JoinRecData]. *)
Definition joinrecdata_join (A B : Type) : JoinRecData A B (Join A B)
  := Build_JoinRecData joinl joinr jglue.

(** Combining these gives a function going in the opposite direction to [join_rec]. *)
Definition join_rec_inv {A B P : Type} (f : Join A B -> P)
  : JoinRecData A B P
  := joinrecdata_fun f (joinrecdata_join A B).

(** Under [Funext], [join_rec] and [join_rec_inv] should be inverse equivalences.  We'll avoid [Funext] and show that they are equivalences of 0-groupoids, where we choose the path structures carefully. *)

(** ** The graph structure on [JoinRecData A B P]

  Under [Funext], this type will be equivalent to the identity type.  But without [Funext], this definition will be more useful. *)

Record JoinRecPath {A B P : Type} {f g : JoinRecData A B P} := {
    hl : forall a, jl f a = jl g a;
    hr : forall b, jr f b = jr g b;
    hg : forall a b, jg f a b @ hr b = hl a @ jg g a b;
  }.

Arguments JoinRecPath {A B P} f g.

(** In the special case where the first two components of [f] and [g] agree definitionally, [hl] and [hr] can be identity paths, and [hg] simplifies slightly. *)
Definition bundle_joinrecpath {A B P : Type} {jl' : A -> P} {jr' : B -> P}
  {f g : forall a b, jl' a = jr' b}
  (h : forall a b, f a b = g a b)
  : JoinRecPath (Build_JoinRecData jl' jr' f) (Build_JoinRecData jl' jr' g).
Proof.
  snrapply Build_JoinRecPath.
  1, 2: reflexivity.
  intros; apply equiv_p1_1q, h.
Defined.

(** A tactic that helps us apply the previous result. *)
Ltac bundle_joinrecpath :=
  hnf;
  match goal with |- JoinRecPath ?F ?G =>
    refine (bundle_joinrecpath (f:=jg F) (g:=jg G) _) end.

(** Using [JoinRecPath], we can restate the beta rule for [join_rec]. This says that [join_rec_inv] is split surjective. *)
Definition join_rec_beta {A B P : Type} (f : JoinRecData A B P)
  : JoinRecPath (join_rec_inv (join_rec f)) f
  := bundle_joinrecpath (join_rec_beta_jg f).

(** [join_rec_inv] is essentially injective, as a map between 0-groupoids. *)
Definition isinj_join_rec_inv {A B P : Type} {f g : Join A B -> P}
  (h : JoinRecPath (join_rec_inv f) (join_rec_inv g))
  : f == g
  := Join_ind_FlFr _ _ (hl h) (hr h) (hg h).

(** ** Lemmas and tactics about intervals and squares

  We now introduce several lemmas and tactics that will dispense with some routine goals. The idea is that a generic interval can be assumed to be trivial on the first vertex, and a generic square can be assumed to be the identity on the domain edge. In order to apply the [paths_ind] and [square_ind] lemmas that make this precise, we need to generalize various terms in the goal. *)

(** This destructs a three component term [f], generalizes each piece evaluated appropriately, and clears all pieces. *)
Ltac generalize_three f a b :=
  let fg := fresh in let fr := fresh in let fl := fresh in
  destruct f as [fl fr fg]; cbn;
  generalize (fg a b); clear fg;
  generalize (fr b); clear fr;
  generalize (fl a); clear fl.

(** For [f : JoinRecData A B P], if we have [a] and [b] and are trying to prove a statement only involving [jl f a], [jr f b] and [jg f a b], we can assume [jr f b] is [jl f a] and that [jg f a b] is reflexivity.  This is just path induction, but it requires generalizing the goal appropriately. *)
Ltac interval_ind f a b :=
  generalize_three f a b;
  intro f; (* We really only wanted two of them generalized here, so we intro one. *)
  apply paths_ind.

(** Similarly, for [h : JoinRecPath f g], if we have [a] and [b] and are trying to prove a goal only involving [h] and [g] evaluated at those points, we can assume that [g] is [f] and that [h] is "reflexivity".  For this, we first define a lemma that is like "path induction on h", and then a tactic that uses it. *)

Definition square_ind {P : Type} (a b : P) (ab : a = b)
  (Q : forall (a' b' : P) (ab' : a' = b') (ha : a = a') (hb : b = b') (k : ab @ hb = ha @ ab'), Type)
  (s : Q a b ab idpath idpath (equiv_p1_1q idpath))
  : forall a' b' ab' ha hb k, Q a' b' ab' ha hb k.
Proof.
  intros.
  destruct ha, hb.
  revert k; equiv_intro (equiv_p1_1q (p:=ab) (q:=ab')) k'; destruct k'.
  destruct ab.
  exact s.
Defined.

(* [g] should be the codomain of [h]. *)
Global Ltac square_ind g h a b :=
  generalize_three h a b;
  generalize_three g a b;
  apply square_ind.

(** ** Use the WildCat library to organize things *)

(** We begin by showing that [JoinRecData A B P] is a 0-groupoid, one piece at a time. *)
Global Instance isgraph_joinrecdata (A B P : Type) : IsGraph (JoinRecData A B P)
  := {| Hom := JoinRecPath |}.

Global Instance is01cat_joinrecdata (A B P : Type) : Is01Cat (JoinRecData A B P).
Proof.
  apply Build_Is01Cat.
  - intro f.
    bundle_joinrecpath.
    reflexivity.
  - intros f1 f2 f3 h2 h1.
    snrapply Build_JoinRecPath; intros; cbn beta.
    + exact (hl h1 a @ hl h2 a).
    + exact (hr h1 b @ hr h2 b).
    + (* Some simple path algebra works as well. *)
      square_ind f3 h2 a b.
      square_ind f2 h1 a b.
      by interval_ind f1 a b.
Defined.

Global Instance is0gpd_joinrecdata (A B P : Type) : Is0Gpd (JoinRecData A B P).
Proof.
  apply Build_Is0Gpd.
  intros f g h.
  snrapply Build_JoinRecPath; intros; cbn beta.
  + exact (hl h a)^.
  + exact (hr h b)^.
  + (* Some simple path algebra works as well. *)
    square_ind g h a b.
    by interval_ind f a b.
Defined.

Definition joinrecdata_0gpd (A B P : Type) : ZeroGpd
  := Build_ZeroGpd (JoinRecData A B P) _ _ _.

(** ** [joinrecdata_0gpd A B] is a 1-functor from [Type] to [ZeroGpd]

  It's a 1-functor that lands in [ZeroGpd], and the morphisms of [ZeroGpd] are 0-functors, so it's easy to get confused about the levels. *)

(** First we need to show that the induced map is a morphism in [ZeroGpd], i.e. that it is a 0-functor. *)
Global Instance is0functor_joinrecdata_fun {A B P Q : Type} (g : P -> Q)
  : Is0Functor (@joinrecdata_fun A B P Q g).
Proof.
  apply Build_Is0Functor.
  intros f1 f2 h.
  snrapply Build_JoinRecPath; intros; cbn.
  - exact (ap g (hl h a)).
  - exact (ap g (hr h b)).
  - square_ind f2 h a b.
    by interval_ind f1 a b.
Defined.

(** [joinrecdata_0gpd A B] is a 0-functor from [Type] to [ZeroGpd] (one level up). *)
Global Instance is0functor_joinrecdata_0gpd (A B : Type) : Is0Functor (joinrecdata_0gpd A B).
Proof.
  apply Build_Is0Functor.
  intros P Q g.
  snrapply Build_Morphism_0Gpd.
  - exact (joinrecdata_fun g).
  - apply is0functor_joinrecdata_fun.
Defined.

(** [joinrecdata_0gpd A B] is a 1-functor from [Type] to [ZeroGpd]. *)
Global Instance is1functor_joinrecdata_0gpd (A B : Type) : Is1Functor (joinrecdata_0gpd A B).
Proof.
  apply Build_Is1Functor.
  (* If [g1 g2 : P -> Q] are homotopic, then the induced maps are homotopic: *)
  - intros P Q g1 g2 h f; cbn in *.
    snrapply Build_JoinRecPath; intros; cbn.
    1, 2: apply h.
    interval_ind f a b; cbn.
    apply concat_1p_p1.
  (* The identity map [P -> P] is sent to a map homotopic to the identity. *)
  - intros P f; cbn.
    bundle_joinrecpath; intros; cbn.
    apply ap_idmap.
  (* It respects composition. *)
  - intros P Q R g1 g2 f; cbn.
    bundle_joinrecpath; intros; cbn.
    apply ap_compose.
Defined.

Definition joinrecdata_0gpd_fun (A B : Type) : Fun11 Type ZeroGpd
  := Build_Fun11 _ _ (joinrecdata_0gpd A B).

(** By the Yoneda lemma, it follows from [JoinRecData] being a 1-functor that given [JoinRecData] in [J], we get a map [(J -> P) $-> (JoinRecData A B P)] of 0-groupoids which is natural in [P]. Below we will specialize to the case where [J] is [Join A B] with the canonical [JoinRecData]. *)
Definition join_nattrans_recdata {A B J : Type} (f : JoinRecData A B J)
  : NatTrans (opyon_0gpd J) (joinrecdata_0gpd_fun A B).
Proof. 
  snrapply Build_NatTrans.
  1: rapply opyoneda_0gpd.
  2: exact _.
  exact f.
Defined.

(** Thus we get a map [(Join A B -> P) $-> (JoinRecData A B P)] of 0-groupoids, natural in [P]. The underlying map is [join_rec_inv A B P]. *)
Definition join_rec_inv_nattrans (A B : Type)
  : NatTrans (opyon_0gpd (Join A B)) (joinrecdata_0gpd_fun A B)
  := join_nattrans_recdata (joinrecdata_join A B).

(** This natural transformation is in fact a natural equivalence of 0-groupoids. *)
Definition join_rec_inv_natequiv (A B : Type)
  : NatEquiv (opyon_0gpd (Join A B)) (joinrecdata_0gpd_fun A B).
Proof.
  snrapply Build_NatEquiv'.
  1: apply join_rec_inv_nattrans.
  intro P.
  apply isequiv_0gpd_issurjinj.
  apply Build_IsSurjInj.
  - intros f; cbn in f.
    exists (join_rec f).
    apply join_rec_beta.
  - exact (@isinj_join_rec_inv A B P).
Defined.

(** It will be handy to name the inverse natural equivalence. *)
Definition join_rec_natequiv (A B : Type)
  := natequiv_inverse (join_rec_inv_natequiv A B).

(** [join_rec_natequiv A B P] is an equivalence of 0-groupoids whose underlying function is definitionally [join_rec]. *)
Local Definition join_rec_natequiv_check (A B P : Type)
  : equiv_fun_0gpd (join_rec_natequiv A B P) = @join_rec A B P
  := idpath.

(** It follows that [join_rec A B P] is a 0-functor. *)
Global Instance is0functor_join_rec (A B P : Type) : Is0Functor (@join_rec A B P).
Proof.
  change (Is0Functor (equiv_fun_0gpd (join_rec_natequiv A B P))).
  exact _.
Defined.

(** And that [join_rec A B] is natural.   The [$==] in the statement is just [==], but we use WildCat notation so that we can invert and compose these with WildCat notation. *)
Definition join_rec_nat (A B : Type) {P Q : Type} (g : P -> Q) (f : JoinRecData A B P)
  : join_rec (joinrecdata_fun g f) $== g o join_rec f.
Proof.
  exact (isnat (join_rec_natequiv A B) g f).
Defined.

(** * Various types of equalities between paths in joins *)

(** Naturality squares for given paths in [A] and [B]. *)
Section JoinNatSq.

  Definition join_natsq {A B : Type} {a a' : A} {b b' : B}
    (p : a = a') (q : b = b')
    : (ap joinl p) @ (jglue a' b') = (jglue a b) @ (ap joinr q).
  Proof.
    destruct p, q.
    apply concat_1p_p1.
  Defined.

  Definition join_natsq_v {A B : Type} {a a' : A} {b b' : B}
    (p : a = a') (q : b = b')
    : PathSquare (ap joinl p) (ap joinr q) (jglue a b) (jglue a' b').
  Proof.
    destruct p, q.
    apply sq_refl_v.
  Defined.

  Definition join_natsq_h {A B : Type} {a a' : A} {b b' : B}
    (p : a = a') (q : b = b')
    : PathSquare (jglue a b) (jglue a' b') (ap joinl p) (ap joinr q).
  Proof.
    destruct p, q.
    apply sq_refl_h.
  Defined.

End JoinNatSq.

(** The triangles that arise when one of the given paths is reflexivity. *)
Section Triangle.

  Context {A B : Type}.

  Definition triangle_h {a a' : A} (b : B) (p : a = a')
    : ap joinl p @ (jglue a' b) = jglue a b.
  Proof.
    destruct p.
    apply concat_1p.
  Defined.

  Definition triangle_h' {a a' : A} (b : B) (p : a = a')
    : jglue a b @ (jglue a' b)^ = ap joinl p.
  Proof.
    destruct p.
    apply concat_pV.
  Defined.

  Definition triangle_v (a : A) {b b' : B} (p : b = b')
    : jglue a b @ ap joinr p = jglue a b'.
  Proof.
    destruct p.
    apply concat_p1.
  Defined.

  Definition triangle_v' (a : A) {b b' : B} (p : b = b')
    : (jglue a b)^ @ jglue a b' = ap joinr p.
  Proof.
    destruct p.
    apply concat_Vp.
  Defined.

  (** For just one of the above, we give a rule for how it behaves on inverse paths. *)
  Definition triangle_v_V (a : A) {b b' : B} (p : b = b')
    : triangle_v a p^ = (1 @@ ap_V joinr p) @ moveR_pV _ _ _ (triangle_v a p)^.
  Proof.
    destruct p; cbn.
    rhs nrapply concat_1p.
    symmetry; apply concat_pV_p.
  Defined.

End Triangle.

(** Diamond lemmas for Join *)
Section Diamond.

  Context {A B : Type}.

  Definition Diamond (a a' : A) (b b' : B)
    := PathSquare (jglue a b) (jglue a' b')^ (jglue a b') (jglue a' b)^.

  Definition diamond_h {a a' : A} (b b' : B) (p : a = a')
    : jglue a b @ (jglue a' b)^ = jglue a b' @ (jglue a' b')^.
  Proof.
    destruct p.
    exact (concat_pV _ @ (concat_pV _)^).
  Defined.

  Definition diamond_h_sq {a a' : A} (b b' : B) (p : a = a')
    : Diamond a a' b b'.
  Proof.
    by apply sq_path, diamond_h.
  Defined.

  Definition diamond_v (a a' : A) {b b' : B} (p : b = b')
    : jglue a b @ (jglue a' b)^ = jglue a b' @ (jglue a' b')^.
  Proof.
    by destruct p.
  Defined.

  Definition diamond_v_sq (a a' : A) {b b' : B} (p : b = b')
    : Diamond a a' b b'.
  Proof.
    by apply sq_path, diamond_v.
  Defined.

  Lemma diamond_symm (a : A) (b : B)
    : diamond_v_sq a a 1 = diamond_h_sq b b 1.
  Proof.
    unfold diamond_v_sq, diamond_h_sq, diamond_v, diamond_h.
    symmetry; apply ap, concat_pV.
  Defined.

End Diamond.

Definition diamond_twist {A : Type} {a a' : A} (p : a = a')
  : DPath (fun x => Diamond a' x a x) p
    (diamond_v_sq a' a 1) (diamond_h_sq a a' 1).
Proof.
  destruct p.
  apply diamond_symm.
Defined.

(** * Functoriality of Join. *)
Section FunctorJoin.

  (** In some cases, we'll need to refer to the recursion data that defines [functor_join], so we make it a separate definition. *)
  Definition functor_join_recdata {A B C D} (f : A -> C) (g : B -> D)
    : JoinRecData A B (Join C D)
    := {| jl := joinl o f; jr := joinr o g; jg := fun a b => jglue (f a) (g b); |}.

  Definition functor_join {A B C D} (f : A -> C) (g : B -> D)
    : Join A B -> Join C D
    := join_rec (functor_join_recdata f g).

  Definition functor_join_beta_jglue {A B C D : Type} (f : A -> C) (g : B -> D)
    (a : A) (b : B)
    : ap (functor_join f g) (jglue a b) = jglue (f a) (g b)
    := join_rec_beta_jg _ a b.

  Definition functor_join_compose {A B C D E F}
    (f : A -> C) (g : B -> D) (h : C -> E) (i : D -> F)
    : functor_join (h o f) (i o g) == functor_join h i o functor_join f g.
  Proof.
    snrapply Join_ind_FlFr.
    1,2: reflexivity.
    intros a b.
    simpl.
    apply equiv_p1_1q.
    lhs nrapply functor_join_beta_jglue; symmetry.
    lhs nrapply (ap_compose (functor_join f g) _ (jglue a b)).
    lhs nrefine (ap _ (functor_join_beta_jglue _ _ _ _)).
    apply functor_join_beta_jglue.
  Defined.

  Definition functor_join_idmap {A B}
    : functor_join idmap idmap == (idmap : Join A B -> Join A B).
  Proof.
    snrapply Join_ind_FlFr.
    1,2: reflexivity.
    intros a b.
    simpl.
    apply equiv_p1_1q.
    lhs nrapply functor_join_beta_jglue.
    symmetry; apply ap_idmap.
  Defined.

  Definition functor2_join {A B C D} {f f' : A -> C} {g g' : B -> D}
    (h : f == f') (k : g == g')
    : functor_join f g == functor_join f' g'.
  Proof.
    srapply Join_ind_FlFr.
    - simpl; intros; apply ap, h.
    - simpl; intros; apply ap, k.
    - intros a b; cbn beta.
      lhs nrapply (functor_join_beta_jglue _ _ _ _ @@ 1).
      symmetry.
      lhs nrapply (1 @@ functor_join_beta_jglue _ _ _ _).
      apply join_natsq.
  Defined.

  Global Instance isequiv_functor_join {A B C D}
    (f : A -> C) `{!IsEquiv f} (g : B -> D) `{!IsEquiv g}
    : IsEquiv (functor_join f g).
  Proof.
    snrapply isequiv_adjointify.
    - apply (functor_join f^-1 g^-1).
    - etransitivity.
      1: symmetry; apply functor_join_compose.
      etransitivity.
      1: exact (functor2_join (eisretr f) (eisretr g)).
      apply functor_join_idmap.
    - etransitivity.
      1: symmetry; apply functor_join_compose.
      etransitivity.
      1: exact (functor2_join (eissect f) (eissect g)).
      apply functor_join_idmap.
  Defined.

  Definition equiv_functor_join {A B C D} (f : A <~> C) (g : B <~> D)
    : Join A B <~> Join C D := Build_Equiv _ _ (functor_join f g) _.

  Global Instance is0bifunctor_join : Is0Bifunctor Join.
  Proof.
    snrapply Build_Is0Bifunctor'.
    1,2: exact _.
    apply Build_Is0Functor.
    intros A B [f g].
    exact (functor_join f g).
  Defined.

  Global Instance is1bifunctor_join : Is1Bifunctor Join.
  Proof.
    snrapply Build_Is1Bifunctor'.
    nrapply Build_Is1Functor.
    - intros A B f g [p q].
      exact (functor2_join p q).
    - intros A; exact functor_join_idmap.
    - intros A B C [f g] [h k].
      exact (functor_join_compose f g h k).
  Defined.

End FunctorJoin.

(** * Symmetry of Join

  We'll use the recursion equivalence above to prove the symmetry of Join, using the Yoneda lemma.  The idea is that [Join A B -> P] is equivalent (as a 0-groupoid) to [JoinRecData A B P], and the latter is very symmetrical by construction, which makes it easy to show that it is equivalent to [JoinRecData B A P].  Going back along the first equivalence gets us to [Join B A -> P].  These equivalences are natural in [P], so the symmetry equivalence follows from the Yoneda lemma.  This is mainly meant as a warmup to proving the associativity of the join. *)

Section JoinSym.

  Definition joinrecdata_sym (A B P : Type)
    : joinrecdata_0gpd A B P $-> joinrecdata_0gpd B A P.
  Proof.
    snrapply Build_Morphism_0Gpd.
    (* The map of types [JoinRecData A B P -> JoinRecData B A P]: *)
    - intros [fl fr fg].
      snrapply (Build_JoinRecData fr fl).
      intros b a; exact (fg a b)^.
    (* It respects the paths. *)
    - apply Build_Is0Functor.
      intros f g h; simpl.
      snrapply Build_JoinRecPath; simpl.
      1, 2: intros; apply h.
      intros b a.
      square_ind g h a b.
      by interval_ind f a b.
  Defined.

  (** This map is its own inverse in the 1-category of 0-groupoids. *)
  Definition joinrecdata_sym_inv (A B P : Type)
    : joinrecdata_sym B A P $o joinrecdata_sym A B P $== Id _.
  Proof.
    intro f; simpl.
    bundle_joinrecpath.
    intros a b; simpl.
    apply inv_V.
  Defined.

  (** We get the symmetry natural equivalence on [TriJoinRecData]. *)
  Definition joinrecdata_sym_natequiv (A B : Type)
    : NatEquiv (joinrecdata_0gpd_fun A B) (joinrecdata_0gpd_fun B A).
  Proof.
    snrapply Build_NatEquiv.
    (* An equivalence of 0-groupoids for each [P]: *)
    - intro P.
      snrapply cate_adjointify.
      1, 2: apply joinrecdata_sym.
      1, 2: apply joinrecdata_sym_inv.
    (* Naturality: *)
    - snrapply Build_Is1Natural.
      intros P Q g f; simpl.
      bundle_joinrecpath.
      intros b a; simpl.
      symmetry; apply ap_V.
  Defined.

  (** Combining with the recursion equivalence [join_rec_inv_natequiv] and its inverse gives the symmetry natural equivalence between the representable functors. *)
  Definition joinrecdata_fun_sym (A B : Type)
    : NatEquiv (opyon_0gpd (Join A B)) (opyon_0gpd (Join B A))
    := natequiv_compose (join_rec_natequiv B A)
        (natequiv_compose (joinrecdata_sym_natequiv A B) (join_rec_inv_natequiv A B)).

  (** The Yoneda lemma for 0-groupoid valued functors therefore gives us an equivalence between the representing objects.  We mark this with a prime, since we'll use a homotopic map with a slightly simpler definition. *)
  Definition equiv_join_sym' (A B : Type)
    : Join A B <~> Join B A.
  Proof.
    rapply (opyon_equiv_0gpd (A:=Type)).
    apply joinrecdata_fun_sym.
  Defined.

  (** It has the nice property that the underlying function of the inverse is again [equiv_join_sym'], with arguments permuted. *)
  Local Definition equiv_join_sym_check1 (A B : Type)
    : (equiv_join_sym' A B)^-1 = equiv_fun (equiv_join_sym' B A)
    := idpath.

  (** The definition we end up with is almost the same as the obvious one, but has an extra [ap idmap] in it. *)
  Local Definition equiv_join_sym_check2 (A B : Type)
    : equiv_fun (equiv_join_sym' A B) = Join_rec (fun a : A => joinr a) (fun b : B => joinl b)
                                          (fun (a : A) (b : B) => (ap idmap (jglue b a))^)
    := idpath.

  (** The next two give the obvious definition. *)
  Definition join_sym_recdata (A B : Type)
    : JoinRecData A B (Join B A)
    := Build_JoinRecData joinr joinl (fun a b => (jglue b a)^).

  Definition join_sym (A B : Type)
    : Join A B -> Join B A
    := join_rec (join_sym_recdata A B).

  Definition join_sym_beta_jglue {A B} (a : A) (b : B)
    : ap (join_sym A B) (jglue a b) = (jglue b a)^
    := Join_rec_beta_jglue _ _ _ _ _.

  (** The obvious definition is homotopic to the definition via the Yoneda lemma. *)
  Definition join_sym_homotopic (A B : Type)
    : join_sym A B == equiv_join_sym' A B.
  Proof.
    symmetry.
    (** Both sides are [join_rec] applied to [JoinRecData]: *)
    rapply (fmap join_rec).
    bundle_joinrecpath; intros; cbn.
    refine (ap inverse _).
    apply ap_idmap.
  Defined.

  (** Therefore the obvious definition is also an equivalence, and the inverse function can also be chosen to be [join_sym]. *)
  Definition equiv_join_sym (A B : Type) : Join A B <~> Join B A
    := equiv_homotopic_inverse (equiv_join_sym' A B)
                              (join_sym_homotopic A B)
                              (join_sym_homotopic B A).

  Global Instance isequiv_join_sym A B : IsEquiv (join_sym A B)
    := equiv_isequiv (equiv_join_sym A B).

  (** It's also straightforward to directly prove that [join_sym] is an equivalence.  The above approach is meant to illustrate the Yoneda lemma.  In the case of [equiv_trijoin_twist], the Yoneda approach seems to be more straightforward. *)
  Definition join_sym_inv A B : join_sym A B o join_sym B A == idmap.
  Proof.
    snrapply (Join_ind_FFlr (join_sym B A)).
    - reflexivity.
    - reflexivity.
    - intros a b; cbn beta.
      apply equiv_p1_1q.
      refine (ap _ (join_rec_beta_jg _ a b) @ _); cbn.
      refine (ap_V _ (jglue b a) @ _).
      refine (ap inverse (join_rec_beta_jg _ b a) @ _).
      apply inv_V.
  Defined.

  (** Finally, one can also prove that the join is symmetric using [pushout_sym] and [equiv_prod_symm], but this results in an equivalence whose inverse isn't of the same form. *)

  (** We give a direct proof that [join_sym] is natural. *)
  Definition join_sym_nat {A B A' B'} (f : A -> A') (g : B -> B')
    : join_sym A' B' o functor_join f g == functor_join g f o join_sym A B.
  Proof.
    snrapply Join_ind_FlFr.
    1, 2: reflexivity.
    intros a b; cbn beta.
    apply equiv_p1_1q.
    lhs nrefine (ap_compose' (functor_join f g) _ (jglue a b)).
    lhs nrefine (ap _ (functor_join_beta_jglue _ _ _ _)).
    lhs nrapply join_sym_beta_jglue.
    symmetry.
    lhs nrefine (ap_compose' (join_sym A B) _ (jglue a b)).
    lhs nrefine (ap _ (join_sym_beta_jglue a b)).
    refine (ap_V _ (jglue b a) @ ap inverse _).
    apply functor_join_beta_jglue.
  Defined.

End JoinSym.

(** * Other miscellaneous results about joins *)

(** Relationship to truncation levels and connectedness. *)
Section JoinTrunc.

  (** Joining with a contractible type produces a contractible type *)
  Global Instance contr_join A B `{Contr A} : Contr (Join A B).
  Proof.
    apply (Build_Contr _ (joinl (center A))).
    snrapply Join_ind.
    - intros a; apply ap, contr.
    - intros b; apply jglue.
    - intros a b; cbn.
      lhs nrapply transport_paths_r.
      apply triangle_h.
  Defined.

  (** The join of hprops is an hprop *)
  Global Instance ishprop_join `{Funext} A B `{IsHProp A} `{IsHProp B} : IsHProp (Join A B).
  Proof.
    apply hprop_inhabited_contr.
    snrapply Join_rec.
    - intros a; apply contr_join.
      exact (contr_inhabited_hprop A a).
    - intros b; refine (contr_equiv (Join B A) (equiv_join_sym B A)).
      apply contr_join.
      exact (contr_inhabited_hprop B b).
    (* The two proofs of contractibility are equal because [Contr] is an [HProp].  This uses [Funext]. *)
    - intros a b; apply path_ishprop.
  Defined.

  Lemma equiv_into_hprop `{Funext} {A B P : Type} `{IsHProp P} (f : A -> P)
    : (Join A B -> P) <~> (B -> P).
  Proof.
    apply equiv_iff_hprop.
    1: exact (fun f => f o joinr).
    intros g.
    snrapply Join_rec.
    1,2: assumption.
    intros a b.
    apply path_ishprop.
  Defined.

  (** And coincides with their disjunction *)
  Definition equiv_join_hor `{Funext} A B `{IsHProp A} `{IsHProp B}
    : Join A B <~> hor A B.
  Proof.
    apply equiv_iff_hprop.
    - exact (Join_rec (fun a => tr (inl a)) (fun b => tr (inr b)) (fun _ _ => path_ishprop _ _)).
    - apply Trunc_rec, push.
  Defined.

  (** Joins add connectivity *)
  Global Instance isconnected_join `{Funext} {m n : trunc_index}
         (A B : Type) `{IsConnected m A} `{IsConnected n B}
    : IsConnected (m +2+ n) (Join A B).
  Proof.
    apply isconnected_from_elim; intros C ? k.
    pose @istrunc_inO_tr.
    pose proof (istrunc_extension_along_conn
                  (fun b:B => tt) (fun _ => C) (k o joinr)).
    unfold ExtensionAlong in *.
    transparent assert (f : (A -> {s : Unit -> C &
                                   forall x, s tt = k (joinr x)})).
    { intros a; exists (fun _ => k (joinl a)); intros b.
      exact (ap k (jglue a b)). }
    assert (h := isconnected_elim
                   m {s : Unit -> C & forall x : B, s tt = k (joinr x)} f).
    unfold NullHomotopy in *; destruct h as [[c g] h].
    exists (c tt).
    snrapply Join_ind.
    - intros a; cbn. exact (ap10 (h a)..1 tt).
    - intros b; cbn. exact ((g b)^).
    - intros a b.
      rewrite transport_paths_FlFr, ap_const, concat_p1; cbn.
      subst f; set (ha := h a); clearbody ha; clear h;
      assert (ha2 := ha..2); set (ha1 := ha..1) in *;
      clearbody ha1; clear ha; cbn in *.
      rewrite <- (inv_V (ap10 ha1 tt)).
      rewrite <- inv_pp.
      apply inverse2.
      refine (_ @ apD10 ha2 b); clear ha2.
      rewrite transport_forall_constant, transport_paths_FlFr.
      rewrite ap_const, concat_p1.
      reflexivity.
  Defined.

End JoinTrunc.

(** Join with Empty *)
Section JoinEmpty.

  Definition equiv_join_empty_right A : Join A Empty <~> A.
  Proof.
    snrapply equiv_adjointify.
    - apply join_rec; snrapply (Build_JoinRecData idmap); contradiction.
    - exact joinl.
    - reflexivity.
    - snrapply Join_ind; [reflexivity| |]; contradiction.
  Defined.

  Definition equiv_join_empty_left A : Join Empty A <~> A
    := equiv_join_empty_right _ oE equiv_join_sym _ _.

  Global Instance join_right_unitor : RightUnitor Join Empty.
  Proof.
    snrapply Build_NatEquiv.
    - apply equiv_join_empty_right.
    - snrapply Build_Is1Natural.
      intros A B f.
      cbn -[equiv_join_empty_right].
      snrapply Join_ind_FlFr.
      + intro a.
        reflexivity.
      + intros [].
      + intros a [].
  Defined.

  Global Instance join_left_unitor : LeftUnitor Join Empty.
  Proof.
    snrapply Build_NatEquiv.
    - apply equiv_join_empty_left.
    - snrapply Build_Is1Natural.
      intros A B f x.
      cbn -[equiv_join_empty_right].
      rhs_V rapply (isnat_natequiv join_right_unitor).
      cbn -[equiv_join_empty_right].
      apply ap, join_sym_nat.
  Defined.

End JoinEmpty.

Arguments equiv_join_empty_right : simpl never.

(** Iterated Join powers of a type. *)
Section JoinPower.

  (** The join of [n.+1] copies of a type. This is convenient because it produces [A] definitionally when [n] is [0]. We annotate the universes to reduce universe variables. *)
  Definition iterated_join (A : Type@{u}) (n : nat) : Type@{u}
    := nat_iter n (Join A) A.

  (** The join of [n] copies of a type. This is sometimes convenient for proofs by induction as it gives a trivial base case. *)
  Definition join_power (A : Type@{u}) (n : nat) : Type@{u}
    := nat_iter n (Join A) (Empty : Type@{u}).

  Definition equiv_join_powers (A : Type) (n : nat) : join_power A n.+1 <~> iterated_join A n.
  Proof.
    induction n as [|n IHn]; simpl.
    - exact (equiv_join_empty_right A).
    - exact (equiv_functor_join equiv_idmap IHn).
  Defined.

End JoinPower.

(** ** Doulbe recursion for Join *)

Section Rec2.
  Context {A B C D : Type} (P : Type)
    (P_AC : A -> C -> P) (P_AD : A -> D -> P) (P_BC : B -> C -> P) (P_BD : B -> D -> P)
    (P_gAx : forall a c d, P_AC a c = P_AD a d)
    (P_gBx : forall b c d, P_BC b c = P_BD b d)
    (P_gxC : forall c a b, P_AC a c = P_BC b c)
    (P_gxD : forall d a b, P_AD a d = P_BD b d)
    (P_g : forall a b c d, P_gAx a c d @ P_gxD d a b = P_gxC c a b @ P_gBx b c d).

  Definition Join_rec2 : Join A B -> Join C D -> P.
  Proof.
    intros x y; revert x.
    snrapply Join_rec.
    1: intros a; exact (Join_rec (P_AC a) (P_AD a) (P_gAx a) y).
    1: intros b; exact (Join_rec (P_BC b) (P_BD b) (P_gBx b) y).
    intros a b.
    revert y.
    snrapply Join_ind_FlFr.
    1: intros c; exact (P_gxC c a b).
    1: intros d; exact (P_gxD d a b).
    intros c d.
    simpl.
    lhs nrapply whiskerR.
    1: apply Join_rec_beta_jglue.
    rhs nrapply whiskerL.
    2: apply Join_rec_beta_jglue.
    exact (P_g a b c d).
  Defined.

End Rec2.
