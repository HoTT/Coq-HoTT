From HoTT Require Import Basics Types Join.Core Join.TriJoin Spaces.Nat.Core.
From HoTT.WildCat Require Import Core Universe Equiv ZeroGroupoid
  Yoneda FunctorCat NatTrans Monoidal.

(** * The associativity of [Join]

  We use the recursion principle for the triple join (from TriJoin.v) to prove the associativity of Join.  We'll use the common technique of combining symmetry and a twist equivalence.  Temporarily writing * for Join, symmetry says that [A * B <~> B * A] and the twist says that [A * (B * C) <~> B * (A * C)].  From these we get a composite equivalence [A * (B * C) <~> A * (C * B) <~> C * (A * B) <~> (A * B) * C].  One advantage of this approach is that both symmetry and the twist are their own inverses, so there are fewer maps to define and fewer composites to prove are homotopic to the identity. Symmetry is proved in Join/Core.v. *)

(** ** The twist equivalence [TriJoin A B C <~> TriJoin B A C]

  We prove the twist equivalence using the Yoneda lemma.  The idea is that [TriJoin A B C -> P] is equivalent (as a 0-groupoid) to [TriJoinRecData A B C P], and the latter is very symmetrical by construction, which makes it easy to show that it is equivalent to [TriJoinRecData B A C P].  Going back along the first equivalence gets us to [TriJoin B A C -> P].  These equivalences are natural in [P], so the twist equivalence follows from the Yoneda lemma. *)

(** First we define a map of 0-groupoids that will underlie the natural equivalence. *)
Definition trijoinrecdata_twist (A B C P : Type)
  : trijoinrecdata_0gpd A B C P $-> trijoinrecdata_0gpd B A C P.
Proof.
  snapply Build_Fun01'.
  (* The map of types [TriJoinRecData A B C P -> TriJoinRecData B A C P]: *)
  - cbn.
    intros [f1 f2 f3 f12 f13 f23 f123].
    snapply (Build_TriJoinRecData f2 f1 f3).
    + intros b a; exact (f12 a b)^.
    + exact f23.
    + exact f13.
    + intros a b c; cbn beta.
      apply moveR_Vp.
      symmetry; apply f123.
  (* It respects the paths. *)
  - intros f g h; cbn in *.
    snapply Build_TriJoinRecPath; intros; simpl.
    1, 2, 3, 5, 6: apply h.
    + cbn zeta.
      prism_ind_two g h b a _X_; cbn beta.
      apply concat_p1_1p.
    + cbn beta zeta.
      prism_ind g h b a c; cbn beta.
      by triangle_ind f b a c.
Defined.

(** This map is its own inverse in the 1-category of 0-groupoids. *)
Definition trijoinrecdata_twist_inv (A B C P : Type)
  : trijoinrecdata_twist B A C P $o trijoinrecdata_twist A B C P $== Id _.
Proof.
  intro f; simpl.
  bundle_trijoinrecpath.
  all: intros; cbn.
  - apply inv_V.
  - reflexivity.
  - reflexivity.
  - by triangle_ind f a b c.
Defined.

(** We get the twist natural equivalence on [TriJoinRecData]. *)
Definition trijoinrecdata_twist_natequiv (A B C : Type)
  : NatEquiv (trijoinrecdata_0gpd_fun A B C) (trijoinrecdata_0gpd_fun B A C).
Proof.
  snapply Build_NatEquiv.
  (* An equivalence of 0-groupoids for each [P]: *)
  - intro P.
    snapply cate_adjointify.
    1, 2: apply trijoinrecdata_twist.
    1, 2: apply trijoinrecdata_twist_inv.
  (* Naturality: *)
  - snapply Build_Is1Natural.
    intros P Q g f; simpl.
    bundle_trijoinrecpath.
    all: intros; cbn.
    + symmetry; apply ap_V.
    + reflexivity.
    + reflexivity.
    + by triangle_ind f b a c.
Defined.

(** Combining with the recursion equivalence [trijoin_rec_inv_natequiv] and its inverse gives the twist natural equivalence between the representable functors. *)
Definition trijoinrecdata_fun_twist (A B C : Type)
  : NatEquiv (opyon_0gpd (TriJoin A B C)) (opyon_0gpd (TriJoin B A C))
  := natequiv_compose (trijoin_rec_natequiv B A C)
      (natequiv_compose (trijoinrecdata_twist_natequiv A B C) (trijoin_rec_inv_natequiv A B C)).

(** The Yoneda lemma for 0-groupoid valued functors therefore gives us an equivalence between the representing objects.  We mark this with a prime, since we'll use a homotopic map with a slightly simpler definition. *)
Definition equiv_trijoin_twist' (A B C : Type)
  : TriJoin A B C <~> TriJoin B A C.
Proof.
  tapply (opyon_equiv_0gpd (A:=Type)).
  apply trijoinrecdata_fun_twist.
Defined.

(** It has the nice property that the underlying function of the inverse is again [equiv_trijoin_twist'], with arguments permuted. *)
Local Definition trijoin_twist_check1 (A B C : Type)
  : (equiv_trijoin_twist' A B C)^-1 = equiv_fun (equiv_trijoin_twist' B A C)
  := idpath.

(** The definition we end up with is almost the same as the obvious one, but has some extra [ap idmap]s in it. *)
Local Definition twijoin_twist_check2 (A B C : Type)
  : equiv_fun (equiv_trijoin_twist' A B C)
    = trijoin_rec {| j1 := join2; j2 := join1; j3 := join3;
      j12 := fun (b : A) (a : B) => (ap idmap (join12 a b))^;
      j13 := fun (b : A) (c : C) => ap idmap (join23 b c);
      j23 := fun (a : B) (c : C) => ap idmap (join13 a c);
      j123 := fun (a : A) (b : B) (c : C) =>
               moveR_Vp _ _ _ (ap_triangle idmap (join123 b a c))^ |}
  := idpath.

(** The next two give the obvious definition. *)
Definition trijoin_twist_recdata (A B C : Type)
  : TriJoinRecData A B C (TriJoin B A C)
  := Build_TriJoinRecData join2 join1 join3
      (fun a b => (join12 b a)^) join23 join13
      (fun a b c => moveR_Vp _ _ _ (join123 b a c)^).

Definition trijoin_twist (A B C : Type)
  : TriJoin A B C -> TriJoin B A C
  := trijoin_rec (trijoin_twist_recdata A B C).

(** As an aside, note that [trijoin_twist] computes nicely on [joinr]. *)
Local Definition trijoin_twist_joinr (A B C : Type)
  : trijoin_twist A B C o joinr = functor_join idmap joinr
  := idpath.

(** The obvious definition is homotopic to the definition via the Yoneda lemma. *)
Definition trijoin_twist_homotopic (A B C : Type)
  : trijoin_twist A B C == equiv_trijoin_twist' A B C.
Proof.
  symmetry.
  (** Both sides are [trijoin_rec] applied to [TriJoinRecData]: *)
  tapply (fmap trijoin_rec).
  bundle_trijoinrecpath; intros; cbn.
  1: refine (ap inverse _).
  1, 2, 3: apply ap_idmap.
  generalize (join123 b a c).
  generalize (join23 (A:=B) a c).
  generalize (join13 (B:=A) b c).
  generalize (join12 (C:=C) b a).
  generalize (join3 (A:=B) (B:=A) c).
  generalize (join2 (A:=B) (C:=C) a).
  generalize (join1 (B:=A) (C:=C) b).
  intros k1 k2 k3 k12 k13 k23 k123.
  induction k12, k23, k123.
  reflexivity.
Defined.

(** Therefore the obvious definition is also an equivalence, and the inverse function can also be chosen to be [trijoin_twist]. *)
Definition equiv_trijoin_twist (A B C : Type)
  : TriJoin A B C <~> TriJoin B A C
  := equiv_homotopic_inverse (equiv_trijoin_twist' A B C)
                            (trijoin_twist_homotopic A B C)
                            (trijoin_twist_homotopic B A C).

(** ** The associativity of [Join] *)

(** [trijoin_twist] corresponds to the permutation (1,2).  The equivalence corresponding to the permutation (2,3) also plays a key role, so we name it here. *)
Definition trijoin_id_sym A B C : TriJoin A B C <~> TriJoin A C B
  := equiv_functor_join equiv_idmap (equiv_join_sym B C).

Arguments trijoin_id_sym : simpl never.

Definition join_assoc A B C : Join A (Join B C) <~> Join (Join A B) C.
Proof.
  refine (_ oE trijoin_id_sym _ _ _).
  refine (_ oE equiv_trijoin_twist _ _ _).
  apply equiv_join_sym.
Defined.

Arguments join_assoc : simpl never.

(** As a consequence, we get associativity of powers. *)
Corollary join_join_power A n m
  : Join (join_power A n) (join_power A m) <~> join_power A (n + m)%nat.
Proof.
  induction n as [|n IHn].
  1: exact (equiv_join_empty_left _).
  simpl. refine (_ oE (join_assoc _ _ _)^-1%equiv).
  exact (equiv_functor_join equiv_idmap IHn).
Defined.

(** ** Naturality of [trijoin_twist] *)

(** Our goal is to prove that [trijoin_twist A' B' C' o functor_join f (functor_join g h)] is homotopic to [functor_join g (functor_join f h) o trijoin_twist A B C]. *)

(** We first give a way to write anything of the form [trijoin_rec f o trijoin_twist A B C] as [trijoin_rec] applied to some [TriJoinRecData]. *)
Definition trijoin_rec_trijoin_twist {A B C P} (f : TriJoinRecData B A C P)
  : trijoin_rec f o trijoin_twist A B C == trijoin_rec (trijoinrecdata_twist _ _ _ _ f).
Proof.
  (* We first replace [trijoin_twist] with [equiv_trijoin_twist']. *)
  transitivity (trijoin_rec f o equiv_trijoin_twist' A B C).
  1: exact (fun x => ap (trijoin_rec f) (trijoin_twist_homotopic A B C x)).
  (* The LHS is now the twist natural transformation applied to [Id], followed by postcomposition; naturality states that that is the same as the natural trans applied to [trijoin_rec f]. *)
  refine ((isnat_natequiv (trijoinrecdata_fun_twist B A C) (trijoin_rec f) _)^$ $@ _).
  (* The LHS simplifies to [trijoinrecdata_fun_twist] applied to [trijoin_rec f].  The former is a composite of [trijoin_rec], [trijoinrecdata_twist] and [trijoin_rec_inv], so we can write the LHS as: *)
  change (?L $== ?R) with (trijoin_rec (trijoinrecdata_twist B A C P (trijoin_rec_inv (trijoin_rec f))) $== R).
  refine (fmap trijoin_rec _).
  refine (fmap (trijoinrecdata_twist B A C P) _).
  apply trijoin_rec_beta.
Defined.

(** Naturality of [trijoin_twist].  This version uses [functor_trijoin] and simply combines previous results. *)
Definition trijoin_twist_nat' {A B C A' B' C'} (f : A -> A') (g : B -> B') (h : C -> C')
  : trijoin_twist A' B' C' o functor_trijoin f g h
    == functor_trijoin g f h o trijoin_twist A B C.
Proof.
  intro x.
  rhs napply trijoin_rec_trijoin_twist.
  napply trijoin_rec_functor_trijoin.
Defined.

(** And now a version using [functor_join]. *)
Definition trijoin_twist_nat {A B C A' B' C'} (f : A -> A') (g : B -> B') (h : C -> C')
  : trijoin_twist A' B' C' o functor_join f (functor_join g h)
    == functor_join g (functor_join f h) o trijoin_twist A B C.
Proof.
  intro x.
  lhs nrefine (ap _ (functor_trijoin_as_functor_join f g h x)).
  rhs napply functor_trijoin_as_functor_join.
  apply trijoin_twist_nat'.
Defined.

(** ** Naturality of [trijoin_id_sym] *)

(** Naturality of [trijoin_id_sym], using [functor_join].  In this case, it's easier to do this version first. *)
Definition trijoin_id_sym_nat {A B C A' B' C'} (f : A -> A') (g : B -> B') (h : C -> C')
  : trijoin_id_sym A' B' C' o functor_join f (functor_join g h)
    == functor_join f (functor_join h g) o trijoin_id_sym A B C.
Proof.
  intro x; simpl.
  lhs_V napply functor_join_compose.
  rhs_V napply functor_join_compose.
  apply functor2_join.
  - reflexivity.
  - apply join_sym_nat.
Defined.

(** Naturality of [trijoin_id_sym], using [functor_trijoin]. *)
Definition trijoin_id_sym_nat' {A B C A' B' C'} (f : A -> A') (g : B -> B') (h : C -> C')
  : trijoin_id_sym A' B' C' o functor_trijoin f g h
    == functor_trijoin f h g o trijoin_id_sym A B C.
Proof.
  intro x.
  lhs_V nrefine (ap _ (functor_trijoin_as_functor_join f g h x)).
  rhs_V napply functor_trijoin_as_functor_join.
  apply trijoin_id_sym_nat.
Defined.

(** ** Naturality of [join_assoc] *)

(** Since [join_assoc] is a composite of [join_sym], [trijoin_twist] and [trijoin_id_sym], we just use their naturality. *)
Definition join_assoc_nat {A B C A' B' C'} (f : A -> A') (g : B -> B') (h : C -> C')
  : join_assoc A' B' C' o functor_join f (functor_join g h)
    == functor_join (functor_join f g) h o join_assoc A B C.
Proof.
  (* We'll work from right to left, as it is easier to work near the head of a term. *)
  intro x.
  unfold join_assoc; cbn.
  (* First we pass the [functor_joins]s through the outer [join_sym]. *)
  rhs_V napply join_sym_nat.
  (* Strip off the outer [join_sym]. *)
  apply (ap _).
  (* Next we pass the [functor_join]s through [trijoin_twist]. *)
  rhs_V napply trijoin_twist_nat.
  (* Strip off the [trijoin_twist]. *)
  apply (ap _).
  (* Finally, we pass the [functor_join]s through [trijoin_id_sym]. *)
  apply trijoin_id_sym_nat.
Defined.

Instance join_associator : Associator Join.
Proof.
  snapply Build_Associator; simpl.
  - exact join_assoc.
  - snapply Build_Is1Natural.
    intros [[A B] C] [[A' B'] C'] [[f g] h]; cbn.
    apply join_assoc_nat.
Defined.

(** ** The Triangle Law *)

(** The unitors were defined in Join/Core.v, since they do not require associativity. *)

(** Here's a version of the triangle law expressed using [trijoin_twist] instead of [join_assoc], and only using the right unitor. Since the left unitor is defined using [join_sym], the usual triangle law follows. *)
Definition join_trianglelaw' A B
  : join_sym B A o functor_join idmap (equiv_join_empty_right A) o trijoin_twist A B Empty
    == functor_join idmap (equiv_join_empty_right B).
Proof.
  (* A direct proof with [Join_ind] three times is not hard, but the path algebra is slightly simpler if we manipulate things ahead of time using [functor_join_join_rec] and [trijoin_rec_trijoin_twist]. *)
  intro x.
  rapply moveR_equiv_M.
  unfold equiv_join_empty_right at 1; cbn.
  lhs napply functor_join_join_rec; cbn.
  lhs napply trijoin_rec_trijoin_twist.
  revert x.
  apply moveR_trijoin_rec.
  snapply Build_TriJoinRecPath; intros; cbn.
  3, 5, 6, 7: by destruct c.
  - reflexivity.
  - reflexivity.
  - apply equiv_p1_1q.
    symmetry.
    lhs napply (ap_compose (functor_join idmap _) _ (join12 a b)).
    lhs napply ap.
    1: apply functor_join_beta_jglue.
    apply join_sym_beta_jglue.
Defined.

Definition join_trianglelaw : TriangleIdentity Join Empty.
Proof.
  intros A B x; cbn. 
  lhs napply (functor_join_compose idmap _ idmap _).
  lhs_V napply join_trianglelaw'.
  unfold join_assoc; cbn.
  apply join_sym_nat.
Defined.

(** ** The hexagon axiom *)

(** For the hexagon, we'll need to know how to compose [trijoin_id_sym] with something of the form [trijoin_rec f]. For some reason, the proof is harder than it was for [trijoin_twist]. *)

(** This describes the transformation on [TriJoinRecData] corresponding to precomposition with [trijoin_id_sym], as in the next result. *)
Definition trijoinrecdata_id_sym {A B C P} (f : TriJoinRecData A B C P)
  : TriJoinRecData A C B P.
Proof.
  snapply (Build_TriJoinRecData (j1 f) (j3 f) (j2 f)); intros.
  - apply (j13 f).
  - apply (j12 f).
  - symmetry; apply (j23 f).
  - cbn beta.  apply moveR_pV; symmetry.
    apply (j123 f).
Defined.

(** This is analogous to [trijoin_rec_trijoin_twist] above, with [trijoin_twist] replaced by [trijoin_id_sym]. *)
Definition trijoin_rec_id_sym {A B C P} (f : TriJoinRecData A C B P)
  : trijoin_rec f o trijoin_id_sym A B C == trijoin_rec (trijoinrecdata_id_sym f).
Proof.
  (* First we use [functor_join_join_rec] on the LHS. *)
  etransitivity.
  { refine (cat_postwhisker (A:=Type) (trijoin_rec f) _).
    apply functor_join_join_rec. }
  unfold join_sym_recdata, jl, jr, jg.
  (* And now we use naturality of the second [trijoin_rec] on the LHS. *)
  refine ((trijoin_rec_nat A B C (trijoin_rec f) _)^$ $@ _).
  refine (fmap trijoin_rec _).
  (* Finally, we provide the needed [TriJoinRecPath]. *)
  bundle_trijoinrecpath; intros; cbn.
  - apply trijoin_rec_beta_join13.
  - apply trijoin_rec_beta_join12.
  - lhs refine (ap _ (ap_V _ _)).
    lhs refine (ap_V (trijoin_rec f) _).
    apply (ap inverse).
    apply trijoin_rec_beta_join23.
  - unfold prism'.
    rewrite ap_trijoin_V.
    rewrite trijoin_rec_beta_join123.
    set (f' := f).
    destruct f as [f1 f2 f3 f12 f13 f23 f123]; cbn.
    generalize (f123 a c b).
    generalize (trijoin_rec_beta_join23 f' c b); cbn.
    generalize (f23 c b).
    generalize (trijoin_rec_beta_join13 f' a b); cbn.
    generalize (f13 a b).
    generalize (trijoin_rec_beta_join12 f' a c); cbn.
    generalize (f12 a c); cbn.
    intros p12 beta12 p13 beta13 p23 beta23 p123.
    induction beta12, beta13, beta23; cbn.
    rewrite 3 concat_p1, concat_1p.
    reflexivity.
Defined.

(** Here is our first hexagon law.  This is not the usual hexagon axiom, but we will see that it is equivalent, and is itself useful.  This law states that the following diagram commutes, where we write [*] for [Join]:
<<
    A * (B * C) -> A * (C * B) -> C * (A * B)
        |                            |
        v                            v
    B * (A * C) -> B * (C * A) -> C * (B * A)
>>
Here every arrow is either [trijoin_twist _ _ _] or [trijoin_id_sym _ _ _], and they alternate as you go around.  These correspond to the permutations (1,2) and (2,3) in the symmetric group on three letters.  We already know that they are their own inverses, i.e., they have order two.  The above says that the composite (1,2)(2,3) has order three.  These are the only relations in this presentation of [S_3].  Note also that every object in this diagram is parenthesized in the same way.  That will be important in our proof. *)
Definition hexagon_join_twist_sym A B C
  : trijoin_id_sym C A B o trijoin_twist A C B o trijoin_id_sym A B C
    == trijoin_twist B C A o trijoin_id_sym B A C o trijoin_twist A B C.
Proof.
  (* It's enough to show that both sides induces the same natural transformation under the covariant Yoneda embedding, i.e., after postcomposing with a general function [f]. *)
  tapply (opyon_faithful_0gpd (A:=Type)).
  intros P f.
  (* We replace [f] by [trijoin_rec t] for generic [t].  This will allow induction later. *)
  pose proof (p := issect_trijoin_rec_inv f).
  intro x; refine ((p _)^ @ _ @ p _); clear p.
  generalize (trijoin_rec_inv f) as t.
  intro t; clear f.
  (* Now we use how these various maps postcompose with [trijoin_rec foo]. *)
  lhs rapply trijoin_rec_id_sym.
  lhs rapply trijoin_rec_trijoin_twist.
  lhs rapply trijoin_rec_id_sym.
  rhs rapply trijoin_rec_trijoin_twist.
  rhs rapply trijoin_rec_id_sym.
  rhs rapply trijoin_rec_trijoin_twist.
  revert x; refine (fmap trijoin_rec _).
  bundle_trijoinrecpath; intros; cbn.
  1, 2, 3: reflexivity.
  by triangle_ind t c b a.
Defined.

(** Next we paste on a naturality square for [join_sym] on the right of the diagram:
<<
    A * (B * C) -> A * (C * B) -> C * (A * B) -> (A * B) * C
        |                            |                |
        v                            v                v
    B * (A * C) -> B * (C * A) -> C * (B * A) -> (B * A) * C
>>
The new horizontal maps are [join_sym _ _] and the new vertical map is [functor_join (join_sym A B) idmap]. This makes both horizontal composites definitionally equal to [join_assoc _ _ _], so the statement is about a square. *)
Definition square_join_sym_assoc_twist A B C
  : functor_join (join_sym A B) idmap o join_assoc A B C
    == join_assoc B A C o trijoin_twist A B C.
Proof.
  unfold join_assoc; cbn.
  intro x; lhs_V rapply join_sym_nat.
  apply ap.
  apply hexagon_join_twist_sym.
Defined.

(** Finally, we paste on the defining square for [join_assoc] on the left to get the hexagon axiom for the symmetric monoidal structure:
<<
    A * (C * B) -> A * (B * C) -> (A * B) * C
         |              |              |
         v              v              v
    (A * C) * B -> B * (A * C) -> (B * A) * C
>>
The right-hand square is a horizontally-compressed version of the rectangle from the previous result, whose horizontal arrows are associativity. In the left-hand square, the new vertical map is [join_assoc A C B] and the horizontal maps are [trijoin_id_sym A C B] and [join_sym (Join A C) B]. *)
Definition hexagon_join_assoc_sym A B C
  : functor_join (join_sym A B) idmap o join_assoc A B C o trijoin_id_sym A C B
    == join_assoc B A C o join_sym (Join A C) B o join_assoc A C B.
Proof.
  intro x.
  refine (square_join_sym_assoc_twist A B C _ @ _).
  apply ap.
  simpl.
  symmetry.
  exact (eissect (equiv_join_sym B (Join A C)) _).
Defined.
