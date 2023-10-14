Require Import Basics Types WildCat Join.Core Join.TriJoin Spaces.Nat.Core HoTT.Tactics.

(** * The associativity of [Join]

  We use the recursion principle for the triple join (from TriJoin.v) to prove the associativity of Join.  We'll use the common technique of combining symmetry and a twist equivalence.  Temporarily writing * for Join, symmetry says that [A * B <~> B * A] and the twist says that [A * (B * C) <~> B * (A * C)].  From these we get a composite equivalence [A * (B * C) <~> A * (C * B) <~> C * (A * B) <~> (A * B) * C].  One advantage of this approach is that both symmetry and the twist are their own inverses, so there are fewer maps to define and fewer composites to prove are homotopic to the identity. Symmetry is proved in Join/Core.v. *)

(** ** The twist equivalence [TriJoin A B C <~> TriJoin B A C]

  We prove the twist equivalence using the Yoneda lemma.  The idea is that [TriJoin A B C -> P] is equivalent (as a 0-groupoid) to [TriJoinRecData A B C P], and the latter is very symmetrical by construction, which makes it easy to show that it is equivalent to [TriJoinRecData B A C P].  Going back along the first equivalence gets us to [TriJoin B A C -> P].  These equivalences are natural in [P], so the twist equivalence follows from the Yoneda lemma. *)

(** First we define a map of 0-groupoids that will underlie the natural equivalence. *)
Definition trijoinrecdata_twist (A B C P : Type)
  : trijoinrecdata_0gpd A B C P $-> trijoinrecdata_0gpd B A C P.
Proof.
  snrapply Build_Morphism_0Gpd.
  (* The map of types [TriJoinRecData A B C P -> TriJoinRecData B A C P]: *)
  - cbn.
    intros [f1 f2 f3 f12 f13 f23 f123].
    snrapply (Build_TriJoinRecData f2 f1 f3).
    + intros b a; exact (f12 a b)^.
    + exact f23.
    + exact f13.
    + intros a b c; cbn beta.
      apply moveR_Vp.
      symmetry; apply f123.
  (* It respects the paths. *)
  - apply Build_Is0Functor.
    intros f g h; cbn in *.
    snrapply Build_TriJoinRecPath; intros; simpl.
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
  snrapply Build_NatEquiv.
  (* An equivalence of 0-groupoids for each [P]: *)
  - intro P.
    snrapply cate_adjointify.
    1, 2: apply trijoinrecdata_twist.
    1, 2: apply trijoinrecdata_twist_inv.
  (* Naturality: *)
  - intros P Q g f; simpl.
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
  rapply (opyon_equiv_0gpd (A:=Type)).
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
  rapply (fmap trijoin_rec).
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

Definition join_assoc A B C : Join A (Join B C) <~> Join (Join A B) C.
Proof.
  refine (_ oE equiv_functor_join equiv_idmap (equiv_join_sym B C)).
  refine (_ oE equiv_trijoin_twist _ _ _).
  apply equiv_join_sym.
Defined.

(** As a consequence, we get associativity of powers. *)
Corollary join_join_power A n m
  : Join (join_power A n) (join_power A m) <~> join_power A (n + m)%nat.
Proof.
  induction n as [|n IHn].
  1: exact (equiv_join_empty' _).
  simpl. refine (_ oE (join_assoc _ _ _)^-1%equiv).
  exact (equiv_functor_join equiv_idmap IHn).
Defined.

(** ** Naturality of [trijoin_twist] *)

(** Our goal is to prove that [trijoin_twist A' B' C' o functor_join f (functor_join g h)] is homotopic to [functor_join g (functor_join f h) o trijoin_twist A B C].  We will study the LHS and RHS separately, expressed using [functor_trijoin], and meet in the middle. *)

Definition trijoin_twist_nat_rhs {A B C P} (f : TriJoinRecData B A C P)  (* P is TriJoin B' A' C' above *)
  : trijoin_rec (trijoinrecdata_twist _ _ _ _ f)
    == trijoin_rec f o trijoin_twist A B C.
Proof.
  (* We first replace [trijoin_twist] with [equiv_trijoin_twist']. *)
  transitivity (trijoin_rec f o equiv_trijoin_twist' A B C).
  2: exact (fun x => ap (trijoin_rec f) (trijoin_twist_homotopic A B C x)^).
  (* The RHS is now the twist natural transformation applied to [Id], followed by postcomposition; naturality states that that is the same as the natural trans applied to [trijoin_rec f]. *)
  refine (_ $@ isnat_natequiv (trijoinrecdata_fun_twist B A C) (trijoin_rec f) _).
  (* The RHS simplifies to [trijoinrecdata_fun_twist] applied to [trijoin_rec f].  The former is a composite of [trijoin_rec], [trijoinrecdata_twist] and [trijoin_rec_inv], so we can write the RHS as: *)
  change (?L $== ?R) with (L $== trijoin_rec (trijoinrecdata_twist B A C P (trijoin_rec_inv (trijoin_rec f)))).
  refine (fmap trijoin_rec _).
  refine (fmap (trijoinrecdata_twist B A C P) _).
  symmetry; apply trijoin_rec_beta.
Defined.

(** We can precompose [k : TriJoinRecData] with a triple of maps. *)
Definition trijoinrecdata_tricomp {A B C A' B' C' P} (k : TriJoinRecData A B C P)
  (f : A' -> A) (g : B' -> B) (h : C' -> C)
  : TriJoinRecData A' B' C' P
  := {| j1 := j1 k o f; j2 := j2 k o g; j3 := j3 k o h;
       j12 := fun a b => j12 k (f a) (g b);
       j13 := fun a c => j13 k (f a) (h c);
       j23 := fun b c => j23 k (g b) (h c);
       j123 := fun a b c => j123 k (f a) (g b) (h c); |}.

(** Precomposition with a triple respects paths. *)
Definition trijoinrecdata_tricomp_0fun {A B C A' B' C' P}
  {k l : TriJoinRecData A B C P} (p : k $== l)
  (f : A' -> A) (g : B' -> B) (h : C' -> C)
  : trijoinrecdata_tricomp k f g h $== trijoinrecdata_tricomp l f g h.
Proof.
  (* This line is not needed, but clarifies the proof. *)
  unfold trijoinrecdata_tricomp; destruct p.
  snrapply Build_TriJoinRecPath; intros; cbn; apply_hyp.
  (* E.g., the first goal is [j1 k (f a) = j1 l (f a)], and this is solved by [h1 p (f a)]. We just precompose all fields of [p] with [f], [g] and [h]. *)
Defined.

(** We generalize the LHS to the LHS of the following result, which is a partial functoriality of [trijoin_rec] in [A], [B] and [C]. *)
Definition trijoin_twist_nat_lhs {A B C A' B' C' P} (f : A -> A') (g : B -> B') (h : C -> C')
  (k : TriJoinRecData A' B' C' P)
  : trijoin_rec k o functor_trijoin f g h
    == trijoin_rec (trijoinrecdata_tricomp k f g h).
Proof.
  (* On the LHS, we use naturality of the [trijoin_rec] inside [functor_trijoin]: *)
  refine ((trijoin_rec_nat _ _ _ _ _)^$ $@ _).
  refine (fmap trijoin_rec _).
  (* Just to clarify to the reader what is going on: *)
  change (?L $-> ?R) with (trijoinrecdata_tricomp (trijoin_rec_inv (trijoin_rec k)) f g h $-> R).
  exact (trijoinrecdata_tricomp_0fun (trijoin_rec_beta k) f g h).
Defined.

(** Naturality of [trijoin_twist].  This version uses [functor_trijoin] and simply combines the above. *)
Definition trijoin_twist_nat' {A B C A' B' C'} (f : A -> A') (g : B -> B') (h : C -> C')
  : trijoin_twist A' B' C' o functor_trijoin f g h
    == functor_trijoin g f h o trijoin_twist A B C.
Proof.
  intro x.
  rhs_V nrapply trijoin_twist_nat_rhs.
  nrapply trijoin_twist_nat_lhs.
Defined.

(** And now a version using [functor_join]. *)
Definition trijoin_twist_nat {A B C A' B' C'} (f : A -> A') (g : B -> B') (h : C -> C')
  : trijoin_twist A' B' C' o functor_join f (functor_join g h)
    == functor_join g (functor_join f h) o trijoin_twist A B C.
Proof.
  intro x.
  lhs nrefine (ap _ (functor_trijoin_as_functor_join f g h x)).
  rhs nrapply functor_trijoin_as_functor_join.
  apply trijoin_twist_nat'.
Defined.

(** ** Naturality of [join_assoc] *)

Definition join_assoc_nat {A B C A' B' C'} (f : A -> A') (g : B -> B') (h : C -> C')
  : join_assoc A' B' C' o functor_join f (functor_join g h)
    == functor_join (functor_join f g) h o join_assoc A B C.
Proof.
  (* Since [join_assoc] is a composite of [trijoin_twist] and [join_sym], we just use their naturality. We'll work from right to left, as it is easier to work near the head of a term. *)
  intro x.
  unfold join_assoc; simpl.
  (* First we pass the [functor_joins]s through the outer [join_sym]. *)
  rhs_V nrapply join_sym_nat.
  (* Strip off the outer [join_sym]. *)
  apply (ap _).
  (* Next we pass the [functor_join]s through [trijoin_twist]. *)
  rhs_V nrapply trijoin_twist_nat.
  (* Strip off the [trijoin_twist]. *)
  apply (ap _).
  (* Finally, we pass the [functor_join]s through the inner [join_sym]. *)
  lhs_V nrapply functor_join_compose.
  rhs_V nrapply functor_join_compose.
  apply functor2_join.
  - reflexivity.
  - apply join_sym_nat.
Defined.
