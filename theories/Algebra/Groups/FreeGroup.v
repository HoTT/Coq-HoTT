Require Import Basics Types Group Subgroup
  WildCat.Core Colimits.Coeq
  Truncations.Core Truncations.SeparatedTrunc
  Spaces.List.Core Spaces.List.Theory.

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

(** [IsFreeGroup] is defined in Group.v. In this file we construct free groups and and prove properties about them. *)

(** We construct the free group on a type [A] as a higher inductive type. This construction is due to Kraus-Altenkirch 2018 arXiv:1805.02069. Their construction is actually more general, but we set-truncate it to suit our needs which is the free group as a set. This is a very simple HIT in a similar manner to the abelianization HIT used in Algebra.AbGroup.Abelianization. *)

Section Reduction.

  Universe u.
  Context (A : Type@{u}).

  (** We define words (with inverses) on A to be lists of marked elements of A *)
  Local Definition Words : Type@{u} := list (A + A).

  (** Given a marked element of A we can change its mark *)
  Local Definition change_sign : A + A -> A + A := equiv_sum_symm A A.

  (** We introduce a local notation for [change_sign]. It is only defined in this section however. *)
  Local Notation "x ^" := (change_sign x).

  (** Changing sign is an involution *)
  Local Definition change_sign_inv a : a^^ = a.
  Proof.
    by destruct a.
  Defined.

  (** We can concatenate words using list concatenation *)
  Local Definition word_concat : Words -> Words -> Words := @app _.

  (** We introduce a local notation for word_concat. *)
  Local Infix "@" := word_concat.

  Local Definition word_concat_w_nil x : x @ nil = x.
  Proof.
    induction x; trivial.
    cbn; f_ap.
  Defined.

  Local Definition word_concat_w_ww x y z : x @ (y @ z) = (x @ y) @ z.
  Proof.
    apply app_assoc.
  Defined.

  (** Singleton word *)
  Local Definition word_sing (x : A + A) : Words := (cons x nil).

  Local Notation "[ x ]" := (word_sing x).

  (** Now we wish to define the free group on A as the following HIT: 

    HIT N(A) : hSet
     | eta : Words -> N(A)
     | tau (x : Words) (a : A + A) (y : Words)
         : eta (x @ [a] @ [a^] @ y) = eta (x @ y).

    Since we cannot write our HITs directly like this (without resorting to private inductive types), we will construct this HIT out of HITs we know. In fact, we can define N(A) as a coequalizer. *)

  Local Definition map1 : Words * (A + A) * Words -> Words.
  Proof.
    intros [[x a] y].
    exact (x @ [a] @ [a^] @ y).
  Defined.

  Local Definition map2 : Words * (A + A) * Words -> Words.
  Proof.
    intros [[x a] y].
    exact (x @ y).
  Defined.

  (** Now we can define the underlying type of the free group as the 0-truncated coequalizer of these two maps *)
  Definition freegroup_type : Type := Tr 0 (Coeq map1 map2).

  (** This is the point constructor *)
  Definition freegroup_eta : Words -> freegroup_type := tr o coeq.

  (** This is the path constructor *)
  Definition freegroup_tau (x : Words) (a : A + A) (y : Words)
    : freegroup_eta (x @ [a] @ [a^] @ y) = freegroup_eta (x @ y).
  Proof.
    apply path_Tr, tr.
    exact ((cglue (x, a, y))).
  Defined.

  (** The group operation *)
  Global Instance sgop_freegroup : SgOp freegroup_type.
  Proof.
    intros x y.
    strip_truncations.
    revert x; snrapply Coeq_rec.
    { intros x; revert y.
      snrapply Coeq_rec.
      { intros y.
        exact (freegroup_eta (x @ y)). }
      intros [[y a] z]; cbn.
      refine (concat (ap _ _) _).
      { refine (concat (word_concat_w_ww _ _ _) _).
        rapply (ap (fun t => t @ _)).
        refine (concat (word_concat_w_ww _ _ _) _).
        rapply (ap (fun t => t @ _)).
        refine (word_concat_w_ww _ _ _). }
      refine (concat _ (ap _ _^)).
      2: apply word_concat_w_ww.
      apply freegroup_tau. }
    intros [[c b] d].
    simpl.
    revert y.
    snrapply Coeq_ind.
    { simpl.
      intro a.
      rewrite <- word_concat_w_ww.
      rewrite <- (word_concat_w_ww _ _ a).
      rapply (freegroup_tau c b (d @ a)). }
    intro; rapply path_ishprop.
  Defined.

  (** The unit of the free group is the empty word *)
  Global Instance monunit_freegroup_type : MonUnit freegroup_type.
  Proof.
    apply freegroup_eta.
    exact nil.
  Defined.

  (** We can change the sign of all the elements in a word and reverse the order. This will be the inversion in the group *)
  Fixpoint word_change_sign (x : Words) : Words.
  Proof.
    destruct x as [|x xs].
    1: exact nil.
    exact (word_change_sign xs @ [change_sign x]).
  Defined.

  (** Changing the sign changes the order of word concatenation *)
  Definition word_change_sign_ww (x y : Words)
    : word_change_sign (x @ y) = word_change_sign y @ word_change_sign x.
  Proof.
    induction x.
    { symmetry.
      apply word_concat_w_nil. }
    simpl.
    refine (concat _ (inverse (word_concat_w_ww _ _ _))).
    f_ap.
  Defined.

  (** This is also involutive *)
  Lemma word_change_sign_inv x : word_change_sign (word_change_sign x) = x.
  Proof.
    induction x.
    1: reflexivity.
    simpl.
    rewrite word_change_sign_ww.
    cbn; f_ap.
    apply change_sign_inv.
  Defined.

  (** Changing the sign gives us left inverses *)
  Lemma word_concat_Vw x : freegroup_eta (word_change_sign x @ x) = mon_unit.
  Proof.
    induction x.
    1: reflexivity.
    simpl.
    set (a' := a^).
    rewrite <- (change_sign_inv a).
    change (freegroup_eta ((word_change_sign x @ [a']) @ ([a'^] @ x)) = mon_unit).
    rewrite word_concat_w_ww.
    rewrite freegroup_tau.
    apply IHx.
  Defined.

  (** And since changing the sign is involutive we get right inverses from left inverses *)
  Lemma word_concat_wV x : freegroup_eta (x @ word_change_sign x) = mon_unit.
  Proof.
    set (x' := word_change_sign x).
    rewrite <- (word_change_sign_inv x).
    change (freegroup_eta (word_change_sign x' @ x') = mon_unit).
    apply word_concat_Vw.
  Defined.

  (** Negation is defined by changing the order of a word that appears in eta. Most of the work here is checking that it is agreeable with the path constructor. *)
  Global Instance negate_freegroup_type : Negate freegroup_type.
  Proof.
    intro x.
    strip_truncations.
    revert x; srapply Coeq_rec.
    { intro x.
      apply freegroup_eta.
      exact (word_change_sign x). }
    intros [[b a] c].
    unfold map1, map2.
    refine (concat _ (ap _ (inverse _))).
    2: apply word_change_sign_ww.
    refine (concat (ap _ _) _).
    { refine (concat (word_change_sign_ww _ _) _).
      apply ap.
      refine (concat (ap _ (inverse (word_concat_w_ww _ _ _))) _).
      refine (concat (word_change_sign_ww _ _) _).
      rapply (ap (fun t => t @ word_change_sign b)).
      apply word_change_sign_ww. }
    refine (concat _ (freegroup_tau _ a _)).
    apply ap.
    refine (concat (word_concat_w_ww _ _ _) _); f_ap.
    refine (concat (word_concat_w_ww _ _ _) _); f_ap.
    f_ap; cbn; f_ap.
    apply change_sign_inv.
  Defined.

  (** Now we can start to prove the group laws. Since these are hprops we can ignore what happens with the path constructor. *)

  (** Our operation is associative *)
  Global Instance associative_freegroup_type : Associative sg_op.
  Proof.
    intros x y z.
    strip_truncations.
    revert x; snrapply Coeq_ind; intro x; [ | apply path_ishprop].
    revert y; snrapply Coeq_ind; intro y; [ | apply path_ishprop].
    revert z; snrapply Coeq_ind; intro z; [ | apply path_ishprop].
    rapply (ap (tr o coeq)).
    apply word_concat_w_ww.
  Defined.

  (** Left identity *)
  Global Instance leftidentity_freegroup_type : LeftIdentity sg_op mon_unit.
  Proof.
    rapply Trunc_ind.
    srapply Coeq_ind; intro x; [ | apply path_ishprop].
    reflexivity.
  Defined.

  (** Right identity *)
  Global Instance rightidentity_freegroup_type : RightIdentity sg_op mon_unit.
  Proof.
    rapply Trunc_ind.
    srapply Coeq_ind; intro x; [ | apply path_ishprop].
    apply (ap tr), ap.
    apply word_concat_w_nil.
  Defined.

  (** Left inverse *)
  Global Instance leftinverse_freegroup_type : LeftInverse sg_op negate mon_unit.
  Proof.
    rapply Trunc_ind.
    srapply Coeq_ind; intro x; [ | apply path_ishprop].
    apply word_concat_Vw.
  Defined.

  (** Right inverse *)
  Global Instance rightinverse_freegroup_type : RightInverse sg_op negate mon_unit.
  Proof.
    rapply Trunc_ind.
    srapply Coeq_ind; intro x; [ | apply path_ishprop].
    apply word_concat_wV.
  Defined.

  (** Finally we have defined the free group on [A] *)
  Definition FreeGroup : Group.
  Proof.
    snrapply (Build_Group freegroup_type); repeat split; exact _.
  Defined.

  Definition words_rec (G : Group) (s : A -> G) : Words -> G.
  Proof.
    intro x.
    induction x as [|x xs].
    1: exact mon_unit.
    refine (_ * IHxs).
    destruct x as [x|x].
    1: exact (s x).
    exact (- s x).
  Defined.

  Lemma words_rec_pp (G : Group) (s : A -> G)  (x y : Words)
    : words_rec G s (x @ y) = words_rec G s x * words_rec G s y.
  Proof.
    induction x.
    1: symmetry; apply left_identity.
    cbn; rewrite <- simple_associativity.
    f_ap.
  Defined.

  Lemma words_rec_coh (G : Group) (s : A -> G) (a : A + A) (b c : Words)
    : words_rec G s (map1 (b, a, c)) = words_rec G s (map2 (b, a, c)).
  Proof.
    unfold map1, map2.
    refine (concat _ (words_rec_pp G s _ _)^).
    refine (concat (words_rec_pp G s _ _) _); f_ap.
    refine (concat _ (right_identity _)).
    refine (concat (ap _ (word_concat_w_ww _ _ _)^) _).
    refine (concat (words_rec_pp G s _ _) _); f_ap.
    refine (concat (concat (simple_associativity _ _ _) _) (left_identity mon_unit)).
    destruct a; simpl; f_ap.
    + apply right_inverse.
    + apply left_inverse.
  Defined.

  (** Given a group [G] we can construct a group homomorphism [FreeGroup A -> G] if we have a map [A -> G] *)
  Definition FreeGroup_rec (G : Group) (s : A -> G)
    : GroupHomomorphism FreeGroup G.
  Proof.
    snrapply Build_GroupHomomorphism.
    { rapply Trunc_rec.
      srapply Coeq_rec.
      1: apply words_rec, s.
      intros [[b a] c].
      apply words_rec_coh. }
    intros x y; strip_truncations.
    revert x; snrapply Coeq_ind; hnf; intro x; [ | apply path_ishprop ].
    revert y; snrapply Coeq_ind; hnf; intro y; [ | apply path_ishprop ].
    simpl.
    apply words_rec_pp.
  Defined.

  (** Now we need to prove that the free group satisifes the unviersal property of the free group. *)
  (** TODO: remove funext from here and universal property of free group *)
  Global Instance isfreegroupon_freegroup `{Funext}
    : IsFreeGroupOn A FreeGroup (freegroup_eta o word_sing o inl).
  Proof.
    intros G f.
    snrapply Build_Contr.
    { srefine (_;_); simpl.
      1: apply FreeGroup_rec, f.
      intro x; simpl.
      apply right_identity. }
    intros [g h].
    nrapply path_sigma_hprop; [ exact _ |].
    simpl.
    apply equiv_path_grouphomomorphism.
    intro x.
    rewrite <- (path_forall _ _ h).
    strip_truncations; revert x.
    snrapply Coeq_ind; intro x; [|apply path_ishprop].
    hnf; symmetry.
    induction x.
    1: apply (grp_homo_unit g).
    refine (concat (grp_homo_op g (freegroup_eta [a]) (freegroup_eta x)) _).
    simpl.
    f_ap.
    destruct a.
    1: reflexivity.
    exact (grp_homo_inv g (freegroup_eta [inl a])).
  Defined.

  (** Typeclass search can already find this but we leave it here as a definition for reference. *)
  Definition isfreegroup_freegroup `{Funext} : IsFreeGroup FreeGroup := _.

  Definition freegroup_in : A -> FreeGroup
    := freegroup_eta o word_sing o inl.

  Lemma FreeGroup_rec_beta {G : Group} (f : A -> G)
    : FreeGroup_rec _ f o freegroup_in == f.
  Proof.
    intros x.
    apply grp_unit_r.
  Defined.

  Coercion freegroup_in : A >-> group_type.

End Reduction.

Arguments freegroup_eta {A}.
Arguments freegroup_in {A}.

(** Properties of free groups *)

(* Given a function on the generators, there is an induced group homomorphism from the free group. *)
Definition isfreegroupon_rec {S : Type} {F_S : Group}
  {i : S -> F_S} `{IsFreeGroupOn S F_S i}
  {G : Group} (f : S -> G) : F_S $-> G
  := (center (FactorsThroughFreeGroup S F_S i G f)).1.

(* The propositional computation rule for the recursor. *)
Definition isfreegroupon_rec_beta
  {S : Type} {F_S : Group} {i : S -> F_S} `{IsFreeGroupOn S F_S i}
  {G : Group} (f : S -> G)
  : isfreegroupon_rec f o i == f
  := (center (FactorsThroughFreeGroup S F_S i G f)).2.

(* Two homomorphisms from a free group are equal if they agree on the generators. *)
Definition path_homomorphism_from_free_group {S : Type}
  {F_S : Group} {i : S -> F_S} `{IsFreeGroupOn S F_S i}
  {G : Group} (f g : F_S $-> G) (K : f o i == g o i)
  : f = g.
Proof.
  (* By assumption, the type [FactorsThroughFreeGroup S F_S i G (g o i)] of factorizations of [g o i] through [i] is contractible.  Therefore the two elements we have are equal.  Therefore, their first components are equal. *)
  exact (path_contr (f; K) (g; fun x => idpath))..1.
Defined.

Global Instance isequiv_isfreegroupon_rec `{Funext} {S : Type}
  {F_S : Group} {i : S -> F_S} `{IsFreeGroupOn S F_S i} {G : Group}
  : IsEquiv (@isfreegroupon_rec S F_S i _ G).
Proof.
  apply (isequiv_adjointify isfreegroupon_rec (fun f => f o i)).
  - intro f.
    apply path_homomorphism_from_free_group.
    apply isfreegroupon_rec_beta.
  - intro f.
    (* here we need [Funext]: *)
    apply path_arrow, isfreegroupon_rec_beta.
Defined.

(** The universal property of a free group. *)
Definition equiv_isfreegroupon_rec `{Funext} {G F : Group} {A : Type}
  {i : A -> F} `{IsFreeGroupOn A F i}
  : (A -> G) <~> (F $-> G) := Build_Equiv _ _ isfreegroupon_rec _.

(** The above theorem is true regardless of the implementation of free groups. This lets us state the more specific theorem about the canonical free groups. This can be read as [FreeGroup] is left adjoint to the forgetful functor [group_type]. *)
Definition equiv_freegroup_rec `{Funext} (G : Group) (A : Type)
  : (A -> G) <~> (FreeGroup A $-> G)
  := equiv_isfreegroupon_rec.

Global Instance ishprop_isfreegroupon `{Funext} (F : Group) (A : Type) (i : A -> F)
  : IsHProp (IsFreeGroupOn A F i).
Proof.
  unfold IsFreeGroupOn.
  apply istrunc_forall.
Defined.

(** Both ways of stating the universal property are equivalent. *)
Definition equiv_isfreegroupon_isequiv_precomp `{Funext}
  (F : Group) (A : Type) (i : A -> F)
  : IsFreeGroupOn A F i <~> forall G, IsEquiv (fun f : F $-> G => f o i).
Proof.
  srapply equiv_iff_hprop.
  1: intros ? ?; exact (equiv_isequiv (equiv_isfreegroupon_rec)^-1).
  intros k G g.
  specialize (k G).
  snrapply contr_equiv'.
  1: exact (hfiber (fun f x => grp_homo_map F G f (i x)) g).
  { rapply equiv_functor_sigma_id.
    intro y; symmetry.
    apply equiv_path_forall. }
  exact _.
Defined.

(** ** Subgroups of free groups *)

(* We say that a group [G] is generated by a subtype [X] if the natural map from the subgroup generated by [X] to [G] is a surjection.  One could equivalently say [IsEquiv (subgroup_incl (subgroup_generated X))], [forall g, subgroup_generated X g], or [subgroup_generated X = maximal_subgroup], but the definition using surjectivity is convenient later. *)
Definition isgeneratedby (G : Group) (X : G -> Type)
  := IsSurjection (subgroup_incl (subgroup_generated X)).

Section FreeGroupGenerated.
  (* In this Section, we prove that the free group [F_S] on a type [S] is generated in the above sense by the image of [S].  We conclude that the inclusion map is an equivalence, and that the free group is isomorphic as a group to the subgroup. We show that the inclusion is a surjection by showing that it is split epi in the category of groups. *)

  Context {S : Type} {F_S : Group} {i : S -> F_S} `{IsFreeGroupOn S F_S i}.

  (* We define a group homomorphism from [F_S] to the subgroup [G] generated by [S] by sending a generator [s] to "itself".  This map will be a section of the inclusion map. *)
  Local Definition to_subgroup_generated
    : F_S $-> subgroup_generated (hfiber i).
  Proof.
    apply isfreegroupon_rec.
    intro s.
    snrapply subgroup_generated_gen_incl.
    - exact (i s).
    - exact (s; idpath).
  Defined.

  (* We record the computation rule that [to_subgroup_generated] satisfies. *)
  Local Definition to_subgroup_generated_beta (s : S)
    : to_subgroup_generated (i s) = subgroup_generated_gen_incl (i s) (s; idpath)
    := isfreegroupon_rec_beta _ _.

  (* It follows that [to_subgroup_generated] is a section of the inclusion map from [G] to [F_S]. *)
  Local Definition is_retraction
    : (subgroup_incl _) $o to_subgroup_generated = grp_homo_id.
  Proof.
    apply path_homomorphism_from_free_group; cbn.
    intro s.
    exact (ap pr1 (to_subgroup_generated_beta s)).
  Defined.

  (* It follows that the inclusion map is a surjection, i.e., that [F_S] is generated by the image of [S]. *)
  Definition isgenerated_isfreegroupon
    : isgeneratedby F_S (hfiber i).
  Proof.
    snrapply issurj_retr.
    - apply to_subgroup_generated.
    - apply ap10; cbn.
      exact (ap (grp_homo_map F_S F_S) (is_retraction)).
  Defined.

  (* Therefore, the inclusion map is an equivalence, since it is known to be an embedding. *)
  Definition isequiv_subgroup_incl_freegroupon
    : IsEquiv (subgroup_incl (subgroup_generated (hfiber i))).
  Proof.
    apply isequiv_surj_emb.
    - apply isgenerated_isfreegroupon.
    - exact _.
  Defined.

  (* Therefore, the subgroup is isomorphic to the free group. *)
  Definition iso_subgroup_incl_freegroupon
    : GroupIsomorphism (subgroup_generated (hfiber i)) F_S.
  Proof.
    nrapply Build_GroupIsomorphism.
    apply isequiv_subgroup_incl_freegroupon.
  Defined.

End FreeGroupGenerated.
