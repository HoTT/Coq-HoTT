Require Import Basics Types Group Subgroup
  WildCat.Core WildCat.Universe Colimits.Coeq
  Truncations.Core Truncations.SeparatedTrunc
  Spaces.List.Core Spaces.List.Theory.

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

(** [IsFreeGroup] is defined in Group.v. In this file we construct free groups and and prove properties about them. *)

(** We construct the free group on a type [A] as a higher inductive type. This construction is due to Kraus-Altenkirch 2018 arXiv:1805.02069. Their construction is actually more general, but we set-truncate it to suit our needs which is the free group as a set. This is a very simple HIT in a similar manner to the abelianization HIT used in Algebra.AbGroup.Abelianization. *)

Section Reduction.

  Universe u.
  Context (A : Type@{u}).
  
  Local Open Scope list_scope.

  (** We define words (with inverses) on A to be lists of marked elements of A *)
  Local Definition Words : Type@{u} := list (A + A).

  (** Given a marked element of A we can change its mark *)
  Local Definition change_sign : A + A -> A + A := equiv_sum_symm A A.

  (** We introduce a local notation for [change_sign]. It is only defined in this section however. *)
  Local Notation "a ^'" := (change_sign a) (at level 1).

  (** Changing sign is an involution *)
  Local Definition change_sign_inv a : a^'^' = a.
  Proof.
    by destruct a.
  Defined.

  (** Now we wish to define the free group on A as the following HIT: 

    HIT N(A) : hSet
     | eta : Words -> N(A)
     | tau (x : Words) (a : A + A) (y : Words)
         : eta (x ++ [a] ++ [a^] ++ y) = eta (x ++ y).

    Since we cannot write our HITs directly like this (without resorting to private inductive types), we will construct this HIT out of HITs we know. In fact, we can define N(A) as a coequalizer. *)

  Local Definition map1 : Words * (A + A) * Words -> Words.
  Proof.
    intros [[x a] y].
    exact (x ++ [a] ++ [a^'] ++ y).
  Defined.
  
  Arguments map1 _ /.

  Local Definition map2 : Words * (A + A) * Words -> Words.
  Proof.
    intros [[x a] y].
    exact (x ++ y).
  Defined.
  
  Arguments map2 _ /.

  (** Now we can define the underlying type of the free group as the 0-truncated coequalizer of these two maps *)
  Definition freegroup_type : Type := Tr 0 (Coeq map1 map2).

  (** This is the point constructor *)
  Definition freegroup_eta : Words -> freegroup_type := tr o coeq.

  (** This is the path constructor *)
  Definition freegroup_tau (x : Words) (a : A + A) (y : Words)
    : freegroup_eta (x ++ [a] ++ [a^'] ++ y) = freegroup_eta (x ++ y).
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
        exact (freegroup_eta (x ++ y)). }
      intros [[y a] z]; simpl.
      change (freegroup_eta (x ++ y ++ ([a] ++ [a^'] ++ z))
        = freegroup_eta (x ++ y ++ z)).
      rhs nrapply ap.
      2: nrapply app_assoc.
      lhs nrapply ap.
      1: nrapply app_assoc.
      nrapply (freegroup_tau _ a). }
    intros [[c b] d].
    revert y.
    srapply Coeq_ind_hprop.
    intro a.
    change (freegroup_eta ((c ++ [b] ++ [b^'] ++ d) ++ a)
      = freegroup_eta ((c ++ d) ++ a)).
    lhs_V nrapply ap.
    1: nrapply app_assoc.
    lhs_V nrapply (ap (fun x => freegroup_eta (c ++ x))).
    1: nrapply app_assoc.
    lhs_V nrapply (ap (fun x => freegroup_eta (c ++ _ ++ x))).
    1: nrapply app_assoc.
    rhs_V nrapply ap.
    2: nrapply app_assoc.
    nrapply freegroup_tau.
  Defined.

  (** The unit of the free group is the empty word *)
  Global Instance monunit_freegroup_type : MonUnit freegroup_type
    := freegroup_eta nil.

  (** We can change the sign of all the elements in a word and reverse the order. This will be the inversion in the group *)
  Definition word_change_sign (x : Words) : Words
    := reverse (list_map change_sign x).

  (** Changing the sign changes the order of word concatenation *)
  Definition word_change_sign_ww (x y : Words)
    : word_change_sign (x ++ y) = word_change_sign y ++ word_change_sign x.
  Proof.
    unfold word_change_sign.
    lhs nrapply (ap reverse).
    1: nrapply list_map_app.
    nrapply reverse_app.
  Defined.

  (** This is also involutive *)
  Lemma word_change_sign_inv x : word_change_sign (word_change_sign x) = x.
  Proof.
    unfold word_change_sign.
    lhs_V nrapply list_map_reverse.
    lhs nrapply ap.
    1: nrapply reverse_reverse. 
    lhs_V nrapply list_map_compose.
    snrapply list_map_id.
    intros a ?.
    apply change_sign_inv.
  Defined.

  (** Changing the sign gives us left inverses *)
  Lemma word_concat_Vw x : freegroup_eta (word_change_sign x ++ x) = mon_unit.
  Proof.
    induction x.
    1: reflexivity.
    lhs nrapply (ap (fun x => freegroup_eta (x ++ _))).
    1: nrapply reverse_cons.
    change (freegroup_eta ((word_change_sign x ++ [a^']) ++ [a] ++ x)
      = mon_unit). 
    lhs_V nrapply ap.
    1: nrapply app_assoc.
    set (a' := a^').
    rewrite <- (change_sign_inv a).
    lhs nrapply freegroup_tau.
    apply IHx.
  Defined.

  (** And since changing the sign is involutive we get right inverses from left inverses *)
  Lemma word_concat_wV x : freegroup_eta (x ++ word_change_sign x) = mon_unit.
  Proof.
    set (x' := word_change_sign x).
    rewrite <- (word_change_sign_inv x).
    change (freegroup_eta (word_change_sign x' ++ x') = mon_unit).
    apply word_concat_Vw.
  Defined.

  (** Inverses are defined by changing the order of a word that appears in eta. Most of the work here is checking that it is agreeable with the path constructor. *)
  Global Instance inverse_freegroup_type : Inverse freegroup_type.
  Proof.
    intro x.
    strip_truncations.
    revert x; srapply Coeq_rec.
    { intro x.
      apply freegroup_eta.
      exact (word_change_sign x). }
    intros [[b a] c].
    unfold map1, map2.
    lhs nrapply ap.
    { lhs nrapply word_change_sign_ww.
      nrapply (ap (fun x => x ++ _)). 
      lhs nrapply word_change_sign_ww.
      nrapply (ap (fun x => x ++ _)). 
      lhs nrapply word_change_sign_ww.
      nrapply (ap (fun x => _ ++ x)).
      nrapply (word_change_sign_inv [a]). }
    lhs_V nrapply ap.
    1: rhs_V nrapply app_assoc.
    1: nrapply app_assoc.
    rhs nrapply ap.
    2: nrapply word_change_sign_ww.
    nrapply freegroup_tau.
  Defined.

  (** Now we can start to prove the group laws. Since these are hprops we can ignore what happens with the path constructor. *)

  (** Our operation is associative *)
  Global Instance associative_freegroup_type : Associative sg_op.
  Proof.
    intros x y z.
    strip_truncations.
    revert x; srapply Coeq_ind_hprop; intro x.
    revert y; srapply Coeq_ind_hprop; intro y.
    revert z; srapply Coeq_ind_hprop; intro z.
    nrapply (ap (tr o coeq)).
    nrapply app_assoc.
  Defined.

  (** Left identity *)
  Global Instance leftidentity_freegroup_type : LeftIdentity sg_op mon_unit.
  Proof.
    rapply Trunc_ind.
    srapply Coeq_ind_hprop; intros x.
    reflexivity.
  Defined.

  (** Right identity *)
  Global Instance rightidentity_freegroup_type : RightIdentity sg_op mon_unit.
  Proof.
    rapply Trunc_ind.
    srapply Coeq_ind_hprop; intros x.
    apply (ap tr), ap.
    nrapply app_nil.
  Defined.

  (** Left inverse *)
  Global Instance leftinverse_freegroup_type : LeftInverse (.*.) (^) mon_unit.
  Proof.
    rapply Trunc_ind.
    srapply Coeq_ind_hprop; intro x.
    apply word_concat_Vw.
  Defined.

  (** Right inverse *)
  Global Instance rightinverse_freegroup_type : RightInverse (.*.) (^) mon_unit.
  Proof.
    rapply Trunc_ind.
    srapply Coeq_ind_hprop; intro x.
    apply word_concat_wV.
  Defined.

  (** Finally we have defined the free group on [A] *)
  Definition FreeGroup : Group.
  Proof.
    snrapply (Build_Group freegroup_type); repeat split; exact _.
  Defined.
  
  Definition word_rec (G : Group) (s : A -> G) : A + A -> G.
  Proof.
    intros [x|x].
    - exact (s x).
    - exact (s x)^.
  Defined.

  (** When we have a list of words we can recursively define a group element. The obvious choice would be to map [nil] to the identity and [x :: xs] to [x * words_rec xs]. This has the disadvantage that a single generating element gets mapped to [x * 1] instead of [x]. To fix this issue, we map [nil] to the identity, the singleton to the element we want, and do the rest recursively. *)
  Definition words_rec (G : Group) (s : A -> G) : Words -> G.
  Proof.
    intro xs.
    induction xs as [|x [|y xs] IHxs].
    - exact mon_unit.
    - exact (word_rec G s x).
    - exact (word_rec G s x * IHxs).
  Defined.

  Definition words_rec_cons (G : Group) (s : A -> G) (x : A + A) (xs : Words)
    : words_rec G s (x :: xs)%list = word_rec G s x * words_rec G s xs.
  Proof.
    induction xs in x |- *.
    - symmetry; nrapply grp_unit_r.
    - reflexivity.
  Defined.

  Lemma words_rec_pp (G : Group) (s : A -> G)  (x y : Words)
    : words_rec G s (x ++ y) = words_rec G s x * words_rec G s y.
  Proof.
    induction x as [|x xs IHxs] in y |- *.
    - symmetry; nrapply grp_unit_l.
    - change ((?x :: ?xs) ++ y) with (x :: xs ++ y).
      lhs nrapply words_rec_cons.
      lhs nrapply ap.
      1: nrapply IHxs.
      lhs nrapply grp_assoc.
      nrapply (ap (.* _)).
      symmetry.
      apply words_rec_cons.
  Defined.

  Lemma words_rec_coh (G : Group) (s : A -> G) (a : A + A) (b c : Words)
    : words_rec G s (map1 (b, a, c)) = words_rec G s (map2 (b, a, c)).
  Proof.
    unfold map1, map2.
    rhs nrapply (words_rec_pp G s).
    lhs nrapply words_rec_pp.
    nrapply (ap (_ *.)).
    lhs nrapply words_rec_pp.
    lhs nrapply ap.
    1: nrapply words_rec_pp.
    lhs nrapply grp_assoc.
    rhs_V nrapply grp_unit_l.
    nrapply (ap (.* _)).
    destruct a; simpl.
    - nrapply grp_inv_r.
    - nrapply grp_inv_l.
  Defined.

  (** Given a group [G] we can construct a group homomorphism [FreeGroup A $-> G] if we have a map [A -> G]. *)
  Definition FreeGroup_rec {G : Group} (s : A -> G) : FreeGroup $-> G.
  Proof.
    snrapply Build_GroupHomomorphism.
    { rapply Trunc_rec.
      srapply Coeq_rec.
      1: apply words_rec, s.
      intros [[b a] c].
      apply words_rec_coh. }
    intros x y; strip_truncations.
    revert x; srapply Coeq_ind_hprop; intro x.
    revert y; srapply Coeq_ind_hprop; intro y. 
    simpl.
    apply words_rec_pp.
  Defined.

  Definition freegroup_in : A -> FreeGroup
    := freegroup_eta o (fun x => [ x ]) o inl.

  Definition FreeGroup_rec_beta {G : Group} (f : A -> G)
    : FreeGroup_rec f o freegroup_in == f
    := fun _ => idpath.

  Coercion freegroup_in : A >-> group_type.
  
  Definition FreeGroup_ind_hprop' (P : FreeGroup -> Type)
    `{forall x, IsHProp (P x)}
    (H1 : forall w, P (freegroup_eta w))
    : forall x, P x.
  Proof.
    rapply Trunc_ind.
    srapply Coeq_ind_hprop.
    exact H1.
  Defined.
 
  Definition FreeGroup_ind_hprop (P : FreeGroup -> Type)
    `{forall x, IsHProp (P x)}
    (H1 : P mon_unit)
    (Hin : forall x, P (freegroup_in x))
    (Hop : forall x y, P x -> P y -> P (x^ * y))
    : forall x, P x.
  Proof.
    rapply FreeGroup_ind_hprop'.
    intros w.
    induction w as [|a w IHw].
    - exact H1.
    - destruct a as [a|a].
      + change (P ((freegroup_in a) * freegroup_eta w)).  
        rewrite <- (grp_inv_inv a).
        apply Hop.
        * rewrite <- grp_unit_r.
          by apply Hop.
        * assumption.
      + change (P ((freegroup_in a)^ * freegroup_eta w)).
        by apply Hop.
  Defined.
  
  Definition FreeGroup_ind_homotopy {G : Group} {f f' : FreeGroup $-> G}
    (H : forall x, f (freegroup_in x) = f' (freegroup_in x))
    : f $== f'.
  Proof.
    rapply FreeGroup_ind_hprop.
    - exact (concat (grp_homo_unit f) (grp_homo_unit f')^).
    - exact H.
    - intros x y p q. refine (grp_homo_op_agree f f' _ q).
      lhs nrapply grp_homo_inv.
      rhs nrapply grp_homo_inv.
      exact (ap _ p).
  Defined.

  (** Now we need to prove that the free group satisifes the unviersal property of the free group. *)
  (** TODO: remove funext from here and universal property of free group *)
  Global Instance isfreegroupon_freegroup `{Funext}
    : IsFreeGroupOn A FreeGroup freegroup_in.
  Proof.
    intros G f.
    snrapply Build_Contr.
    { srefine (_;_); simpl.
      1: apply FreeGroup_rec, f.
      intro x; reflexivity. }
    intros [g h].
    nrapply path_sigma_hprop; [ exact _ |].
    simpl.
    apply equiv_path_grouphomomorphism.
    symmetry.
    snrapply FreeGroup_ind_homotopy.
    exact h.
  Defined.

  (** Typeclass search can already find this but we leave it here as a definition for reference. *)
  Definition isfreegroup_freegroup `{Funext} : IsFreeGroup FreeGroup := _.

End Reduction.

Arguments FreeGroup_rec {A G}.
Arguments FreeGroup_ind_homotopy {A G f f'}.
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
  1: exact (hfiber (fun f x => grp_homo_map f (i x)) g).
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
      exact (ap grp_homo_map is_retraction).
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

(** ** Properties of recursor *)

Definition freegroup_rec_in {A : Type}
  : FreeGroup_rec freegroup_in $== Id (FreeGroup A).
Proof.
  by snrapply FreeGroup_ind_homotopy.
Defined.

Definition freegroup_rec_compose {A B : Type}
  (f : A -> FreeGroup B) {G : Group} (i : FreeGroup B $-> G)
  : FreeGroup_rec (i o f) $== i $o FreeGroup_rec f.
Proof.
  by snrapply FreeGroup_ind_homotopy; intros x.
Defined.

Definition freegroup_const {A : Type} {G : Group}
  : FreeGroup_rec (fun _ : A => 1) $== @grp_homo_const _ G.
Proof.
  by snrapply FreeGroup_ind_homotopy.
Defined.
  
(** ** Functoriality *)

Global Instance is0functor_freegroup : Is0Functor FreeGroup.
Proof.
  snrapply Build_Is0Functor.
  intros X Y f.
  snrapply FreeGroup_rec.
  exact (freegroup_in o f).
Defined.

Global Instance is1functor_freegroup : Is1Functor FreeGroup.
Proof.
  snrapply Build_Is1Functor.
  - intros X Y f g p.
    snrapply FreeGroup_ind_homotopy.
    intros x.
    exact (ap freegroup_in (p x)).
  - intro; nrapply freegroup_rec_in.
  - intros X Y Z f g.
    by snrapply FreeGroup_ind_homotopy.
Defined.
