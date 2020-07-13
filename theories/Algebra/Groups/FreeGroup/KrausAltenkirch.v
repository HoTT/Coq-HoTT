Require Import Basics Types.
Require Import Groups.Group.
Require Import Truncations.
Require Import HIT.Coeq.

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

(** In this file we construct the free abelian group on a type [A] as a higher inductive type. This construction is due to Kraus and Altenkirch. Their construction is actually more general, but we set truncate it to suit our needs which is the free group as a set. *)

Section Reduction.

  Context (A : Type).

  (** We define words (with inverses) on A to be lists of marked elements of A *)
  Definition Words : Type := list (A + A).

  (** Given a marked element of A we can change its mark *)
  Definition change_sign : A + A -> A + A
    := fun x => match x with
                | inl a => inr a
                | inr a => inl a
                end.

  (** We introduce a local notation for [change_sign]. It is only defined in this section however. *)
  Notation "x ^" := (change_sign x).

  (** Changing sign is an involution *)
  Definition change_sign_inv a : a^^ = a.
  Proof.
    by destruct a.
  Defined.

  (** We can concatenate words using list concatenation *)
  Definition word_concat : Words -> Words -> Words := @app _.

  (** We introduce a local notation for word_concat. *)
  Infix "@" := word_concat.

  Definition word_concat_w_nil x : x @ nil = x.
  Proof.
    induction x; trivial.
    cbn; f_ap.
  Defined.

  Definition word_concat_w_ww x y z : x @ (y @ z) = (x @ y) @ z.
  Proof.
    revert x z.
    induction y; intros x z.
    { f_ap; symmetry.
      apply word_concat_w_nil. }
    simpl; revert z y IHy.
    induction x; trivial.
    intros z y IHy.
    simpl; f_ap.
    apply IHx, IHy.
  Defined.

  (** Singleton word *)
  Definition word_sing (x : A + A) : Words := (cons x nil).

  Notation "[ x ]" := (word_sing x).

  (** We define an inductive family [Red] on [Words] which expresses whether a given word can be reduced to the empty list *)
  Inductive Red : Words -> Type :=
    | red_zero : Red nil
    | red_step (y z : Words) (a : A + A)
      : Red (y @ z) -> Red (y @ [a] @ [a^] @ z).

  (** Now we wish to define the free group on A as the following HIT: 

    HIT N(A) : hSet
     | eta : Words -> N(A)
     | tau (x : Words) (a : A + A) (y : Words)
         : eta (x @ [a] @ [a^] @ y) = eta (x @ y).

    Since we cannot write our HITs directly like this (without resorting to private inductive types), we will construct this HIT out of HITs we know. In fact, we can define N(A) as a coequalizer. *)

  Definition map1 : Words * (A + A) * Words -> Words.
  Proof.
    intros [[x a] y].
    exact (x @ [a] @ [a^] @ y).
  Defined.

  Definition map2 : Words * (A + A) * Words -> Words.
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
(*      apply tr. *)
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
    cbn.
    set (a' := a^).
    rewrite <- (change_sign_inv a).
    change a^ with a'.
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
    cbn; apply ap.
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

  Lemma words_rec_coh (G : Group) (s : A -> G) (a : A + A) (b c : Words)
    : words_rec G s (map1 (b, a, c)) = words_rec G s (map2 (b, a, c)).
  Proof.
    
  Admitted.

  Lemma words_rec_pp  (G : Group) (s : A -> G)  (x y : Words)
    : words_rec G s (x @ y) = words_rec G s x * words_rec G s y.
  Proof.
    induction x.
    1: symmetry; apply left_identity.
    cbn; rewrite <- simple_associativity.
    f_ap.
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
  Definition isfreegroup_freegrup `{Funext} : IsFreeGroup FreeGroup := _.

End Reduction.




