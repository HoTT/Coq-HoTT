Require Import Basics Types WildCat.Core WildCat.Universe HFiber.
Require Import Modalities.Modality.
(** Users of this file almost always want to be able to write [Tr n] for both a [Modality] and a [ReflectiveSubuniverse], so they want the coercion [modality_to_reflective_subuniverse]: *)
Require Export (coercions) Modalities.Modality.

(** * Truncations of types *)

Local Open Scope path_scope.
Generalizable Variables A X n.

(** ** The definition *)

(** The definition of [Trunc n], the n-truncation of a type.

If Coq supported higher inductive types natively, we would construct this as something like:

   Inductive Trunc n (A : Type) : Type :=
   | tr : A -> Trunc n A
   | istrunc_truncation : forall (f : Sphere n.+1 -> Trunc n A)
       (x : Sphere n.+1), f x = f North.

However, while we are faking our higher-inductives anyway, we can take some shortcuts, rather than translating the definition above.  Firstly, we directly posit a “constructor” giving truncatedness, rather than rephrasing it in terms of maps of spheres.  Secondly, we omit the “computation rule” for this constructor, since it is implied by truncatedness of the result type (and, for essentially that reason, is never wanted in practice anyway).
*)

Module Export Trunc.

  Cumulative Private Inductive Trunc (n : trunc_index) (A :Type) : Type :=
    tr : A -> Trunc n A.
  Arguments tr {n A} a.

  (** Without explicit universe parameters, this instance is insufficiently polymorphic. *)
  Global Instance istrunc_truncation (n : trunc_index) (A : Type@{i})
    : IsTrunc@{j} n (Trunc@{i} n A).
  Admitted.

  Definition Trunc_ind {n A}
    (P : Trunc n A -> Type) {Pt : forall aa, IsTrunc n (P aa)}
    : (forall a, P (tr a)) -> (forall aa, P aa)
    := fun f aa => match aa with tr a => fun _ => f a end Pt.

End Trunc.

(** The non-dependent version of the eliminator. *)

Definition Trunc_rec {n A X} `{IsTrunc n X}
  : (A -> X) -> (Trunc n A -> X)
  := Trunc_ind (fun _ => X).

Definition Trunc_rec_tr n {A : Type}
  : Trunc_rec (A:=A) (tr (n:=n)) == idmap
  := Trunc_ind _ (fun a => idpath).

(** ** [Trunc] is a modality *)

Definition Tr (n : trunc_index) : Modality.
Proof.
  srapply (Build_Modality (fun A => IsTrunc n A)); cbn.
  - intros A B ? f ?; rapply (istrunc_isequiv_istrunc A f).
  - exact (Trunc n).
  - intros; apply istrunc_truncation.
  - intros A; apply tr.
  - intros A B ? f oa; cbn in *.
    exact (Trunc_ind B f oa).
  - intros; reflexivity.
  - exact (@istrunc_paths' n).
Defined.

(** We don't usually declare modalities as coercions, but this particular one is convenient so that lemmas about (for instance) connected maps can be applied to truncation modalities without the user/reader needing to be (particularly) aware of the general notion of modality. *)
Coercion Tr : trunc_index >-> Modality.
(** However, if the coercion is not printed, then we get things like [Tr (-1) X] being printed as [(-1) X], which is terribly confusing.  So we tell Coq to always print this coercion.  This does mean that although the user can type things like [IsConnected n X], it will always be displayed back as [IsConnected (Tr n) X]. *)
Add Printing Coercion Tr.

Section TruncationModality.
  Context (n : trunc_index).

  Definition trunc_iff_isequiv_truncation (A : Type)
    : IsTrunc n A <-> IsEquiv (@tr n A)
    := inO_iff_isequiv_to_O (Tr n) A.

  Global Instance isequiv_tr A `{IsTrunc n A} : IsEquiv (@tr n A)
    := fst (trunc_iff_isequiv_truncation A) _.

  Definition equiv_tr (A : Type) `{IsTrunc n A}
    : A <~> Tr n A
  := Build_Equiv _ _ (@tr n A) _.

  Definition untrunc_istrunc {A : Type} `{IsTrunc n A}
    : Tr n A -> A
    := (@tr n A)^-1.

  (** ** Functoriality *)

  (** Since a modality lives on a single universe, by default if we simply define [Trunc_functor] to be [O_functor] then it would force [X] and [Y] to live in the same universe.  But since we defined [Trunc] as a cumulative inductive, if we add universe annotations we can make [Trunc_functor] more universe-polymorphic than [O_functor] is.  This is sometimes useful.  *)
  Definition Trunc_functor@{i j k | i <= k, j <= k} {X : Type@{i}} {Y : Type@{j}} (f : X -> Y)
    : Tr@{i} n X -> Tr@{j} n Y
    := O_functor@{k k k} (Tr n) f.

  Global Instance is0functor_Tr : Is0Functor (Tr n)
    := Build_Is0Functor _ _ _ _ (Tr n) (@Trunc_functor).

  Global Instance Trunc_functor_isequiv {X Y : Type}
    (f : X -> Y) `{IsEquiv _ _ f}
    : IsEquiv (Trunc_functor f)
    := isequiv_O_functor (Tr n) f.

  Definition Trunc_functor_equiv {X Y : Type} (f : X <~> Y)
    : Tr n X <~> Tr n Y
    := equiv_O_functor (Tr n) f.

  Definition Trunc_functor_compose {X Y Z} (f : X -> Y) (g : Y -> Z)
    : Trunc_functor (g o f) == Trunc_functor g o Trunc_functor f
    := O_functor_compose (Tr n) f g.

  Definition Trunc_functor_idmap (X : Type)
    : @Trunc_functor X X idmap == idmap
    := O_functor_idmap (Tr n) X.

  Definition equiv_Trunc_prod_cmp {X Y}
    : Tr n (X * Y) <~> Tr n X * Tr n Y
    := equiv_O_prod_cmp (Tr n) X Y.

  Global Instance is1functor_Tr : Is1Functor (Tr n).
  Proof.
    apply Build_Is1Functor.
    - apply @O_functor_homotopy.
    - apply @Trunc_functor_idmap.
    - apply @Trunc_functor_compose.
  Defined.

End TruncationModality.

(** We have to teach Coq to translate back and forth between [IsTrunc n] and [In (Tr n)]. *)
Global Instance inO_tr_istrunc {n : trunc_index} (A : Type) `{IsTrunc n A}
  : In (Tr n) A.
Proof.
  assumption.
Defined.

(** Having both of these as [Instance]s would cause infinite loops. *)
Definition istrunc_inO_tr {n : trunc_index} (A : Type) `{In (Tr n) A}
  : IsTrunc n A.
Proof.
  assumption.
Defined.

(** Instead, we make the latter an immediate instance, but with high cost (i.e. low priority) so that it doesn't override the ordinary lemmas about truncation.  Unfortunately, [Hint Immediate] doesn't allow specifying a cost, so we use [Hint Extern] instead. *)
(** Hint Immediate istrunc_inO_tr : typeclass_instances. *)
(** See https://github.com/coq/coq/issues/11697 *)
#[export]
Hint Extern 1000 (IsTrunc _ _) => simple apply istrunc_inO_tr; solve [ trivial ] : typeclass_instances.
(** This doesn't seem to be quite the same as [Hint Immediate] with a different cost either, though.  *)

(** Unfortunately, this isn't perfect; Coq still can't always find [In n] hypotheses in the context when it wants [IsTrunc].  You can always apply [istrunc_inO_tr] explicitly, but sometimes it also works to just [pose] it into the context. *)

(** We do the same for [IsTruncMap n] and [MapIn (Tr n)]. *)
Global Instance mapinO_tr_istruncmap {n : trunc_index} {A B : Type}
  (f : A -> B) `{IsTruncMap n A B f}
  : MapIn (Tr n) f.
Proof.
  assumption.
Defined.

Definition istruncmap_mapinO_tr {n : trunc_index} {A B : Type}
  (f : A -> B) `{MapIn (Tr n) _ _ f}
  : IsTruncMap n f.
Proof.
  assumption.
Defined.

#[export]
Hint Immediate istruncmap_mapinO_tr : typeclass_instances.

(** ** A few special things about the (-1)-truncation *)

Local Open Scope trunc_scope.

(** We define [merely A] to be an inhabitant of the universe [hProp] of hprops, rather than a type.  We can always treat it as a type because there is a coercion, but this means that if we need an element of [hProp] then we don't need a separate name for it. *)

Definition merely (A : Type@{i}) : HProp@{i} := Build_HProp (Tr (-1) A).

Definition hexists {X} (P : X -> Type) : HProp := merely (sig P).

Definition hor (P Q : Type) : HProp := merely (P + Q).

Declare Scope hprop_scope.
Notation "A \/ B" := (hor A B) : hprop_scope.

Definition himage {X Y} (f : X -> Y) := image (Tr (-1)) f.

Definition contr_inhab_prop {A} `{IsHProp A} (ma : merely A) : Contr A.
Proof.
  refine (@contr_trunc_conn (Tr (-1)) A _ _); try assumption.
  refine (contr_inhabited_hprop _ ma).
Defined.

(** A stable type is logically equivalent to its (-1)-truncation. (It follows that this is true for decidable types as well.) *)
Definition merely_inhabited_iff_inhabited_stable {A} {A_stable : Stable A}
  : Tr (-1) A <-> A.
Proof.
  refine (_, tr).
  intro ma.
  apply stable; intro na.
  revert ma; rapply Trunc_ind; exact na.
Defined.

(** ** Surjections *)

(** Surjections are the (-1)-connected maps, but they can be characterized more simply since an inhabited hprop is automatically contractible. *)
Notation IsSurjection := (IsConnMap (Tr (-1))).

Definition BuildIsSurjection {A B} (f : A -> B)
  : (forall b, merely (hfiber f b)) -> IsSurjection f.
Proof.
  intros H b; refine (contr_inhabited_hprop _ _).
  apply H.
Defined.

(** A family of types is pointwise merely inhabited if and only if the corresponding fibration is surjective. *)
Lemma iff_merely_issurjection {X : Type} (P : X -> Type)
  : (forall x, merely (P x)) <-> IsSurjection (pr1 : {x : X & P x} -> X).
Proof.
  refine (iff_compose _ (iff_forall_inO_mapinO_pr1 (Conn _) P)).
  apply iff_functor_forall; intro a.
  symmetry; apply (iff_contr_hprop (Tr (-1) (P a))).
Defined.

Lemma equiv_merely_issurjection `{Funext} {X : Type} (P : X -> Type)
  : (forall x, merely (P x)) <~> IsSurjection (pr1 : {x : X & P x} -> X).
Proof. (* Can also be proved from equiv_forall_inO_mapinO_pr1. *)
  exact (equiv_iff_hprop_uncurried (iff_merely_issurjection P)).
Defined.

(** Surjections cancel on the right *)
Lemma cancelR_issurjection {A B C : Type} (f : A -> B) (g : B -> C)
      (isconn : IsSurjection (g o f))
  : IsSurjection g.
Proof.
  intro c.
  rapply contr_inhabited_hprop.
  rapply (Trunc_functor _ (X:= (hfiber (g o f) c))).
  - intros [a p].
    exact (f a; p).
  - apply center, isconn.
Defined.

(** Retractions are surjective. *)
Definition issurj_retr {X Y : Type} {r : X -> Y} (s : Y -> X) (h : forall y:Y, r (s y) = y)
  : IsSurjection r.
Proof.
  intro y.
  rapply contr_inhabited_hprop.
  exact (tr (s y; h y)).
Defined.

(** ** Embeddings *)

(** Since embeddings are the (-1)-truncated maps, a map that is both a surjection and an embedding is an equivalence. *)
Definition isequiv_surj_emb {A B} (f : A -> B)
  `{IsSurjection f} `{IsEmbedding f}
  : IsEquiv f.
Proof.
  apply (@isequiv_conn_ino_map (Tr (-1))); assumption.
Defined.

(** As a corollary, it follows that if [i o f] is an equivalence and [i] is an embedding, then [f] is an equivalence. *)
Definition isequiv_isequiv_compose_embedding {X Y Z : Type}
  {f : X -> Y} (i : Y -> Z) `{IsEmbedding i}
  `{!IsEquiv (i o f)}
  : IsEquiv f.
Proof.
  rapply (cancelL_isequiv i).
  refine (isequiv_surj_emb i).
  rapply (cancelR_issurjection f).
Defined.

(** If [X] is a set and [f : Y -> Z] is a surjection, then [- o f] is an embedding. *)
Definition isembedding_precompose_surjection_hset `{Funext} {X Y Z : Type}
  `{IsHSet X} (f : Y -> Z) `{IsSurjection f}
  : IsEmbedding (fun phi : Z -> X => phi o f).
Proof.
  intros phi; apply istrunc_S.
  intros g0 g1; cbn.
  rapply contr_inhabited_hprop.
  apply path_sigma_hprop, equiv_path_arrow.
  rapply conn_map_elim; intro y.
  exact (ap10 (g0.2 @ g1.2^) y).
Defined.

(** We next prove that [paths : X -> (X -> Type)] is an embedding. This was proved by Escardo as Lemma 15 in "Injective types in univalent mathematics", but we give an argument similar to the proof of Thm 2.25 of CORS. *)

(** This will be an inverse to [ap paths].  We'll want to show that it is an embedding, so we'll construct it out of pieces that are clearly equivalences, except for one step, [equiv_fun]. *)
Definition ap_paths_inverse `{Univalence} {X : Type} (x1 x2 : X)
  : paths x1 = paths x2 -> x1 = x2.
Proof.
  refine (_ o @equiv_ap10 _ X Type (paths x1) (paths x2)).
  refine (_ o equiv_functor_forall_id (fun y => equiv_equiv_path (x1 = y) (x2 = y))).
  refine (_ o functor_forall_id (fun y => @equiv_fun (x1 = y) (x2 = y))).
  refine (_ o (equiv_paths_ind x1 (fun y p => x2 = y))^-1%equiv).
  exact (equiv_path_inverse x2 x1).
Defined.

(** A Yoneda-like embedding for path types: [paths : X -> (X -> Type)] is an embedding. *)
Definition isembedding_paths `{Univalence} {X : Type@{u}} : IsEmbedding (@paths X).
Proof.
  (* To show that [paths] is an embedding, it suffices to show that [ap paths : x1 = x2 -> (paths x1) = (paths x2)] is an equivalence. *)
  snrapply isembedding_isequiv_ap.
  intros x1 x2.
  (* And for that, it suffices to show that [i o (ap paths)] is an equivalence for a well-chosen embedding [i]. *)
  snrapply (isequiv_isequiv_compose_embedding (ap_paths_inverse x1 x2)).
  - (* [ap_paths_inverse x1 x2] is an embedding since it is a composite of four equivalences and one embedding.  We can group these into three parts. *)
    unfold ap_paths_inverse.
    nrefine (mapinO_compose (O:=Tr (-1)) _ (equiv_path_inverse x2 x1 oE _)).
    2: exact _. (* The second part is an equivalence, so it's an embedding. *)
    nrefine (mapinO_compose _ (functor_forall_id _)).
    1: exact _. (* The first part is an equivalence, so it's an embedding. *)
    rapply mapinO_functor_forall_id.
    intro y.
    apply isembedding_equiv_fun.
  - (* The composite is an equivalence because it is homotopic to the identity. *)
    simpl.
    srapply (isequiv_homotopic idmap).
    intros [].
    reflexivity.
Defined.

(** ** Tactic to remove truncations in hypotheses if possible *)

Ltac strip_truncations :=
  (** search for truncated hypotheses *)
  progress repeat
    match goal with
    | [ T : _ |- _ ]
      => revert_opaque T;
        refine (@Trunc_ind _ _ _ _ _);
        (** ensure that we didn't generate more than one subgoal, i.e. that the goal was appropriately truncated *)
        [];
        intro T
  end.

(** See [strip_reflections] and [strip_modalities] for generalizations to other reflective subuniverses and modalities.  We provide this version because it sometimes needs fewer universes (due to the cumulativity of [Trunc]).  However, that same cumulativity sometimes causes free universe variables.  For a hypothesis of type [Trunc@{i} X], we can use [Trunc_ind@{i j}], but sometimes Coq uses [Trunc_ind@{k j}] with [i <= k] and [k] otherwise free.  In these cases, [strip_reflections] and/or [strip_modalities] may generate fewer universe variables. *)

(** ** Iterated truncations *)

(** Compare to [O_leq_Tr] and [O_strong_leq_Tr] in SeparatedTrunc.v. *)
Definition O_leq_Tr_leq {n m : trunc_index} (Hmn : m <= n)
  : O_leq (Tr m) (Tr n).
Proof.
  intros A; rapply istrunc_leq.
Defined.

Definition Trunc_min n m X : Tr (trunc_index_min n m) X <~> Tr n (Tr m X).
Proof.
  destruct (trunc_index_min_path n m) as [p|q].
  + assert (l := trunc_index_min_leq_right n m).
    destruct p^; clear p.
    snrapply (Build_Equiv _ _ (Trunc_functor _ tr)).
    nrapply O_inverts_conn_map.
    rapply (conn_map_O_leq _ (Tr m)).
    rapply O_leq_Tr_leq.
  + assert (l := trunc_index_min_leq_left n m).
    destruct q^; clear q.
    srapply equiv_tr.
    srapply istrunc_leq.
Defined.

Definition Trunc_swap n m X : Tr n (Tr m X) <~> Tr m (Tr n X).
Proof.
  refine (Trunc_min m n _ oE equiv_transport (fun k => Tr k _) _ oE (Trunc_min n m _)^-1).
  apply trunc_index_min_swap.
Defined.

(** If you are looking for a theorem about truncation, you may want to read the note "Finding Theorems" in "STYLE.md". *)
