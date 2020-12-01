(* -*- mode: coq; mode: visual-line -*- *)

Require Import Basics Types.
Require Import TruncType HProp.
Require Import Modalities.Modality Modalities.Descent.

(** * Truncations of types, in all dimensions. *)

Local Open Scope path_scope.
Generalizable Variables A X n.

(** ** Definition. *)

(** The definition of [Trunc n], the n-truncation of a type.

If Coq supported higher inductive types natively, we would construct this as somthing like:

   Inductive Trunc n (A : Type) : Type :=
   | tr : A -> Trunc n A
   | istrunc_truncation : forall (f : Sphere n.+1 -> Trunc n A)
       (x : Sphere n.+1), f x = f North.

However, while we are faking our higher-inductives anyway, we can take some shortcuts, rather than translating the definition above.  Firstly, we directly posit a “constructor” giving truncatedness, rather than rephrasing it in terms of maps of spheres.  Secondly, we omit the “computation rule” for this constructor, since it is implied by truncatedness of the result type (and, for essentially that reason, is never wanted in practice anyway).
*)

Module Export Trunc.
Delimit Scope trunc_scope with trunc.

Cumulative Private Inductive Trunc (n : trunc_index) (A :Type) : Type :=
  tr : A -> Trunc n A.
Bind Scope trunc_scope with Trunc.
Arguments tr {n A} a.

(** Without explicit universe parameters, this instance is insufficiently polymorphic. *)
Global Instance istrunc_truncation (n : trunc_index) (A : Type@{i})
: IsTrunc@{j} n (Trunc@{i} n A).
Admitted.

Definition Trunc_ind {n A}
  (P : Trunc n A -> Type) {Pt : forall aa, IsTrunc n (P aa)}
  : (forall a, P (tr a)) -> (forall aa, P aa)
:= (fun f aa => match aa with tr a => fun _ => f a end Pt).

End Trunc.

(** The non-dependent version of the eliminator. *)

Definition Trunc_rec {n A X} `{IsTrunc n X}
  : (A -> X) -> (Trunc n A -> X)
:= Trunc_ind (fun _ => X).

(** ** [Trunc] is a modality *)

Definition Tr (n : trunc_index) : Modality.
Proof.
  srapply (Build_Modality (IsTrunc n)).
  - intros A B ? f ?; apply (trunc_equiv A f).
  - exact (Trunc n).
  - intros; apply istrunc_truncation.
  - intros A; apply tr.
  - intros A B ? f oa; cbn in *.
    exact (Trunc_ind B f oa).
  - intros; reflexivity.
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
  Definition Trunc_functor@{i j k} {X : Type@{i}} {Y : Type@{j}} (f : X -> Y)
    : Tr@{i} n X -> Tr@{j} n Y
    := O_functor@{k k k} (Tr n) f.

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

  Definition isequiv_Trunc_functor {X Y} (f : X -> Y) `{IsEquiv _ _ f}
    : IsEquiv (Trunc_functor f)
    := isequiv_O_functor (Tr n) f.

  Definition equiv_Trunc_prod_cmp `{Funext} {X Y}
    : Tr n (X * Y) <~> Tr n X * Tr n Y
    := equiv_O_prod_cmp (Tr n) X Y.

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
Hint Extern 1000 (IsTrunc _ _) => simple apply istrunc_inO_tr; solve [ trivial ] : typeclass_instances.
(** This doesn't seem to be quite the same as [Hint Immediate] with a different cost either, though; see the comment in the proof of [Trunc_min] below.  *)

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

Hint Immediate istruncmap_mapinO_tr : typeclass_instances.

(** ** A few special things about the (-1)-truncation. *)

Local Open Scope trunc_scope.

(** We define [merely A] to be an inhabitant of the universe [hProp] of hprops, rather than a type.  We can always treat it as a type because there is a coercion, but this means that if we need an element of [hProp] then we don't need a separate name for it. *)

Definition merely (A : Type@{i}) : hProp@{i} := BuildhProp (Tr (-1) A).

Definition hexists {X} (P : X -> Type) : hProp := merely (sigT P).

Definition hor (P Q : Type) : hProp := merely (P + Q).

Notation "A \/ B" := (hor A B) : type_scope.

Definition himage {X Y} (f : X -> Y) := image (Tr (-1)) f.

Definition contr_inhab_prop {A} `{IsHProp A} (ma : merely A) : Contr A.
Proof.
  refine (@contr_trunc_conn (Tr (-1)) A _ _); try assumption.
  refine (contr_inhabited_hprop _ ma).
Defined.

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

Definition isequiv_surj_emb {A B} (f : A -> B)
  `{IsSurjection f} `{IsEmbedding f}
  : IsEquiv f.
Proof.
  apply (@isequiv_conn_ino_map (Tr (-1))); assumption.
Defined.

(** ** Tactic to remove truncations in hypotheses if possible. *)
Ltac strip_truncations :=
  (** search for truncated hypotheses *)
  progress repeat match goal with
                    | [ T : _ |- _ ]
                      => revert_opaque T;
                        refine (@Trunc_ind _ _ _ _ _);
                        (** ensure that we didn't generate more than one subgoal, i.e. that the goal was appropriately truncated *)
                        [];
                        intro T
                  end.

(** ** Iterated truncations *)

Definition Trunc_min n m X : Tr n (Tr m X) <~> Tr (trunc_index_min n m) X.
Proof.
  destruct (trunc_index_min_path n m) as [p|q].
  + assert (l := trunc_index_min_leq_right n m).
    destruct p^; clear p.
    symmetry.
    srapply equiv_adjointify.
    { srapply Trunc_rec.
      exact (fun x => tr (tr x)). }
    { srapply Trunc_rec.
      srapply Trunc_rec.
      1: srapply trunc_leq.
      exact tr. }
    { srapply Trunc_ind.
      simpl.
      srapply (Trunc_ind (n:=m)).
      2: reflexivity.
      intro.
      apply istrunc_paths.
      srapply (trunc_leq (m:=n)).
      by apply trunc_index_leq_succ'. }
    srapply Trunc_ind; reflexivity.
  + set (min := trunc_index_min n m).
    refine (paths_ind _
      (fun m _ => Tr n (Tr m X) <~> Tr min X) _ m q).
    unfold min; clear min.
    symmetry.
    srapply equiv_tr.
    srapply trunc_leq.
    3:{ (** Strangely, if [istrunc_inO_tr] were a [Hint Immediate], rather than our [Hint Extern], then typeclass inference would be able to find this all on its own, although the documentation for [Hint Immediate] suggests that it shouldn't because the following tactic doesn't solve it completely. *)
        simple apply istrunc_inO_tr; trivial.
        exact _. }
    apply trunc_index_min_leq_left.
Defined.

Definition Trunc_swap n m X : Tr n (Tr m X) <~> Tr m (Tr n X).
Proof.
  refine (_ oE equiv_transport (fun x => Tr x _) _ _ _ oE Trunc_min n m _).
  2: apply trunc_index_min_swap.
  symmetry.
  apply Trunc_min.
Defined.

(** ** Separatedness and path-spaces of truncations *)

Section SeparatedTrunc.

Local Open Scope subuniverse_scope.

(** The [n.+1]-truncation modality consists of the separated types for the [n]-truncation modality. *)
Global Instance O_eq_Tr (n : trunc_index)
  : Tr n.+1 <=> Sep (Tr n).
Proof.
  split; intros A A_inO.
  - intros x y; exact _.
  - exact _.
Defined.

(** It follows that [Tr n <<< Tr n.+1].  However, it is easier to prove this directly than to go through separatedness. *)
Global Instance O_leq_Tr (n : trunc_index)
  : Tr n <= Tr n.+1.
Proof.
  intros A ?; exact _.
Defined.

Global Instance O_strong_leq_Tr (n : trunc_index)
  : Tr n << Tr n.+1.
Proof.
  srapply O_strong_leq_trans_l.
Defined.

(** For some reason, this causes typeclass search to spin. *)
Local Instance O_lex_leq_Tr `{Univalence} (n : trunc_index)
  : Tr n <<< Tr n.+1.
Proof.
  intros A; unshelve econstructor; intros P' P_inO; pose (P := fun x => BuildTruncType n (P' x)).
  - refine (Trunc_rec P).
  - intros; exact _.
  - intros; cbn. reflexivity.
Defined.

Definition path_Tr {n A} (x y : A)
  : Tr n (x = y) -> (tr x = tr y :> Tr n.+1 A)
  := path_OO (Tr n.+1) (Tr n) x y.

Definition equiv_path_Tr `{Univalence} {n A} (x y : A)
  : Tr n (x = y) <~> (tr x = tr y :> Tr n.+1 A)
  := equiv_path_OO (Tr n.+1) (Tr n) x y.

End SeparatedTrunc.

(** If you are looking for a theorem about truncation, you may want to read the note "Finding Theorems" in "STYLE.md". *)
