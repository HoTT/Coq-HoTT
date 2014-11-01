(* -*- mode: coq; mode: visual-line -*- *)

(** * Truncations of types, in all dimensions. *)

Require Import HoTT.Basics Types.Sigma ReflectiveSubuniverse Modality TruncType HProp.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
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

Private Inductive Trunc (n : trunc_index) (A :Type) : Type :=
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

(** Trunc is a modality *)

Section TruncationModality.
  Context (n : trunc_index).

  (** Without a universe annotation here, the two universe parameters of [Modality] get collapsed. *)
  Definition Tr : Modality@{sm lg}.
  Proof.
    refine (Build_Modality
              (Build_UnitSubuniverse
                 (Trunc@{sm} n)
                 (IsTrunc@{lg} n)
                 _
                 (@tr n)
                 (** Again, we have to use [Lift'] to prevent the universes from getting collapsed. *)
                 (fun A B Atr f feq =>
                    (@trunc_equiv (Lift'@{sm lg} A) (Lift'@{sm lg} B)
                                  (lift'@{sm lg} o f o lift'@{sm lg}^-1) n _ _))
                 _)
              (@Trunc_ind n)
              (fun A B B_inO f a => 1)
              _); cbn; try exact _.
  Defined.

  Definition trunc_iff_isequiv_truncation (A : Type)
  : IsTrunc n A <-> IsEquiv (@tr n A)
  := @inO_iff_isequiv_to_O Tr A.

  Global Instance isequiv_tr A `{IsTrunc n A} : IsEquiv (@tr n A)
  := fst (trunc_iff_isequiv_truncation A) _.

  Definition equiv_tr (A : Type) `{IsTrunc n A}
  : A <~> Trunc n A
  := BuildEquiv _ _ (@tr n A) _.

  Definition untrunc_istrunc {A : Type} `{IsTrunc n A}
  : Trunc n A -> A
  := (@tr n A)^-1.

  (** ** Functoriality *)

  (* This ought to be [O_functor], but currently that would be insufficiently universe polymorphic. *)
  Definition Trunc_functor {X Y} (f : X -> Y)
  : Trunc n X -> Trunc n Y
  := Trunc_rec (tr o f).

  Definition Trunc_functor_compose {X Y Z} (f : X -> Y) (g : Y -> Z)
  : Trunc_functor (g o f) == Trunc_functor g o Trunc_functor f
  := O_functor_compose Tr f g.

  Definition Trunc_functor_idmap (X : Type)
  : @Trunc_functor X X idmap == idmap
  := O_functor_idmap Tr X.

  Definition isequiv_Trunc_functor {X Y} (f : X -> Y) `{IsEquiv _ _ f}
  : IsEquiv (Trunc_functor f)
  := isequiv_O_functor Tr f.

  Definition equiv_Trunc_prod_cmp `{Funext} {X Y}
  : Trunc n (X * Y) <~> Trunc n X * Trunc n Y
  := equiv_O_prod_cmp Tr X Y.

End TruncationModality.

(** This coercion allows us to use truncation indices where a modality is expected and refer to the corresponding truncation modality.  For instance, the general theory of O-connected maps specializes to the theory of n-connected maps. *)
Coercion Tr : trunc_index >-> Modality.

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

(* Instead, we make the latter an immediate instance. *)
Hint Immediate istrunc_inO_tr : typeclass_instances.

(* Unfortunately, this isn't perfect; Coq still can't always find [In Tr] hypotheses in the context when it wants [IsTrunc]. *)


(** It's sometimes convenient to use "infinity" to refer to the identity modality in a similar way.  This clashes with some uses in higher topos theory, where "oo-truncated" means instead "hypercomplete", but this has not yet been a big problem. *)
Notation oo := purely.

(** ** A few special things about the (-1)-truncation. *)

Local Open Scope trunc_scope.

(** This definition is doubly sneaky.  Firstly, we define [merely A] to be an inhabitant of the universe [hProp] of hprops, rather than a type.  We can always treat it as a type because there is a coercion, but this means that if we need an element of [hProp] then we don't need a separate name for it.  Secondly, rather than define it as [Trunc -1] we define it as [Tr -1], the action of the truncation modality.  These are of course judgmentally equal, but choosing the latter means that Coq has an easier time applying general modality theorems to it. *)
Definition merely A : hProp := BuildhProp (Tr -1 A).

Definition hexists {X} (P : X -> Type) : hProp := merely (sigT P).

Definition hor (P Q : Type) : hProp := merely (P + Q).

Definition contr_inhab_prop {A} `{IsHProp A} (ma : merely A) : Contr A.
Proof.
  refine (@contr_trunc_conn -1 A _ _); try assumption.
  refine (contr_inhabited_hprop _ ma).
Defined.

(** Surjections are the (-1)-connected maps, but they can be characterized more simply since an inhabited hprop is automatically contractible. *)
Notation IsSurjection := (IsConnMap -1).

Definition BuildIsSurjection {A B} (f : A -> B) :
  (forall b, merely (hfiber f b)) -> IsSurjection f.
Proof.
  intros H b; refine (contr_inhabited_hprop _ _).
  apply H.
Defined.

Definition isequiv_surj_emb {A B} (f : A -> B)
           `{IsSurjection f} `{IsEmbedding f}
: IsEquiv f.
Proof.
  apply (@isequiv_conn_ino_map -1); assumption.
Defined.


(** ** Tactic to remove truncations in hypotheses if possible. *)
Ltac strip_truncations :=
  (** search for truncated hypotheses *)
  progress repeat match goal with
                    | [ T : _ |- _ ]
                      => revert T;
                        refine (@Trunc_ind _ _ _ _ _);
                        (** ensure that we didn't generate more than one subgoal, i.e. that the goal was appropriately truncated *)
                        [];
                        intro T
                  end.
