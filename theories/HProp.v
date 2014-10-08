(** * HPropositions *)

Require Import HoTT.Basics.
Require Import types.Forall types.Sigma types.Prod types.Record types.Paths types.Unit types.Empty.

Local Open Scope equiv_scope.
Local Open Scope path_scope.

(** ** Facts about [IsHProp] *)

(** Maybe this should go to a separate file? *)

Generalizable Variables A B.

(** An inhabited proposition is contractible.
   This is not an [Instance] because it causes infinite loops.
   *)
Lemma contr_inhabited_hprop (A : Type) `{H : IsHProp A} (x : A)
  : Contr A.
Proof.
  exists x.
  intro y.
  apply center, H.
Defined.

(** If inhabitation implies contractibility, then we have an h-proposition.  We probably won't often have a hypothesis of the form [A -> Contr A], so we make sure we give priority to other instances. *)
Global Instance hprop_inhabited_contr (A : Type) : (A -> Contr A) -> IsHProp A | 10000.
Proof.
  intros H x y.
  pose (C := H x).
  apply contr_paths_contr.
Defined.

(** If a type is contractible, then so is its type of contractions.
    Using [issig_contr] and the [equiv_intro] tactic, we can transfer this to the equivalent problem of contractibility of a certain Sigma-type, in which case we can apply the general path-construction functions. *)
Global Instance contr_contr `{Funext} (A : Type)
  : Contr A -> Contr (Contr A) | 100.
Proof.
  intros c; exists c; generalize c.
  equiv_intro (issig_contr A) c'.
  equiv_intro (issig_contr A) d'.
  refine (ap _ _).
  refine (path_sigma _ _ _ ((contr (c'.1))^ @ contr (d'.1)) _).
  refine (path_forall _ _ _); intros x.
  apply path2_contr.
Qed.

(** This provides the base case in a proof that truncatedness is a proposition. *)
Global Instance hprop_trunc `{Funext} (n : trunc_index) (A : Type)
  : IsHProp (IsTrunc n A) | 0.
Proof.
  apply hprop_inhabited_contr.
  revert A.
  induction n as [| n I]; unfold IsTrunc; simpl.
  - intros A ?.
    exact _.
  - intros A AH1.
    exists AH1.
    intro AH2.
    apply path_forall; intro x.
    apply path_forall; intro y.
    apply @path_contr.
    apply I, AH1.
Qed.

(** Similarly, a map being truncated is also a proposition. *)
Global Instance isprop_istruncmap `{Funext} (n : trunc_index) {X Y : Type} (f : X -> Y)
: IsHProp (IsTruncMap n f).
Proof.
  unfold IsTruncMap.
  exact _.
Defined.

(** We can induct on the truncation index to get that [IsTrunc] is (n+1)-truncated for all [n]. *)
Lemma istrunc_s__ishprop `{IsHProp A} {n} : IsTrunc n.+1 A.
Proof.
  induction n; typeclasses eauto.
Defined.

Global Instance trunc_trunc `{Funext} A m n : IsTrunc n.+1 (IsTrunc m A) | 0
  := istrunc_s__ishprop.

(** Chracterization of [IsHProp] in terms of all points being connected by paths. *)

Theorem path_ishprop `{H : IsHProp A} : forall x y : A, x = y.
Proof.
  apply H.
Defined.

Theorem hprop_allpath (A : Type) : (forall (x y : A), x = y) -> IsHProp A.
  intros H x y.
  pose (C := BuildContr A x (H x)).
  apply contr_paths_contr.
Defined.

Theorem equiv_hprop_allpath `{Funext} (A : Type)
  : IsHProp A <~> (forall (x y : A), x = y).
Proof.
  apply (equiv_adjointify (@path_ishprop A) (@hprop_allpath A));
  (* The proofs of the two homotopies making up this equivalence are almost identical.  First we start with a thing [f]. *)
    intro f;
  (* Then we apply funext a couple of times *)
    apply path_forall; intro x;
    apply path_forall; intro y;
  (* Now we conclude that [A] is contractible *)
    try pose (C := BuildContr A x (f x));
    try pose (D := contr_inhabited_hprop A x);
  (* And conclude because we have a path in a contractible space. *)
    apply path_contr.
Defined.

(** Two propositions are equivalent as soon as there are maps in both
   directions. *)

Definition isequiv_iff_hprop `{IsHProp A} `{IsHProp B}
  (f : A -> B) (g : B -> A)
: IsEquiv f.
Proof.
  apply (isequiv_adjointify f g);
    intros ?; apply path_ishprop.
Defined.

Definition equiv_iff_hprop_uncurried `{IsHProp A} `{IsHProp B}
  : (A <-> B) -> (A <~> B).
Proof.
  intros [f g].
  apply (equiv_adjointify f g);
    intros ?; apply path_ishprop.
Defined.

Definition equiv_iff_hprop `{IsHProp A} `{IsHProp B}
  : (A -> B) -> (B -> A) -> (A <~> B)
  := fun f g => equiv_iff_hprop_uncurried (f, g).

(** Being a contractible space is a proposition. *)

Global Instance hprop_contr `{Funext} (A : Type) : IsHProp (Contr A) | 0.
Proof.
  apply hprop_inhabited_contr.
  intro cA.
  exact _.
Defined.

(** Here is an alternate characterization of propositions. *)

Global Instance HProp_HProp `{Funext} A : IsHProp (IsHProp A) | 0
  := hprop_trunc -1 A.

Theorem equiv_hprop_inhabited_contr `{Funext} {A}
  : IsHProp A <~> (A -> Contr A).
Proof.
  apply (equiv_adjointify (@contr_inhabited_hprop A) (@hprop_inhabited_contr A)).
  - intro ic. by_extensionality x.
    apply @path_contr. apply contr_contr. exact (ic x).
  - intro hp. by_extensionality x. by_extensionality y.
    apply @path_contr. apply contr_contr. exact (hp x y).
Defined.

(** Here are some alternate characterizations of contractibility. *)
Theorem equiv_contr_inhabited_hprop `{Funext} {A}
  : Contr A <~> A * IsHProp A.
Proof.
  assert (f : Contr A -> A * IsHProp A).
    intro P. split. exact (@center _ P). apply @trunc_succ. exact P.
  assert (g : A * IsHProp A -> Contr A).
    intros [a P]. apply (@contr_inhabited_hprop _ P a).
  refine (@equiv_iff_hprop _ _ _ _ f g).
  apply hprop_inhabited_contr; intro p.
  apply @contr_prod.
  exact (g p). apply (@contr_inhabited_hprop _ _ (snd p)).
Defined.

Theorem equiv_contr_inhabited_allpath `{Funext} {A}
  : Contr A <~> A * forall (x y : A), x = y.
Proof.
  transitivity ( A * IsHProp A).
  apply equiv_contr_inhabited_hprop.
  apply equiv_functor_prod'. apply equiv_idmap. apply equiv_hprop_allpath.
Defined.

(** If the second component of a sigma type is an hProp, then to prove equality, we only need equality of the first component. *)
Definition path_sigma_hprop {A : Type} {P : A -> Type}
           `{forall x, IsHProp (P x)}
           (u v : sigT P)
: u.1 = v.1 -> u = v
  := path_sigma_uncurried P u v o pr1^-1.

Global Instance isequiv_path_sigma_hprop {A P} `{forall x : A, IsHProp (P x)} {u v : sigT P}
: IsEquiv (@path_sigma_hprop A P _ u v) | 100
  := isequiv_compose.

Hint Immediate isequiv_path_sigma_hprop : typeclass_instances.

(** The sigma of an hprop over a type can be viewed as a subtype. In particular, paths in the subtype are equivalent to paths in the original type. *)
Definition equiv_path_sigma_hprop {A : Type} {P : A -> Type}
           {HP : forall a, IsHProp (P a)} (u v : sigT P)
: (u.1 = v.1) <~> (u = v)
  := BuildEquiv _ _ (path_sigma_hprop _ _) _.

(** The type of Propositions *)
Record hProp := hp { hproptype : Type ; isp : IsHProp hproptype}.
(** This one would allow us to turn the record type of contractible types
into an [hProp].
<<
Canonical Structure default_HProp:= fun T P => (@hp T P).
>>
*)
Coercion hproptype : hProp >-> Sortclass.
Global Existing Instance isp.

Definition Unit_hp : hProp := (hp Unit _).

Definition False_hp : hProp := (hp Empty _).

Definition Negation_hp `{Funext} (hprop : hProp) : hProp := hp (~hprop) _.
(** We could continue with products etc *)

Definition issig_hProp: (sigT IsHProp) <~> hProp.
Proof.
  issig hp hproptype isp.
Defined.

(** Prove that [ap hproptype] is an equivalence. *)
Global Instance isequiv_ap_hproptype `{Funext} X Y : IsEquiv (@ap _ _ hproptype X Y).
Proof.
  (* TODO: This is a bit slow... can we speed it up? *)
  pose proof
       (isequiv_homotopic
          ((@path_sigma_hprop _ _ _ _ _)^-1 o (@ap _ _ issig_hProp^-1 X Y)))
    as H'.
  apply H'; clear H'.
  - apply @isequiv_compose.
    + typeclasses eauto.
    + apply @isequiv_inverse.
  - intros []; reflexivity.
Defined.

Definition path_hprop `{Funext} X Y := (@ap _ _ hproptype X Y)^-1%equiv.

Lemma if_hprop_then_equiv_Unit (hprop : hProp) :  hprop -> hprop <~> Unit.
Proof.
  intro p. 
  apply equiv_iff_hprop.
  exact (fun _ => tt).
  exact (fun _ => p).
Defined.

Lemma if_not_hprop_then_equiv_Empty (hprop : hProp) : ~hprop -> hprop <~> Empty.
Proof.
  intro np. 
  exact (BuildEquiv _ _ np _).
Defined.

