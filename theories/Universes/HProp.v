(** * HPropositions *)

Require Import HoTT.Basics HoTT.Types.

Local Open Scope path_scope.

Generalizable Variables A B.

(** ** Alternate characterization of hprops. *)

Theorem equiv_hprop_allpath `{Funext} (A : Type)
  : IsHProp A <~> (forall (x y : A), x = y).
Proof.
  rapply (equiv_iff_hprop (@path_ishprop A) (@hprop_allpath A)).
  apply hprop_allpath; intros f g.
  funext x y.
  pose (C := Build_Contr A x (f x)).
  apply path_contr.
Defined.

Theorem equiv_hprop_inhabited_contr `{Funext} {A}
  : IsHProp A <~> (A -> Contr A).
Proof.
  apply (equiv_adjointify (@contr_inhabited_hprop A) (@hprop_inhabited_contr A)).
  - intro ic. by_extensionality x.
    apply @path_contr. apply contr_istrunc. exact (ic x).
  - intro hp.
    apply path_ishprop.
Defined.

(** Being an hprop is also equivalent to the diagonal being an equivalence. *)
Definition ishprop_isequiv_diag {A} `{IsEquiv _ _ (fun (a:A) => (a,a))}
: IsHProp A.
Proof.
  apply hprop_allpath; intros x y.
  set (d := fun (a:A) => (a,a)) in *.
  transitivity (fst (d (d^-1 (x,y)))).
  - exact (ap fst (eisretr d (x,y))^).
  - transitivity (snd (d (d^-1 (x,y)))).
    + unfold d; reflexivity.
    + exact (ap snd (eisretr d (x,y))).
Defined.

Global Instance isequiv_diag_ishprop {A} `{IsHProp A}
: IsEquiv (fun (a:A) => (a,a)).
Proof.
  refine (isequiv_adjointify _ fst _ _).
  - intros [x y].
    apply path_prod; simpl.
    + reflexivity.
    + apply path_ishprop.
  - intros a; simpl.
    reflexivity.
Defined.

(** ** A map is an embedding as soon as its ap's have sections. *)

Definition isembedding_sect_ap {X Y} (f : X -> Y)
           (s : forall x1 x2, (f x1 = f x2) -> (x1 = x2))
           (H : forall x1 x2, (@ap X Y f x1 x2) o (s x1 x2) == idmap)
  : IsEmbedding f.
Proof.
  intros y.
  apply hprop_allpath.
  intros [x1 p1] [x2 p2].
  apply path_sigma with (s x1 x2 (p1 @ p2^)).
  abstract (rewrite transport_paths_Fl; cbn;
            rewrite (H x1 x2 (p1 @ p2^));
            rewrite inv_pp, inv_V; apply concat_pV_p).
Defined.

(** ** Alternate characterizations of contractibility. *)

Theorem equiv_contr_inhabited_hprop `{Funext} {A}
  : Contr A <~> A * IsHProp A.
Proof.
  assert (f : Contr A -> A * IsHProp A).
  - intro P. split.
    + exact (@center _ P).
    + apply @istrunc_succ. exact P.
  - assert (g : A * IsHProp A -> Contr A).
    + intros [a P]. apply (@contr_inhabited_hprop _ P a).
    + refine (@equiv_iff_hprop _ _ _ _ f g).
      apply hprop_inhabited_contr; intro p.
      apply @contr_prod.
      * exact (g p).
      * apply (@contr_inhabited_hprop _ _ (snd p)).
Defined.

Theorem equiv_contr_inhabited_allpath `{Funext} {A}
  : Contr A <~> A * forall (x y : A), x = y.
Proof.
  transitivity (A * IsHProp A).
  - apply equiv_contr_inhabited_hprop.
  - exact (1 *E equiv_hprop_allpath _).
Defined.

(** ** Logical equivalence of hprops *)

(** Logical equivalence of hprops is not just logically equivalent to equivalence, it is equivalent to it. *)
Global Instance isequiv_equiv_iff_hprop_uncurried
       `{Funext} {A B} `{IsHProp A} `{IsHProp B}
: IsEquiv (@equiv_iff_hprop_uncurried A _ B _) | 0.
Proof.
  pose (@istrunc_equiv).
  refine (isequiv_adjointify
            equiv_iff_hprop_uncurried
            (fun e => (@equiv_fun _ _ e, @equiv_inv _ _ e _))
            _ _);
    intro;
      by apply path_ishprop.
Defined.

Definition equiv_equiv_iff_hprop
       `{Funext} (A B : Type) `{IsHProp A} `{IsHProp B}
  : (A <-> B) <~> (A <~> B)
  := Build_Equiv _ _ (@equiv_iff_hprop_uncurried A _ B _) _.

(** ** Inhabited and uninhabited hprops *)

(** If an hprop is inhabited, then it is equivalent to [Unit]. *)
Lemma if_hprop_then_equiv_Unit (hprop : Type) `{IsHProp hprop} :  hprop -> hprop <~> Unit.
Proof.
  intro p.
  apply equiv_iff_hprop.
  - exact (fun _ => tt).
  - exact (fun _ => p).
Defined.

(** If an hprop is not inhabited, then it is equivalent to [Empty]. *)
Lemma if_not_hprop_then_equiv_Empty (hprop : Type) `{IsHProp hprop} : ~hprop -> hprop <~> Empty.
Proof.
  intro np.
  exact (Build_Equiv _ _ np _).
Defined.

(** Thus, a decidable hprop is either equivalent to [Unit] or [Empty]. *)
Definition equiv_decidable_hprop (hprop : Type)
           `{IsHProp hprop} `{Decidable hprop}
: (hprop <~> Unit) + (hprop <~> Empty).
Proof.
  destruct (dec hprop) as [x|nx].
  - exact (inl (if_hprop_then_equiv_Unit hprop x)).
  - exact (inr (if_not_hprop_then_equiv_Empty hprop nx)).
Defined.

(** Under function extensionality, if [A] is decidable, then [~~A] is the propositional truncation of [A]. Here, for dependency reasons, we don't give the equivalence to [Tr (-1) A], but just show that the recursion principle holds. See ../Metatheory/ImpredicativeTruncation.v for a generalization to all types. *)

(** Any negation is an hprop, by [istrunc_Empty] and [istrunc_arrow]. In particular, double-negation is an hprop. *)
Definition ishprop_not_not `{Funext} {A : Type} : IsHProp (~~A) := _.

Definition not_not_unit {A : Type} : A -> ~~A
  := fun a na => na a.

(** The recursion principle for [~~A]. *)
Definition not_not_rec {A : Type} `{Decidable A} (P : HProp) (f : A -> P)
  : ~~A -> P.
Proof.
  intro nna.
  destruct (dec A) as [a | na].
  - exact (f a).
  - elim (nna na).
Defined.

(** The computation rule only holds propositionally. *)
Definition not_not_rec_beta {A : Type} `{Decidable A} (P : HProp) (f : A -> P) (a : A)
  : not_not_rec P f (not_not_unit a) = f a
  := path_ishprop _ _.

(** Under [Funext], [ishprop_decpaths] shows that [DecidablePaths A] is an hprop.  More generally, it's also an hprop with the first argument fixed. *)
Global Instance ishprop_decpaths' `{Funext} {A : Type} (x : A)
  : IsHProp (forall (y : A), Decidable (x = y)).
Proof.
  apply hprop_allpath; intros d d'.
  (* Define [C] to be the component of [A] containing [x]. Since [x = y] is decidable, we can use [~~(x = y)] as an elementary form of propositional truncation. It also works to use [merely] here, but that brings in further dependencies and requires HITs. *)
  pose (C := {y : A & ~~(x = y)}).
  assert (cC : Contr C).
  { snrapply (Build_Contr C (x; not_not_unit idpath)).
    intros [y p].
    srapply path_sigma_hprop; cbn.
    (* [d y] either solves the goal or contradicts [p]. *)
    by destruct (d y). }
  funext y.
  generalize (d y); clear d; intros d.
  generalize (d' y); clear d'; intros d'.
  destruct d as [d | nd]; destruct d' as [d' | nd'].
  - apply ap.
    (* [x] and [y] are "in" the component [C]: *)
    pose (xC := (x; not_not_unit idpath) : C).
    pose (yC := (y; not_not_unit d) : C).
    (* [d] and [d'] can be lifted to equalities of type [xC = yC] using [path_sigma_hprop], and so up to the computation rule for [pr1_path] (denoted "..1"), our goal is in the image of "..1". *)
    refine ((pr1_path_path_sigma_hprop xC yC d)^ @ _ @ pr1_path_path_sigma_hprop xC yC d').
    (* But since [C] is an hset, the paths in [C] are equal. *)
    apply ap, path_ishprop.
  (* The remaining cases are the same as in [ishprop_decpaths], but the last bullet is shorter since typeclass search tells us that [x <> y] is an hprop. *)
  - elim (nd' d).
  - elim (nd d').
  - apply ap, path_ishprop.
Defined.
