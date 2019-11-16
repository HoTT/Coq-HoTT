(* -*- mode: coq; mode: visual-line -*-  *)
(** * HPropositions *)

Require Import HoTT.Basics HoTT.Types.

Local Open Scope path_scope.

Generalizable Variables A B.

(** ** Truncatedness is an hprop *)

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
  simple_induction n n IH; unfold IsTrunc; simpl.
  - intros A ?.
    exact _.
  - intros A AH1.
    exists AH1.
    intro AH2.
    apply path_forall; intro x.
    apply path_forall; intro y.
    apply @path_contr.
    apply IH, AH1.
Qed.
(** By [trunc_hprop], it follows that [IsTrunc n A] is also [m]-truncated for any [m >= -1]. *)

(** Similarly, a map being truncated is also a proposition. *)
Global Instance isprop_istruncmap `{Funext} (n : trunc_index) {X Y : Type} (f : X -> Y)
: IsHProp (IsTruncMap n f).
Proof.
  unfold IsTruncMap.
  exact _.
Defined.

(** ** Alternate characterization of hprops. *)

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
    try pose (C := Build_Contr A x (f x));
    try pose (D := contr_inhabited_hprop A x);
  (* And conclude because we have a path in a contractible space. *)
    apply path_contr.
Defined.

Theorem equiv_hprop_inhabited_contr `{Funext} {A}
  : IsHProp A <~> (A -> Contr A).
Proof.
  apply (equiv_adjointify (@contr_inhabited_hprop A) (@hprop_inhabited_contr A)).
  - intro ic. by_extensionality x.
    apply @path_contr. apply contr_contr. exact (ic x).
  - intro hp. by_extensionality x. by_extensionality y.
    apply @path_contr. apply contr_contr. exact (hp x y).
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
           (H : forall x1 x2, Sect (s x1 x2) (@ap X Y f x1 x2))
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
    + apply @trunc_succ. exact P.
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
