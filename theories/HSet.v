(* -*- mode: coq; mode: visual-line -*-  *)
(** * H-Sets *)

Require Import Overture PathGroupoids Contractible Equivalences Trunc HProp.
Require Import types.Paths types.Sigma types.Empty types.Record types.Unit.
Require Import FunextVarieties.

Local Open Scope equiv_scope.
Local Open Scope path_scope.

(** A type is a set if and only if it satisfies Axiom K. *)

Definition axiomK A := forall (x : A) (p : x = x), p = idpath x.

Definition axiomK_hset {A} : IsHSet A -> axiomK A.
Proof.
  intros H x p.
  apply (H x x p (idpath x)).
Defined.

Definition hset_axiomK {A} `{axiomK A} : IsHSet A.
Proof.
  intros x y H.
  apply @hprop_allpath.
  intros p q.
  by induction p.
Defined.

Section AssumeFunext.
Context `{Funext}.

Theorem equiv_hset_axiomK {A} : IsHSet A <~> axiomK A.
Proof.
  apply (equiv_adjointify (@axiomK_hset A) (@hset_axiomK A)).
  - intros K. by_extensionality x. by_extensionality x'.
    cut (Contr (x=x)). intro. eapply path_contr.
    exists 1. intros. apply symmetry, K.
  - intro K. by_extensionality x. by_extensionality x'.
    eapply allpath_hprop.
Defined.

Global Instance axiomK_isprop A : IsHProp (axiomK A) | 0.
Proof.
  apply (trunc_equiv equiv_hset_axiomK).
Defined.

Theorem set_path2 {A} `{IsHSet A} {x y : A} (p q : x = y):
  p = q.
Proof.
  induction q.
  apply axiomK_hset; assumption.
Defined.

(** Recall that axiom K says that any self-path is homotopic to the
   identity path.  In particular, the identity path is homotopic to
   itself.  The following lemma says that the endo-homotopy of the
   identity path thus specified is in fact (homotopic to) its identity
   homotopy (whew!).  *)
(* TODO: What was the purpose of this lemma?  Do we need it at all?  It's actually fairly trivial. *)
Lemma axiomK_idpath {A} (x : A) (K : axiomK A) :
  K x (idpath x) = idpath (idpath x).
Proof.
  pose (T1A := @trunc_succ _ A (@hset_axiomK A K)).
  exact (@set_path2 (x=x) (T1A x x) _ _ _ _).
Defined.

(** Hedberg's theorem: any type with "decidable equality" is a set. *)

Definition decidable_paths (A : Type) :=
  forall (x y : A), (x = y) + (~ (x = y)).

(* Usually this lemma would be proved with [discriminate], but unfortunately that tactic is hardcoded to work only with Coq's [Prop]-valued equality.
   TODO: This should be in types/Sum. *)
Definition inl_injective {A B : Type} {x y : A} (p : inl B x = inl B y) : x = y :=
  (@transport _ (fun (s : A + B) => x = (match s with inl a => a | inr b => x end)) _ _ p (idpath x)).

Theorem axiomK_decidable {A : Type} : @decidable_paths A -> @axiomK A.
Proof.
  intro d.
  intros x p.
  set (qp := apD (d x) p).
  set (q := d x x) in *.
  clearbody qp; revert qp.
  destruct q as [q | q'].
    intro qp0; apply (cancelL q). path_via (transport _ p q).
      symmetry; apply transport_paths_r.
      path_via q. apply @inl_injective with (B := (~ x = x)).
      exact ((ap_transport p (fun y => @inl (x = y) (~x = y)) q) @ qp0).
  induction (q' p).
Defined.

Corollary hset_decidable {A : Type} : @decidable_paths A -> IsHSet A.
Proof.
  intro.
  by apply @hset_axiomK, @axiomK_decidable.
Defined.

End AssumeFunext.

Record hSet := BuildhSet {setT:> Type; iss :> IsHSet setT}.
(** This one is needed in [epi_surj] to coerce [hProp] into [hSet]*)
Canonical Structure default_HSet:= fun T P => (@BuildhSet T P).
Hint Resolve iss.
Global Existing Instance iss.

(** We will now prove that for sets, monos and injections are equivalent.*)
Definition mono {X Y} (f : X -> Y)
  := forall Z : hSet,
     forall g h : Z -> X, f o g = f o h -> g = h.

Definition inj {X Y} (f : X -> Y)
  := forall x0 x1 : X,
       f x0 = f x1 -> x0 = x1.

Lemma inj_mono `{Funext} {X Y} (f : X -> Y) : inj f -> mono f.
Proof.
  intros ? ? ? ? H'.
  apply path_forall.
  apply ap10 in H'.
  hnf in *; unfold compose in *.
  eauto.
Qed.

Definition mono_inj {X Y} (f : X -> Y)
           (H : mono f)
: inj f
  := fun x0 x1 H' =>
       ap10 (H (BuildhSet Unit _)
               (fun _ => x0)
               (fun _ => x1)
               (ap (fun x => unit_name x) H'))
            tt.

Lemma mono_isequiv `{Funext} X Y (f : X -> Y) `{IsEquiv _ _ f}
: mono f.
Proof.
  intros ? g h H'.
  apply ap10 in H'.
  apply path_forall.
  intro x.
  transitivity (f^-1 (f (g x))).
  - by rewrite eissect.
  - transitivity (f^-1 (f (h x))).
    * apply ap. apply H'.
    * by rewrite eissect.
Qed.
