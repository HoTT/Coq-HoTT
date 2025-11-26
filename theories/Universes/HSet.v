From HoTT Require Import Basics.
Require Import Types.Sigma Types.Paths Types.Unit Types.Arrow.

(** * H-Sets *)

Local Open Scope path_scope.

(** A type is a set if and only if it satisfies Axiom K. *)

Definition axiomK A := forall (x : A) (p : x = x), p = idpath x.

Definition axiomK_hset {A} : IsHSet A -> axiomK A.
Proof.
  intros H x p.
  napply path_ishprop.
  exact (H x x).
Defined.

Definition hset_axiomK {A} `{axiomK A} : IsHSet A.
Proof.
  apply istrunc_S; intros x y.
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
    cut (Contr (x=x)).
    + intro. eapply path_contr.
    + apply (Build_Contr _ 1). intros. symmetry; apply K.
  - intro K.
    eapply path_ishprop.
Defined.

#[export] Instance axiomK_isprop A : IsHProp (axiomK A) | 0.
Proof.
  exact (istrunc_equiv_istrunc _ equiv_hset_axiomK).
Defined.

Theorem hset_path2 {A} `{IsHSet A} {x y : A} (p q : x = y):
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
  pose (T1A := @istrunc_succ _ A (@hset_axiomK A K)).
  exact (@hset_path2 (x=x) (T1A x x) _ _ _ _).
Defined.

End AssumeFunext.

(** We prove that if [R] is a reflexive mere relation on [X] implying identity, then [X] is an hSet, and hence [R x y] is equivalent to [x = y]. *)
Lemma ishset_hrel_subpaths
      {X R}
      `{Reflexive X R}
      `{forall x y, IsHProp (R x y)}
      (f : forall x y, R x y -> x = y)
: IsHSet X.
Proof.
  apply @hset_axiomK.
  intros x p.
  refine (_ @ concat_Vp (f x x (transport (R x) p^ (reflexivity _)))).
  apply moveL_Vp.
  refine ((transport_paths_r _ _)^ @ _).
  refine ((transport_arrow _ _ _)^ @ _).
  refine ((ap10 (apD (f x) p) (@reflexivity X R _ x)) @ _).
  apply ap.
  apply path_ishprop.
Defined.

Instance isequiv_hrel_subpaths
       X R
       `{Reflexive X R}
       `{forall x y, IsHProp (R x y)}
       (f : forall x y, R x y -> x = y)
       x y
: IsEquiv (f x y) | 10000.
Proof.
  pose proof (ishset_hrel_subpaths f).
  refine (isequiv_adjointify
            (f x y)
            (fun p => transport (R x) p (reflexivity x))
            _
            _);
  intro;
  apply path_ishprop.
Defined.

(** We will now prove that for sets, monos and injections are equivalent.*)
Definition ismono {X Y} (f : X -> Y)
  := forall (Z : HSet),
     forall g h : Z -> X, f o g = f o h -> g = h.

Instance isinj_embedding {A B : Type} (m : A -> B)
  : IsEmbedding m -> IsInjective m.
Proof.
  intros ise x y p.
  pose (ise (m y)).
  assert (q : (x;p) = (y;1) :> hfiber m (m y)) by apply path_ishprop.
  exact (ap pr1 q).
Defined.

(** Computation rule for [isinj_embedding]. *)
Lemma isinj_embedding_beta {X Y : Type} (f : X -> Y) {I : IsEmbedding f} {x : X}
  : (isinj_embedding f I x x idpath) = idpath.
Proof.
  exact (ap (ap pr1) (contr (idpath : (x;idpath) = (x;idpath)))).
Defined.

Definition isinj_section {A B : Type} {s : A -> B} {r : B -> A}
      (H : r o s == idmap) : IsInjective s.
Proof.
  intros a a' alpha.
  exact ((H a)^ @ ap r alpha @ H a').
Defined.

Lemma isembedding_isinj_hset {A B : Type} `{IsHSet B} (m : A -> B)
: IsInjective m -> IsEmbedding m.
Proof.
  intros isi b.
  apply hprop_allpath; intros [x p] [y q].
  apply path_sigma_hprop; simpl.
  exact (isi x y (p @ q^)).
Defined.

Lemma ismono_isinj `{Funext} {X Y} (f : X -> Y) : IsInjective f -> ismono f.
Proof.
  intros ? ? ? ? H'.
  apply path_forall.
  apply ap10 in H'.
  hnf in *.
  eauto.
Qed.

Definition isinj_ismono {X Y} (f : X -> Y)
           (H : ismono f)
: IsInjective f
  := fun x0 x1 H' =>
       ap10 (H (Build_HSet Unit)
               (fun _ => x0)
               (fun _ => x1)
               (ap (fun x => unit_name x) H'))
            tt.

Lemma ismono_isequiv `{Funext} X Y (f : X -> Y) `{IsEquiv _ _ f}
: ismono f.
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

Lemma cancelL_isembedding {A B C : Type} `{IsHSet B} {f : A -> B} {g : B -> C} `{IsEmbedding (g o f)}
  : IsEmbedding f.
Proof.
  rapply isembedding_isinj_hset.
  exact (isinj_cancelL _ g).
Defined.
