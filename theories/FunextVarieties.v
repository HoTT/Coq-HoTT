(* -*- mode: coq; mode: visual-line -*- *)
(** * Varieties of function extensionality *)

Require Import HoTT.Basics HoTT.Types EquivalenceVarieties.
Local Open Scope path_scope.

(** In the Overture, we defined function extensionality to be the assertion that the map [apD10] is an equivalence.   We now prove that this follows from a couple of weaker-looking forms of function extensionality.  We do require eta conversion, which Coq 8.4+ has judgmentally.

   This proof is originally due to Voevodsky; it has since been simplified by Peter Lumsdaine and Michael Shulman. *)

(** Naive funext is the simple assertion that pointwise equal functions are equal.  The domain and codomain could live in different universes; the third universe argument is essentially the max of [i] and [j] (and similarly for all subsequent axioms). *)

Definition NaiveFunext :=
  forall (A : Type@{i}) (P : A -> Type@{j}) (f g : forall x, P x),
    (forall x, f x = g x) -> (f = g).
Check NaiveFunext@{i j max}.

(** Naive non-dependent funext is the same, but only for non-dependent functions.  *)

Definition NaiveNondepFunext :=
  forall (A B : Type) (f g : A -> B),
    (forall x, f x = g x) -> (f = g).
Check NaiveNondepFunext@{i j max}.

(** Weak funext says that a product of contractible types is contractible. *)

Definition WeakFunext :=
  forall (A : Type) (P : A -> Type),
    (forall x, Contr (P x)) -> Contr (forall x, P x).
Check WeakFunext@{i j max}.

(** We define a variant of [Funext] which does not invoke an axiom. *)
Definition Funext_type :=
  forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).
Check Funext_type@{i j max}.

(** The obvious implications are
   Funext -> NaiveFunext -> WeakFunext and NaiveFunext -> NaiveNondepFunext.
   None of these do anything fiddly with the universes either.
   *)

Definition Funext_implies_NaiveFunext@{i j max}
  : Funext_type@{i j max} -> NaiveFunext@{i j max}.
Proof.
  intros fe A P f g h.
  unfold Funext_type in *.
  exact ((@apD10 A P f g)^-1 h).
Defined.

Definition NaiveFunext_implies_WeakFunext@{i j max}
  : NaiveFunext@{i j max} -> WeakFunext@{i j max}.
Proof.
  intros nf A P Pc.
  exists (fun x => center (P x)).
  intros f; apply nf; intros x.
  apply contr.
Defined.

Definition NaiveFunext_implies_NaiveNondepFunext@{i j max}
  : NaiveFunext@{i j max} -> NaiveNondepFunext@{i j max}
  := fun nf A B f g => nf A (fun _ => B) f g.

(** The non-obvious directions are that WeakFunext implies Funext and that NaiveNondepFunext implies WeakFunext (and hence all four are logically equivalent). *)

(** ** Weak funext implies Funext *)

(** To show that WeakFunext implies Funext, the point is that under weak funext, the space of "pointwise homotopies" has the same universal property as the space of paths. *)

Section Homotopies.

  Context (wf : WeakFunext).
  Context {A:Type} {B : A -> Type}.

  Context (f : forall x, B x).

  (* Recall that [f == g] is the type of pointwise paths (or "homotopies") from [f] to [g]. *)
  Let idhtpy : f == f := fun x => idpath (f x).

  (** Weak funext implies that the "based homotopy space" of the Pi-type is contractible, just like the based path space. *)
  (** Use priority 1, so we don't override [Contr Unit]. *)
  Global Instance contr_basedhtpy : Contr {g : forall x, B x & f == g } | 1.
  Proof.
    unfold WeakFunext in wf.    (* Allow typeclass inference to find it *)
    exists (f;idhtpy). intros [g h].
    (* The trick is to show that the type [{g : forall x, B x & f == g }] is a retract of [forall x, {y : B x & f x = y}], which is contractible due to J and weak funext.  Here are the retraction and its section. *)
    pose (r := fun k => existT (fun g => f == g)
      (fun x => (k x).1) (fun x => (k x).2)).
    pose (s := fun (g : forall x, B x) (h : f == g) x => (g x ; h x)).
    (* Because of judgemental eta-conversion, the retraction is actually definitional, so we can just replace the goal. *)
    change (r (fun x => (f x ; idpath (f x))) = r (s g h)).
    apply ap; serapply path_contr.
  Defined.

  (** This enables us to prove that pointwise homotopies have the same elimination rule as the identity type. *)

  Context (Q : forall g (h : f == g), Type).
  Context (d : Q f idhtpy).

  Definition htpy_ind g h : Q g h
    := @transport _ (fun gh => Q gh.1 gh.2) (f;idhtpy) (g;h)
         (@path_contr _ _ _ _) d.

  (** The computation rule, of course, is only propositional. *)
  Definition htpy_ind_beta : htpy_ind f idhtpy = d
    := transport (fun p : (f;idhtpy) = (f;idhtpy) =>
                    transport (fun gh => Q gh.1 gh.2) p d = d)
         (@path2_contr _ _ _ _
           (path_contr (f;idhtpy) (f;idhtpy)) (idpath _))^
         (idpath _).

End Homotopies.

(** Now the proof is fairly easy; we can just use the same induction principle on both sides.  This proof also preserves all the universes. *)
Theorem WeakFunext_implies_Funext@{i j max}
  : WeakFunext@{i j max} -> Funext_type@{i j max}.
Proof.
  intros wf; hnf; intros A B f g.
  refine (isequiv_adjointify (@apD10 A B f g)
    (htpy_ind wf f (fun g' _ => f = g') idpath g) _ _).
  - revert g; refine (htpy_ind wf _ _ _).
    refine (ap _ (htpy_ind_beta wf _ _ _)).
  - intros h; destruct h.
    refine (htpy_ind_beta wf _ _ _).
Defined.

(** We add some hints to the typeclass database, so if we happen to have hypotheses of [WeakFunext] or [NaiveFunext] floating around, we get [Funext] automatically. *)
Definition NaiveFunext_implies_Funext : NaiveFunext -> Funext_type
  := WeakFunext_implies_Funext o NaiveFunext_implies_WeakFunext.

(** ** Naive non-dependent funext implies weak funext  *)

(** First we show that naive non-dependent funext suffices to show that postcomposition with an equivalence is an equivalence. *)
Definition equiv_postcompose_from_NaiveNondepFunext
           (nf : NaiveNondepFunext) {A B C : Type} (f : B <~> C)
  : (A -> B) <~> (A -> C)
  := Build_Equiv
       _ _ (fun (g:A->B) => f o g)
       (isequiv_adjointify
          (fun (g:A->B) => f o g)
          (fun h => f^-1 o h)
          (fun h => nf _ _ _ _ (fun x => eisretr f (h x)))
          (fun g => nf _ _ _ _ (fun y => eissect f (g y)))).

(** Now, if each [P x] is contractible, the projection [pr1 : {x:X & P x} -> X] is an equivalence (this requires no funext).  Thus, postcomposition with it is also an equivalence, and hence the fiber of postcomposition over [idmap X] is contractible.  But this fiber is "the type of sections of [pr1]" and hence equivalent to [forall x:X, P x].  The latter equivalence requires full funext to prove, but without any funext we can show that [forall x:X, P x] is a *retract* of the type of sections, hence also contractible. *)
Theorem NaiveNondepFunext_implies_WeakFunext
  : NaiveNondepFunext -> WeakFunext.
Proof.
  intros nf X P H.
  pose (T := (hfiber (equiv_postcompose_from_NaiveNondepFunext nf (equiv_pr1 P)) idmap)).
  assert (X1 : Contr T).
  { apply fcontr_isequiv; exact _. }
  exact (@contr_retract T _ _
           (fun fp x => transport P (ap10 fp.2 x) (fp.1 x).2)
           (fun f => ((fun x => (x ; f x)) ; 1)) (fun f => 1)).
Defined.

(** Therefore, naive nondependent funext also implies full funext.  Interestingly, this requires the universe of the assumption codomain to be not just that of the conclusion codomain, but the max of that universe with the domain universe (which is unchanged). *)
Definition NaiveNondepFunext_implies_Funext@{i j max}
  : NaiveNondepFunext@{i max max} -> Funext_type@{i j max}
  := WeakFunext_implies_Funext o NaiveNondepFunext_implies_WeakFunext.


(** ** Functional extensionality is downward closed *)

(** If universe [U_i] is functionally extensional, then so are universes [U_j] for [j ≤ i]. *)
Lemma Funext_downward_closed `{H : Funext_type} : Funext_type.
Proof.
  apply @NaiveFunext_implies_Funext.
  apply Funext_implies_NaiveFunext in H.
  hnf in *.
  intros A P f g H'.
  (** We want to just use [H] here.  But we need to adjust the universe level in four places: for [A], for [P], for the input path, and for the output path. *)
  case (H (Lift A) (fun x => Lift (P x)) f g (fun x => ap lift (H' x))).
  exact idpath.
Defined.

(** We re-declare this instance depending on the global [Funext] typeclass, since it is useful on its own. *)
Global Instance contr_basedhomotopy `{Funext}
       {A:Type} {B : A -> Type} (f : forall x, B x)
: Contr {g : forall x, B x & f == g }.
Proof.
  apply contr_basedhtpy.
  apply NaiveFunext_implies_WeakFunext.
  apply Funext_implies_NaiveFunext.
  unfold Funext_type; exact _.
Defined.
