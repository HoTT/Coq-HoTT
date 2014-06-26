(* -*- mode: coq; mode: visual-line -*- *)
(** * Varieties of function extensionality *)

Require Import Overture PathGroupoids Contractible Equivalences types.UniverseLevel.
Local Open Scope path_scope.

(** In the Overture, we defined function extensionality to be the assertion that the map [apD10] is an equivalence.   We now prove that this follows from a couple of weaker-looking forms of function extensionality.  We do require eta conversion, which Coq 8.4+ has judgmentally.

   This proof is originally due to Voevodsky; it has since been simplified by Peter Lumsdaine and Michael Shulman. *)

(** Naive funext is the simple assertion that pointwise equal functions are equal. *)

Definition NaiveFunext :=
  forall (A : Type) (P : A -> Type) (f g : forall x, P x),
    (forall x, f x = g x) -> (f = g).

(** Weak funext says that a product of contractible types is contractible. *)

Definition WeakFunext :=
  forall (A : Type) (P : A -> Type),
    (forall x, Contr (P x)) -> Contr (forall x, P x).

(** The obvious implications are
   Funext -> NaiveFunext -> WeakFunext
   *)

Definition Funext_implies_NaiveFunext : Funext_type -> NaiveFunext.
Proof.
  intros fe A P f g h. apply fe. red. apply h.
Defined.

Definition NaiveFunext_implies_WeakFunext : NaiveFunext -> WeakFunext.
Proof.
  intros nf A P Pc.
  exists (fun x => center (P x)).
  intros f; apply nf; intros x.
  apply contr.
Defined.

(** The less obvious direction is that WeakFunext implies Funext (and hence all three are logically equivalent).  The point is that under weak funext, the space of "pointwise homotopies" has the same universal property as the space of paths. *)

Section Homotopies.

  Context (wf : WeakFunext).
  Context {A:Type} {B : A -> Type}.

  Context (f : forall x, B x).

  (* Recall that [f == g] is the type of pointwise paths (or "homotopies") from [f] to [g]. *)
  Let idhtpy : f == f := fun x => idpath (f x).

  (** Weak funext implies that the "based homotopy space" of the Pi-type is contractible, just like the based path space. *)
  Global Instance contr_basedhtpy : Contr {g : forall x, B x & f == g } | 0.
  Proof.
    exists (f;idhtpy). intros [g h].
    (* The trick is to show that the type [{g : forall x, B x & f == g }] is a retract of [forall x, {y : B x & f x = y}], which is contractible due to J and weak funext.  Here are the retraction and its section. *)
    pose (r := fun k => existT (fun g => f == g)
      (fun x => (k x).1) (fun x => (k x).2)).
    pose (s := fun (g : forall x, B x) (h : f == g) x => (g x ; h x)).
    (* Because of judgemental eta-conversion, the retraction is actually definitional, so we can just replace the goal. *)
    change (r (fun x => (f x ; idpath (f x))) = r (s g h)).
    apply ap; refine (@path_contr _ _ _ _).
    apply wf. intros x; exact (contr_basedpaths (f x)).
  Defined.

  (** This enables us to prove that pointwise homotopies have the same elimination rule as the identity type. *)

  Context (Q : forall g (h : f == g), Type).
  Context (d : Q f idhtpy).

  Definition htpy_rect g h : Q g h
    := @transport _ (fun gh => Q gh.1 gh.2) (f;idhtpy) (g;h)
         (@path_contr _ _ _ _) d.

  (** The computation rule, of course, is only propositional. *)
  Definition htpy_rect_beta : htpy_rect f idhtpy = d
    := transport (fun p : (f;idhtpy) = (f;idhtpy) =>
                    transport (fun gh => Q gh.1 gh.2) p d = d)
         (@path2_contr _ _ _ _
           (path_contr (f;idhtpy) (f;idhtpy)) (idpath _))^
         (idpath _).

End Homotopies.

(** Now the proof is fairly easy; we can just use the same induction principle on both sides. *)
Theorem WeakFunext_implies_Funext : WeakFunext -> Funext_type.
Proof.
  intros wf; intros A B f g.
  refine (isequiv_adjointify (@apD10 A B f g)
    (htpy_rect wf f (fun g' _ => f = g') idpath g) _ _).
  revert g; refine (htpy_rect wf _ _ _).
    refine (ap _ (htpy_rect_beta wf _ _ _)).
  intros h; destruct h.
    refine (htpy_rect_beta wf _ _ _).
Defined.

(** We add some hints to the typeclass database, so if we happen to have hypotheses of [WeakFunext] or [NaiveFunext] floating around, we get [Funext] automatically. *)
Definition NaiveFunext_implies_Funext : NaiveFunext -> Funext_type
  := WeakFunext_implies_Funext o NaiveFunext_implies_WeakFunext.

Hint Immediate WeakFunext_implies_Funext NaiveFunext_implies_Funext : typeclass_instances.

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

(** We permit the use of [Funext_downward_closed] exactly once in typeclass resolution.  So long as typeclass resolution backtracks on instances of functional extensionality, this will hopefully mean that we'll never need to worry about instances of functional extensionality, at least when we make definitions all in one go. *)
Hint Immediate Funext_downward_closed : typeclass_instances.
