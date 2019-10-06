(* -*- mode: coq; mode: visual-line -*- *)

(** * The Freudenthal Suspension Theorem, and related results. (INCOMPLETE) *)

Require Import HoTT.Basics HoTT.Types.
Require Import HProp EquivalenceVarieties.
Require Import HIT.Connectedness HIT.Suspension HIT.Truncations.
Import TrM.
Local Open Scope trunc_scope.
Local Open Scope path_scope.

Generalizable Variables X A B f g n.

(** [proof_admitted] is used to implement the admit tactic, as in Coq 8.5 beta 1. *)
Local Axiom proof_admitted : False.
Local Ltac admit := case proof_admitted.

(* ** Connectedness of the suspension *)

Global Instance isconn_susp {n : trunc_index} {X : Type} `{H : IsConnected n X}
  : IsConnected n.+1 (Susp X).
Proof.
  apply isconnected_from_elim.
  intros C H' f. exists (f North).
  assert ({ p0 : f North = f South & forall x:X, ap f (merid x) = p0 })
    as [p0 allpath_p0] by (apply (isconnected_elim n); apply H').
  apply (Susp_ind (fun a => f a = f North) 1 p0^).
  intros x.
  apply (concat (transport_paths_Fl _ _)).
  apply (concat (concat_p1 _)).
  apply ap, allpath_p0.
Defined.

(** ** The Freudenthal Suspension Theorem *)
Section Freudenthal.

(** We assume funext and univalence.  In fact, since we will use funext at two different levels and local assumptions are monomorphic, we need to assume funext twice; we give the second assumption of it a name (so we can use it explicitly when we want it), and a different type (so it doesn’t get used when we don’t want it). TODO: perhaps this could be handled in a more uniform way?? *)
Context `{Funext} (funext_large : Funext * Unit) `{Univalence}
        {n : trunc_index} {Hn : ~ n = -2}
        (X : Type) (x0:X) `{IsConnMap n _ _ (unit_name x0)}.

(* TODO: eventually, change these to the weaker assumptions:
Context {n : trunc_index} (X : Type) `{IsConnected n.+1 X}.
*)

(** For convenience, we add some local abbreviations. *)
Notation No := (@North X).
Notation So := (@South X).
Notation mer := (@merid X).
Definition mer' := (fun x => mer x @ (mer x0)^).

(** The eventual theorem we want is: *)
Global Instance Freudenthal
  : IsConnMap (n +2+ n) (mer').
Proof.
  intros p. unfold IsConnected.
(** We are not ready to prove this yet.  For the remainder of the section, we will generalize this goal a bit, and prove some auxiliary lemmas; then we will return to the theorem. *)
Abort.

(** The goal we require for the FST is: *)
Definition FST_Codes_No (p : No = No)
  := (Trunc (n +2+ n) (hfiber mer' p)).

(** To prove it, we generalise it over [Susp X], by [Susp_ind].  This requires three components, which we construct (the main parts of) as lemmas in advance. *)
Definition FST_Codes_So (q : No = So)
  := (Trunc (n +2+ n) (hfiber mer q)).

(* TODO: move! *)
Definition hfiber_pair {A B} {f: A -> B} {b} (a:A) (p:f a = b) : hfiber f b
  := (a;p).

Definition FST_Codes_cross (x1 : X) (q : No = So)
  : FST_Codes_No (q @ (mer x1) ^) -> FST_Codes_So q.
Proof.
  unfold FST_Codes_No, FST_Codes_So, mer'.
  apply Trunc_rec.
  intros [x2 p]. revert x1 x2 p.
  refine (@wedge_incl_elim_uncurried _ n n X x0 _ X x0 _
    (fun x1 x2 => (mer x2 @ (mer x0) ^ = q @ (mer x1) ^)
                    -> Trunc (n +2+ n) (hfiber mer q)) _ _).
  refine (pr1 (@isconnected_elim n.+1 X _ _ _ _)).
  { apply @trunc_sigma; try typeclasses eauto.
    { apply @trunc_forall; try typeclasses eauto; intro.
      apply @trunc_arrow; try typeclasses eauto; intro.
      intros.
      admit. }
    admit. }
  refine (pr1 (@isconnected_elim n.+1 X _ _ _ _)).
  { apply @trunc_arrow; try typeclasses eauto; intros.
    admit. }
  { exists (fun b s => tr (hfiber_pair b (cancelR _ _ _ s))).
    exists (fun a r => tr (hfiber_pair a
                                                    (cancelR _ _ _ ((concat_pV _) @ (concat_pV _)^ @ r)))).
    apply path_forall; intros s. apply ap, ap, ap.
    exact ((concat_1p _)^ @ whiskerR (concat_pV _)^ _). }
Defined.

(** We will need to show that [FST_Codes_cross] is an equivalence, for each [x1, q]. By connectedness of [X], it will be enough to show this for the case [x1 = x0]; to show this, we first write that case in a tidier form. *)
Definition FST_Codes_cross_x0 (q : No = So)
  : FST_Codes_No (q @ (mer x0)^) -> FST_Codes_So q.
Proof.
  unfold FST_Codes_No, FST_Codes_So.
  apply Trunc_functor, (functor_sigma idmap).
  unfold mer'; intros x1. apply cancelR.
Defined.

Definition isequiv_FST_Codes_cross (x : X) (q : No = So)
  : IsEquiv (FST_Codes_cross x q).
Proof.
  revert x.
  apply (@conn_map_elim _ _ _ (unit_name x0) _
    (fun x => IsEquiv (FST_Codes_cross x q))).
  - intros x; generalize dependent n. intros [ | n'] imposs.
    + destruct (imposs 1).
    + intros ?. apply (@trunc_leq -1);[exact tt | apply hprop_isequiv].
  - intros []. unfold FST_Codes_cross.
    refine (isequiv_homotopic (FST_Codes_cross_x0 q) _).
    { unfold FST_Codes_cross_x0.
      apply isequiv_Trunc_functor, @isequiv_functor_sigma.
      - exact _.
      - intros a. apply isequiv_cancelR. }
    { hnf. apply Trunc_ind.
      - intros ?; apply trunc_succ.
      - intros [x r]; simpl.
        unfold functor_sigma; simpl.
        symmetry.
        exact (ap10 (wedge_incl_comp1 x0 x0 _ _ _ _ x) r). }
Defined.

Definition FST_Codes
  : forall (y : Susp X), (No = y) -> Type.
Proof.
  apply (Susp_ind (fun y => (No = y -> Type)) FST_Codes_No FST_Codes_So).
  intros x. apply (@path_forall (fst funext_large)); intros p.
  refine (transport_arrow _ _ _ @ _).
  refine (transport_const _ _ @ _).
  transitivity (FST_Codes_No (p @ (mer x)^)).
  { apply ap, transport_paths_r. }
  apply path_universe_uncurried.
  exists (FST_Codes_cross x p).
  apply isequiv_FST_Codes_cross.
Defined.

(** It now remains to show that each [FST_Codes y p] is contractible. It is easy to provide a canonical inhabitant, by transport. (More directly, we could use path-induction, but we will later need to use transport lemmas to reason about this.) *)
Definition FST_Codes_center (y : Susp X) (p : No = y)
  : FST_Codes y p.
Proof.
  assert (goal' : FST_Codes y (transport _ p 1)).
  - apply transportD. simpl; unfold FST_Codes_No.
    apply tr. exists x0; unfold mer'. apply concat_pV.
  - refine (transport _ _ goal'). refine (transport_paths_r _ _ @ _).
    apply concat_1p.
Defined.

(** TODO: move the following few lemmas. *)
Lemma transport_as_ap {A} (P : A -> Type) {x y} (p : x = y)
  : transport P p == transport idmap (ap P p).
Proof.
  intros ?; destruct p; exact 1.
Defined.

Lemma transportD'
  {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1)
: C x1 y -> C x2 (transport B p y).
Proof.
  refine (transport idmap _).
  refine (_ @ ap10 (apD C p) _).
  apply inverse.
  refine (transport_arrow _ _ _ @ _).
  refine (transport_const _ _ @ _).
  apply ap, transport_Vp.
Defined.

Arguments transportD' / [_] _ _ [_ _] _ _ _.

Lemma transportD_as_apD
  {A : Type} (B : A -> Type) (C : forall a : A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1)
: transportD B C p y == transportD' B C p y.
Proof.
  intros ?; destruct p; simpl. exact 1.
Defined.

(** A transport lemma. *)
Definition FST_Codes_transportD_concrete (x1 : X) (p : No = No)
  : FST_Codes No p -> FST_Codes So (transport (paths No) (mer x1) p).
Proof.
  intro rr. assert (goal' : FST_Codes So (p @ mer x1)).
  - apply (FST_Codes_cross x1).
    refine (transport FST_Codes_No _ rr). symmetry; apply concat_pp_V.
  - refine (transport FST_Codes_So _ goal').
    apply inverse, transport_paths_r.
Defined.

Definition FST_Codes_transportD (x1 : X) (p : No = No) (rr : FST_Codes No p)
  : transportD (paths No) FST_Codes (mer x1) p rr
  = FST_Codes_transportD_concrete x1 p rr.
Proof.
  refine (transportD_as_apD _ _ _ _ _ @ _).
  unfold transportD'.
  unfold FST_Codes. rewrite (Susp_ind_beta_merid _ _ _ _ x1); simpl.
    rewrite (@ap10_path_forall (fst funext_large)).
  unfold FST_Codes_transportD_concrete.
  rewrite ! transport_pp.
  refine (transport_path_universe _ _ @ _).
(*rewrite transport_paths_r.
  rewrite transport_as_ap.*)
Admitted.


(** Showing it is contractible, we will again need the universal property of the suspension. We will prove the components as separate lemmas first; to see the required types of these, we temporarily set up the theorem. *)
Definition FST_Codes_contr (y : Susp X) (p : No = y) (rr : FST_Codes y p)
  : rr = FST_Codes_center y p.
Proof.
  revert y p rr.
  Check (Susp_ind (fun y => forall p rr, rr = FST_Codes_center y p)).
Abort.

Definition FST_Codes_contr_No (p : No = No) (rr : FST_Codes No p)
  : (rr = FST_Codes_center No p).
Proof.
  revert rr. apply Trunc_ind.
  - intros ?; apply trunc_succ.
  - intros [x1 r]. destruct r. unfold FST_Codes_center. simpl.
  (*transitivity (tr
    (transport (fun p => hfiber mer' p) (transport_paths_r p 1 @ concat_1p p)
    (transportD (paths No))))
simpl in *.*)
Admitted.

Global Instance Freudenthal
  : IsConnMap (n +2+ n) (@merid X).
Proof.
  intros p; apply isconnected_from_elim; intros C ? f.
Admitted.

End Freudenthal.
