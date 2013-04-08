(* -*- mode: coq; mode: visual-line -*- *)

(** * The Freudenthal Suspension Theorem, and related results. *)

Require Import Overture PathGroupoids Fibrations Equivalences Trunc EquivalenceVarieties Forall Sigma Paths Unit Universe Arrow Connectedness Suspension Truncations.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

(* ** Connectedness of the suspension *)

Instance isconn_susp {n : trunc_index} {X : Type} `{IsConnected n X}
  : IsConnected (trunc_S n) (Susp X).
Proof.
  intros C ? f. exists (f North).
  assert ({ p0 : f North = f South & forall x:X, ap f (merid x) = p0 })
    as [p0 allpath_p0] by auto.
  apply (Susp_rect (fun a => f a = f North) 1 p0^).
  intros x. 
  apply (concat (transport_paths_Fl _ _)).
  apply (concat (concat_p1 _)).
  apply ap, allpath_p0.
Defined.

(** ** The Freudenthal Suspension Theorem *)
Section Freudenthal.

(** We assume funext and univalence.  In fact, since we will use funext at two different levels and local assumptions are monomorphic, we need to assume funext twice; we give the second assumption of it a name (so we can use it explicitly when we want it), and a different type (so it doesn’t get used when we don’t want it). *)
Context `{Funext} (funext_large : Funext * Unit) `{Univalence}
        {n : trunc_index} {Hn : ~ n = minus_two}
        (X : Type) (x0:X) `{IsConnMap n _ _ (unit_name x0)}.

(* TODO: eventually, change these to the weaker assumptions:
Context {n : trunc_index} (X : Type) `{IsConnected (trunc_S n) X}.
*)

(** For convenience, we add some local abbreviations. *)
Notation No := (@North X).
Notation So := (@South X).
Notation mer := (@merid X).
Definition mer' := (fun x => mer x @ (mer x0)^).

(** The eventual theorem we want is: *)
Instance Freudenthal
  : IsConnMap (n -2+ n) (mer').
Proof.
  intros p. apply @isconnected_from_iscontr_truncation.
(** We are not ready to prove this yet.  For the remainder of the section, we will generalize this goal a bit, and prove some auxiliary lemmas; then we will return to the theorem. *)
Abort.

(** The goal we require for the FST is: *)
Definition FST_Codes_No (p : No = No)
  := (Truncation (n -2+ n) (hfiber mer' p)).

(** To prove it, we generalise it over [Susp X], by [Susp_rect].  This requires three components, which we construct (the main parts of) as lemmas in advance. *)
Definition FST_Codes_So (q : No = So)
  := (Truncation (n -2+ n) (hfiber mer q)).

(* TODO: move! *)
Definition hfiber_pair {A B} {f: A -> B} {b} (a:A) (p:f a = b) : hfiber f b
  := (a;p).

Definition FST_Codes_cross (x1 : X) (q : No = So)
  : FST_Codes_No (q @ (mer x1) ^) -> FST_Codes_So q.
Proof.
  unfold FST_Codes_No, FST_Codes_So, mer'.
  apply Truncation_rect_nondep.
  intros [x2 p]. revert x1 x2 p.
  refine (@wedge_incl_elim_uncurried _ _ n n X x0 _ X x0 _
    (fun x1 x2 => (mer x2 @ (mer x0) ^ = q @ (mer x1) ^)
                    -> Truncation (n -2+ n) (hfiber mer q)) _ _).
  apply (conn_pointed_type x0). apply (conn_pointed_type x0).  
  intros; apply trunc_arrow.
  exists (fun b s => truncation_incl (hfiber_pair b (cancelR _ _ _ s))).
  exists (fun a r => truncation_incl (hfiber_pair a
                 (cancelR _ _ _ ((concat_pV _) @ (concat_pV _)^ @ r)))).
  apply path_forall; intros s. apply ap, ap, ap.
  exact ((concat_1p _)^ @ whiskerR (concat_pV _)^ _).
Defined.

(** We will need to show that [FST_Codes_cross] is an equivalence, for each [x1, q]. By connectedness of [X], it will be enough to show this for the case [x1 = x0]; to show this, we first write that case in a tidier form. *)
Definition FST_Codes_cross_x0 (q : No = So)
  : FST_Codes_No (q @ (mer x0)^) -> FST_Codes_So q.
Proof.
  unfold FST_Codes_No, FST_Codes_So.
  apply functor_Truncation, (functor_sigma idmap).
  unfold mer'; intros x1. apply cancelR.
Defined.

Definition isequiv_FST_Codes_cross (x : X) (q : No = So)
  : IsEquiv (FST_Codes_cross x q).
Proof.
  revert x. 
  apply (@conn_map_elim _ _ _ (unit_name x0) _
    (fun x => IsEquiv (FST_Codes_cross x q))).
    intros x; generalize dependent n. intros [ | n'] imposs.
      destruct (imposs 1).
      intros ?. apply (@trunc_leq minus_one). exact tt. apply hprop_isequiv.
  intros []. unfold FST_Codes_cross.
  apply (isequiv_homotopic (FST_Codes_cross_x0 q)). Focus 2.
    apply Truncation_rect. intros ?; apply trunc_succ.
    intros [x r]; simpl.
    unfold functor_sigma; simpl.
    apply symmetry. refine (ap10 (wedge_incl_comp1 x0 x0 _ _ _ _ x) r).
  unfold FST_Codes_cross_x0.
  apply isequiv_functor_Truncation, @isequiv_functor_sigma. refine _.
  intros a. apply isequiv_cancelR.
Defined.

Definition FST_Codes 
  : forall (y : Susp X), (No = y) -> Type.
Proof.
  apply (Susp_rect (fun y => (No = y -> Type)) FST_Codes_No FST_Codes_So).
  intros x. apply (@path_forall (fst funext_large)); intros p.
  refine (transport_arrow _ _ _ @ _).
  refine (transport_const _ _ @ _).
  path_via (FST_Codes_No (p @ (mer x)^)).
    apply ap, transport_paths_r.
  apply path_universe_uncurried.
  exists (FST_Codes_cross x p).
  apply isequiv_FST_Codes_cross.
Defined.

Instance Freudenthal
  : IsConnMap (n -2+ n) (@merid X).
Proof.
  intros p C ? f.
Admitted.

End Freudenthal.