(* -*- mode: coq; mode: visual-line -*- *)

(** * The Freudenthal Suspension Theorem, and related results. *)

Require Import Overture PathGroupoids Fibrations Trunc Forall Sigma Paths Unit Universe Arrow Connectedness Suspension Spheres.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

(* ** Connectedness of the suspension *)

Instance isconn_susp {n : trunc_index} {X : Type} `{IsConnected n X}
  : IsConnected (trunc_S n) (Susp X).
Proof.
  intros C ? f. exists (f North).
  assert ({ p0 : f North = f South & forall x:X, ap f (merid x) = p0 })
    as [p0 alleq_p0] by auto.
  apply (Susp_rect (fun a => f a = f North) 1 p0^).
  intros x. 
  apply (concat (transport_paths_Fl _ _)).
  apply (concat (concat_p1 _)).
  apply ap, alleq_p0.
Defined.

(** ** The Freudenthal Suspension Theorem *)
Section Freudenthal.

Context `{Funext} `{Univalence}.

Context {n : trunc_index} (X : Type) (x0:X) `{IsConnMap n _ _ (unit_name x0)}.

(* TODO: eventually, change these to the weaker assumptions:
Context {n : trunc_index} (X : Type) `{IsConnected (trunc_S n) X}.
*)

Notation No := (@North X).
Notation So := (@South X).
Notation mer := (@merid X).
Definition mer' := (fun x => mer x @ (mer x0)^).

(** The eventual theorem we want is: *)
Instance Freudenthal
  : IsConnMap (n -2+ n) (@merid X).
Proof.
  intros p C ? f.
(** We are not ready to prove this.  For the remainder of the section, we will fix some suitably truncated [C], and show that for all [p], [f], the current goal holds; we will then return to this theorem. *)
Abort.

Section Fix_C.

Context (C : Type) `{IsTrunc (n -2+ n) C}.

(** The goal we require for the FST is: *)
Definition FST_Codes_So (p : No = So :> Susp X)
  := forall (f : hfiber mer p -> C), NullHomotopy f.

(** To prove it, we generalise it over [Susp X], by [Susp_rect].  This requires three components, which we construct (the main parts of) as lemmas in advance. *)
Definition FST_Codes_No (p : No = No :> Susp X)
  := forall (f : hfiber mer' p -> C), NullHomotopy f.

Definition FST_Codes_cross (x1 : X) (p : No = So)
  : FST_Codes_No (p @ (mer x1) ^) -> FST_Codes_So p.
Proof.
  unfold FST_Codes_No, FST_Codes_So, mer'.
  intros HH f.
Admitted.

Definition isequiv_FST_Codes_cross (x : X) (p : No = So)
  : IsEquiv (FST_Codes_cross x p).
Proof.
  case n as [ | n'].
    admit. (* Oops, should have ruled out this case earlier! *)
  revert x. apply (@conn_map_elim (trunc_S n') _ _ (unit_name x0)).
    assumption. (* Trying to infer this just spins. *)
    admit.  (*Need leq on trunc_levels!*)
  intros [].
Admitted.

Definition FST_Codes 
  : forall (y : Susp X), (No = y) -> Type.
Proof.
  apply (Susp_rect (fun y => (No = y -> Type)) FST_Codes_No FST_Codes_So).
  intros x. apply path_forall; intros p.
  refine (transport_arrow _ _ _ @ _).
  refine (transport_const _ _ @ _).
  path_via (FST_Codes_No (p @ (mer x)^)).
    apply ap, transport_paths_r.
  apply path_universe_uncurried.
  exists (FST_Codes_cross x p).
  apply isequiv_FST_Codes_cross.
Defined.

End Fix_C.

Instance Freudenthal
  : IsConnMap (n -2+ n) (@merid X).
Proof.
  intros p C ? f.
Admitted.

End Freudenthal.