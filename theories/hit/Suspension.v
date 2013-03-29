(* -*- mode: coq; mode: visual-line -*- *)

(** * The suspension of a type *)

Require Import Overture PathGroupoids Fibrations Contractible Trunc Sigma Forall Arrow Paths Universe Unit Connectedness TruncType.
Local Open Scope path_scope.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

(* ** Definition of suspension. *)

Module Export Suspension.

Local Inductive Susp (X : Type) : Type :=
  | North : Susp X
  | South : Susp X.

Global Arguments North {X}.
Global Arguments South {X}.

Axiom merid : forall (X : Type) (x : X), North = South :> Susp X.
Global Arguments merid {X} x.

Definition Susp_rect {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S)
: forall (y:Susp X), P y
:= fun y => match y with North => H_N | South => H_S end.

Axiom Susp_comp_merid : forall {X : Type} (P : Susp X -> Type)
  (H_N : P North) (H_S : P South)
  (H_merid : forall x:X, (merid x) # H_N = H_S)
  (x:X),
apD (Susp_rect P H_N H_S H_merid) (merid x) = H_merid x.

End Suspension.

(* ** Non-dependent eliminator. *)

Definition Susp_rect_nd {X Y : Type}
  (H_N H_S : Y) (H_merid : X -> H_N = H_S)
: Susp X -> Y.
Proof.
  apply (Susp_rect (fun _ => Y) H_N H_S).
  intros x. exact (transport_const _ _ @ H_merid x).
Defined.

Definition Susp_comp_nd_merid {X Y : Type}
  {H_N H_S : Y} {H_merid : X -> H_N = H_S} (x:X)
: ap (Susp_rect_nd H_N H_S H_merid) (merid x) = H_merid x.
Proof.
  apply (cancelL (transport_const (merid x) H_N)).
  path_via (apD (Susp_rect_nd H_N H_S H_merid) (merid x)).
  symmetry; refine (apD_const (Susp_rect_nd H_N H_S H_merid) _).
  refine (Susp_comp_merid (fun _ : Susp X => Y) _ _ _ _).
Defined.

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

Section Auxiliary.

Context `{Funext} `{Univalence}.

(* TODO: move!  Also: better name?  “Constant” or similar is tempting — but that is not quite right, since this retains the element of Y.  E.g. the unique map (0 -> Y) should surely be constant in just one way, rather than in Y-many ways. *)
Definition NullHomotopy {X Y : Type} (f : X -> Y)
  := {y : Y & forall x:X, f x = y}.

Lemma istrunc_nullhomotopy {X Y : Type} (f : X -> Y) `{IsTrunc n Y} 
  : IsTrunc n (NullHomotopy f).
Proof.
  apply @trunc_sigma; auto.
  intros y. apply (@trunc_forall _). 
  intros x. apply trunc_succ.
Defined.

End Auxiliary.

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
  assert (forall 
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

(* Claim: enough to (a) construct this function in general, (b) show that it’s an equivalence at x0. *)
Admitted.

End Fix_C.

Instance Freudenthal
  : IsConnMap (n -2+ n) (@merid X).
Proof.
  intros p C ? f.
Admitted.

End Freudenthal.