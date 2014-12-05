(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import HoTT.Tactics.

Local Open Scope path_scope.
Local Open Scope equiv_scope.

(** * Splitting of Idempotents *)

(** The naive definition of "idempotent" would be a morphism [f : X -> X] such that [forall x, f (f x) = f x].  However, homotopically we may naturally expect to need some coherence on the witness to idempotency.  Indeed, in homotopy theory there are "idempotents" in this sense which do not split; see for instance Warning 1.2.4.8 in *Higher Algebra*.

A priori, a "coherent idempotent" would involve infinitely many data.  However, Lemma 7.3.5.14 of *Higher Algebra* suggests that for an idempotent to be coherent (or, at least, coherentifiable), it suffices to have *one* additional datum.  By modifying the construction given there, we can show in type theory that any idempotent satisfying an additional coherence datum splits. *)

Section CoherentIdempotents.
  (** We need funext because our construction will involve a sequential limit.  We could probably also use a HIT sequential colimit, which is more like what Lurie does. *)
  Context `{Funext}.
  Context {X : Type} (f : X -> X) (I : forall x, f (f x) = f x).
  (** Here is the extra coherence datum. *)
  Context (J : forall x, ap f (I x) = I (f x)).

  (** The splitting will be the sequential limit of the sequence [... -> X -> X -> X]. *)
  Definition split_idempotent : Type
    := { a : nat -> X & forall n, f (a (n.+1)) = a n }.

  Definition split_idempotent_pr1 : split_idempotent -> (nat -> X)
    := pr1.
  Coercion split_idempotent_pr1 : split_idempotent >-> Funclass.
  Arguments split_idempotent_pr1 / .

  (** The section, retraction, and the fact that the composite in one direction is [f] are easy. *)

  Definition split_idempotent_sect : split_idempotent -> X
    := fun a => a 0.
  Arguments split_idempotent_sect / .

  Definition split_idempotent_retr : X -> split_idempotent.
  Proof.
    intros x.
    exists (fun n => f x).
    exact (fun n => I x).
  Defined.
  Arguments split_idempotent_retr / .

  Definition split_idempotent_splits (x : X)
  : split_idempotent_sect (split_idempotent_retr x) = f x
    := 1.

  (** What remains is to show that the composite in the other direction is the identity.  We begin by showing how to construct paths in [split_idempotent]. *)

  Definition path_split_idempotent {a a' : split_idempotent}
             (p : a.1 == a'.1)
             (q : forall n, a.2 n @ p n
                            = ap f (p n.+1) @ a'.2 n)
  : a = a'.
  Proof.
    refine (path_sigma' _ _ _).
    - apply path_arrow; intros n.
      exact (p n).
    - apply path_forall; intros n.
      rewrite transport_forall_constant.
      rewrite transport_paths_FlFr.
      rewrite ap_apply_l, ap10_path_arrow.
      rewrite (ap_compose (fun b => b n.+1) (fun x => f x) _).
      rewrite ap_apply_l, ap10_path_arrow.
      rewrite concat_pp_p.
      apply moveR_Vp; by symmetry.
  Qed.

  (** Next we show that every element of [split_idempotent] can be nudged to an equivalent one in which all the elements of [X] occurring are double applications of [f]. *)

  Local Definition nudge (a : split_idempotent) : split_idempotent.
  Proof.
    exists (fun n => f (f (a (n.+1)))).
    exact (fun n => ap f (ap f (a.2 n.+1))).
  Defined.

  Local Definition nudge_eq a : nudge a = a.
  Proof.
    transparent assert (a' : split_idempotent).
    { exists (fun n => f (a (n.+1))).
      exact (fun n => ap f (a.2 n.+1)). }
    transitivity a'; refine (path_split_idempotent _ _); intros n; simpl.
    - exact (I (a n.+1)).
    - exact ((ap_compose f f _ @@ 1)^
               @ concat_Ap I (a.2 n.+1)
               @ (J _ @@ 1)^).
    - exact (a.2 n).
    - reflexivity.
  Defined.

  (** Now we're ready to prove the final condition. *)

  Definition split_idempotent_issect (a : split_idempotent)
  : split_idempotent_retr (split_idempotent_sect a) = a.
  Proof.
    refine (_ @ nudge_eq a); symmetry.
    transparent assert (p : (forall n, f (f (a n.+1)) = f (a 0))).
    { induction n as [|n IH].
      - exact (ap f (a.2 0)).
      - exact ((I (f (a n.+2)))^ @ (ap f (ap f (a.2 n.+1))) @ IH). }
    refine (path_split_idempotent _ _); [ exact p | intros n; simpl ].
    induction n as [|n IH]; simpl.
    Open Scope long_path_scope.
    - rewrite !ap_pp, ap_V.
      rewrite_moveL_Vp_p.
      rewrite J.
      rewrite <- !ap_pp.
      with_rassoc ltac:(rewrite <- !ap_pp).
      rewrite <- ap_compose.
      exact ((concat_Ap I (ap f (a.2 1%nat) @ a.2 0))^).
    - (* For some reason [rewrite concat_pp_p] here rewrites *twice*? *)
      refine ((1 @@ concat_pp_p _ _ _) @ _).
      rewrite IH.
      rewrite !ap_pp, !concat_p_pp.
      do 4 apply whiskerR.
      rewrite ap_V; apply moveL_Vp; rewrite concat_p_pp; apply moveR_pV.
      refine (_ @ (ap_compose f f _ @@ 1)).
      rewrite J.
      exact ((concat_Ap I (ap f (a.2 n.+2)))^).
    Close Scope long_path_scope.
  Qed.

  (** Note that a splitting of [f] induces a witness of idempotency of [f] and also any amount of coherence on it that one might ask for.  We ought in theory to investigate whether these witnesses arising from this splitting agree with the given [I] and [J]. *)

End CoherentIdempotents.
