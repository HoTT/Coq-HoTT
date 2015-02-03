(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics HoTT.Types.
Require Import EquivalenceVarieties Idempotents.
Require Import Spaces.BAut Spaces.BAut.Bool.

Local Open Scope path_scope.

(** * An incoherent quasi-idempotent on [BAut (BAut Bool)]. *)

Section IncoherentQuasiIdempotent.
  Context `{Univalence}.

  (** We use the identity map, and the nontrivial 2-central element of [BAut (BAut Bool)]. *)
  Definition nontrivial_qidem_baut_baut_bool
  : IsQuasiIdempotent (preidem_idmap (BAut (BAut Bool)))
    := negb_center2_baut_baut_bool.

  Let s := retract_sect (splitting_preidem_retractof_qidem (preidem_idmap (BAut (BAut Bool)))).
  Let r := retract_retr (splitting_preidem_retractof_qidem (preidem_idmap (BAut (BAut Bool)))).
  Let issect := retract_issect (splitting_preidem_retractof_qidem (preidem_idmap (BAut (BAut Bool)))) : r o s == idmap.

  (** Since the space of splittings of the identity pre-idempotent is contractible, nontriviality of this 2-central element implies that not every quasi-idempotence witness of the identity is recoverable from its own splitting. *)
  Definition splitting_preidem_notequiv_qidem_baut_baut_bool
  : ~ (s o r == idmap).
  Proof.
    intros oops.
    assert (p := oops nontrivial_qidem_baut_baut_bool).
    assert (q := oops (isqidem_idmap (BAut (BAut Bool)))); clear oops.
    apply nontrivial_negb_center_baut_baut_bool.
    refine (p^ @ ap s _ @ q).
    pose (contr_splitting_preidem_idmap (BAut (BAut Bool))).
    apply path_contr.
  Defined.

  (** Therefore, not every quasi-idempotence witness is obtainable from *any* splitting, i.e. it may not have any coherentification. *)
  Definition not_all_coherent_qidem_baut_baut_bool
  : ~ (forall q : IsQuasiIdempotent (preidem_idmap (BAut (BAut Bool))),
         { S : Splitting_PreIdempotent (preidem_idmap _) & s S = q }).
  Proof.
    intros oops.
    assert (IsEquiv s).
    { apply isequiv_biinv; split.
      - exists r; exact issect.
      - exists (fun q => (oops q).1).
        exact (fun q => (oops q).2). }
    apply splitting_preidem_notequiv_qidem_baut_baut_bool; intros q.
    refine (ap s (ap r (eisretr s q)^) @ _).
    refine (ap s (issect (s^-1 q)) @ _).
    apply eisretr.
  Defined.

  (** These results show only that not *every* quasi-idempotence witness is coherent.  "Clearly" the nontrivial quasi-idempotence witness [nontrivial_qidem_baut_baut_bool] should be the one that is not coherent.  To show this, we would probably need to show that [isqidem_idmap] *is* in the image of [s], and this seems rather annoying to do based on our construction of [splitting_preidem_retractof_qidem]. *)

End IncoherentQuasiIdempotent.
