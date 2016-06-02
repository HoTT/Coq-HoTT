Require Import HoTTClasses.interfaces.abstract_algebra.
Require Export HoTT.Types.Bool.

Instance bool_bottom: Bottom Bool := false.
Instance bool_top: Top Bool := true.
Instance bool_join: Join Bool := orb.
Instance bool_meet: Meet Bool := andb.

Lemma orb_assoc : Associative orb.
Proof.
intros [|] [|] [|];reflexivity.
Qed.

Lemma orb_false_r : forall b, orb b false = b.
Proof.
intros [|];reflexivity.
Qed.

Lemma orb_comm : Commutative orb.
Proof.
intros [|] [|];reflexivity.
Qed.

Lemma orb_diag : forall b, orb b b = b.
Proof.
intros [|];reflexivity.
Qed.

Instance: BoundedJoinSemiLattice Bool.
Proof.
repeat split.
- apply orb_assoc.
- exact orb_false_r.
- apply orb_comm.
- exact orb_diag.
Qed.

Lemma andb_assoc : Associative andb.
Proof.
intros [|] [|] [|];reflexivity.
Qed.

Lemma andb_comm : Commutative andb.
Proof.
intros [|] [|];reflexivity.
Qed.

Lemma andb_diag : BinaryIdempotent andb.
Proof.
intros [|];reflexivity.
Qed.

Instance: MeetSemiLattice Bool.
Proof.
repeat split.
- apply andb_assoc.
- apply andb_comm.
- apply andb_diag.
Qed.

Lemma absorption_orb : Absorption join meet.
Proof.
intros [|] [|];reflexivity.
Qed.

Lemma absorption_andb : Absorption meet join.
Proof.
intros [|] [|];reflexivity.
Qed.

Lemma orb_andb_distrib_r : LeftDistribute join meet.
Proof.
intros [|] [|] [|];reflexivity.
Qed.

Instance: DistributiveLattice Bool.
Proof.
repeat (split; try apply _).
- apply absorption_orb.
- apply absorption_andb.
- apply orb_andb_distrib_r.
Qed.

(* We don't have a boolean algebra class yet *)