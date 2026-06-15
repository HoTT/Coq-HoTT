From HoTT Require Import Basics Types Truncations.Core.
Require Import Spaces.Nat.Core.
Require Import AbGroups.AbelianGroup AbGroups.AbProjective.
Require Import Algebra.AbSES.Core Algebra.AbSES.HigherExt.
Require Import Groups.Group.

Local Open Scope nat_scope.

(** * Vanishing of higher Ext above a projective resolution

    Following the dimension-shifting argument behind Christensen and Flaten,
    Proposition 2.5.4: if a short exact sequence has projective middle and its
    kernel already has vanishing Ext one degree down, then [B] has vanishing
    Ext one degree further up. *)

(** The dimension-shift step: splicing with a projective-middle sequence carries
    the vanishing of [Ext^{m+1}(K,-)] to the vanishing of [Ext^{m+2}(B,-)]. *)
Definition abses_ext_vanish_step `{Univalence} {K B : AbGroup} (zeta : AbSES B K)
  `{IsAbProjective (middle zeta)} {A : AbGroup} (m : nat)
  (hK : forall x : abses_ext m.+1 K A, x = abses_ext_zero m.+1 K A)
  (x : abses_ext m.+2 B A)
  : x = abses_ext_zero m.+2 B A.
Proof.
  pose proof (abses_ext_splice_projective_surjective zeta m.+1 x) as hsurj.
  strip_truncations; destruct hsurj as [y py].
  refine (py^ @ ap (abses_ext_splice m.+1 zeta) (hK y) @ _).
  exact (grp_homo_unit (grp_homo_abses_ext_splice m.+1 zeta)).
Defined.

(** A projective resolution of length [k]: a tower of short exact sequences with
    projective middles ending in a projective module. *)
Fixpoint proj_resolution `{Univalence} (k : nat) (B : AbGroup@{u}) : Type :=
  match k with
  | 0%nat => IsAbProjective B
  | S k => { K : AbGroup@{u}
             & { zeta : AbSES B K
               & (IsAbProjective (middle zeta) * proj_resolution k K)%type } }
  end.

(** Higher Ext vanishes above the length of a projective resolution. *)
Definition abses_ext_vanish_resolution `{Univalence} (k : nat)
  : forall (B : AbGroup@{u}), proj_resolution k B
    -> forall (A : AbGroup@{u}) (n : nat) (x : abses_ext (k + n).+1 B A),
       x = abses_ext_zero (k + n).+1 B A.
Proof.
  induction k as [|k IH]; intros B res A n x.
  - assert (res' : IsAbProjective B) by exact res.
    exact (abses_ext_projective_vanish n x).
  - destruct res as [K [zeta [hp rK]]].
    refine (abses_ext_vanish_step zeta (k + n) _ x).
    intro y.
    exact (IH K rK A n y).
Defined.
