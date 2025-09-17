(** * The fan theorem *)

From HoTT Require Import Basics Types. 
Require Import Truncations.Core.
Require Import Spaces.Nat.Core.
Require Import Misc.UStructures BarInduction. 
Require Import Spaces.NatSeq.Core Spaces.NatSeq.UStructure.
Require Import Spaces.List.Core Spaces.List.Theory.

Local Open Scope nat_scope.
Local Open Scope type_scope.
Local Open Scope list_scope.

Definition DecidableFanTheorem (A : Type) :=
  forall (B : list A -> Type)
  (dec : forall l : list A, Decidable (B l))
  (bar : IsBar B),
  IsUniformBar B.

Definition MonotoneFanTheorem (A : Type) :=
  forall (B : list A -> Type)
  (mon : IsMonotone B)
  (bar : IsBar B),
  IsUniformBar B.

Definition FanTheorem (A : Type) :=
  forall (B : list A -> Type)
  (bar : IsBar B),
  IsUniformBar B.

Definition fantheorem_empty : FanTheorem Empty.
Proof.
  intros B bB.
  exists 0.
  intro s.
  contradiction (s 0).
Defined.

Definition fantheorem_contr (A : Type) `{Contr A} : FanTheorem A.
Proof.
  intros B bB.
  pose (c := fun (_ : nat) => center A).
  exists (bB c).1.
  intro s.
  assert (p : forall n : nat, list_restrict s n = list_restrict c n).
  { intro n.
    srapply path_list_nth'.
    1: by rewrite !length_list_restrict.
    intros m h.
    by apply path_contr. }
  exists (bB c).1; split.
  - reflexivity.
  - rewrite p.
    exact (bB c).2.
Defined.

(** The family we use when applying the fan theorem in our proof that continuity implies uniform continuity. *)
Definition uc_theorem_family {A : Type} (p : (nat -> A) -> Bool)
  : list A -> Type
  := fun l =>
      forall (u v : nat -> A) (h : list_restrict u (length l) = l)
        (h' : list_restrict v (length l) = l), p u = p v.

Definition is_bar_uc_theorem_family {A : Type}
  (p : (nat -> A) -> Bool) (cont : IsContinuous p)
  : IsBar (uc_theorem_family p).
Proof.
  intro s.
  specialize (cont s 0) as [n H].
  exists n.
  intros u v h t.
  symmetry in h,t.
  rewrite length_list_restrict in h, t.
  apply list_restrict_eq_iff_seq_agree_lt in h, t.
  exact ((H _ h)^ @ (H _ t)).
Defined.

(** The fan theorem implies that every continuous function is uniformly continuous. The current proof uses the full fan theorem. Less powerful versions might be enough. *)

Definition uniform_continuity_fantheorem {A : Type} (fan : FanTheorem A)
  (p : (nat -> A) -> Bool) (c : IsContinuous p)
  : uniformly_continuous p.
Proof.
  pose proof (fan' := fan (uc_theorem_family p) (is_bar_uc_theorem_family p c)).
  destruct fan' as [n ub].
  intro m.
  exists n.
  intros u v h.
  specialize (ub v) as [k [bound uctf]].
  apply uctf.
  - rewrite length_list_restrict.
    apply (snd list_restrict_eq_iff_seq_agree_lt).
    apply (us_rel_leq bound h).
  - exact (ap _ (length_list_restrict _ _)).
Defined.
