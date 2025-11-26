(** * Uniform structure on types of sequences *)

From HoTT Require Import Basics Types.
Require Import Spaces.Nat.Core.
Require Import Misc.UStructures.
Require Import List.Core List.Theory.
Require Import Spaces.NatSeq.Core.

Local Open Scope nat_scope.
Local Open Scope type_scope.

(** ** [UStructure] defined by [seq_agree_lt] *)

(** Every type of the form [nat -> X] carries a uniform structure defined by the [seq_agree_lt n] relation for every [n : nat]. *)
Instance sequence_type_us {X : Type} : UStructure (nat -> X) | 10.
Proof.
  snapply Build_UStructure.
  - exact seq_agree_lt.
  - exact (fun _ _ _ _ => idpath).
  - exact (fun _ _ _ h _ _ => (h _ _)^).
  - exact (fun _ _ _ _ h1 h2 _ _ => ((h1 _ _) @ (h2 _ _))).
  - exact (fun _ _ _ h _ _ => h _ _).
Defined.

Definition sequence_type_us_zero {X : Type} (s t : nat -> X) : s =[0] t
  := fun n hn => Empty_rec (not_lt_zero_r n hn).

Definition seq_cons_of_eq {X : Type} {n : nat} {s t : nat -> X} {x : X}
  (h : s =[n] t)
  : (seq_cons x s) =[n.+1] (seq_cons x t).
Proof.
  intros m hm; destruct m.
  - reflexivity.
  - exact (h m _).
Defined.

(** We can also rephrase the definition of [seq_agree_lt] using the [list_restrict] function. *)
Definition list_restrict_eq_iff_seq_agree_lt
  {A : Type} {n : nat} {s t : nat -> A}
  : (list_restrict s n = list_restrict t n) <-> s =[n] t.
Proof.
  constructor.
  - intros h m hm.
    lhs_V exact (nth'_list_restrict s ((length_list_restrict _ _)^ # hm)).
    rhs_V exact (nth'_list_restrict t ((length_list_restrict _ _)^ # hm)).
    exact (nth'_path_list h _ _).
  - intro h.
    apply (path_list_nth' _ _
            (length_list_restrict s n @ (length_list_restrict t n)^)).
    intros i Hi.
    lhs snapply nth'_list_restrict.
    rhs snapply nth'_list_restrict.
    exact (h i ((length_list_restrict s n) # Hi)).
Defined.

Definition list_restrict_eq_iff_seq_agree_inductive
  {A : Type} {n : nat} {s t : nat -> A}
  : list_restrict s n = list_restrict t n <-> seq_agree_inductive n s t
  := iff_compose
      list_restrict_eq_iff_seq_agree_lt
      seq_agree_lt_iff_seq_agree_inductive.

(** ** Continuity *)

(** Following https://martinescardo.github.io/TypeTopology/TypeTopology.CantorSearch.html#920.  *)

(** A uniformly continuous function takes homotopic sequences to outputs that are equivalent with respect to the structure on [Y]. *)
Definition uniformly_continuous_extensionality
  {X Y : Type} {usY : UStructure Y} (p : (nat -> X) -> Y) {m : nat}
  (c : uniformly_continuous p)
  {u v : nat -> X} (h : u == v)
  : p u =[m] p v
  := (c m).2 u v (fun m _ => h m).

(** Composing a uniformly continuous function with the [cons] operation decreases the modulus by 1. Maybe this can be done with greater generality for the structure on [Y]. *)
Definition cons_decreases_modulus {X Y : Type}
  (p : (nat -> X) -> Y) (n : nat) (b : X)
  (hSn : is_modulus_of_uniform_continuity n.+1 p)
  : is_modulus_of_uniform_continuity n (p o seq_cons b).
Proof.
  intros u v huv.
  apply hSn.
  exact (seq_cons_of_eq huv).
Defined.
