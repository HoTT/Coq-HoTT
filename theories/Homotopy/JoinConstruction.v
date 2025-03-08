Require Import Basics Types.
Require Import Limits.Pullback Colimits.Pushout Diagrams.Diagram Diagrams.Sequence Colimits.Colimit Colimits.Sequential.
Require Import Join.Core.
Require Import NullHomotopy.
Require Import Universes.Smallness.

Local Set Printing Universes.

(** * The Join Construction *)

(** ** Propositional Truncation *)

(** Instead of using the propositional truncation defined in Truncations.Core, we instead give a simpler definition here out of simple HITs. This way we can break dependencies and also manage universe levels better. *)
(** TODO: this should be used in Truncations.Core instead of the other definition. *)

Definition merely@{i j} (A : Type@{i}) : Type@{j}.
Proof.
  (** The propositional truncation of a type will be the infinite join power, or the colimit of the sequence of the nth join power. First we define this sequence. *)
  transparent assert (s : Sequence@{j j j}).
  { snrapply Build_Sequence.
    - exact (iterated_join A).
    - intros n.
      apply pushr. }
  (** Then we define the colimit of this sequence. *)
  exact (Colimit s).
Defined.

Definition merely_in@{i j} {A : Type@{i}} (x : A) : merely A.
Proof.
  snrapply colim.
  1: exact O.
  exact x.
Defined.

(** A sequence of null-homotopic maps has a contractible colimit. This is already proven in Sequential.v but we state the hypotheses a little differently here.  *)
Lemma contr_seq_colimit_nullhomotopic `{Funext} (s : Sequence) (x : s O)
  (is_null : forall n : nat, NullHomotopy (@arr (sequence_graph) s n n.+1%nat idpath))
  : Contr (Colimit s).
Proof.
  snrapply contr_colim_seq_into_prop.
  - intros n.
    destruct n.
    + exact x.
    + exact (is_null n).1.
  - intros n y.
    symmetry.
    exact ((is_null n).2 y).
Defined.

Definition merely_rec@{i j k} (A : Type@{i}) (P : Type@{j}) `{IsHProp P}
  : (A -> P) -> merely@{i k} A -> P.
Proof.
  intros f.
  apply Colimit_rec@{i k k k k k k}.
  snrapply Cocone.Build_Cocone.
  2: intros ? ? ? ?; nrapply path_ishprop; exact _.
  simpl.
  intros n.
  induction n.
  1: exact f.
  snrapply Join_rec.
  - exact f.
  - exact IHn.
  - intros ? ?; nrapply path_ishprop; exact _.
Defined.

(* TODO: move *)
Lemma nullhomotopy_joinr (A B : Type) (x : A) : NullHomotopy (@joinr A B).
Proof.
  exists (joinl x).
  intros y.
  symmetry.
  apply jglue.
Defined.

(* TODO: move *)
Lemma nullhomotopy_joinl (A B : Type) (y : B) : NullHomotopy (@joinl A B).
Proof.
  exists (joinr y).
  intros x.
  apply jglue.
Defined.

Global Instance ishprop_merely@{i j} `{Funext} (A : Type@{i})
  : IsHProp (merely@{i j} A).
Proof.
  apply hprop_inhabited_contr.
  rapply merely_rec.
  intros x.
  apply contr_seq_colimit_nullhomotopic.
  - exact x.
  - intros m.
    simpl.
    apply nullhomotopy_joinr.
    exact x.
Defined.

(** We can construct the homotopy image of a map [f : A -> B] using this definition of propositional truncation, which we will later show to be essentially small. *)
Definition himage@{i j} {A : Type@{i}} {B : Type@{j}} (f : A -> B) : Type@{j}
  := {y : B & merely@{j j} (hfiber f y)}.

(** ** Essentially Small and Locally Small Types *)
(* 
(** A type in a universe [v] is essentially small, with respect to a strictly smaller universe [u], if there is a type in the universe [u] that is equivalent to it. *)
Definition IsEssentiallySmall@{u v | u < v} (A : Type@{v})
  := {B : Type@{u} & A <~> B}.

(** A type is locally small if all of its path types are essentially small. *)
Definition IsLocallySmall@{u v | u < v} (A : Type@{v})
  := forall x y : A, IsEssentiallySmall@{u v} (x = y).

(** Under univalence, being essentially small is a proposition. *)
Global Instance ishprop_isessentiallysmall@{u v} `{Univalence} (A : Type@{v})
  : IsHProp (IsEssentiallySmall@{u v} A).
Proof.
  apply hprop_allpath.
  intros [X e] [X' e'].
  snrapply path_sigma.
  - apply path_universe_uncurried.
    exact (e' oE e^-1).
  - apply path_equiv.
    lhs nrapply (transport_equiv' (path_universe_uncurried (e' oE e^-1)) e).
    funext x; simpl.
    rewrite transport_const.
    rewrite transport_path_universe.
    apply ap, eissect.
Defined. *)

(** Therefore, so is being locally small. *)
(* Global Instance ishprop_islocallysmall@{u v} `{Univalence} (A : Type@{v})
  : IsHProp (IsEssentiallySmall@{u v} A) := _. *)

(** A sigma type is essentially small if both of its types are essentially small. *)
(* Definition isessentiallysmall_sigma@{u v k | u <= v, v < k}
  `{Funext} (A : Type@{u}) (P : A -> Type@{v})
  (ies_A : IsSmall@{u k} A)
  (ies_P : forall x, Ismall@{v k} (P x))
  : IsEssentiallySmall@{v k} {x : A & P x}.
Proof.
  eexists.
  nrapply (equiv_functor_sigma'@{u v _ _ k k} ies_A.2).
  nrapply (equiv_ind@{u v k} ies_A.2^-1%equiv).
  1: exact _.
  intros x.
  nrefine (equiv_path@{v k} _ _ _ oE _).
  { apply ap.
    symmetry.
    apply eisretr. }
  exact (ies_P ((ies_A.2)^-1%equiv x)).2.
Defined. *)

(** Every small type is trivially essentially small *)
(* Definition isessentiallysmall_small@{u v} (A : Type@{u})
  : IsEssentiallySmall@{u v} A.
Proof.
  exists A.
  exact equiv_idmap.
Defined. *)

(** The join of two small types is small. *)
Global Instance issmall_join@{u k l big | l < big, u <= l, k <= l}
  (A : Type@{k}) (B : Type@{k})
  (sA : IsSmall@{u k} A) (sB : IsSmall@{u k} B)
  : IsSmall@{u k} (Join@{k k k} A B)
  := Build_IsSmall@{u k}
      (Join@{k k k} A B)
      (Join@{u u u} (smalltype@{u k} A) (smalltype@{u k} B))
      (equiv_functor_join@{u u k k u k l big}
        (equiv_smalltype@{u k} A)
        (equiv_smalltype@{u k} B)).

(** And by induction, the iterated join of a small type is small. *)
Definition issmall_iterated_join@{v k vk big | v <= vk, k <= vk, vk < big}
  (A : Type@{k}) (sA : IsSmall@{v k} A) (n : nat)
  : IsSmall@{v k} (iterated_join@{k} A n).
Proof.
  simple_induction' n.
  - exact sA.
  - by nrapply issmall_join@{v k vk big}.
Defined.

(** A sequential colimit of essentially small types is essentially small. *)
Definition issmall_seq_colimit@{u k uk | u <= uk, k <= uk} `{Funext} (s : Sequence@{k k k})
  (ss : forall n, IsSmall@{u k} (s n))
  : IsSmall@{u k} (Colimit@{k k k k k k k} s).
Proof.
  (** First we build a sequence in the universe [u] from a sequence [s] by replacing each type with a type in the universe [v] with the small version. *)
  snrefine (let s' : Sequence@{u u u} := _ in _).
  { snrapply Build_Sequence@{u u u}.
    - intros n.
      exact (smalltype@{u k} (s n)).
    - hnf; intros n.
      intros x.
      refine (equiv_inv@{u k}
        (f := @equiv_smalltype@{u k} _ (ss n.+1%nat)) _).
      snrapply (sequence_arr s n).
      exact (equiv_fun@{u k} (equiv_smalltype@{u k} _) x). }
  exists (Colimit@{u u u u u u u} s').
  snrapply (equiv_functor_colimit (D1 := s) (D2 := s')).
  - snrapply Build_diagram_equiv.
    + snrapply Build_SequenceMap.
      * intros n.
        exact (equiv_smalltype@{u k} (s n))^-1.
      * intros n f.
        simpl.
        f_ap; f_ap; symmetry.
        apply eisretr.
    + exact _.
  - exact _.
  - exact _.
Admitted.

(*
  (** We also need a lifted version of [s'] since the record types involved are not cumulative. *)
  snrefine (let s'' : Sequence@{uk uk uk} := _ in _).
  { snrapply Build_Sequence@{uk uk uk}.
    - exact s'.
    - snrapply (sequence_arr@{uk uk uk} s'). }
  exists (Colimit@{u u u u u u u} s').
  About equiv_functor_colimit
    @{u0 u1 u u u u u u7 u8 u9
      u10 u11 u12 u13 u14 u15 u16 u17 u18 u19
      u20 u21 u22 u23 u24 u25 u26 u27 u28 u29}.
  snrefine (equiv_functor_colimit
    @{u0 u1 u2 u3 u4 u5 u6 u7 u8 u9
      u10 u11 u12 u13 u14 u15 u16 u17 u18 u19
      u20 u21 u22 u23 u24 u25 u26 u27 u28 u29}
    (G:=sequence_graph) (D1 := s'') (D2 := s') _ _ _).
  { snrapply Build_diagram_equiv.
    { snrapply Build_DiagramMap.
      - intros n.
        exact (equiv_smalltype@{u k} (s' n))^-1.
      - intros n ? p; destruct p; intros x; simpl.
        simpl.
        f_ap; f_ap. }
    exact _. }
  (* 1: snrapply iscolimit_colimit. *)
  1: exact _.
  1: exact _.
Defined.
*)

(** ** Fiber-wise joins of maps *)

(** The fiber-wise join of two maps is the generalization of the join of two spaces, which can be thought of as the fiber-wise join of maps [A -> 1] and [B -> 1]. The fiber-wise join of two maps [f : A -> X] and [g : B -> X] is the pushout of the projections of the pullback of [f] and [g]. *)
Definition FiberwiseJoin@{a b x k}
  {A : Type@{a}} {B : Type@{b}} (X : Type@{x}) (f : A -> X) (g : B -> X)
  : Type@{k}.
Proof.
  nrapply Pushout@{k k k k}.
  - exact (pullback_pr1@{_ _ _ k} (f := f) (g := g)).
  - exact (pullback_pr2@{_ _ _ k}(f := f) (g := g)).
Defined.

(** We can iterate the fiber-wise join for a single map [f : A -> X] to get the fiber-wise join powers. We need to mutually recursively define a type and also a map out of that type. This isn't currently possible with Coq, so we package up both pieces of data in a sigma type and then later project out of it. *)
Record Fiberwise_join_power_data@{u v k}
  {A : Type@{u}} {X : Type@{v}} (f : A -> X) : Type@{k} := {
  fiberwise_join_power_data : Type@{v};
  fiberwise_join_power_data_map : fiberwise_join_power_data -> X;
}.

Fixpoint fiberwise_join_power_and_map@{u v k | u <= v, v < k}
  {A : Type@{u}} {X : Type@{v}} (f : A -> X) (n : nat)
  : @Fiberwise_join_power_data@{u v k} A X f .
Proof.
  destruct n.
  - exists Empty.
    apply Empty_rec.
  - pose (map := (fiberwise_join_power_data_map _ (fiberwise_join_power_and_map A X f n))).
    exists (FiberwiseJoin@{u v v v} X f map).
    snrapply (Pushout_rec@{v v v v v} X f map).
    intros [x [y p]].
    exact p.
Defined.

Definition fiberwise_join_power@{u v k | u <= v, v < k}
  {A : Type@{u}} {X : Type@{v}} (f : A -> X) (n : nat)
  := fiberwise_join_power_data _ (fiberwise_join_power_and_map@{u v k} f n).

Definition fiberwise_join_power_map@{u v k | u <= v, v < k}
  {A : Type@{u}} {X : Type@{v}} (f : A -> X) (n : nat)
  : fiberwise_join_power@{u v k} f n -> X
  := fiberwise_join_power_data_map _ (fiberwise_join_power_and_map@{u v k} f n).

(** Between successive powers there is an inclusion map. *)
Definition fiberwise_join_power_incl@{u v k | u <= v, v < k}
  {A : Type@{u}} {X : Type@{v}} (f : A -> X) (n : nat)
  : fiberwise_join_power f n -> fiberwise_join_power f n.+1.
Proof.
  destruct n.
  - apply Empty_rec.
  - apply pushr.
Defined.

(** This inclusion map commutes appropriately with the maps to [X]. *)
Lemma fiberwise_join_power_incl_comm@{u v k | u <= v, v < k}
  {A : Type@{u}} {X : Type@{v}} (f : A -> X) (n : nat)
  : fiberwise_join_power_map f n.+1 o fiberwise_join_power_incl f n
    == fiberwise_join_power_map f n.
Proof.
  destruct n.
  1: nrapply Empty_ind.
  intros x.
  reflexivity.
Defined.

(** ** Infinite Fiber-wise Join Powers *)

(** The sequence of fiber-wise join power consists of the nth fiber-wise join power and the inclusion map. *)
Definition seq_fiberwise_join_power@{u v k | u <= v, v < k}
  {A : Type@{u}} {X : Type@{v}} (f : A -> X)
  : Sequence@{v v v}.
Proof.
  snrapply Build_Sequence.
  - exact (fiberwise_join_power@{u v k} f).
  - exact (fiberwise_join_power_incl@{u v k} f).
Defined.

(** Infinite fiber-wise join powers are defined as the colimit of the sequence of fiber-wise join powers. *)
Definition infinite_fiberwise_join_power@{u v k | u <= v, v < k}
  {A : Type@{u}} {X : Type@{v}} (f : A -> X)
  := Colimit (seq_fiberwise_join_power@{u v k} f).

Definition infinite_fiberwise_join_power_map@{u v k | u <= v, v < k}
  {A : Type@{u}} {X : Type@{v}} (f : A -> X)
  : infinite_fiberwise_join_power@{u v k} f -> X.
Proof.
  snrapply Colimit_rec.
  snrapply Cocone.Build_Cocone.
  - exact (fiberwise_join_power_map@{u v k} f).
  - simpl; intros n ? p; destruct p.
    apply fiberwise_join_power_incl_comm.
Defined.

(** Here is our main theorem, it says that for any map [f : A -> X] from a small type [A] into a locally small type [X], image is an essentially small type. *)
Definition isessentiallysmall_infinite_fiberwise_join_power
  @{u v k | u <= v, v < k}
  `{Funext} {A : Type@{u}} {X : Type@{v}} (f : A -> X)
  (ils_X : IsLocallySmall@{u v k} 1 X)
  : IsSmall@{v k} (himage@{u v} f)
  := _.
