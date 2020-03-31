Require Import Basics Types.
Require Import NullHomotopy.
Require Import Homotopy.Suspension.
Require Import Colimits.Pushout.
Require Import Colimits.Quotient.
Require Import Truncations.
Require Import HSet.

(** Toda brackets *)

(** If we have four types [W X Y Z] and three maps [f : W -> X], [g : X -> Y] and [h : Y -> Z], then using the proofs p and q that (g o f) and (h o g) are nullhomotopic we can construct a map [toda : Susp W -> Z]. *)

(*

  W --f--> X -----> * --
  |    //  |    //  |   \
  |   //   g   //   |    \
  |  /p    |  /q    |     \
  V //     V //     V      |
  * -----> Y --h--> Z      |
  |                   ^toda|
   \                   \   V
    \_________________> Susp W

*)

Definition toda {W X Y Z : Type} (f : W -> X) (g : X -> Y) (h : Y -> Z)
  : NullHomotopy (g o f) -> NullHomotopy (h o g) -> Susp W -> Z.
Proof.
  intros [y p] [z q].
  unfold Susp.
  snrapply Pushout_rec.
  1: intro; exact (h y).
  1: intro; exact z.
  intro w.
  exact (ap h (p w)^ @ q (f w)).
Defined.

(** The Toda Bracket is a subset of [Susp W, Z] *)
Section Bracket.

  Context `{Funext} {W X Y Z : Type} (f : W -> X) (g : X -> Y) (h : Y -> Z).

  Local Definition TodaNulls : Type
    := NullHomotopy (g o f) * NullHomotopy (h o g).

  (** Now we define a relation on the null homotopies and check if the constructed [toda] map is homotopic. *)
  Definition ishomo_toda : Relation TodaNulls.
  Proof.
    intros [p1 q1] [p2 q2].
    exact (toda f g h p1 q1 == toda f g h p2 q2).
  Defined.

  (** Now we define the toda bracket of [f], [g] and [h] as the quotient *)
  Definition TodaBracket := Quotient ishomo_toda.

  (** The Toda bracket of [f], [g] and [h] is a subset of [Tr 0 (Susp W -> Z)] *)
  Definition toda_incl : TodaBracket -> Tr 0 (Susp W -> Z).
  Proof.
    srapply Quotient_rec.
    + intros [p q].
      apply tr.
      exact (toda f g h p q).
    + intros [p1 q1] [p2 q2] r.
      unfold ishomo_toda in r.
      apply ap.
      apply path_forall.
      exact r.
  Defined.

  (** To show that this is an embedding requires univalence. *)
  Definition isembedding_toda_incl `{Univalence} : IsEmbedding toda_incl.
  Proof.
    apply isembedding_isinj_hset.
    srapply Quotient_ind_hprop; intros [p1 q1].
    srapply Quotient_ind_hprop; intros [p2 q2].
    intros p; simpl in p.
    apply (equiv_path_Tr _ _)^-1%equiv in p.
    strip_truncations.
    apply qglue.
    apply ap10.
    exact p.
  Defined.

End Bracket.

(** TODO: how does this interact with pointed maps? This ought to generalize to pointed wild categories with pushouts. In particular, when [toda_incl] is generalized to pointed maps also, we should be able to say something along the lines of Toda brackets of S^n -> X -> Y -> Z, <f, g, h> should embed into Pi n+1 Z. *)


