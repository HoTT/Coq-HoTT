(** * Fixed points in dcpos *)

From HoTT Require Import Basics Types TruncType Truncations.Core.
From HoTT.Classes.interfaces Require Import canonical_names orders.
From HoTT.Spaces Require Import Nat.Core.
From HoTT.DomainTheory Require Import Dcpo Constructions.

Local Open Scope type_scope.

(** We prove three fixed point theorems. A Scott continuous endomap of a pointed dcpo has a least fixed point, the supremum of its Kleene iteration. The monotone inflationary endomaps of a dcpo have a common fixed point, which needs no propositional resizing; this needs the dcpo to be small, in the sense that its carrier and order live in the universe of index types. Assuming propositional resizing, a monotone endomap of a pointed dcpo has a least fixed point (Pataraia's theorem). *)

(** ** Kleene iteration *)

Section Kleene.
  Context {A : Type} {Ale : Le A} `{Bottom A} `{!IsPointedDcpo Ale}
    (f : A -> A) `{!IsScottContinuous f}.

  Definition kleene_iterate (n : nat) : A
    := nat_iter n f ⊥.

  Definition kleene_iterate_succ (n : nat)
    : kleene_iterate n ≤ kleene_iterate n.+1%nat.
  Proof.
    induction n as [|n IHn].
    - rapply bottom_least.
    - apply (order_preserving f), IHn.
  Defined.

  Definition isdirected_kleene_iterate : IsDirected kleene_iterate
    := isdirected_increasing_sequence kleene_iterate kleene_iterate_succ.

  Definition kleene_fixed_point : A
    := dcpo_sup kleene_iterate isdirected_kleene_iterate.

  Local Definition kleene_iterate_le_prefixed_point (y : A) (fy : f y ≤ y) (n : nat)
    : kleene_iterate n ≤ y.
  Proof.
    induction n as [|n IHn].
    - rapply bottom_least.
    - lhs' apply (order_preserving f), IHn.
      exact fy.
  Defined.

  Definition kleene_fixed_point_least (y : A) (fy : f y ≤ y)
    : kleene_fixed_point ≤ y
    := dcpo_sup_least kleene_iterate isdirected_kleene_iterate y
         (kleene_iterate_le_prefixed_point y fy).

  Definition kleene_fixed_point_isfixed
    : f kleene_fixed_point = kleene_fixed_point.
  Proof.
    apply (antisymmetry Ale).
    - apply (issup_least (scott_continuous f nat kleene_iterate isdirected_kleene_iterate)).
      intro n.
      exact (dcpo_sup_upper kleene_iterate isdirected_kleene_iterate n.+1%nat).
    - apply dcpo_sup_least.
      intros [|n].
      + rapply bottom_least.
      + apply (order_preserving f), (dcpo_sup_upper kleene_iterate isdirected_kleene_iterate n).
  Defined.

End Kleene.

(** ** Inflationary endomaps *)

Class IsInflationary {A : Type} {Ale : Le A} (f : A -> A)
  := inflationary : forall x, x ≤ f x.

Arguments inflationary {A Ale} f {_} x.

Section Inflationary.
  Context {A : Type} {Ale : Le A}.

  #[export] Instance ishprop_isinflationary `{Funext} `{!is_mere_relation A Ale}
    (f : A -> A)
    : IsHProp (IsInflationary f).
  Proof.
    unfold IsInflationary; exact _.
  Defined.

  #[export] Instance isinflationary_idmap `{!Reflexive Ale}
    : IsInflationary (idmap : A -> A)
    := fun x => reflexivity x.

  #[export] Instance isinflationary_compose `{!Transitive Ale}
    (f g : A -> A) `{!IsInflationary f} `{!IsInflationary g}
    : IsInflationary (f o g)
    := fun x => transitivity (inflationary g x) (inflationary f (g x)).

End Inflationary.

(** ** Monotone inflationary endomaps have a common fixed point *)

Section InflationaryFixedPoint.
  Context `{Funext} {A : Type} {Ale : Le A} `{!IsDcpo Ale}.

  Local Notation le_pointwise := (relation_pointwise (fun _ : A => Ale)).

  Definition subset_inflationary : (A -> A) -> HProp
    := fun f => Build_HProp (OrderPreserving f * IsInflationary f).

  #[export] Instance issubdcpo_inflationary
    : IsSubdcpo le_pointwise subset_inflationary.
  Proof.
    intros I f d fI.
    pose (gs := dcpo_sup_pointwise Ale f d).
    split.
    - intros x y p.
      apply (issup_least (gs x)). intro i.
      exact (transitivity (fst (fI i) x y p) (issup_upper (gs y) i)).
    - intro x.
      pose proof (fst d) as i. strip_truncations.
      exact (transitivity (snd (fI i) x) (issup_upper (gs x) i)).
  Defined.

  Local Notation Infl := (sig subset_inflationary).
  Local Notation le_infl := (@le_sig _ le_pointwise subset_inflationary).

  Local Definition orderpreserving_infl (f : Infl) : OrderPreserving f.1
    := fst f.2.

  Local Definition isinflationary_infl (f : Infl) : IsInflationary f.1
    := snd f.2.

  Definition isdirected_inflationary
    : IsDirected (Ale:=le_infl) (idmap : Infl -> Infl).
  Proof.
    split.
    - exact (tr (idmap; (_, _))).
    - intros [f [mf If]] [g [mg Ig]].
      apply tr; exists (f o g; (_, _)). split.
      + intro x.
        apply mf, Ig.
      + intro x.
        exact (If (g x)).
  Defined.

  Definition top_inflationary : A -> A
    := (dcpo_sup (idmap : Infl -> Infl) isdirected_inflationary).1.

  #[export] Instance orderpreserving_top_inflationary
    : OrderPreserving top_inflationary
    := orderpreserving_infl (dcpo_sup (idmap : Infl -> Infl) isdirected_inflationary).

  #[export] Instance isinflationary_top_inflationary
    : IsInflationary top_inflationary
    := isinflationary_infl (dcpo_sup (idmap : Infl -> Infl) isdirected_inflationary).

  Definition top_inflationary_greatest (f : A -> A)
    `{!OrderPreserving f} `{!IsInflationary f}
    : forall x, f x ≤ top_inflationary x
    := dcpo_sup_upper (idmap : Infl -> Infl) isdirected_inflationary
         (f; (_, _)).

  Definition top_inflationary_fixed_point (f : A -> A)
    `{!OrderPreserving f} `{!IsInflationary f} (x : A)
    : f (top_inflationary x) = top_inflationary x.
  Proof.
    apply (antisymmetry Ale).
    - exact (top_inflationary_greatest (f o top_inflationary) x).
    - exact (inflationary f (top_inflationary x)).
  Defined.

End InflationaryFixedPoint.

(** ** Fixed points in subdcpos *)

Section SubdcpoFixedPoint.
  Context `{Funext} {A : Type} {Ale : Le A} `{!IsDcpo Ale}.

  Local Existing Instance le_sig.

  (** This needs no propositional resizing. *)
  Definition fixed_point_subdcpo (f : A -> A) `{!OrderPreserving f}
    (B : A -> HProp) `{!IsSubdcpo Ale B}
    (closed : forall x, B x -> B (f x)) (infl : forall x, B x -> x ≤ f x)
    (b : A) (Bb : B b)
    : {x : A & B x * (f x = x)}.
  Proof.
    pose (g := fun u : sig B => (f u.1; closed u.1 u.2) : sig B).
    assert (mg : OrderPreserving g).
    { intros u v p; apply (order_preserving f), p. }
    assert (Ig : IsInflationary g).
    { intro u; exact (infl u.1 u.2). }
    pose (t := top_inflationary (b; Bb)).
    exists t.1.
    split.
    - exact t.2.
    - exact (ap pr1 (top_inflationary_fixed_point g (b; Bb))).
  Defined.

End SubdcpoFixedPoint.

(** ** Pataraia's fixed point theorem *)

Section LeastFixedPoint.
  Context `{PropResizing} `{Funext} {A : Type} {Ale : Le A} `{Bottom A}
    `{!IsPointedDcpo Ale} (f : A -> A) `{!OrderPreserving f}.

  Local Definition IsAdmissible (B : A -> HProp) : Type
    := IsSubdcpo Ale B * B ⊥ * (forall x, B x -> B (f x)).

  (** This intersection needs propositional resizing. *)
  Local Definition least_admissible : A -> HProp
    := fun x => hprop_meet (fun B : {B : A -> HProp & IsAdmissible B} => B.1 x).

  Local Definition least_admissible_subset (B : A -> HProp) (aB : IsAdmissible B)
    (x : A)
    : least_admissible x -> B x
    := hprop_meet_out (fun B : {B : A -> HProp & IsAdmissible B} => B.1 x) (B; aB).

  Local Definition isadmissible_least_admissible : IsAdmissible least_admissible.
  Proof.
    refine (_, _, _).
    - intros I x d Bx.
      napply hprop_meet_in.
      intros [B [[sB botB] fB]].
      apply sB.
      intro i.
      exact (least_admissible_subset B (sB, botB, fB) (x i) (Bx i)).
    - napply hprop_meet_in.
      intros [B [[sB botB] fB]].
      exact botB.
    - intros x Bx.
      napply hprop_meet_in.
      intros [B aB].
      apply (snd aB).
      exact (least_admissible_subset B aB x Bx).
  Defined.

  Local Definition isadmissible_below (y : A) (fy : f y ≤ y)
    : IsAdmissible (fun x => Build_HProp (x ≤ y)).
  Proof.
    refine (_, _, _).
    - intros I x d Bx.
      exact (dcpo_sup_least x d y Bx).
    - exact (bottom_least y).
    - intros x xy.
      exact (transitivity (order_preserving f x y xy) fy).
  Defined.

  Local Definition isadmissible_increasing
    : IsAdmissible (fun x => Build_HProp (x ≤ f x)).
  Proof.
    refine (_, _, _).
    - intros I x d Bx.
      apply dcpo_sup_least.
      intro i.
      lhs' exact (Bx i).
      apply (order_preserving f).
      exact (dcpo_sup_upper x d i).
    - exact (bottom_least (f ⊥)).
    - intros x xfx.
      apply (order_preserving f), xfx.
  Defined.

  Definition least_fixed_point
    : {a : A & (f a = a) * (forall y, f y ≤ y -> a ≤ y)}.
  Proof.
    destruct isadmissible_least_admissible as [[sB botB] fB].
    destruct (fixed_point_subdcpo f least_admissible fB
                (least_admissible_subset (fun x => Build_HProp (x ≤ f x)) isadmissible_increasing)
                ⊥ botB)
      as [a [Ba p]].
    exists a.
    split.
    - exact p.
    - intros y fy.
      exact (least_admissible_subset (fun x => Build_HProp (x ≤ y))
               (isadmissible_below y fy) a Ba).
  Defined.

End LeastFixedPoint.
