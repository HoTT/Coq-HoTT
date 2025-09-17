From HoTT Require Import Basics Types.Sigma Types.Paths.

(** Equalizers *)

Definition Equalizer {A B} (f g : A -> B)
  := {x : A & f x = g x}.

Definition functor_equalizer {A B A' B'} (f g : A -> B)
           (f' g' : A' -> B')
           (h : B -> B') (k : A -> A')
           (p : h o f == f' o k) (q : h o g == g' o k)
  : Equalizer f g -> Equalizer f' g'.
Proof.
  intros [x r].
  exists (k x).
  exact ((p x)^ @ (ap h r) @ (q x)).
Defined.

Definition equiv_functor_equalizer {A B A' B'} (f g : A -> B)
           (f' g' : A' -> B')
           (h : B <~> B') (k : A <~> A')
           (p : h o f == f' o k) (q : h o g == g' o k)
  : Equalizer f g <~> Equalizer f' g'.
Proof.
  unfold Equalizer.
  srapply (equiv_functor_sigma' k).
  - intro a; cbn.
    refine (_ oE _).
    2: rapply (equiv_ap h).
    exact (equiv_concat_r (q a) _ oE equiv_concat_l (p a)^ _).
Defined.

