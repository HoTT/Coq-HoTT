Require Import HoTT.Basics.
Require Import Types.Sigma.
Local Open Scope path_scope.


(** * Null homotopies of maps *)
Section NullHomotopy.
  Context `{Funext}.

  (** Geometrically, a nullhomotopy of a map [f : X -> Y] is an extension of [f] to a map [Cone X -> Y].  One might more simply call it e.g. [Constant f], but that is a little ambiguous: it could also reasonably mean e.g. a factorisation of [f] through [ Trunc -1 X ].  (Should the unique map [0 -> Y] be constant in one way, or in [Y]-many ways?) *)

  Definition NullHomotopy {X Y : Type} (f : X -> Y)
    := {y : Y & forall x:X, f x = y}.

  Lemma istrunc_nullhomotopy {n : trunc_index}
    {X Y : Type} (f : X -> Y) `{IsTrunc n Y}
    : IsTrunc n (NullHomotopy f).
  Proof.
    apply @istrunc_sigma; auto.
    intros y. apply (@istrunc_forall _).
    intros x. apply istrunc_paths'.
  Defined.

  Definition nullhomotopy_homotopic {X Y : Type} {f g : X -> Y} (p : f == g)
    : NullHomotopy f -> NullHomotopy g.
  Proof.
    intros [y e].
    exists y.
    intros x; exact ((p x)^ @ e x).
  Defined.

  Definition nullhomotopy_composeR {X Y Z : Type} (f : X -> Y) (g : Y -> Z)
    : NullHomotopy g -> NullHomotopy (g o f).
  Proof.
    intros [z e].
    exists z.
    intros x; exact (e (f x)).
  Defined.

  Definition nullhomotopy_composeL {X Y Z : Type} (f : X -> Y) (g : Y -> Z)
    : NullHomotopy f -> NullHomotopy (g o f).
  Proof.
    intros [y e].
    exists (g y).
    intros x; exact (ap g (e x)).
  Defined.

  Definition cancelL_nullhomotopy_equiv
             {X Y Z : Type} (f : X -> Y) (g : Y -> Z) `{IsEquiv _ _ g}
    : NullHomotopy (g o f) -> NullHomotopy f.
  Proof.
    intros [z e].
    exists (g^-1 z).
    intros x; apply moveL_equiv_V, e.
  Defined.

  Definition cancelR_nullhomotopy_equiv
             {X Y Z : Type} (f : X -> Y) (g : Y -> Z) `{IsEquiv _ _ f}
    : NullHomotopy (g o f) -> NullHomotopy g.
  Proof.
    intros [z e].
    exists z.
    intros y; transitivity (g (f (f^-1 y))).
    - symmetry; apply ap, eisretr.
    - apply e.
  Defined.

  Definition nullhomotopy_ap {X Y : Type} (f : X -> Y) (x1 x2 : X)
    : NullHomotopy f -> NullHomotopy (@ap _ _ f x1 x2).
  Proof.
    intros [y e].
    unshelve eexists.
    - exact (e x1 @ (e x2)^).
    - intros p.
      apply moveL_pV.
      refine (concat_Ap e p @ _).
      refine (_ @ concat_p1 _); apply ap.
      apply ap_const.
  Defined.

End NullHomotopy.
