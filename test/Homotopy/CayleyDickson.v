From HoTT Require Import Basics.
From HoTT Require Import Classes.interfaces.abstract_algebra.
From HoTT Require Import Pointed.Core Pointed.pSusp.
From HoTT Require Import Homotopy.HSpace.Core Homotopy.Suspension.
From HoTT Require Import Homotopy.Join.Core Homotopy.CayleyDickson.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** The scalar boundary paths need neither a chosen diamond nor commutativity. *)
Section ScalarBoundaryPaths.
  Universe u.
  Context {X : pType@{u}} `{CayleyDicksonSpheroid X}
    `{!Associative hspace_op}.

  Example boundary_neg_unit (a c : X)
    : a * (c * -(- mon_unit)) = a * c
    := cd_diamond_map_l_neg_unit a c.

  Example boundary_neg_product (a b c d : X)
    : a * (c * -(conj c * conj a * d * conj b)) = (-d) * conj b
    := cd_diamond_map_l_parameter a b c d.

  Example boundary_unit (b c : X)
    : c * (mon_unit * b) = c * b := cd_diamond_map_r_unit b c.

  Example boundary_product (a b c d : X)
    : c * ((conj c * conj a * d * conj b) * b) = conj a * d
    := cd_diamond_map_r_parameter a b c d.
End ScalarBoundaryPaths.

(** The construction works for an arbitrary spheroid and an arbitrary chosen diamond, without commutativity or any further coherence hypotheses. *)
Section Spheroid.
  Universe u.
  Context {X : pType@{u}} `{CayleyDicksonSpheroid X}
    `{!Associative hspace_op} `{!CayleyDicksonDiamond X (-)}.

  Example doubled_hspace : IsHSpace@{u} (pjoin X X) := _.

  Example cd_op_ll (a b : X)
    : cd_op (joinl a) (joinl b) = joinl (a * b) := idpath.

  Example cd_op_lr (a b : X)
    : cd_op (joinl a) (joinr b) = joinr (conj a * b) := idpath.

  Example cd_op_rl (a b : X)
    : cd_op (joinr a) (joinl b) = joinr (b * a) := idpath.

  Example cd_op_rr (a b : X)
    : cd_op (joinr a) (joinr b) = joinl ((-b) * conj a) := idpath.

  (** The one-glue rules, used in the cancellation proof, do not depend on any computation rule for the diamond. *)
  Example cd_op_lg (a b c : X)
    : ap (cd_op (joinl a)) (jglue b c)
      = jglue (a * b) (conj a * c).
  Proof.
    exact (Join_rec_beta_jglue _ _ _ b c).
  Defined.

  Example cd_op_rg (a b c : X)
    : ap (cd_op (joinr a)) (jglue b c)
      = (jglue ((-c) * conj a) (b * a))^.
  Proof.
    exact (Join_rec_beta_jglue _ _ _ b c).
  Defined.

  Example cd_op_gl (a b c : X)
    : ap (fun z => cd_op z (joinl c)) (jglue a b)
      = jglue (a * c) (c * b).
  Proof.
    exact (Join_rec_beta_jglue _ _ _ a b).
  Defined.

  Example cd_op_gr (a b c : X)
    : ap (fun z => cd_op z (joinr c)) (jglue a b)
      = (jglue ((-c) * conj b) (conj a * c))^.
  Proof.
    exact (Join_rec_beta_jglue _ _ _ a b).
  Defined.

  Example doubled_left_identity : LeftIdentity cd_op pt := _.
  Example doubled_right_identity : RightIdentity cd_op pt := _.
  Example doubled_left_inverse : LeftInverse cd_op cd_conjugate pt := _.
  Example doubled_right_inverse : RightInverse cd_op cd_conjugate pt := _.
  Example doubled_factorneg_l : FactorNegLeft cd_negate cd_op := _.
  Example doubled_factorneg_r : FactorNegRight cd_negate cd_op := _.

  (** Simplifying the glue proof preserves the chosen inverse witnesses on points. *)
  Example doubled_left_inverse_joinl (a : X)
    : cd_op_conjugate_left_inverse (joinl a)
      = ap joinl (left_inverse a) := idpath.

  Example doubled_left_inverse_joinr (b : X)
    : cd_op_conjugate_left_inverse (joinr b)
      = ap joinl (right_inverse (-b)) := idpath.

  Example doubled_negate_involutive
    : Involutive (@cd_negate X _) := _.
  Example doubled_conjugate_involutive
    : Involutive (@cd_conjugate X _ _) := _.
  Example doubled_swapop
    : SwapOp (@cd_negate X _) (@cd_conjugate X _ _) := _.
  Example doubled_conjugate_unit
    : @IsUnitPreserving (pjoin X X) (pjoin X X) pt pt cd_conjugate := _.

  Example doubled_conjugate_glue (a b : X)
    : ap cd_conjugate (jglue a b) = jglue (conj a) (-b).
  Proof.
    apply functor_join_beta_jglue.
  Defined.

  Example doubled_negate_glue (a b : X)
    : ap cd_negate (jglue a b) = jglue (-a) (-b).
  Proof.
    apply functor_join_beta_jglue.
  Defined.

  (** A different explicitly supplied diamond is also supported; the laws must not silently select the ambient choice. *)
  Context (D : CayleyDicksonDiamond X (-)).

  Example chosen_diamond_path (t : X)
    : zigzag (-pt) t pt = zigzag (-pt) t t
    := @cd_diamond X (-) D t.

  Example chosen_diamond_hspace
    : @hspace_op (pjoin X X) (@hspace_cd@{u} X _ _ D)
      = @cd_op@{u} X _ _ D := idpath.

  Example chosen_diamond_left_inverse
    : LeftInverse (@cd_op X _ _ D) cd_conjugate pt
    := @cd_op_conjugate_left_inverse X _ _ D.

  Example chosen_diamond_right_inverse
    : RightInverse (@cd_op X _ _ D) cd_conjugate pt
    := @cd_op_conjugate_right_inverse X _ _ D.
End Spheroid.

(** The canonical diamond does not depend on an imaginaroid structure, or even on involutivity of negation. *)
Section SuspensionDiamond.
  Context {A : Type} `{Negate A}.

  Example suspension_diamond : CayleyDicksonDiamond (psusp A) (-) := _.

  Example suspension_diamond_north
    : cd_diamond (X := psusp A) North = diamond_v South North 1
    := idpath.

  Example suspension_diamond_south
    : cd_diamond (X := psusp A) South = diamond_h North South 1
    := idpath.

  Example suspension_diamond_merid (a : A)
    : apD (cd_diamond (X := psusp A)) (merid a)
      = diamond_twist (merid a).
  Proof.
    napply Susp_ind_beta_merid.
  Defined.
End SuspensionDiamond.

(** Imaginaroids still acquire the H-space structure by instance search. *)
Section Imaginaroid.
  Context {A : Type} `{CayleyDicksonImaginaroid A}
    `{!Associative hspace_op}.

  Example imaginaroid_double_hspace
    : IsHSpace (pjoin (psusp A) (psusp A)) := _.

  Example imaginaroid_double_hspace_name
    : IsHSpace (pjoin (psusp A) (psusp A)) := hspace_cdi_susp_assoc.

  (** The formerly judgmental double negation at the unit still reduces in the suspension instance. *)
  Example suspension_unit_normalization (a c : Susp A)
    : cd_diamond_map_l_neg_unit a c
      = ap (a *.) (hspace_right_identity c).
  Proof.
    unfold cd_diamond_map_l_neg_unit.
    apply concat_1p.
  Defined.

  Example imaginaroid_double_inverse (z : Join (Susp A) (Susp A))
    : cd_op (cd_conjugate z) z = joinl North.
  Proof.
    apply left_inverse.
  Defined.
End Imaginaroid.
