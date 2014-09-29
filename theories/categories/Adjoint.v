(** * Adjunctions *)
(** ** Definitions *)
Require Adjoint.Core.
(** *** unit+UMP *)
(** *** counit+UMP *)
(** *** unit+counit+zig+zag *)
Require Adjoint.UnitCounit.
(** *** universal morphisms *)
Require Adjoint.UniversalMorphisms.
(** *** hom-set isomorphism *)
Require Adjoint.Hom.
(** ** Coercions between various definitions *)
Require Adjoint.UnitCounitCoercions.
Require Adjoint.HomCoercions.
(** ** Opposite adjunctions *)
Require Adjoint.Dual.
(** ** Path spaces of adjunctions *)
Require Adjoint.Paths.
(** ** Composition *)
Require Adjoint.Composition.

Include Adjoint.Core.
Include Adjoint.UnitCounit.
Include Adjoint.UniversalMorphisms.
Include Adjoint.Hom.
Include Adjoint.UnitCounitCoercions.
Include Adjoint.HomCoercions.
Include Adjoint.Dual.
Include Adjoint.Paths.
Include Adjoint.Composition.

Require Export Adjoint.Notations.
