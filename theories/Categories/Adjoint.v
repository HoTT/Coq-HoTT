(** * Adjunctions *)
(** ** Definitions *)
Require HoTT.Categories.Adjoint.Core.
(** *** unit+UMP *)
(** *** counit+UMP *)
(** *** unit+counit+zig+zag *)
Require HoTT.Categories.Adjoint.UnitCounit.
(** *** universal morphisms *)
Require HoTT.Categories.Adjoint.UniversalMorphisms.
(** *** hom-set isomorphism *)
Require HoTT.Categories.Adjoint.Hom.
(** ** Coercions between various definitions *)
Require HoTT.Categories.Adjoint.UnitCounitCoercions.
Require HoTT.Categories.Adjoint.HomCoercions.
(** ** Opposite adjunctions *)
Require HoTT.Categories.Adjoint.Dual.
(** ** Path spaces of adjunctions *)
Require HoTT.Categories.Adjoint.Paths.
(** ** Composition *)
Require HoTT.Categories.Adjoint.Composition.
(** ** Pointwise adjunctions *)
Require HoTT.Categories.Adjoint.Pointwise.
(** ** Functoriality of any adjoint construction *)
Require HoTT.Categories.Adjoint.Functorial.

Include Adjoint.Core.
Include Adjoint.UnitCounit.
Include Adjoint.UniversalMorphisms.Core.
Include Adjoint.Hom.
Include Adjoint.UnitCounitCoercions.
Include Adjoint.HomCoercions.
Include Adjoint.Dual.
Include Adjoint.Paths.
Include Adjoint.Composition.
Include Adjoint.Pointwise.
Include Adjoint.Functorial.Core.

Require Export HoTT.Categories.Adjoint.Notations.
