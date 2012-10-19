(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.

(******************************************************************************)
(*   The algebraic part of the Algebraic Hierarchy, as described in           *)
(*          ``Packaging mathematical structures'', TPHOLs09, by               *)
(*   Francois Garillot, Georges Gonthier, Assia Mahboubi, Laurence Rideau     *)
(*                                                                            *)
(* This file defines for each Structure (Zmodule, Ring, etc ...) its type,    *)
(* its packers and its canonical properties :                                 *)
(*                                                                            *)
(*  * Zmodule (additive abelian groups):                                      *)
(*              zmodType == interface type for Zmodule structure.             *)
(* ZmodMixin addA addC add0x addNx == builds the mixin for a Zmodule from the *)
(*                          algebraic properties of its operations.           *)
(*          ZmodType V m == packs the mixin m to build a Zmodule of type      *)
(*                          zmodType. The carrier type V must have a          *)
(*                          choiceType canonical structure.                   *)
(* [zmodType of V for S] == V-clone of the zmodType structure S: a copy of S  *)
(*                          where the sort carrier has been replaced by V,    *)
(*                          and which is therefore a zmodType structure on V. *)
(*                          The sort carrier for S must be convertible to V.  *)
(*       [zmodType of V] == clone of a canonical zmodType structure on V.     *)
(*                          Similar to the above, except S is inferred, but   *)
(*                          possibly with a syntactically different carrier.  *)
(*                     0 == the zero (additive identity) of a Zmodule.        *)
(*                 x + y == the sum of x and y (in a Zmodule).                *)
(*                   - x == the opposite (additive inverse) of x.             *)
(*                 x - y == the difference of x and y; this is only notation  *)
(*                          for x + (- y).                                    *)
(*                x *+ n == n times x, with n in nat (non-negative), i.e.,    *)
(*                          x + (x + .. (x + x)..) (n terms); x *+ 1 is thus  *)
(*                          convertible to x, and x *+ 2 to x + x.            *)
(*                x *- n == notation for - (x *+ n), the opposite of x *+ n.  *)
(*        \sum_<range> e == iterated sum for a Zmodule (cf bigop.v).          *)
(*                  e`_i == nth 0 e i, when e : seq M and M has a zmodType    *)
(*                          structure.                                        *)
(*             support f == 0.-support f, i.e., [pred x | f x != 0].          *)
(*         oppr_closed S <-> collective predicate S is closed under opposite. *)
(*         addr_closed S <-> collective predicate S is closed under finite    *)
(*                           sums (0 and x + y in S, for x, y in S).          *)
(*         zmod_closed S <-> collective predicate S is closed under zmodType  *)
(*                          operations (0 and x - y in S, for x, y in S).     *)
(*                          This property coerces to oppr_pred and addr_pred. *)
(*         OpprPred oppS == packs oppS : oppr_closed S into an opprPred S     *)
(*                          interface structure associating this property to  *)
(*                          the canonical pred_key S, i.e. the k for which S  *)
(*                          has a Canonical keyed_pred k structure (see file  *)
(*                          ssrbool.v).                                       *)
(*         AddrPred addS == packs addS : addr_closed S into an addrPred S     *)
(*                          interface structure associating this property to  *)
(*                          the canonical pred_key S (see above).             *)
(*         ZmodPred oppS == packs oppS : oppr_closed S into an zmodPred S     *)
(*                          interface structure associating the zmod_closed   *)
(*                          property to the canonical pred_key S (see above), *)
(*                          which must already be an addrPred.                *)
(* [zmodMixin of M by <:] == zmodType mixin for a subType whose base type is  *)
(*                          a zmodType and whose predicate's canonical        *)
(*                          pred_key is a zmodPred.                           *)
(* --> Coq can be made to behave as if all predicates had canonical zmodPred  *)
(*     keys by executing Import DefaultKeying GRing.DefaultPred. The required *)
(*     oppr_closed and addr_closed assumptions will be either abstracted,     *)
(*     resolved or issued as separate proof obligations by the ssreflect      *)
(*     plugin abstraction and Prop-irrelevance functions.                     *)
(*  * Ring (non-commutative rings):                                           *)
(*              ringType == interface type for a Ring structure.              *)
(* RingMixin mulA mul1x mulx1 mulDx mulxD == builds the mixin for a Ring from *)
(*                           the algebraic properties of its multiplicative   *)
(*                           operators; the carrier type must have a zmodType *)
(*                           structure.                                       *)
(*           RingType R m == packs the ring mixin m into a ringType.          *)
(*                    R^c == the converse Ring for R: R^c is convertible to R *)
(*                           but when R has a canonical ringType structure    *)
(*                           R^c has the converse one: if x y : R^c, then     *)
(*                           x * y = (y : R) * (x : R).                       *)
(*  [ringType of R for S] == R-clone of the ringType structure S.             *)
(*        [ringType of R] == clone of a canonical ringType structure on R.    *)
(*                      1 == the multiplicative identity element of a Ring.   *)
(*                   n%:R == the ring image of an n in nat; this is just      *)
(*                           notation for 1 *+ n, so 1%:R is convertible to 1 *)
(*                           and 2%:R to 1 + 1.                               *)
(*                  x * y == the ring product of x and y.                     *)
(*        \prod_<range> e == iterated product for a ring (cf bigop.v).        *)
(*                 x ^+ n == x to the nth power with n in nat (non-negative), *)
(*                           i.e., x * (x * .. (x * x)..) (n factors); x ^+ 1 *)
(*                           is thus convertible to x, and x ^+ 2 to x * x.   *)
(*         GRing.sign R b := (-1) ^+ b in R : ringType, with b : bool.        *)
(*                           This is a parsing-only helper notation, to be    *)
(*                           used for defining more specific instances.       *)
(*         GRing.comm x y <-> x and y commute, i.e., x * y = y * x.           *)
(*           GRing.lreg x <-> x if left-regular, i.e., *%R x is injective.    *)
(*           GRing.rreg x <-> x if right-regular, i.e., *%R x is injective.   *)
(*               [char R] == the characteristic of R, defined as the set of   *)
(*                           prime numbers p such that p%:R = 0 in R. The set *)
(*                           [char p] has a most one element, and is          *)
(*                           implemented as a pred_nat collective predicate   *)
(*                           (see prime.v); thus the statement p \in [char R] *)
(*                           can be read as `R has characteristic p', while   *)
(*                           [char R] =i pred0 means `R has characteristic 0' *)
(*                           when R is a field.                               *)
(*     Frobenius_aut chRp == the Frobenius automorphism mapping x in R to     *)
(*                           x ^+ p, where chRp : p \in [char R] is a proof   *)
(*                           that R has (non-zero) characteristic p.          *)
(*          mulr_closed S <-> collective predicate S is closed under finite   *)
(*                           products (1 and x * y in S for x, y in S).       *)
(*         smulr_closed S <-> collective predicate S is closed under products *)
(*                           and opposite (-1 and x * y in S for x, y in S).  *)
(*      semiring_closed S <-> collective predicate S is closed under semiring *)
(*                           operations (0, 1, x + y and x * y in S).         *)
(*       subring_closed S <-> collective predicate S is closed under ring     *)
(*                           operations (1, x - y and x * y in S).            *)
(*          MulrPred mulS == packs mulS : mulr_closed S into a mulrPred S,    *)
(*        SmulrPred mulS     smulrPred S, semiringPred S, or subringPred S    *)
(*     SemiringPred mulS     interface structure, corresponding to the above  *)
(*      SubRingPred mulS     properties, respectively, provided S already has *)
(*                           the supplementary zmodType closure properties.   *)
(*                           The properties above coerce to subproperties so, *)
(*                           e.g., ringS : subring_closed S can be used for   *)
(*                           the proof obligations of all prerequisites.      *)
(* [ringMixin of R by <:] == ringType mixin for a subType whose base type is  *)
(*                           a ringType and whose predicate's canonical key   *)
(*                           is a SubringPred.                                *)
(*  --> As for zmodType predicates, Import DefaultKeying GRing.DefaultPred    *)
(*      turns unresolved GRing.Pred unification constraints into proof        *)
(*      obligations for basic closure assumptions.                            *)
(*                                                                            *)
(*  * ComRing (commutative Rings):                                            *)
(*            comRingType == interface type for commutative ring structure.   *)
(*     ComRingType R mulC == packs mulC into a comRingType; the carrier type  *)
(*                           R must have a ringType canonical structure.      *)
(* ComRingMixin mulA mulC mul1x mulDx == builds the mixin for a Ring (i.e., a *)
(*                           *non commutative* ring), using the commutativity *)
(*                           to reduce the number of proof obligagtions.      *)
(* [comRingType of R for S] == R-clone of the comRingType structure S.        *)
(*     [comRingType of R] == clone of a canonical comRingType structure on R. *)
(* [comRingMixin of R by <:] == comutativity mixin axiom for R when it is a   *)
(*                           subType of a commutative ring.                   *)
(*                                                                            *)
(*  * UnitRing (Rings whose units have computable inverses):                  *)
(*           unitRingType == interface type for the UnitRing structure.       *)
(* UnitRingMixin mulVr mulrV unitP inv0id == builds the mixin for a UnitRing  *)
(*                           from the properties of the inverse operation and *)
(*                           the boolean test for being a unit (invertible).  *)
(*                           The inverse of a non-unit x is constrained to be *)
(*                           x itself (property inv0id). The carrier type     *)
(*                           must have a ringType canonical structure.        *)
(*       UnitRingType R m == packs the unit ring mixin m into a unitRingType. *)
(*                  WARNING: while it is possible to omit R for most of the   *)
(*                           XxxType functions, R MUST be explicitly given    *)
(*                           when UnitRingType is used with a mixin produced  *)
(*                           by ComUnitRingMixin, otherwise the resulting     *)
(*                           structure will have the WRONG sort key and will  *)
(*                           NOT BE USED during type inference.               *)
(* [unitRingType of R for S] == R-clone of the unitRingType structure S.      *)
(*    [unitRingType of R] == clones a canonical unitRingType structure on R.  *)
(*     x \is a GRing.unit <=> x is a unit (i.e., has an inverse).             *)
(*                   x^-1 == the ring inverse of x, if x is a unit, else x.   *)
(*                  x / y == x divided by y (notation for x * y^-1).          *)
(*                 x ^- n := notation for (x ^+ n)^-1, the inverse of x ^+ n. *)
(*         invr_closed S <-> collective predicate S is closed under inverse.  *)
(*         divr_closed S <-> collective predicate S is closed under division  *)
(*                           (1 and x / y in S).                              *)
(*        sdivr_closed S <-> collective predicate S is closed under division  *)
(*                           and opposite (-1 and x / y in S, for x, y in S). *)
(*      divring_closed S <-> collective predicate S is closed under unitRing  *)
(*                           operations (1, x - y and x / y in S).            *)
(*         DivrPred invS == packs invS : mulr_closed S into a divrPred S,     *)
(*        SdivrPred invS    sdivrPred S or divringPred S interface structure, *)
(*      DivringPred invS    corresponding to the above properties, resp.,     *)
(*                          provided S already has the supplementary ringType *)
(*                          closure properties. The properties above coerce   *)
(*                          to subproperties, as explained above.             *)
(* [unitRingMixin of R by <:] == unitRingType mixin for a subType whose base  *)
(*                           type is a unitRingType and whose predicate's     *)
(*                           canonical key is a divringPred and whose ring    *)
(*                           structure is compatible with the base type's.    *)
(*                                                                            *)
(*  * ComUnitRing (commutative rings with computable inverses):               *)
(*        comUnitRingType == interface type for ComUnitRing structure.        *)
(* ComUnitRingMixin mulVr unitP inv0id == builds the mixin for a UnitRing (a  *)
(*                           *non commutative* unit ring, using commutativity *)
(*                           to simplify the proof obligations; the carrier   *)
(*                           type must have a comRingType structure.          *)
(*                           WARNING: ALWAYS give an explicit type argument   *)
(*                           to UnitRingType along with a mixin produced by   *)
(*                           ComUnitRingMixin (see above).                    *)
(* [comUnitRingType of R] == a comUnitRingType structure for R created by     *)
(*                           merging canonical comRingType and unitRingType   *)
(*                           structures on R.                                 *)
(*                                                                            *)
(*  * IntegralDomain (integral, commutative, ring with partial inverses):     *)
(*            idomainType == interface type for the IntegralDomain structure. *)
(* IdomainType R mulf_eq0 == packs the integrality property into an           *)
(*                           idomainType integral domain structure; R must    *)
(*                           have a comUnitRingType canonical structure.      *)
(* [idomainType of R for S] == R-clone of the idomainType structure S.        *)
(*     [idomainType of R] == clone of a canonical idomainType structure on R. *)
(* [idomainMixin of R by <:] == mixin axiom for a idomain subType.            *)
(*                                                                            *)
(*  * Field (commutative fields):                                             *)
(*              fieldType == interface type for fields.                       *)
(*  GRing.Field.axiom inv == the field axiom (x != 0 -> inv x * x = 1).       *)
(* FieldUnitMixin mulVx unitP inv0id == builds a *non commutative unit ring*  *)
(*                           mixin, using the field axiom to simplify proof   *)
(*                           obligations. The carrier type must have a        *)
(*                           comRingType canonical structure.                 *)
(*       FieldMixin mulVx == builds the field mixin from the field axiom. The *)
(*                           carrier type must have a comRingType structure.  *)
(*    FieldIdomainMixin m == builds an *idomain* mixin from a field mixin m.  *)
(*          FieldType R m == packs the field mixin M into a fieldType. The    *)
(*                           carrier type R must be an idomainType.           *)
(* [fieldType of F for S] == F-clone of the fieldType structure S.            *)
(*       [fieldType of F] == clone of a canonical fieldType structure on F.   *)
(*   [fieldMixin of R by <:] == mixin axiom for a field subType.              *)
(*                                                                            *)
(*  * DecidableField (fields with a decidable first order theory):            *)
(*           decFieldType == interface type for DecidableField structure.     *)
(*     DecFieldMixin satP == builds the mixin for a DecidableField from the   *)
(*                           correctness of its satisfiability predicate. The *)
(*                           carrier type must have a unitRingType structure. *)
(*       DecFieldType F m == packs the decidable field mixin m into a         *)
(*                           decFieldType; the carrier type F must have a     *)
(*                           fieldType structure.                             *)
(* [decFieldType of F for S] == F-clone of the decFieldType structure S.      *)
(*    [decFieldType of F] == clone of a canonical decFieldType structure on F *)
(*           GRing.term R == the type of formal expressions in a unit ring R  *)
(*                           with formal variables 'X_k, k : nat, and         *)
(*                           manifest constants x%:T, x : R. The notation of  *)
(*                           all the ring operations is redefined for terms,  *)
(*                           in scope %T.                                     *)
(*        GRing.formula R == the type of first order formulas over R; the %T  *)
(*                           scope binds the logical connectives /\, \/, ~,   *)
(*                           ==>, ==, and != to formulae; GRing.True/False    *)
(*                           and GRing.Bool b denote constant formulae, and   *)
(*                           quantifiers are written 'forall/'exists 'X_k, f. *)
(*                             GRing.Unit x tests for ring units              *)
(*                             GRing.If p_f t_f e_f emulates if-then-else     *)
(*                             GRing.Pick p_f t_f e_f emulates fintype.pick   *)
(*                             foldr GRing.Exists/Forall q_f xs can be used   *)
(*                               to write iterated quantifiers.               *)
(*         GRing.eval e t == the value of term t with valuation e : seq R     *)
(*                           (e maps 'X_i to e`_i).                           *)
(*  GRing.same_env e1 e2 <-> environments e1 and e2 are extensionally equal.  *)
(*        GRing.qf_form f == f is quantifier-free.                            *)
(*        GRing.holds e f == the intuitionistic CiC interpretation of the     *)
(*                           formula f holds with valuation e.                *)
(*      GRing.qf_eval e f == the value (in bool) of a quantifier-free f.      *)
(*          GRing.sat e f == valuation e satisfies f (only in a decField).    *)
(*          GRing.sol n f == a sequence e of size n such that e satisfies f,  *)
(*                           if one exists, or [::] if there is no such e.    *)
(* QEdecFieldMixin wfP okP == a decidable field Mixin built from a quantifier *)
(*                           eliminator p and proofs wfP : GRing.wf_QE_proj p *)
(*                           and okP : GRing.valid_QE_proj p that p returns   *)
(*                           well-formed and valid formulae, i.e., p i (u, v) *)
(*                           is a quantifier-free formula equivalent to       *)
(*        'exists 'X_i, u1 == 0 /\ ... /\ u_m == 0 /\ v1 != 0 ... /\ v_n != 0 *)
(*                                                                            *)
(*  * ClosedField (algebraically closed fields):                              *)
(*        closedFieldType == interface type for the ClosedField structure.    *)
(*    ClosedFieldType F m == packs the closed field mixin m into a            *)
(*                           closedFieldType. The carrier F must have a       *)
(*                           decFieldType structure.                          *)
(* [closedFieldType of F on S] == F-clone of a closedFieldType structure S.   *)
(* [closedFieldType of F] == clone of a canonicalclosedFieldType structure    *)
(*                           on F.                                            *)
(*                                                                            *)
(*  * Lmodule (module with left multiplication by external scalars).          *)
(*             lmodType R == interface type for an Lmodule structure with     *)
(*                           scalars of type R; R must have a ringType        *)
(*                           structure.                                       *)
(* LmodMixin scalA scal1v scalxD scalDv == builds an Lmodule mixin from the   *)
(*                           algebraic properties of the scaling operation;   *)
(*                           the module carrier type must have a zmodType     *)
(*                           structure, and the scalar carrier must have a    *)
(*                           ringType structure.                              *)
(*         LmodType R V m == packs the mixin v to build an Lmodule of type    *)
(*                           lmodType R. The carrier type V must have a       *)
(*                           zmodType structure.                              *)
(* [lmodType R of V for S] == V-clone of an lmodType R structure S.           *)
(*      [lmodType R of V] == clone of a canonical lmodType R structure on V.  *)
(*                 a *: v == v scaled by a, when v is in an Lmodule V and a   *)
(*                           is in the scalar Ring of V.                      *)
(*        scaler_closed S <-> collective predicate S is closed under scaling. *)
(*        linear_closed S <-> collective predicate S is closed under linear   *)
(*                           combinations (a *: u + v in S when u, v in S).   *)
(*        submod_closed S <-> collective predicate S is closed under lmodType *)
(*                           operations (0 and a *: u + v in S).              *)
(*      SubmodPred scaleS == packs scaleS : scaler_closed S in a submodPred S *)
(*                           interface structure corresponding to the above   *)
(*                           property, provided S's key is a zmodPred;        *)
(*                           submod_closed coerces to all the prerequisites.  *)
(* [lmodMixin of V by <:] == mixin for a subType of an lmodType, whose        *)
(*                           predicate's key is a submodPred.                 *)
(*                                                                            *)
(*  * Lalgebra (left algebra, ring with scaling that associates on the left): *)
(*             lalgType R == interface type for Lalgebra structures with      *)
(*                           scalars in R; R must have ringType structure.    *)
(*    LalgType R V scalAl == packs scalAl : k (x y) = (k x) y into an         *)
(*                           Lalgebra of type lalgType R. The carrier type V  *)
(*                           must have both lmodType R and ringType canonical *)
(*                           structures.                                      *)
(*                    R^o == the regular algebra of R: R^o is convertible to  *)
(*                           R, but when R has a ringType structure then R^o  *)
(*                           extends it to an lalgType structure by letting R *)
(*                           act on itself: if x : R and y : R^o then         *)
(*                           x *: y = x * (y : R).                            *)
(*                   k%:A == the image of the scalar k in an L-algebra; this  *)
(*                           is simply notation for k *: 1.                   *)
(* [lalgType R of V for S] == V-clone the lalgType R structure S.             *)
(*      [lalgType R of V] == clone of a canonical lalgType R structure on V.  *)
(*        subalg_closed S <-> collective predicate S is closed under lalgType *)
(*                           operations (1, a *: u + v and u * v in S).       *)
(*      SubalgPred scaleS == packs scaleS : scaler_closed S in a subalgPred S *)
(*                           interface structure corresponding to the above   *)
(*                           property, provided S's key is a subringPred;     *)
(*                           subalg_closed coerces to all the prerequisites.  *)
(* [lalgMixin of V by <:] == mixin axiom for a subType of an lalgType.        *)
(*                                                                            *)
(*  * Algebra (ring with scaling that associates both left and right):        *)
(*              algType R == type for Algebra structure with scalars in R.    *)
(*                           R should be a commutative ring.                  *)
(*     AlgType R A scalAr == packs scalAr : k (x y) = x (k y) into an Algebra *)
(*                           Structure of type algType R. The carrier type A  *)
(*                           must have an lalgType R structure.               *)
(*        CommAlgType R A == creates an Algebra structure for an A that has   *)
(*                           both lalgType R and comRingType structures.      *)
(* [algType R of V for S] == V-clone of an algType R structure on S.          *)
(*       [algType R of V] == clone of a canonical algType R structure on V.   *)
(*  [algMixin of V by <:] == mixin axiom for a subType of an algType.         *)
(*                                                                            *)
(*  * UnitAlgebra (algebra with computable inverses):                         *)
(*          unitAlgType R == interface type for UnitAlgebra structure with    *)
(*                           scalars in R; R should have a unitRingType       *)
(*                           structure.                                       *)
(*   [unitAlgType R of V] == a unitAlgType R structure for V created by       *)
(*                           merging canonical algType and unitRingType on V. *)
(*        divalg_closed S <-> collective predicate S is closed under all      *)
(*                           unitAlgType operations (1, a *: u + v and u / v  *)
(*                           are in S fo u, v in S).                          *)
(*      DivalgPred scaleS == packs scaleS : scaler_closed S in a divalgPred S *)
(*                           interface structure corresponding to the above   *)
(*                           property, provided S's key is a divringPred;     *)
(*                           divalg_closed coerces to all the prerequisites.  *)
(*                                                                            *)
(*   In addition to this strcture hierarchy, we also develop a separate,      *)
(* parallel hierarchy for morphisms linking these structures:                 *)
(*                                                                            *)
(* * Additive (additive functions):                                           *)
(*             additive f <-> f of type U -> V is additive, i.e., f maps the  *)
(*                           Zmodule structure of U to that of V, 0 to 0,     *)
(*                           - to - and + to + (equivalently, binary - to -). *)
(*                        := {morph f : u v / u + v}.                         *)
(*      {additive U -> V} == the interface type for a Structure (keyed on     *)
(*                           a function f : U -> V) that encapsulates the     *)
(*                           additive property; both U and V must have        *)
(*                           zmodType canonical structures.                   *)
(*         Additive add_f == packs add_f : additive f into an additive        *)
(*                           function structure of type {additive U -> V}.    *)
(*   [additive of f as g] == an f-clone of the additive structure on the      *)
(*                           function g -- f and g must be convertible.       *)
(*        [additive of f] == a clone of an existing additive structure on f.  *)
(*                                                                            *)
(* * RMorphism (ring morphisms):                                              *)
(*       multiplicative f <-> f of type R -> S is multiplicative, i.e., f     *)
(*                           maps 1 and * in R to 1 and * in S, respectively, *)
(*                           R ans S must have canonical ringType structures. *)
(*            rmorphism f <-> f is a ring morphism, i.e., f is both additive  *)
(*                           and multiplicative.                              *)
(*     {rmorphism R -> S} == the interface type for ring morphisms, i.e.,     *)
(*                           a Structure that encapsulates the rmorphism      *)
(*                           property for functions f : R -> S; both R and S  *)
(*                           must have ringType structures.                   *)
(*      RMorphism morph_f == packs morph_f : rmorphism f into a Ring morphism *)
(*                           structure of type {rmorphism R -> S}.            *)
(*     AddRMorphism mul_f == packs mul_f : multiplicative f into an rmorphism *)
(*                           structure of type {rmorphism R -> S}; f must     *)
(*                           already have an {additive R -> S} structure.     *)
(*  [rmorphism of f as g] == an f-clone of the rmorphism structure of g.      *)
(*       [rmorphism of f] == a clone of an existing additive structure on f.  *)
(*  -> If R and S are UnitRings the f also maps units to units and inverses   *)
(*     of units to inverses; if R is a field then f if a field isomorphism    *)
(*     between R and its image.                                               *)
(*  -> As rmorphism coerces to both additive and multiplicative, all          *)
(*     structures for f can be built from a single proof of rmorphism f.      *)
(*  -> Additive properties (raddf_suffix, see below) are duplicated and       *)
(*     specialised for RMorphism (as rmorph_suffix). This allows more         *)
(*     precise rewriting and cleaner chaining: although raddf lemmas will     *)
(*     recognize RMorphism functions, the converse will not hold (we cannot   *)
(*     add reverse inheritance rules because of incomplete backtracking in    *)
(*     the Canonical Projection unification), so one would have to insert a   *)
(*     /= every time one switched from additive to multiplicative rules.      *)
(*  -> The property duplication also means that it is not strictly necessary  *)
(*     to declare all Additive instances.                                     *)
(*                                                                            *)
(* * Linear (linear functions):                                               *)
(*             scalable f <-> f of type U -> V is scalable, i.e., f morphs    *)
(*                           scaling on U to scaling on V, a *: _ to a *: _.  *)
(*                           U and V must both have lmodType R structures,    *)
(*                           for the same ringType R.                         *)
(*       scalable_for s f <-> f is scalable for scaling operator s, i.e.,     *)
(*                           f morphs a *: _ to s a _; the range of f only    *)
(*                           need to be a zmodType. The scaling operator s    *)
(*                           should be one of *:%R (see scalable, above), *%R *)
(*                           or a combination nu \; *%R or nu \; *:%R with    *)
(*                           nu : {rmorphism _}; otherwise some of the theory *)
(*                           (e.g., the linearZ rule) will not apply.         *)
(*               linear f <-> f of type U -> V is linear, i.e., f morphs      *)
(*                           linear combinations a *: u + v in U to similar   *)
(*                           linear combinations in V; U and V must both have *)
(*                           lmodType R structures, for the same ringType R.  *)
(*                        := forall a, {morph f: u v / a *: u + v}.           *)
(*               scalar f <-> f of type U -> R is a scalar function, i.e.,    *)
(*                           f (a *: u + v) = a * f u + f v.                  *)
(*         linear_for s f <-> f is linear for the scaling operator s, i.e.,   *)
(*                           f (a *: u + v) = s a (f u) + f v. The range of f *)
(*                           only needs to be a zmodType, but s MUST be of    *)
(*                           the form described in in scalable_for paragraph  *)
(*                           for this predicate to type check.                *)
(*            lmorphism f <-> f is both additive and scalable. This is in     *)
(*                           fact equivalent to linear f, although somewhat   *)
(*                           less convenient to prove.                        *)
(*     lmorphism_for s f <-> f is both additive and scalable for s.           *)
(*        {linear U -> V} == the interface type for linear functions, i.e., a *)
(*                           Structure that encapsulates the linear property  *)
(*                           for functions f : U -> V; both U and V must have *)
(*                           lmodType R structures, for the same R.           *)
(*             {scalar U} == the interface type for scalar functions, of type *)
(*                           U -> R where U has an lmodType R structure.      *)
(*    {linear U -> V | s} == the interface type for functions linear for s.   *)
(*           Linear lin_f == packs lin_f : lmorphism_for s f into a linear    *)
(*                           function structure of type {linear U -> V | s}.  *)
(*                           As linear_for s f coerces to lmorphism_for s f,  *)
(*                           Linear can be used with lin_f : linear_for s f   *)
(*                           (indeed, that is the recommended usage). Note    *)
(*                           that as linear f, scalar f, {linear U -> V} and  *)
(*                           {scalar U} are simply notation for corresponding *)
(*                           generic "_for" forms, Linear can be used for any *)
(*                           of these special cases, transparantly.           *)
(*       AddLinear scal_f == packs scal_f : scalable_for s f into a           *)
(*                           {linear U -> V | s} structure; f must already    *)
(*                           have an additive structure; as with Linear,      *)
(*                           AddLinear can be used with lin_f : linear f, etc *)
(*     [linear of f as g] == an f-clone of the linear structure of g.         *)
(*          [linear of f] == a clone of an existing linear structure on f.    *)
(*          (a *: u)%Rlin == transient forms that simplifiy to a *: u, a * u, *)
(*           (a * u)%Rlin    nu a *: u, and nu a * u, respectively, and are   *)
(*       (a *:^nu u)%Rlin    created by rewriting with the linearZ lemma. The *)
(*        (a *^nu u)%Rlin    forms allows the RHS of linearZ to be matched    *)
(*                           reliably, using the GRing.Scale.law structure.   *)
(* -> Similarly to Ring morphisms, additive properties are specialized for    *)
(*    linear functions.                                                       *)
(* -> Although {scalar U} is convertible to {linear U -> R^o}, it does not    *)
(*    actually use R^o, so that rewriting preserves the canonical structure   *)
(*    of the range of scalar functions.                                       *)
(* -> The generic linearZ lemma uses a set of bespoke interface structures to *)
(*    ensure that both left-to-right and right-to-left rewriting work even in *)
(*    the presence of scaling functions that simplify non-trivially (e.g.,    *)
(*    idfun \; *%R). Because most of the canonical instances and projections  *)
(*    are coercions the machinery will be mostly invisible (with only the     *)
(*    {linear ...} structure and %Rlin notations showing), but users should   *)
(*    beware that in (a *: f u)%Rlin, a actually occurs in the f u subterm.   *)
(* -> The simpler linear_LR, or more specialized linearZZ and scalarZ rules   *)
(*    should be used instead of linearZ if there are complexity issues, as    *)
(*    well as for explicit forward and backward application, as the main      *)
(*    parameter of linearZ is a proper sub-interface of {linear fUV | s}.     *)
(*                                                                            *)
(* * LRMorphism (linear ring morphisms, i.e., algebra morphisms):             *)
(*           lrmorphism f <-> f of type A -> B is a linear Ring (Algebra)     *)
(*                           morphism: f is both additive, multiplicative and *)
(*                           scalable. A and B must both have lalgType R      *)
(*                           canonical structures, for the same ringType R.   *)
(*     lrmorphism_for s f <-> f a linear Ring morphism for the scaling        *)
(*                           operator s: f is additive, multiplicative and    *)
(*                           scalable for s. A must be an lalgType R, but B   *)
(*                           only needs to have a ringType structure.         *)
(*    {lrmorphism A -> B} == the interface type for linear morphisms, i.e., a *)
(*                           Structure that encapsulates the lrmorphism       *)
(*                           property for functions f : A -> B; both A and B  *)
(*                           must have lalgType R structures, for the same R. *)
(* {lrmorphism A -> B | s} == the interface type for morphisms linear for s.  *)
(*   LRmorphism lrmorph_f == packs lrmorph_f : lrmorphism_for s f into a      *)
(*                           linear morphism structure of type                *)
(*                           {lrmorphism A -> B | s}. Like Linear, LRmorphism *)
(*                           can be used transparently for lrmorphism f.      *)
(*   AddLRmorphism scal_f == packs scal_f : scalable_for s f into a linear    *)
(*                           morphism structure of type                       *)
(*                           {lrmorphism A -> B | s}; f must already have an  *)
(*                           {rmorphism A -> B} structure, and AddLRmorphism  *)
(*                           can be applied to a linear_for s f, linear f,    *)
(*                           scalar f, etc argument, like AddLinear.          *)
(*      [lrmorphism of f] == creates an lrmorphism structure from existing    *)
(*                           rmorphism and linear structures on f; this is    *)
(*                           the preferred way of creating lrmorphism         *)
(*                           structures.                                      *)
(*  -> Linear and rmorphism properties do not need to be specialized for      *)
(*     as we supply inheritance join instances in both directions.            *)
(* Finally we supply some helper notation for morphisms:                      *)
(*                    x^f == the image of x under some morphism. This         *)
(*                           notation is only reserved (not defined) here;    *)
(*                           it is bound locally in sections where some       *)
(*                           morphism is used heavily (e.g., the container    *)
(*                           morphism in the parametricity sections of poly   *)
(*                           and matrix, or the Frobenius section here).      *)
(*                     \0 == the constant null function, which has a          *)
(*                           canonical linear structure, and simplifies on    *)
(*                           application (see ssrfun.v).                      *)
(*                 f \+ g == the additive composition of f and g, i.e., the   *)
(*                           function x |-> f x + g x; f \+ g is canonically  *)
(*                           linear when f and g are, and simplifies on       *)
(*                           application (see ssrfun.v).                      *)
(*                 f \- g == the function x |-> f x - g x, canonically        *)
(*                           linear when f and g are, and simplifies on       *)
(*                           application.                                     *)
(*                k \*: f == the function x |-> k *: f x, which is            *)
(*                           canonically linear when f is and simplifies on   *)
(*                           application (this is a shorter alternative to    *)
(*                           *:%R k \o f).                                    *)
(*         GRing.in_alg A == the ring morphism that injects R into A, where A *)
(*                           has an lalgType R structure; GRing.in_alg A k    *)
(*                           simplifies to k%:A.                              *)
(*                a \*o f == the function x |-> a * f x, canonically linear   *)
(*                           linear when f is and its codomain is an algType  *)
(*                           and which simplifies on application.             *)
(*                a \o* f == the function x |-> f x * a, canonically linear   *)
(*                           linear when f is and its codomain is an lalgType *)
(*                           and which simplifies on application.             *)
(* The Lemmas about these structures are contained in both the GRing module   *)
(* and in the submodule GRing.Theory, which can be imported when unqualified  *)
(* access to the theory is needed (GRing.Theory also allows the unqualified   *)
(* use of additive, linear, Linear, etc). The main GRing module should NOT be *)
(* imported.                                                                  *)
(*   Notations are defined in scope ring_scope (delimiter %R), except term    *)
(* and formula notations, which are in term_scope (delimiter %T).             *)
(*   This library also extends the conventional suffixes described in library *)
(* ssrbool.v with the following:                                              *)
(*   0 -- ring 0, as in addr0 : x + 0 = x.                                    *)
(*   1 -- ring 1, as in mulr1 : x * 1 = x.                                    *)
(*   D -- ring addition, as in linearD : f (u + v) = f u + f v.               *)
(*   B -- ring substraction, as in opprB : - (x - y) = y - x.                 *)
(*   M -- ring multiplication, as in invfM : (x * y)^-1 = x^-1 * y^-1.        *)
(*  Mn -- ring by nat multiplication, as in raddfMn : f (x *+ n) = f x *+ n.  *)
(*   N -- ring opposite, as in mulNr : (- x) * y = - (x * y).                 *)
(*   V -- ring inverse, as in mulVr : x^-1 * x = 1.                           *)
(*   X -- ring exponentiation, as in rmorphX : f (x ^+ n) = f x ^+ n.         *)
(*   Z -- (left) module scaling, as in linearZ : f (a *: v)  = s *: f v.      *)
(* The operator suffixes D, B, M and X are also used for the corresponding    *)
(* operations on nat, as in natrX : (m ^ n)%:R = m%:R ^+ n. For the binary    *)
(* power operator, a trailing "n" suffix is used to indicate the operator     *)
(* suffix applies to the left-hand ring argument, as in                       *)
(*   expr1n : 1 ^+ n = 1 vs. expr1 : x ^+ 1 = x.                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "+%R" (at level 0).
Reserved Notation "-%R" (at level 0).
Reserved Notation "*%R" (at level 0).
Reserved Notation "n %:R" (at level 2, left associativity, format "n %:R").
Reserved Notation "k %:A" (at level 2, left associativity, format "k %:A").
Reserved Notation "[ 'char' F ]" (at level 0, format "[ 'char'  F ]").

Reserved Notation "x %:T" (at level 2, left associativity, format "x %:T").
Reserved Notation "''X_' i" (at level 8, i at level 2, format "''X_' i").
(* Patch for recurring Coq parser bug: Coq seg faults when a level 200 *)
(* notation is used as a pattern.                                      *)
Reserved Notation "''exists' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''exists'  ''X_' i , '/ '  f ']'").
Reserved Notation "''forall' ''X_' i , f"
  (at level 199, i at level 2, right associativity,
   format "'[hv' ''forall'  ''X_' i , '/ '  f ']'").

Reserved Notation "x ^f" (at level 2, left associativity, format "x ^f").

Reserved Notation "\0" (at level 0).
Reserved Notation "f \+ g" (at level 50, left associativity).
Reserved Notation "f \- g" (at level 50, left associativity).
Reserved Notation "a \*o f" (at level 40).
Reserved Notation "a \o* f" (at level 40).
Reserved Notation "a \*: f" (at level 40).

Delimit Scope ring_scope with R.
Delimit Scope term_scope with T.
Local Open Scope ring_scope.

Module Import GRing.

Import Monoid.Theory.

Module Zmodule.

Record mixin_of (V : Type) : Type := Mixin {
  zero : V;
  opp : V -> V;
  add : V -> V -> V;
  _ : associative add;
  _ : commutative add;
  _ : left_id zero add;
  _ : left_inverse zero opp add
}.

Section ClassDef.

Record class_of T := Class { base : Choice.class_of T; mixin : mixin_of T }.
Local Coercion base : class_of >-> Choice.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation zmodType := type.
Notation ZmodType T m := (@pack T m _ _ id).
Notation ZmodMixin := Mixin.
Notation "[ 'zmodType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'zmodType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'zmodType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'zmodType'  'of'  T ]") : form_scope.
End Exports.

End Zmodule.
Import Zmodule.Exports.

Definition zero V := Zmodule.zero (Zmodule.class V).
Definition opp V := Zmodule.opp (Zmodule.class V).
Definition add V := Zmodule.add (Zmodule.class V).

Local Notation "0" := (zero _) : ring_scope.
Local Notation "-%R" := (@opp _) : ring_scope.
Local Notation "- x" := (opp x) : ring_scope.
Local Notation "+%R" := (@add _) : ring_scope.
Local Notation "x + y" := (add x y) : ring_scope.
Local Notation "x - y" := (x + - y) : ring_scope.

Definition natmul V x n := nosimpl iterop _ n +%R x (zero V).

Local Notation "x *+ n" := (natmul x n) : ring_scope.
Local Notation "x *- n" := (- (x *+ n)) : ring_scope.

Local Notation "\sum_ ( i <- r | P ) F" := (\big[+%R/0]_(i <- r | P) F).
Local Notation "\sum_ ( m <= i < n ) F" := (\big[+%R/0]_(m <= i < n) F).
Local Notation "\sum_ ( i < n ) F" := (\big[+%R/0]_(i < n) F).
Local Notation "\sum_ ( i 'in' A ) F" := (\big[+%R/0]_(i in A) F).

Local Notation "s `_ i" := (nth 0 s i) : ring_scope.

Section ZmoduleTheory.

Variable V : zmodType.
Implicit Types x y : V.

Lemma addrA : @associative V +%R. Proof. by case V => T [? []]. Qed.
Lemma addrC : @commutative V V +%R. Proof. by case V => T [? []]. Qed.
Lemma add0r : @left_id V V 0 +%R. Proof. by case V => T [? []]. Qed.
Lemma addNr : @left_inverse V V V 0 -%R +%R. Proof. by case V => T [? []]. Qed.

Lemma addr0 : @right_id V V 0 +%R.
Proof. by move=> x; rewrite addrC add0r. Qed.
Lemma addrN : @right_inverse V V V 0 -%R +%R.
Proof. by move=> x; rewrite addrC addNr. Qed.
Definition subrr := addrN.

Canonical add_monoid := Monoid.Law addrA add0r addr0.
Canonical add_comoid := Monoid.ComLaw addrC.

Lemma addrCA : @left_commutative V V +%R. Proof. exact: mulmCA. Qed.
Lemma addrAC : @right_commutative V V +%R. Proof. exact: mulmAC. Qed.
Lemma addrACA : @interchange V +%R +%R. Proof. exact: mulmACA. Qed.

Lemma addKr : @left_loop V V -%R +%R.
Proof. by move=> x y; rewrite addrA addNr add0r. Qed.
Lemma addNKr : @rev_left_loop V V -%R +%R.
Proof. by move=> x y; rewrite addrA addrN add0r. Qed.
Lemma addrK : @right_loop V V -%R +%R.
Proof. by move=> x y; rewrite -addrA addrN addr0. Qed.
Lemma addrNK : @rev_right_loop V V -%R +%R.
Proof. by move=> x y; rewrite -addrA addNr addr0. Qed.
Definition subrK := addrNK.
Lemma addrI : @right_injective V V V +%R.
Proof. move=> x; exact: can_inj (addKr x). Qed.
Lemma addIr : @left_injective V V V +%R.
Proof. move=> y; exact: can_inj (addrK y). Qed.
Lemma opprK : @involutive V -%R.
Proof. by move=> x; apply: (@addIr (- x)); rewrite addNr addrN. Qed.
Lemma oppr_inj : @injective V V -%R.
Proof. exact: inv_inj opprK. Qed.
Lemma oppr0 : -0 = 0 :> V.
Proof. by rewrite -[-0]add0r subrr. Qed.
Lemma oppr_eq0 x : (- x == 0) = (x == 0).
Proof. by rewrite (inv_eq opprK) oppr0. Qed.

Lemma subr0 x : x - 0 = x. Proof. by rewrite oppr0 addr0. Qed.
Lemma sub0r x : 0 - x = - x. Proof. by rewrite add0r. Qed.

Lemma opprD : {morph -%R: x y / x + y : V}.
Proof.
by move=> x y; apply: (@addrI (x + y)); rewrite addrA subrr addrAC addrK subrr.
Qed.

Lemma opprB x y : - (x - y) = y - x.
Proof. by rewrite opprD addrC opprK. Qed.

Lemma subr_eq x y z : (x - z == y) = (x == y + z).
Proof. exact: can2_eq (subrK z) (addrK z) x y. Qed.

Lemma subr_eq0 x y : (x - y == 0) = (x == y).
Proof. by rewrite subr_eq add0r. Qed.

Lemma addr_eq0 x y : (x + y == 0) = (x == - y).
Proof. by rewrite -[x == _]subr_eq0 opprK. Qed.

Lemma eqr_opp x y : (- x == - y) = (x == y).
Proof. exact: can_eq opprK x y. Qed.

Lemma eqr_oppLR x y : (- x == y) = (x == - y).
Proof. exact: inv_eq opprK x y. Qed. 

Lemma mulr0n x : x *+ 0 = 0. Proof. by []. Qed.
Lemma mulr1n x : x *+ 1 = x. Proof. by []. Qed.
Lemma mulr2n x : x *+ 2 = x + x. Proof. by []. Qed.

Lemma mulrS x n : x *+ n.+1 = x + x *+ n.
Proof. by case: n => //=; rewrite addr0. Qed.

Lemma mulrSr x n : x *+ n.+1 = x *+ n + x.
Proof. by rewrite addrC mulrS. Qed.

Lemma mulrb x (b : bool) : x *+ b = (if b then x else 0).
Proof. by case: b. Qed.

Lemma mul0rn n : 0 *+ n = 0 :> V.
Proof. by elim: n => // n IHn; rewrite mulrS add0r. Qed.

Lemma mulNrn x n : (- x) *+ n = x *- n.
Proof. by elim: n => [|n IHn]; rewrite ?oppr0 // !mulrS opprD IHn. Qed.

Lemma mulrnDl n : {morph (fun x => x *+ n) : x y / x + y}.
Proof.
move=> x y; elim: n => [|n IHn]; rewrite ?addr0 // !mulrS.
by rewrite addrCA -!addrA -IHn -addrCA.
Qed.

Lemma mulrnDr x m n : x *+ (m + n) = x *+ m + x *+ n.
Proof.
elim: m => [|m IHm]; first by rewrite add0r.
by rewrite !mulrS IHm addrA.
Qed.

Lemma mulrnBl n : {morph (fun x => x *+ n) : x y / x - y}.
Proof.
move=> x y; elim: n => [|n IHn]; rewrite ?subr0 // !mulrS -!addrA; congr(_ + _).
by rewrite addrC IHn -!addrA opprD [_ - y]addrC.
Qed.

Lemma mulrnBr x m n : n <= m -> x *+ (m - n) = x *+ m - x *+ n.
Proof.
elim: m n => [|m IHm] [|n le_n_m]; rewrite ?subr0 // {}IHm //.
by rewrite mulrSr mulrS opprD addrA addrK.
Qed.

Lemma mulrnA x m n : x *+ (m * n) = x *+ m *+ n.
Proof.
by rewrite mulnC; elim: n => //= n IHn; rewrite mulrS mulrnDr IHn.
Qed.

Lemma mulrnAC x m n : x *+ m *+ n = x *+ n *+ m.
Proof. by rewrite -!mulrnA mulnC. Qed.

Lemma sumrN I r P (F : I -> V) :
  (\sum_(i <- r | P i) - F i = - (\sum_(i <- r | P i) F i)).
Proof. by rewrite (big_morph _ opprD oppr0). Qed.

Lemma sumrB I r (P : pred I) (F1 F2 : I -> V) :
  \sum_(i <- r | P i) (F1 i - F2 i)
     = \sum_(i <- r | P i) F1 i - \sum_(i <- r | P i) F2 i.
Proof. by rewrite -sumrN -big_split /=. Qed.

Lemma sumrMnl I r P (F : I -> V) n :
  \sum_(i <- r | P i) F i *+ n = (\sum_(i <- r | P i) F i) *+ n.
Proof. by rewrite (big_morph _ (mulrnDl n) (mul0rn _)). Qed.

Lemma sumrMnr x I r P (F : I -> nat) :
  \sum_(i <- r | P i) x *+ F i = x *+ (\sum_(i <- r | P i) F i).
Proof. by rewrite (big_morph _ (mulrnDr x) (erefl _)). Qed.

Lemma sumr_const (I : finType) (A : pred I) (x : V) :
  \sum_(i in A) x = x *+ #|A|.
Proof. by rewrite big_const -iteropE. Qed.

Section ClosedPredicates.

Variable S : predPredType V.

Definition addr_closed := 0 \in S /\ {in S &, forall u v, u + v \in S}.
Definition oppr_closed := {in S, forall u, - u \in S}.
Definition subr_2closed := {in S &, forall u v, u - v \in S}.
Definition zmod_closed := 0 \in S /\ subr_2closed.

Lemma zmod_closedN : zmod_closed -> oppr_closed.
Proof. by case=> S0 SB y Sy; rewrite -sub0r !SB. Qed.

Lemma zmod_closedD : zmod_closed -> addr_closed.
Proof.
by case=> S0 SB; split=> // y z Sy Sz; rewrite -[z]opprK -[- z]sub0r !SB.
Qed.

End ClosedPredicates.

End ZmoduleTheory.

Implicit Arguments addrI [[V] x1 x2].
Implicit Arguments addIr [[V] x1 x2].
Implicit Arguments oppr_inj [[V] x1 x2].

Module Ring.

Record mixin_of (R : zmodType) : Type := Mixin {
  one : R;
  mul : R -> R -> R;
  _ : associative mul;
  _ : left_id one mul;
  _ : right_id one mul;
  _ : left_distributive mul +%R;
  _ : right_distributive mul +%R;
  _ : one != 0
}.

Definition EtaMixin R one mul mulA mul1x mulx1 mul_addl mul_addr nz1 :=
  let _ := @Mixin R one mul mulA mul1x mulx1 mul_addl mul_addr nz1 in
  @Mixin (Zmodule.Pack (Zmodule.class R) R) _ _
     mulA mul1x mulx1 mul_addl mul_addr nz1.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : Zmodule.class_of R;
  mixin : mixin_of (Zmodule.Pack base R)
}.
Local Coercion base : class_of >-> Zmodule.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).


Definition pack b0 (m0 : mixin_of (@Zmodule.Pack T b0 T)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Notation ringType := type.
Notation RingType T m := (@pack T _ m _ _ id _ id).
Notation RingMixin := Mixin.
Notation "[ 'ringType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'ringType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'ringType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'ringType'  'of'  T ]") : form_scope.
End Exports.

End Ring.
Import Ring.Exports.

Definition one (R : ringType) : R := Ring.one (Ring.class R).
Definition mul (R : ringType) : R -> R -> R := Ring.mul (Ring.class R).
Definition exp R x n := nosimpl iterop _ n (@mul R) x (one R).
Notation sign R b := (exp (- one R) (nat_of_bool b)) (only parsing).
Definition comm R x y := @mul R x y = mul y x.
Definition lreg R x := injective (@mul R x).
Definition rreg R x := injective ((@mul R)^~ x).

Local Notation "1" := (one _) : ring_scope.
Local Notation "- 1" := (- (1)) : ring_scope.
Local Notation "n %:R" := (1 *+ n) : ring_scope.
Local Notation "*%R" := (@mul _).
Local Notation "x * y" := (mul x y) : ring_scope.
Local Notation "x ^+ n" := (exp x n) : ring_scope.

Local Notation "\prod_ ( i <- r | P ) F" := (\big[*%R/1]_(i <- r | P) F).
Local Notation "\prod_ ( i | P ) F" := (\big[*%R/1]_(i | P) F).
Local Notation "\prod_ ( i 'in' A ) F" := (\big[*%R/1]_(i in A) F).

(* The ``field'' characteristic; the definition, and many of the theorems,   *)
(* has to apply to rings as well; indeed, we need the Frobenius automorphism *)
(* results for a non commutative ring in the proof of Gorenstein 2.6.3.      *)
Definition char (R : Ring.type) of phant R : nat_pred :=
  [pred p | prime p & p%:R == 0 :> R].

Local Notation "[ 'char' R ]" := (char (Phant R)) : ring_scope.

(* Converse ring tag. *)
Definition converse R : Type := R.
Local Notation "R ^c" := (converse R) (at level 2, format "R ^c") : type_scope.

Section RingTheory.

Variable R : ringType.
Implicit Types x y : R.

Lemma mulrA : @associative R *%R. Proof. by case R => T [? []]. Qed.
Lemma mul1r : @left_id R R 1 *%R. Proof. by case R => T [? []]. Qed.
Lemma mulr1 : @right_id R R 1 *%R. Proof. by case R => T [? []]. Qed.
Lemma mulrDl : @left_distributive R R *%R +%R.
Proof. by case R => T [? []]. Qed.
Lemma mulrDr : @right_distributive R R *%R +%R.
Proof. by case R => T [? []]. Qed.
Lemma oner_neq0 : 1 != 0 :> R. Proof. by case R => T [? []]. Qed.
Lemma oner_eq0 : (1 == 0 :> R) = false. Proof. exact: negbTE oner_neq0. Qed.

Lemma mul0r : @left_zero R R 0 *%R.
Proof.
by move=> x; apply: (addIr (1 * x)); rewrite -mulrDl !add0r mul1r.
Qed.
Lemma mulr0 : @right_zero R R 0 *%R.
Proof.
by move=> x; apply: (addIr (x * 1)); rewrite -mulrDr !add0r mulr1.
Qed.
Lemma mulrN x y : x * (- y) = - (x * y).
Proof. by apply: (addrI (x * y)); rewrite -mulrDr !subrr mulr0. Qed.
Lemma mulNr x y : (- x) * y = - (x * y).
Proof. by apply: (addrI (x * y)); rewrite -mulrDl !subrr mul0r. Qed.
Lemma mulrNN x y : (- x) * (- y) = x * y.
Proof. by rewrite mulrN mulNr opprK. Qed.
Lemma mulN1r x : -1 * x = - x.
Proof. by rewrite mulNr mul1r. Qed.
Lemma mulrN1 x : x * -1 = - x.
Proof. by rewrite mulrN mulr1. Qed.

Canonical mul_monoid := Monoid.Law mulrA mul1r mulr1.
Canonical muloid := Monoid.MulLaw mul0r mulr0.
Canonical addoid := Monoid.AddLaw mulrDl mulrDr.

Lemma mulr_suml I r P (F : I -> R) x :
  (\sum_(i <- r | P i) F i) * x = \sum_(i <- r | P i) F i * x.
Proof. exact: big_distrl. Qed.

Lemma mulr_sumr I r P (F : I -> R) x :
  x * (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) x * F i.
Proof. exact: big_distrr. Qed.

Lemma mulrBl x y z : (y - z) * x = y * x - z * x.
Proof. by rewrite mulrDl mulNr. Qed.

Lemma mulrBr x y z : x * (y - z) = x * y - x * z.
Proof. by rewrite mulrDr mulrN. Qed.

Lemma mulrnAl x y n : (x *+ n) * y = (x * y) *+ n.
Proof. by elim: n => [|n IHn]; rewrite ?mul0r // !mulrS mulrDl IHn. Qed.

Lemma mulrnAr x y n : x * (y *+ n) = (x * y) *+ n.
Proof. by elim: n => [|n IHn]; rewrite ?mulr0 // !mulrS mulrDr IHn. Qed.

Lemma mulr_natl x n : n%:R * x = x *+ n.
Proof. by rewrite mulrnAl mul1r. Qed.

Lemma mulr_natr x n : x * n%:R = x *+ n.
Proof. by rewrite mulrnAr mulr1. Qed.

Lemma natrD m n : (m + n)%:R = m%:R + n%:R :> R.
Proof. exact: mulrnDr. Qed.

Lemma natrB m n : n <= m -> (m - n)%:R = m%:R - n%:R :> R.
Proof. exact: mulrnBr. Qed.

Definition natr_sum := big_morph (natmul 1) natrD (mulr0n 1).

Lemma natrM m n : (m * n)%:R = m%:R * n%:R :> R.
Proof. by rewrite mulrnA -mulr_natr. Qed.

Lemma expr0 x : x ^+ 0 = 1. Proof. by []. Qed.
Lemma expr1 x : x ^+ 1 = x. Proof. by []. Qed.
Lemma expr2 x : x ^+ 2 = x * x. Proof. by []. Qed.

Lemma exprS x n : x ^+ n.+1 = x * x ^+ n.
Proof. by case: n => //; rewrite mulr1. Qed.

Lemma expr0n n : 0 ^+ n = (n == 0%N)%:R :> R.
Proof. by case: n => // n; rewrite exprS mul0r. Qed.

Lemma expr1n n : 1 ^+ n = 1 :> R.
Proof. by elim: n => // n IHn; rewrite exprS mul1r. Qed.

Lemma exprD x m n : x ^+ (m + n) = x ^+ m * x ^+ n.
Proof. by elim: m => [|m IHm]; rewrite ?mul1r // !exprS -mulrA -IHm. Qed.

Lemma exprSr x n : x ^+ n.+1 = x ^+ n * x.
Proof. by rewrite -addn1 exprD expr1. Qed.

Lemma commr_sym x y : comm x y -> comm y x. Proof. by []. Qed.
Lemma commr_refl x : comm x x. Proof. by []. Qed.

Lemma commr0 x : comm x 0.
Proof. by rewrite /comm mulr0 mul0r. Qed.

Lemma commr1 x : comm x 1.
Proof. by rewrite /comm mulr1 mul1r. Qed.

Lemma commrN x y : comm x y -> comm x (- y).
Proof. by move=> com_xy; rewrite /comm mulrN com_xy mulNr. Qed.

Lemma commrN1 x : comm x (-1).
Proof. apply: commrN; exact: commr1. Qed.

Lemma commrD x y z : comm x y -> comm x z -> comm x (y + z).
Proof. by rewrite /comm mulrDl mulrDr => -> ->. Qed.

Lemma commrMn x y n : comm x y -> comm x (y *+ n).
Proof.
rewrite /comm => com_xy.
by elim: n => [|n IHn]; rewrite ?commr0 // mulrS commrD.
Qed.

Lemma commrM x y z : comm x y -> comm x z -> comm x (y * z).
Proof. by move=> com_xy; rewrite /comm mulrA com_xy -!mulrA => ->. Qed.

Lemma commr_nat x n : comm x n%:R.
Proof. by apply: commrMn; exact: commr1. Qed.

Lemma commrX x y n : comm x y -> comm x (y ^+ n).
Proof.
rewrite /comm => com_xy.
by elim: n => [|n IHn]; rewrite ?commr1 // exprS commrM.
Qed.

Lemma exprMn_comm x y n : comm x y -> (x * y) ^+ n = x ^+ n * y ^+ n.
Proof.
move=> com_xy; elim: n => /= [|n IHn]; first by rewrite mulr1.
by rewrite !exprS IHn !mulrA; congr (_ * _); rewrite -!mulrA -commrX.
Qed.

Lemma commr_sign x n : comm x ((-1) ^+ n).
Proof. exact: (commrX n (commrN1 x)). Qed.

Lemma exprMn_n x m n : (x *+ m) ^+ n = x ^+ n *+ (m ^ n) :> R.
Proof.
elim: n => [|n IHn]; first by rewrite mulr1n.
rewrite exprS IHn -mulr_natr -mulrA -commr_nat mulr_natr -mulrnA -expnSr.
by rewrite -mulr_natr mulrA -exprS mulr_natr.
Qed.

Lemma exprM x m n : x ^+ (m * n) = x ^+ m ^+ n.
Proof.
elim: m => [|m IHm]; first by rewrite expr1n.
by rewrite mulSn exprD IHm exprS exprMn_comm //; exact: commrX.
Qed.

Lemma exprAC x m n : (x ^+ m) ^+ n = (x ^+ n) ^+ m.
Proof. by rewrite -!exprM mulnC. Qed.

Lemma expr_mod n x i : x ^+ n = 1 -> x ^+ (i %% n) = x ^+ i.
Proof.
move=> xn1; rewrite {2}(divn_eq i n) exprD mulnC exprM xn1.
by rewrite expr1n mul1r.
Qed.

Lemma expr_dvd n x i : x ^+ n = 1 -> n %| i -> x ^+ i = 1.
Proof.
by move=> xn1 dvd_n_i; rewrite -(expr_mod i xn1) (eqnP dvd_n_i).
Qed.

Lemma natrX n k : (n ^ k)%:R = n%:R ^+ k :> R.
Proof. by rewrite exprMn_n expr1n. Qed.

Lemma signr_odd n : (-1) ^+ (odd n) = (-1) ^+ n :> R.
Proof.
elim: n => //= n IHn; rewrite exprS -{}IHn.
by case/odd: n; rewrite !mulN1r ?opprK.
Qed.

Lemma signr_eq0 n : ((-1) ^+ n == 0 :> R) = false.
Proof. by rewrite -signr_odd; case: odd; rewrite ?oppr_eq0 oner_eq0. Qed.

Lemma mulr_sign (b : bool) x : (-1) ^+ b * x = (if b then - x else x).
Proof. by case: b; rewrite ?mulNr mul1r. Qed.

Lemma signr_addb b1 b2 : (-1) ^+ (b1 (+) b2) = (-1) ^+ b1 * (-1) ^+ b2 :> R.
Proof. by rewrite mulr_sign; case: b1 b2 => [] []; rewrite ?opprK. Qed.

Lemma signrE (b : bool) : (-1) ^+ b = 1 - b.*2%:R :> R.
Proof. by case: b; rewrite ?subr0 // opprD addNKr. Qed.

Lemma signrN b : (-1) ^+ (~~ b) = - (-1) ^+ b :> R.
Proof. by case: b; rewrite ?opprK. Qed.

Lemma mulr_signM (b1 b2 : bool) x1 x2 :
  ((-1) ^+ b1 * x1) * ((-1) ^+ b2 * x2) = (-1) ^+ (b1 (+) b2) * (x1 * x2).
Proof.
by rewrite signr_addb -!mulrA; congr (_ * _); rewrite !mulrA commr_sign.
Qed.

Lemma exprNn x n : (- x) ^+ n = (-1) ^+ n * x ^+ n :> R.
Proof. by rewrite -mulN1r exprMn_comm // /comm mulN1r mulrN mulr1. Qed.

Lemma sqrrN x : (- x) ^+ 2 = x ^+ 2.
Proof. exact: mulrNN. Qed.

Lemma sqrr_sign n : ((-1) ^+ n) ^+ 2 = 1 :> R.
Proof. by rewrite exprAC sqrrN !expr1n. Qed.

Lemma signrMK n : @involutive R ( *%R ((-1) ^+ n)).
Proof. by move=> x; rewrite mulrA -expr2 sqrr_sign mul1r. Qed.

Lemma mulrI_eq0 x y : lreg x -> (x * y == 0) = (y == 0).
Proof. by move=> reg_x; rewrite -{1}(mulr0 x) (inj_eq reg_x). Qed.

Lemma lreg_neq0 x : lreg x -> x != 0.
Proof. by move=> reg_x; rewrite -[x]mulr1 mulrI_eq0 ?oner_eq0. Qed.

Lemma mulrI0_lreg x : (forall y, x * y = 0 -> y = 0) -> lreg x.
Proof.
move=> reg_x y z eq_xy_xz; apply/eqP; rewrite -subr_eq0 [y - z]reg_x //.
by rewrite mulrBr eq_xy_xz subrr.
Qed.

Lemma lregN x : lreg x -> lreg (- x).
Proof. by move=> reg_x y z; rewrite !mulNr => /oppr_inj/reg_x. Qed.

Lemma lreg1 : lreg (1 : R).
Proof. by move=> x y; rewrite !mul1r. Qed.

Lemma lregM x y : lreg x -> lreg y -> lreg (x * y).
Proof. by move=> reg_x reg_y z t; rewrite -!mulrA => /reg_x/reg_y. Qed.

Lemma lregX x n : lreg x -> lreg (x ^+ n).
Proof.
by move=> reg_x; elim: n => [|n]; [exact: lreg1 | rewrite exprS; exact: lregM].
Qed.

Lemma lreg_sign n : lreg ((-1) ^+ n : R).
Proof. by apply: lregX; apply: lregN; apply: lreg1. Qed.

Lemma prodr_const (I : finType) (A : pred I) (x : R) :
  \prod_(i in A) x = x ^+ #|A|.
Proof. by rewrite big_const -iteropE. Qed.

Lemma prodrXr x I r P (F : I -> nat) :
  \prod_(i <- r | P i) x ^+ F i = x ^+ (\sum_(i <- r | P i) F i).
Proof. by rewrite (big_morph _ (exprD _) (erefl _)). Qed.

Lemma prodrN (I : finType) (A : pred I) (F : I -> R) :
  \prod_(i in A) - F i = (- 1) ^+ #|A| * \prod_(i in A) F i.
Proof.
rewrite -sum1_card  -!(big_filter _ A) !unlock.
elim: {A}(filter _ _) => /= [|i r ->]; first by rewrite mul1r.
by rewrite mulrA -mulN1r (commrX _ (commrN1 _)) exprSr !mulrA.
Qed.

Lemma prodrMn n (I : finType) (A : pred I) (F : I -> R) :
  \prod_(i in A) (F i *+ n) = \prod_(i in A) F i *+ n ^ #|A|.
Proof.
rewrite -sum1_card /= -!(big_filter _ A) !unlock.
elim: {A}(filter _ _) => //= i r ->; by rewrite mulrnAr mulrnAl expnS mulrnA.
Qed.

Lemma exprDn_comm x y n (cxy : comm x y) :
  (x + y) ^+ n = \sum_(i < n.+1) (x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof.
elim: n => [|n IHn]; rewrite big_ord_recl mulr1 ?big_ord0 ?addr0 //=.
rewrite exprS {}IHn /= mulrDl !big_distrr /= big_ord_recl mulr1 subn0.
rewrite !big_ord_recr /= !binn !subnn !mul1r !subn0 bin0 !exprS -addrA.
congr (_ + _); rewrite addrA -big_split /=; congr (_ + _).
apply: eq_bigr => i _; rewrite !mulrnAr !mulrA -exprS -subSn ?(valP i) //.
by rewrite  subSS (commrX _ (commr_sym cxy)) -mulrA -exprS -mulrnDr.
Qed.

Lemma exprBn_comm x y n (cxy : comm x y) :
  (x - y) ^+ n =
    \sum_(i < n.+1) ((-1) ^+ i * x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof.
rewrite exprDn_comm; last exact: commrN.
by apply: eq_bigr => i _; congr (_ *+ _); rewrite -commr_sign -mulrA -exprNn.
Qed.

Lemma subrXX_comm x y n (cxy : comm x y) :
  x ^+ n - y ^+ n = (x - y) * (\sum_(i < n) x ^+ (n.-1 - i) * y ^+ i).
Proof.
case: n => [|n]; first by rewrite big_ord0 mulr0 subrr.
rewrite mulrBl !big_distrr big_ord_recl big_ord_recr /= subnn mulr1 mul1r.
rewrite subn0 -!exprS opprD -!addrA; congr (_ + _); rewrite addrA -sumrB.
rewrite big1 ?add0r // => i _; rewrite !mulrA -exprS -subSn ?(valP i) //.
by rewrite subSS (commrX _ (commr_sym cxy)) -mulrA -exprS subrr.
Qed.

Lemma exprD1n x n : (x + 1) ^+ n = \sum_(i < n.+1) x ^+ i *+ 'C(n, i).
Proof.
rewrite addrC (exprDn_comm n (commr_sym (commr1 x))).
by apply: eq_bigr => i _; rewrite expr1n mul1r.
Qed.

Lemma subrX1 x n : x ^+ n - 1 = (x - 1) * (\sum_(i < n) x ^+ i).
Proof.
rewrite -!(opprB 1) mulNr -{1}(expr1n n).
rewrite (subrXX_comm _ (commr_sym (commr1 x))); congr (- (_ * _)).
by apply: eq_bigr => i _; rewrite expr1n mul1r.
Qed.

Lemma sqrrD1 x : (x + 1) ^+ 2 = x ^+ 2 + x *+ 2 + 1.
Proof.
rewrite exprD1n !big_ord_recr big_ord0 /= add0r.
by rewrite addrC addrA addrAC.
Qed.

Lemma sqrrB1 x : (x - 1) ^+ 2 = x ^+ 2 - x *+ 2 + 1.
Proof. by rewrite -sqrrN opprB addrC sqrrD1 sqrrN mulNrn. Qed.

Lemma subr_sqr_1 x : x ^+ 2 - 1 = (x - 1) * (x + 1).
Proof. by rewrite subrX1 !big_ord_recr big_ord0 /= addrAC add0r. Qed.

Definition Frobenius_aut p of p \in [char R] := fun x => x ^+ p.

Section FrobeniusAutomorphism.

Variable p : nat.
Hypothesis charFp : p \in [char R].

Lemma charf0 : p%:R = 0 :> R. Proof. by apply/eqP; case/andP: charFp. Qed.
Lemma charf_prime : prime p. Proof. by case/andP: charFp. Qed.
Hint Resolve charf_prime.

Lemma mulrn_char x : x *+ p = 0. Proof. by rewrite -mulr_natl charf0 mul0r. Qed.

Lemma natr_mod_char n : (n %% p)%:R = n%:R :> R.
Proof. by rewrite {2}(divn_eq n p) natrD mulrnA mulrn_char add0r. Qed.

Lemma dvdn_charf n : (p %| n)%N = (n%:R == 0 :> R).
Proof.
apply/idP/eqP=> [/dvdnP[n' ->]|n0]; first by rewrite natrM charf0 mulr0.
apply/idPn; rewrite -prime_coprime // => /eqnP pn1.
have [a _ /dvdnP[b]] := Bezoutl n (prime_gt0 charf_prime).
move/(congr1 (fun m => m%:R : R))/eqP.
by rewrite natrD !natrM charf0 n0 !mulr0 pn1 addr0 oner_eq0.
Qed.

Lemma charf_eq : [char R] =i (p : nat_pred).
Proof.
move=> q; apply/andP/eqP=> [[q_pr q0] | ->]; last by rewrite charf0.
by apply/eqP; rewrite eq_sym -dvdn_prime2 // dvdn_charf.
Qed.

Lemma bin_lt_charf_0 k : 0 < k < p -> 'C(p, k)%:R = 0 :> R.
Proof. by move=> lt0kp; apply/eqP; rewrite -dvdn_charf prime_dvd_bin. Qed.

Local Notation "x ^f" := (Frobenius_aut charFp x).

Lemma Frobenius_autE x : x^f = x ^+ p. Proof. by []. Qed.
Local Notation fE := Frobenius_autE.

Lemma Frobenius_aut0 : 0^f = 0.
Proof. by rewrite fE -(prednK (prime_gt0 charf_prime)) exprS mul0r. Qed.

Lemma Frobenius_aut1 : 1^f = 1.
Proof. by rewrite fE expr1n. Qed.

Lemma Frobenius_autD_comm x y (cxy : comm x y) : (x + y)^f = x^f + y^f.
Proof.
have defp := prednK (prime_gt0 charf_prime).
rewrite !fE exprDn_comm // big_ord_recr subnn -defp big_ord_recl /= defp.
rewrite subn0 mulr1 mul1r bin0 binn big1 ?addr0 // => i _.
by rewrite -mulr_natl bin_lt_charf_0 ?mul0r //= -{2}defp ltnS (valP i).
Qed.

Lemma Frobenius_autMn x n : (x *+ n)^f = x^f *+ n.
Proof.
elim: n => [|n IHn]; first exact: Frobenius_aut0.
rewrite !mulrS Frobenius_autD_comm ?IHn //; exact: commrMn.
Qed.

Lemma Frobenius_aut_nat n : (n%:R)^f = n%:R.
Proof. by rewrite Frobenius_autMn Frobenius_aut1. Qed.

Lemma Frobenius_autM_comm x y : comm x y -> (x * y)^f = x^f * y^f.
Proof. by exact: exprMn_comm. Qed.

Lemma Frobenius_autX x n : (x ^+ n)^f = x^f ^+ n.
Proof. by rewrite !fE -!exprM mulnC. Qed.

Lemma Frobenius_autN x : (- x)^f = - x^f.
Proof.
apply/eqP; rewrite -subr_eq0 opprK addrC.
by rewrite -(Frobenius_autD_comm (commrN _)) // subrr Frobenius_aut0.
Qed.

Lemma Frobenius_autB_comm x y : comm x y -> (x - y)^f = x^f - y^f.
Proof.
by move/commrN/Frobenius_autD_comm->; rewrite Frobenius_autN.
Qed.

End FrobeniusAutomorphism.

Lemma exprNn_char x n : [char R].-nat n -> (- x) ^+ n = - (x ^+ n).
Proof.
pose p := pdiv n; have [|n_gt1 charRn] := leqP n 1; first by case: (n) => [|[]].
have charRp: p \in [char R] by rewrite (pnatPpi charRn) // pi_pdiv.
have /p_natP[e ->]: p.-nat n by rewrite -(eq_pnat _ (charf_eq charRp)).
elim: e => // e IHe; rewrite expnSr !exprM {}IHe.
by rewrite -(Frobenius_autE charRp) Frobenius_autN.
Qed.

Section Char2.

Hypothesis charR2 : 2 \in [char R].

Lemma addrr_char2 x : x + x = 0. Proof. by rewrite -mulr2n mulrn_char. Qed.

Lemma oppr_char2 x : - x = x.
Proof. by apply/esym/eqP; rewrite -addr_eq0 addrr_char2. Qed.

Lemma subr_char2 x y : x - y = x + y. Proof. by rewrite oppr_char2. Qed.

Lemma addrK_char2 x : involutive (+%R^~ x).
Proof. by move=> y; rewrite /= -subr_char2 addrK. Qed.

Lemma addKr_char2 x : involutive (+%R x).
Proof. by move=> y; rewrite -{1}[x]oppr_char2 addKr. Qed.

End Char2.

Canonical converse_eqType := [eqType of R^c].
Canonical converse_choiceType := [choiceType of R^c].
Canonical converse_zmodType := [zmodType of R^c].

Definition converse_ringMixin :=
  let mul' x y := y * x in
  let mulrA' x y z := esym (mulrA z y x) in
  let mulrDl' x y z := mulrDr z x y in
  let mulrDr' x y z := mulrDl y z x in
  @Ring.Mixin converse_zmodType
    1 mul' mulrA' mulr1 mul1r mulrDl' mulrDr' oner_neq0.
Canonical converse_ringType := RingType R^c converse_ringMixin.

Section ClosedPredicates.

Variable S : predPredType R.

Definition mulr_2closed := {in S &, forall u v, u * v \in S}.
Definition mulr_closed := 1 \in S /\ mulr_2closed.
Definition smulr_closed := -1 \in S /\ mulr_2closed.
Definition semiring_closed := addr_closed S /\ mulr_closed.
Definition subring_closed := [/\ 1 \in S, subr_2closed S & mulr_2closed].

Lemma smulr_closedM : smulr_closed -> mulr_closed.
Proof. by case=> SN1 SM; split=> //; rewrite -[1]mulr1 -mulrNN SM. Qed.

Lemma smulr_closedN : smulr_closed -> oppr_closed S.
Proof. by case=> SN1 SM x Sx; rewrite -mulN1r SM. Qed.

Lemma semiring_closedD : semiring_closed -> addr_closed S. Proof. by case. Qed.

Lemma semiring_closedM : semiring_closed -> mulr_closed. Proof. by case. Qed.

Lemma subring_closedB : subring_closed -> zmod_closed S.
Proof. by case=> S1 SB _; split; rewrite // -(subrr 1) SB. Qed.

Lemma subring_closedM : subring_closed -> smulr_closed.
Proof.
by case=> S1 SB SM; split; rewrite ?(zmod_closedN (subring_closedB _)).
Qed.

Lemma subring_closed_semi : subring_closed -> semiring_closed.
Proof.
by move=> ringS; split; [apply/zmod_closedD/subring_closedB | case: ringS].
Qed.
 
End ClosedPredicates.

End RingTheory.

Section RightRegular.

Variable R : ringType.
Implicit Types x y : R.
Let Rc := converse_ringType R.

Lemma mulIr_eq0 x y : rreg x -> (y * x == 0) = (y == 0).
Proof. exact: (@mulrI_eq0 Rc). Qed.

Lemma mulIr0_rreg x : (forall y, y * x = 0 -> y = 0) -> rreg x.
Proof. exact: (@mulrI0_lreg Rc). Qed.

Lemma rreg_neq0 x : rreg x -> x != 0.
Proof. exact: (@lreg_neq0 Rc). Qed.

Lemma rregN x : rreg x -> rreg (- x).
Proof. exact: (@lregN Rc). Qed.

Lemma rreg1 : rreg (1 : R).
Proof. exact: (@lreg1 Rc). Qed.

Lemma rregM x y : rreg x -> rreg y -> rreg (x * y).
Proof. by move=> reg_x reg_y; exact: (@lregM Rc). Qed.

Lemma revrX x n : (x : Rc) ^+ n = (x : R) ^+ n.
Proof. by elim: n => // n IHn; rewrite exprS exprSr IHn. Qed.

Lemma rregX x n : rreg x -> rreg (x ^+ n).
Proof. by move/(@lregX Rc x n); rewrite revrX. Qed.

End RightRegular.

Module Lmodule.

Structure mixin_of (R : ringType) (V : zmodType) : Type := Mixin {
  scale : R -> V -> V;
  _ : forall a b v, scale a (scale b v) = scale (a * b) v;
  _ : left_id 1 scale;
  _ : right_distributive scale +%R;
  _ : forall v, {morph scale^~ v: a b / a + b}
}.

Section ClassDef.

Variable R : ringType.

Structure class_of V := Class {
  base : Zmodule.class_of V;
  mixin : mixin_of R (Zmodule.Pack base V)
}.
Local Coercion base : class_of >-> Zmodule.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).


Definition pack b0 (m0 : mixin_of R (@Zmodule.Pack T b0 T)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> Zmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Notation lmodType R := (type (Phant R)).
Notation LmodType R T m := (@pack _ (Phant R) T _ m _ _ id _ id).
Notation LmodMixin := Mixin.
Notation "[ 'lmodType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'lmodType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'lmodType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'lmodType'  R  'of'  T ]") : form_scope.
End Exports.

End Lmodule.
Import Lmodule.Exports.

Definition scale (R : ringType) (V : lmodType R) :=
  Lmodule.scale (Lmodule.class V).

Local Notation "*:%R" := (@scale _ _).
Local Notation "a *: v" := (scale a v) : ring_scope.

Section LmoduleTheory.

Variables (R : ringType) (V : lmodType R).
Implicit Types (a b c : R) (u v : V).

Local Notation "*:%R" := (@scale R V).

Lemma scalerA a b v : a *: (b *: v) = a * b *: v.
Proof. by case: V v => ? [] ? []. Qed.

Lemma scale1r : @left_id R V 1 *:%R.
Proof. by case: V => ? [] ? []. Qed.

Lemma scalerDr a : {morph *:%R a : u v / u + v}.
Proof. by case: V a => ? [] ? []. Qed.

Lemma scalerDl v : {morph *:%R^~ v : a b / a + b}.
Proof. by case: V v => ? [] ? []. Qed.

Lemma scale0r v : 0 *: v = 0.
Proof. by apply: (addIr (1 *: v)); rewrite -scalerDl !add0r. Qed.

Lemma scaler0 a : a *: 0 = 0 :> V.
Proof. by rewrite -{1}(scale0r 0) scalerA mulr0 scale0r. Qed.

Lemma scaleNr a v : - a *: v = - (a *: v).
Proof. by apply: (addIr (a *: v)); rewrite -scalerDl !addNr scale0r. Qed.

Lemma scaleN1r v : (- 1) *: v = - v.
Proof. by rewrite scaleNr scale1r. Qed.

Lemma scalerN a v : a *: (- v) = - (a *: v).
Proof. by apply: (addIr (a *: v)); rewrite -scalerDr !addNr scaler0. Qed.

Lemma scalerBl a b v : (a - b) *: v = a *: v - b *: v.
Proof. by rewrite scalerDl scaleNr. Qed.

Lemma scalerBr a u v : a *: (u - v) = a *: u - a *: v.
Proof. by rewrite scalerDr scalerN. Qed.

Lemma scaler_nat n v : n%:R *: v = v *+ n.
Proof.
elim: n => /= [|n ]; first by rewrite scale0r.
by rewrite !mulrS scalerDl ?scale1r => ->.
Qed.

Lemma scaler_sign (b : bool) v: (-1) ^+ b *: v = (if b then - v else v).
Proof. by case: b; rewrite ?scaleNr scale1r. Qed.

Lemma signrZK n : @involutive V ( *:%R ((-1) ^+ n)).
Proof. by move=> u; rewrite scalerA -expr2 sqrr_sign scale1r. Qed.

Lemma scalerMnl a v n : a *: v *+ n = (a *+ n) *: v.
Proof.
elim: n => [|n IHn]; first by rewrite !mulr0n scale0r.
by rewrite !mulrSr IHn scalerDl.
Qed.

Lemma scalerMnr a v n : a *: v *+ n = a *: (v *+ n).
Proof.
elim: n => [|n IHn]; first by rewrite !mulr0n scaler0.
by rewrite !mulrSr IHn scalerDr.
Qed.

Lemma scaler_suml v I r (P : pred I) F :
  (\sum_(i <- r | P i) F i) *: v = \sum_(i <- r | P i) F i *: v.
Proof. exact: (big_morph _ (scalerDl v) (scale0r v)). Qed.

Lemma scaler_sumr a I r (P : pred I) (F : I -> V) :
  a *: (\sum_(i <- r | P i) F i) = \sum_(i <- r | P i) a *: F i.
Proof. exact: big_endo (scalerDr a) (scaler0 a) I r P F. Qed.

Section ClosedPredicates.

Variable S : predPredType V.

Definition scaler_closed := forall a, {in S, forall v, a *: v \in S}.
Definition linear_closed := forall a, {in S &, forall u v, a *: u + v \in S}.
Definition submod_closed := 0 \in S /\ linear_closed.

Lemma linear_closedB : linear_closed -> subr_2closed S.
Proof. by move=> Slin u v Su Sv; rewrite addrC -scaleN1r Slin. Qed.

Lemma submod_closedB : submod_closed -> zmod_closed S.
Proof. by case=> S0 /linear_closedB. Qed.

Lemma submod_closedZ : submod_closed -> scaler_closed.
Proof. by case=> S0 Slin a v Sv; rewrite -[a *: v]addr0 Slin. Qed.

End ClosedPredicates.

End LmoduleTheory.

Module Lalgebra.

Definition axiom (R : ringType) (V : lmodType R) (mul : V -> V -> V) :=
  forall a u v, a *: mul u v = mul (a *: u) v.

Section ClassDef.

Variable R : ringType.

Record class_of (T : Type) : Type := Class {
  base : Ring.class_of T;
  mixin : Lmodule.mixin_of R (Zmodule.Pack base T);
  ext : @axiom R (Lmodule.Pack _ (Lmodule.Class mixin) T) (Ring.mul base)
}.
Definition base2 R m := Lmodule.Class (@mixin R m).
Local Coercion base : class_of >-> Ring.class_of.
Local Coercion base2 : class_of >-> Lmodule.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack T b0 mul0 (axT : @axiom R (@Lmodule.Pack R _ T b0 T) mul0) :=
  fun bT b & phant_id (Ring.class bT) (b : Ring.class_of T) =>
  fun mT m & phant_id (@Lmodule.class R phR mT) (@Lmodule.Class R T b m) =>
  fun ax & phant_id axT ax =>
  Pack (Phant R) (@Class T b m ax) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition lmodType := @Lmodule.Pack R phR cT xclass xT.
Definition lmod_ringType := @Lmodule.Pack R phR ringType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion base2 : class_of >-> Lmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Canonical lmod_ringType.
Notation lalgType R := (type (Phant R)).
Notation LalgType R T a := (@pack _ (Phant R) T _ _ a _ _ id _ _ id _ id).
Notation "[ 'lalgType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'lalgType'  R  'of'  T  'for'  cT ]")
  : form_scope.
Notation "[ 'lalgType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'lalgType'  R  'of'  T ]") : form_scope.
End Exports.

End Lalgebra.
Import Lalgebra.Exports.

(* Scalar injection (see the definition of in_alg A below). *)
Local Notation "k %:A" := (k *: 1) : ring_scope.

(* Regular ring algebra tag. *)
Definition regular R : Type := R.
Local Notation "R ^o" := (regular R) (at level 2, format "R ^o") : type_scope.

Section LalgebraTheory.

Variables (R : ringType) (A : lalgType R).
Implicit Types x y : A.

Lemma scalerAl k (x y : A) : k *: (x * y) = k *: x * y.
Proof. by case: A k x y => ? []. Qed.

Lemma mulr_algl a x : a%:A * x = a *: x.
Proof. by rewrite -scalerAl mul1r. Qed.

Canonical regular_eqType := [eqType of R^o].
Canonical regular_choiceType := [choiceType of R^o].
Canonical regular_zmodType := [zmodType of R^o].
Canonical regular_ringType := [ringType of R^o].

Definition regular_lmodMixin :=
  let mkMixin := @Lmodule.Mixin R regular_zmodType (@mul R) in
  mkMixin (@mulrA R) (@mul1r R) (@mulrDr R) (fun v a b => mulrDl a b v).

Canonical regular_lmodType := LmodType R R^o regular_lmodMixin.
Canonical regular_lalgType := LalgType R R^o (@mulrA regular_ringType).

Section ClosedPredicates.

Variable S : predPredType A.

Definition subalg_closed := [/\ 1 \in S, linear_closed S & mulr_2closed S].

Lemma subalg_closedZ : subalg_closed -> submod_closed S.
Proof. by case=> S1 Slin _; split; rewrite // -(subrr 1) linear_closedB. Qed.

Lemma subalg_closedBM : subalg_closed -> subring_closed S.
Proof. by case=> S1 Slin SM; split=> //; apply: linear_closedB. Qed.

End ClosedPredicates.

End LalgebraTheory.

(* Morphism hierarchy. *)

Module Additive.

Section ClassDef.

Variables U V : zmodType.

Definition axiom (f : U -> V) := {morph f : x y / x - y}.

Structure map (phUV : phant (U -> V)) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation additive f := (axiom f).
Coercion apply : map >-> Funclass.
Notation Additive fA := (Pack (Phant _) fA).
Notation "{ 'additive' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'additive'  fUV }") : ring_scope.
Notation "[ 'additive' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'additive'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'additive' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'additive'  'of'  f ]") : form_scope.
End Exports.

End Additive.
Include Additive.Exports. (* Allows GRing.additive to resolve conflicts. *)

(* Lifted additive operations. *)
Section LiftedZmod.
Variables (U : Type) (V : zmodType).
Definition null_fun_head (phV : phant V) of U : V := let: Phant := phV in 0.
Definition add_fun_head t (f g : U -> V) x := let: tt := t in f x + g x.
Definition sub_fun_head t (f g : U -> V) x := let: tt := t in f x - g x.
End LiftedZmod.

(* Lifted multiplication. *)
Section LiftedRing.
Variables (R : ringType) (T : Type).
Implicit Type f : T -> R.
Definition mull_fun_head t a f x := let: tt := t in a * f x.
Definition mulr_fun_head t a f x := let: tt := t in f x * a.
End LiftedRing.

(* Lifted linear operations. *)
Section LiftedScale.
Variables (R : ringType) (U : Type) (V : lmodType R) (A : lalgType R).
Definition scale_fun_head t a (f : U -> V) x := let: tt := t in a *: f x.
Definition in_alg_head (phA : phant A) k : A := let: Phant := phA in k%:A.
End LiftedScale.

Notation null_fun V := (null_fun_head (Phant V)) (only parsing).
(* The real in_alg notation is declared after GRing.Theory so that at least *)
(* in Coq 8.2 it gets precedence when GRing.Theory is not imported.         *)
Local Notation in_alg_loc A := (in_alg_head (Phant A)) (only parsing).

Local Notation "\0" := (null_fun _) : ring_scope.
Local Notation "f \+ g" := (add_fun_head tt f g) : ring_scope.
Local Notation "f \- g" := (sub_fun_head tt f g) : ring_scope.
Local Notation "a \*: f" := (scale_fun_head tt a f) : ring_scope.
Local Notation "x \*o f" := (mull_fun_head tt x f) : ring_scope.
Local Notation "x \o* f" := (mulr_fun_head tt x f) : ring_scope.

Section AdditiveTheory.

Section Properties.

Variables (U V : zmodType) (k : unit) (f : {additive U -> V}).

Lemma raddfB : {morph f : x y / x - y}. Proof. exact: Additive.class. Qed.

Lemma raddf0 : f 0 = 0.
Proof. by rewrite -[0]subr0 raddfB subrr. Qed.

Lemma raddf_eq0 x : injective f -> (f x == 0) = (x == 0).
Proof. by move=> /inj_eq <-; rewrite raddf0. Qed.

Lemma raddfN : {morph f : x / - x}.
Proof. by move=> x /=; rewrite -sub0r raddfB raddf0 sub0r. Qed.

Lemma raddfD : {morph f : x y / x + y}.
Proof. by move=> x y; rewrite -[y]opprK raddfB -raddfN. Qed.

Lemma raddfMn n : {morph f : x / x *+ n}.
Proof. by elim: n => [|n IHn] x /=; rewrite ?raddf0 // !mulrS raddfD IHn. Qed.

Lemma raddfMNn n : {morph f : x / x *- n}.
Proof. by move=> x /=; rewrite raddfN raddfMn. Qed.

Lemma raddf_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
Proof. exact: (big_morph f raddfD raddf0). Qed.

Lemma can2_additive f' : cancel f f' -> cancel f' f -> additive f'.
Proof. by move=> fK f'K x y /=; apply: (canLR fK); rewrite raddfB !f'K. Qed.

Lemma bij_additive :
  bijective f -> exists2 f' : {additive V -> U}, cancel f f' & cancel f' f.
Proof. by case=> f' fK f'K; exists (Additive (can2_additive fK f'K)). Qed.

Fact locked_is_additive : additive (locked_with k (f : U -> V)).
Proof. by case: k f => [] []. Qed.
Canonical locked_additive := Additive locked_is_additive.

End Properties.

Section RingProperties.

Variables (R S : ringType) (f : {additive R -> S}).

Lemma raddfMnat n x : f (n%:R * x) = n%:R * f x.
Proof. by rewrite !mulr_natl raddfMn. Qed.

Lemma raddfMsign n x : f ((-1) ^+ n * x) = (-1) ^+ n * f x.
Proof. by rewrite !(mulr_sign, =^~ signr_odd) (fun_if f) raddfN. Qed.

Variables (U : lmodType R) (V : lmodType S) (h : {additive U -> V}).

Lemma raddfZnat n u : h (n%:R *: u) = n%:R *: h u.
Proof. by rewrite !scaler_nat raddfMn. Qed.

Lemma raddfZsign n u : h ((-1) ^+ n *: u) = (-1) ^+ n *: h u.
Proof. by rewrite !(scaler_sign, =^~ signr_odd) (fun_if h) raddfN. Qed.

End RingProperties.

Section AddFun.

Variables (U V W : zmodType) (f g : {additive V -> W}) (h : {additive U -> V}).

Fact idfun_is_additive : additive (@idfun U).
Proof. by []. Qed.
Canonical idfun_additive := Additive idfun_is_additive.

Fact comp_is_additive : additive (f \o h).
Proof. by move=> x y /=; rewrite !raddfB. Qed.
Canonical comp_additive := Additive comp_is_additive.

Fact opp_is_additive : additive (-%R : U -> U).
Proof. by move=> x y; rewrite /= opprD. Qed.
Canonical opp_additive := Additive opp_is_additive.

Fact null_fun_is_additive : additive (\0 : U -> V).
Proof. by move=> /=; rewrite subr0. Qed.
Canonical null_fun_additive := Additive null_fun_is_additive.

Fact add_fun_is_additive : additive (f \+ g).
Proof.
by move=> x y /=; rewrite !raddfB addrCA -!addrA addrCA -opprD.
Qed.
Canonical add_fun_additive := Additive add_fun_is_additive.

Fact sub_fun_is_additive : additive (f \- g).
Proof.
by move=> x y /=; rewrite !raddfB addrAC -!addrA -!opprD addrAC addrA.
Qed.
Canonical sub_fun_additive := Additive sub_fun_is_additive.

End AddFun.

Section MulFun.

Variables (R : ringType) (U : zmodType).
Variables (a : R) (f : {additive U -> R}).

Fact mull_fun_is_additive : additive (a \*o f).
Proof. by move=> x y /=; rewrite raddfB mulrBr. Qed.
Canonical mull_fun_additive := Additive mull_fun_is_additive.

Fact mulr_fun_is_additive : additive (a \o* f).
Proof. by move=> x y /=; rewrite raddfB mulrBl. Qed.
Canonical mulr_fun_additive := Additive mulr_fun_is_additive.

End MulFun.

Section ScaleFun.

Variables (R : ringType) (U : zmodType) (V : lmodType R).
Variables (a : R) (f : {additive U -> V}).

Canonical scale_additive := Additive (@scalerBr R V a).
Canonical scale_fun_additive := [additive of a \*: f as f \; *:%R a].

End ScaleFun.

End AdditiveTheory.

Module RMorphism.

Section ClassDef.

Variables R S : ringType.

Definition mixin_of (f : R -> S) :=
  {morph f : x y / x * y}%R * (f 1 = 1) : Type.

Record class_of f : Type := Class {base : additive f; mixin : mixin_of f}.
Local Coercion base : class_of >-> additive.

Structure map (phRS : phant (R -> S)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.
Variables (phRS : phant (R -> S)) (f g : R -> S) (cF : map phRS).

Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Definition clone fM of phant_id g (apply cF) & phant_id fM class :=
  @Pack phRS f fM.

Definition pack (fM : mixin_of f) :=
  fun (bF : Additive.map phRS) fA & phant_id (Additive.class bF) fA =>
  Pack phRS (Class fA fM).

Canonical additive := Additive.Pack phRS class.

End ClassDef.

Module Exports.
Notation multiplicative f := (mixin_of f).
Notation rmorphism f := (class_of f).
Coercion base : rmorphism >-> Additive.axiom.
Coercion mixin : rmorphism >-> multiplicative.
Coercion apply : map >-> Funclass.
Notation RMorphism fM := (Pack (Phant _) fM).
Notation AddRMorphism fM := (pack fM id).
Notation "{ 'rmorphism' fRS }" := (map (Phant fRS))
  (at level 0, format "{ 'rmorphism'  fRS }") : ring_scope.
Notation "[ 'rmorphism' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'rmorphism'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'rmorphism' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'rmorphism'  'of'  f ]") : form_scope.
Coercion additive : map >-> Additive.map.
Canonical additive.
End Exports.

End RMorphism.
Include RMorphism.Exports.

Section RmorphismTheory.

Section Properties.

Variables (R S : ringType) (k : unit) (f : {rmorphism R -> S}).

Lemma rmorph0 : f 0 = 0. Proof. exact: raddf0. Qed.
Lemma rmorphN : {morph f : x / - x}. Proof. exact: raddfN. Qed.
Lemma rmorphD : {morph f : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma rmorphB : {morph f: x y / x - y}. Proof. exact: raddfB. Qed.
Lemma rmorphMn n : {morph f : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma rmorphMNn n : {morph f : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma rmorph_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
Proof. exact: raddf_sum. Qed.
Lemma rmorphMsign n : {morph f : x / (- 1) ^+ n * x}.
Proof. exact: raddfMsign. Qed.

Lemma rmorphismP : rmorphism f. Proof. exact: RMorphism.class. Qed.
Lemma rmorphismMP : multiplicative f. Proof. exact: rmorphismP. Qed.
Lemma rmorph1 : f 1 = 1. Proof. by case: rmorphismMP. Qed.
Lemma rmorphM : {morph f: x y  / x * y}. Proof. by case: rmorphismMP. Qed.

Lemma rmorph_prod I r (P : pred I) E :
  f (\prod_(i <- r | P i) E i) = \prod_(i <- r | P i) f (E i).
Proof. exact: (big_morph f rmorphM rmorph1). Qed.

Lemma rmorphX n : {morph f: x / x ^+ n}.
Proof. by elim: n => [|n IHn] x; rewrite ?rmorph1 // !exprS rmorphM IHn. Qed.

Lemma rmorph_nat n : f n%:R = n%:R. Proof. by rewrite rmorphMn rmorph1. Qed.
Lemma rmorphN1 : f (- 1) = (- 1). Proof. by rewrite rmorphN rmorph1. Qed.

Lemma rmorph_sign n : f ((- 1) ^+ n) = (- 1) ^+ n.
Proof. by rewrite rmorphX rmorphN1. Qed.

Lemma rmorph_char p : p \in [char R] -> p \in [char S].
Proof. by rewrite !inE -rmorph_nat => /andP[-> /= /eqP->]; rewrite rmorph0. Qed.

Lemma rmorph_eq_nat x n : injective f -> (f x == n%:R) = (x == n%:R).
Proof. by move/inj_eq <-; rewrite rmorph_nat. Qed.

Lemma rmorph_eq1 x : injective f -> (f x == 1) = (x == 1).
Proof. exact: rmorph_eq_nat 1%N. Qed.

Lemma can2_rmorphism f' : cancel f f' -> cancel f' f -> rmorphism f'.
Proof.
move=> fK f'K; split; first exact: can2_additive fK f'K.
by split=> [x y|]; apply: (canLR fK); rewrite /= (rmorphM, rmorph1) ?f'K.
Qed.

Lemma bij_rmorphism :
  bijective f -> exists2 f' : {rmorphism S -> R}, cancel f f' & cancel f' f.
Proof. by case=> f' fK f'K; exists (RMorphism (can2_rmorphism fK f'K)). Qed.

Fact locked_is_multiplicative : multiplicative (locked_with k (f : R -> S)).
Proof. by case: k f => [] [? []]. Qed.
Canonical locked_rmorphism := AddRMorphism locked_is_multiplicative.

End Properties.

Section Projections.

Variables (R S T : ringType) (f : {rmorphism S -> T}) (g : {rmorphism R -> S}).

Fact idfun_is_multiplicative : multiplicative (@idfun R).
Proof. by []. Qed.
Canonical idfun_rmorphism := AddRMorphism idfun_is_multiplicative.

Fact comp_is_multiplicative : multiplicative (f \o g).
Proof. by split=> [x y|] /=; rewrite ?rmorph1 ?rmorphM. Qed.
Canonical comp_rmorphism := AddRMorphism comp_is_multiplicative.

End Projections.

Section InAlgebra.

Variables (R : ringType) (A : lalgType R).

Fact in_alg_is_rmorphism : rmorphism (in_alg_loc A).
Proof.
split=> [x y|]; first exact: scalerBl.
by split=> [x y|] /=; rewrite ?scale1r // -scalerAl mul1r scalerA.
Qed.
Canonical in_alg_additive := Additive in_alg_is_rmorphism.
Canonical in_alg_rmorphism := RMorphism in_alg_is_rmorphism.

Lemma in_algE a : in_alg_loc A a = a%:A. Proof. by []. Qed.

End InAlgebra.

End RmorphismTheory.

Module Scale.

Section ScaleLaw.

Structure law (R : ringType) (V : zmodType) (s : R -> V -> V) := Law {
  op : R -> V -> V;
  _ : op = s;
  _ : op (-1) =1 -%R;
  _ : forall a, additive (op a)
}.

Definition mul_law R := Law (erefl *%R) (@mulN1r R) (@mulrBr R).
Definition scale_law R U := Law (erefl *:%R) (@scaleN1r R U) (@scalerBr R U).

Variables (R : ringType) (V : zmodType) (s : R -> V -> V) (s_law : law s).
Local Notation s_op := (op s_law).

Lemma opE : s_op = s. Proof. by case: s_law. Qed.
Lemma N1op : s_op (-1) =1 -%R. Proof. by case: s_law. Qed.
Fact opB a : additive (s_op a). Proof. by case: s_law. Qed.
Definition op_additive a := Additive (opB a).

Variables (aR : ringType) (nu : {rmorphism aR -> R}).
Fact comp_opE : nu \; s_op = nu \; s. Proof. exact: congr1 opE. Qed.
Fact compN1op : (nu \; s_op) (-1) =1 -%R.
Proof. by move=> v; rewrite /= rmorphN1 N1op. Qed.
Definition comp_law : law (nu \; s) := Law comp_opE compN1op (fun a => opB _).

End ScaleLaw.

End Scale.

Module Linear.

Section ClassDef.

Variables (R : ringType) (U : lmodType R) (V : zmodType) (s : R -> V -> V).
Implicit Type phUV : phant (U -> V).

Local Coercion Scale.op : Scale.law >-> Funclass.
Definition axiom (f : U -> V) (s_law : Scale.law s) of s = s_law :=
  forall a, {morph f : u v / a *: u + v >-> s a u + v}.
Definition mixin_of (f : U -> V) :=
  forall a, {morph f : v / a *: v >-> s a v}.

Record class_of f : Type := Class {base : additive f; mixin : mixin_of f}.
Local Coercion base : class_of >-> additive.

Lemma class_of_axiom f s_law Ds : @axiom f s_law Ds -> class_of f.
Proof.
move=> fL; have fB: additive f.
  by move=> x y /=; rewrite -scaleN1r addrC fL Ds Scale.N1op addrC.
by split=> // a v /=; rewrite -[a *: v](addrK v) fB fL addrK Ds.
Qed.

Structure map (phUV : phant (U -> V)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (U -> V)) (f g : U -> V) (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fL of phant_id g (apply cF) & phant_id fL class :=
  @Pack phUV f fL.

Definition pack (fZ : mixin_of f) :=
  fun (bF : Additive.map phUV) fA & phant_id (Additive.class bF) fA =>
  Pack phUV (Class fA fZ).

Canonical additive := Additive.Pack phUV class.

(* Support for right-to-left rewriting with the generic linearZ rule. *)
Notation mapUV := (map (Phant (U -> V))).
Definition map_class := mapUV.
Definition map_at (a : R) := mapUV.
Structure map_for a s_a := MapFor {map_for_map : mapUV; _ : s a = s_a}.
Definition unify_map_at a (f : map_at a) := MapFor f (erefl (s a)).
Structure wrapped := Wrap {unwrap : mapUV}.
Definition wrap (f : map_class) := Wrap f.

End ClassDef.

Module Exports.
Canonical Scale.mul_law.
Canonical Scale.scale_law.
Canonical Scale.comp_law.
Canonical Scale.op_additive.
Delimit Scope linear_ring_scope with linR.
Notation "a *: u" := (@Scale.op _ _ *:%R _ a u) : linear_ring_scope.
Notation "a * u" := (@Scale.op _ _ *%R _ a u) : linear_ring_scope.
Notation "a *:^ nu u" := (@Scale.op _ _ (nu \; *:%R) _ a u)
  (at level 40, nu at level 1, format "a  *:^ nu  u") : linear_ring_scope.
Notation "a *^ nu u" := (@Scale.op _ _ (nu \; *%R) _ a u)
  (at level 40, nu at level 1, format "a  *^ nu  u") : linear_ring_scope.
Notation scalable_for s f := (mixin_of s f).
Notation scalable f := (scalable_for *:%R f).
Notation linear_for s f := (axiom f (erefl s)).
Notation linear f := (linear_for *:%R f).
Notation scalar f := (linear_for *%R f).
Notation lmorphism_for s f := (class_of s f).
Notation lmorphism f := (lmorphism_for *:%R f).
Coercion class_of_axiom : axiom >-> lmorphism_for.
Coercion base : lmorphism_for >-> Additive.axiom.
Coercion mixin : lmorphism_for >-> scalable.
Coercion apply : map >-> Funclass.
Notation Linear fL := (Pack (Phant _) fL).
Notation AddLinear fZ := (pack fZ id).
Notation "{ 'linear' fUV | s }" := (map s (Phant fUV))
  (at level 0, format "{ 'linear'  fUV  |  s }") : ring_scope.
Notation "{ 'linear' fUV }" := {linear fUV | *:%R}
  (at level 0, format "{ 'linear'  fUV }") : ring_scope.
Notation "{ 'scalar' U }" := {linear U -> _ | *%R}
  (at level 0, format "{ 'scalar'  U }") : ring_scope.
Notation "[ 'linear' 'of' f 'as' g ]" := (@clone _ _ _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'linear'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'linear' 'of' f ]" := (@clone _ _ _ _ _ f f _ _ id id)
  (at level 0, format "[ 'linear'  'of'  f ]") : form_scope.
Coercion additive : map >-> Additive.map.
Canonical additive.
(* Support for right-to-left rewriting with the generic linearZ rule. *)
Coercion map_for_map : map_for >-> map.
Coercion unify_map_at : map_at >-> map_for.
Canonical unify_map_at.
Coercion unwrap : wrapped >-> map.
Coercion wrap : map_class >-> wrapped.
Canonical wrap.
End Exports.

End Linear.
Include Linear.Exports.

Section LinearTheory.

Variable R : ringType.

Section GenericProperties.

Variables (U : lmodType R) (V : zmodType) (s : R -> V -> V) (k : unit).
Variable f : {linear U -> V | s}.

Lemma linear0 : f 0 = 0. Proof. exact: raddf0. Qed.
Lemma linearN : {morph f : x / - x}. Proof. exact: raddfN. Qed.
Lemma linearD : {morph f : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma linearB : {morph f : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma linearMn n : {morph f : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma linearMNn n : {morph f : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma linear_sum I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f (E i).
Proof. exact: raddf_sum. Qed.

Lemma linearZ_LR : scalable_for s f. Proof. by case: f => ? []. Qed.
Lemma linearP a : {morph f : u v / a *: u + v >-> s a u + v}.
Proof. by move=> u v /=; rewrite linearD linearZ_LR. Qed.

Fact locked_is_scalable : scalable_for s (locked_with k (f : U -> V)).
Proof. by case: k f => [] [? []]. Qed.
Canonical locked_linear := AddLinear locked_is_scalable.

End GenericProperties.

Section BidirectionalLinearZ.

Variables (U : lmodType R) (V : zmodType) (s : R -> V -> V).

(*   The general form of the linearZ lemma uses some bespoke interfaces to   *)
(* allow right-to-left rewriting when a composite scaling operation such as  *)
(* conjC \; *%R has been expanded, say in a^* * f u. This redex is matched   *)
(* by using the Scale.law interface to recognize a "head" scaling operation  *)
(* h (here *%R), stow away its "scalar" c, then reconcile h c and s a, once  *)
(* s is known, that is, once the Linear.map structure for f has been found.  *)
(* In general, s and a need not be equal to h and c; indeed they need not    *)
(* have the same type! The unification is performed by the unify_map_at      *)
(* default instance for the Linear.map_for U s a h_c sub-interface of        *)
(* Linear.map; the h_c pattern uses the Scale.law structure to insure it is  *)
(* inferred when rewriting right-to-left.                                    *)
(*   The wrap on the rhs allows rewriting f (a *: b *: u) into a *: b *: f u *)
(* with rewrite !linearZ /= instead of rewrite linearZ /= linearZ /=.        *)
(* Without it, the first rewrite linearZ would produce                       *)
(*    (a *: apply (map_for_map (@check_map_at .. a f)) (b *: u)%R)%Rlin      *)
(* and matching the second rewrite LHS would bypass the unify_map_at default *)
(* instance for b, reuse the one for a, and subsequently fail to match the   *)
(* b *: u argument. The extra wrap / unwrap ensures that this can't happen.  *)
(* In the RL direction, the wrap / unwrap will be inserted on the redex side *)
(* as needed, without causing unnecessary delta-expansion: using an explicit *)
(* identity function would have Coq normalize the redex to head normal, then *)
(* reduce the identity to expose the map_for_map projection, and the         *)
(* expanded Linear.map structure would then be exposed in the result.        *)
(*   Most of this machinery will be invisible to a casual user, because all  *)
(* the projections and default instances involved are declared as coercions. *)

Variables (S : ringType) (h : S -> V -> V) (h_law : Scale.law h).

Lemma linearZ c a (h_c := Scale.op h_law c) (f : Linear.map_for U s a h_c) u :
  f (a *: u) = h_c (Linear.wrap f u).
Proof. by rewrite linearZ_LR; case: f => f /= ->. Qed.

End BidirectionalLinearZ.

Section LmodProperties.

Variables (U V : lmodType R) (f : {linear U -> V}).

Lemma linearZZ : scalable f. Proof. exact: linearZ_LR. Qed.
Lemma linearPZ : linear f. Proof. exact: linearP. Qed.

Lemma can2_linear f' : cancel f f' -> cancel f' f -> linear f'.
Proof. by move=> fK f'K a x y /=; apply: (canLR fK); rewrite linearP !f'K. Qed.

Lemma bij_linear :
  bijective f -> exists2 f' : {linear V -> U}, cancel f f' & cancel f' f.
Proof. by case=> f' fK f'K; exists (Linear (can2_linear fK f'K)). Qed.

End LmodProperties.

Section ScalarProperties.

Variable (U : lmodType R) (f : {scalar U}).

Lemma scalarZ : scalable_for *%R f. Proof. exact: linearZ_LR. Qed.
Lemma scalarP : scalar f. Proof. exact: linearP. Qed.

End ScalarProperties.

Section LinearLmod.

Variables (W U : lmodType R) (V : zmodType) (s : R -> V -> V).
Variables (f : {linear U -> V | s}) (h : {linear W -> U}).

Lemma idfun_is_scalable : scalable (@idfun U). Proof. by []. Qed.
Canonical idfun_linear := AddLinear idfun_is_scalable.

Lemma opp_is_scalable : scalable (-%R : U -> U).
Proof. by move=> a v /=; rewrite scalerN. Qed.
Canonical opp_linear := AddLinear opp_is_scalable.

Lemma comp_is_scalable : scalable_for s (f \o h).
Proof. by move=> a v /=; rewrite !linearZ_LR. Qed.
Canonical comp_linear := AddLinear comp_is_scalable.

Variables (s_law : Scale.law s) (g : {linear U -> V | Scale.op s_law}).
Let Ds : s =1 Scale.op s_law. Proof. by rewrite Scale.opE. Qed.

Lemma null_fun_is_scalable : scalable_for (Scale.op s_law) (\0 : U -> V).
Proof. by move=> a v /=; rewrite raddf0. Qed.
Canonical null_fun_linear := AddLinear null_fun_is_scalable.

Lemma add_fun_is_scalable : scalable_for s (f \+ g).
Proof. by move=> a u; rewrite /= !linearZ_LR !Ds raddfD. Qed.
Canonical add_fun_linear := AddLinear add_fun_is_scalable.

Lemma sub_fun_is_scalable : scalable_for s (f \- g).
Proof. by move=> a u; rewrite /= !linearZ_LR !Ds raddfB. Qed.
Canonical sub_fun_linear := AddLinear sub_fun_is_scalable.

End LinearLmod.

Section LinearLalg.

Variables (A : lalgType R) (U : lmodType R).

Variables (a : A) (f : {linear U -> A}).

Fact mulr_fun_is_scalable : scalable (a \o* f).
Proof. by move=> k x /=; rewrite linearZ scalerAl. Qed.
Canonical mulr_fun_linear := AddLinear mulr_fun_is_scalable.

End LinearLalg.

End LinearTheory.

Module LRMorphism.

Section ClassDef.

Variables (R : ringType) (A : lalgType R) (B : ringType) (s : R -> B -> B).

Record class_of (f : A -> B) : Type :=
  Class {base : rmorphism f; mixin : scalable_for s f}.
Local Coercion base : class_of >-> rmorphism.
Definition base2 f (fLM : class_of f) := Linear.Class fLM (mixin fLM).
Local Coercion base2 : class_of >-> lmorphism.

Structure map (phAB : phant (A -> B)) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phAB : phant (A -> B)) (f : A -> B) (cF : map phAB).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

Definition clone :=
  fun (g : RMorphism.map phAB) fM & phant_id (RMorphism.class g) fM =>
  fun (h : Linear.map s phAB) fZ &
     phant_id (Linear.mixin (Linear.class h)) fZ =>
  Pack phAB (@Class f fM fZ).

Definition pack (fZ : scalable_for s f) :=
  fun (g : RMorphism.map phAB) fM & phant_id (RMorphism.class g) fM =>
  Pack phAB (Class fM fZ).

Canonical additive := Additive.Pack phAB class.
Canonical rmorphism := RMorphism.Pack phAB class.
Canonical linear := Linear.Pack phAB class.
Canonical join_rmorphism := @RMorphism.Pack _ _ phAB linear class.
Canonical join_linear := @Linear.Pack R A B s phAB rmorphism class.

End ClassDef.

Module Exports.
Notation lrmorphism_for s f := (class_of s f).
Notation lrmorphism f := (lrmorphism_for *:%R f).
Coercion base : lrmorphism_for >-> RMorphism.class_of.
Coercion base2 : lrmorphism_for >-> lmorphism_for.
Coercion apply : map >-> Funclass.
Notation LRMorphism f_lrM := (Pack (Phant _) (Class f_lrM f_lrM)).
Notation AddLRMorphism fZ := (pack fZ id).
Notation "{ 'lrmorphism' fAB | s }" := (map s (Phant fAB))
  (at level 0, format "{ 'lrmorphism'  fAB  |  s }") : ring_scope.
Notation "{ 'lrmorphism' fAB }" := {lrmorphism fAB | *:%R}
  (at level 0, format "{ 'lrmorphism'  fAB }") : ring_scope.
Notation "[ 'lrmorphism' 'of' f ]" := (@clone _ _ _ _ _ f _ _ id _ _ id)
  (at level 0, format "[ 'lrmorphism'  'of'  f ]") : form_scope.
Coercion additive : map >-> Additive.map.
Canonical additive.
Coercion rmorphism : map >-> RMorphism.map.
Canonical rmorphism.
Coercion linear : map >-> Linear.map.
Canonical linear.
Canonical join_rmorphism.
Canonical join_linear.
End Exports.

End LRMorphism.
Include LRMorphism.Exports.

Section LRMorphismTheory.

Variables (R : ringType) (A B : lalgType R) (C : ringType) (s : R -> C -> C).
Variables (k : unit) (f : {lrmorphism A -> B}) (g : {lrmorphism B -> C | s}).

Definition idfun_lrmorphism := [lrmorphism of @idfun A].
Definition comp_lrmorphism := [lrmorphism of g \o f].
Definition locked_lrmorphism := [lrmorphism of locked_with k (f : A -> B)].

Lemma rmorph_alg a : f a%:A = a%:A.
Proof. by rewrite linearZ rmorph1. Qed.

Lemma lrmorphismP : lrmorphism f. Proof. exact: LRMorphism.class. Qed.

Lemma can2_lrmorphism f' : cancel f f' -> cancel f' f -> lrmorphism f'.
Proof.
move=> fK f'K; split; [exact: (can2_rmorphism fK) | exact: (can2_linear fK)].
Qed.

Lemma bij_lrmorphism :
  bijective f -> exists2 f' : {lrmorphism B -> A}, cancel f f' & cancel f' f.
Proof.
by case/bij_rmorphism=> f' fK f'K; exists (AddLRMorphism (can2_linear fK f'K)).
Qed.

End LRMorphismTheory.

Module ComRing.

Definition RingMixin R one mul mulA mulC mul1x mul_addl :=
  let mulx1 := Monoid.mulC_id mulC mul1x in
  let mul_addr := Monoid.mulC_dist mulC mul_addl in
  @Ring.EtaMixin R one mul mulA mul1x mulx1 mul_addl mul_addr.

Section ClassDef.

Record class_of R :=
  Class {base : Ring.class_of R; mixin : commutative (Ring.mul base)}.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack mul0 (m0 : @commutative T T mul0) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Ring.class_of.
Implicit Arguments mixin [R].
Coercion mixin : class_of >-> commutative.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Notation comRingType := type.
Notation ComRingType T m := (@pack T _ m _ _ id _ id).
Notation ComRingMixin := RingMixin.
Notation "[ 'comRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'comRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'comRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'comRingType'  'of'  T ]") : form_scope.
End Exports.

End ComRing.
Import ComRing.Exports.

Section ComRingTheory.

Variable R : comRingType.
Implicit Types x y : R.

Lemma mulrC : @commutative R R *%R. Proof. by case: R => T []. Qed.
Canonical mul_comoid := Monoid.ComLaw mulrC.
Lemma mulrCA : @left_commutative R R *%R. Proof. exact: mulmCA. Qed.
Lemma mulrAC : @right_commutative R R *%R. Proof. exact: mulmAC. Qed.
Lemma mulrACA : @interchange R *%R *%R. Proof. exact: mulmACA. Qed.

Lemma exprMn n : {morph (fun x => x ^+ n) : x y / x * y}.
Proof. move=> x y; apply: exprMn_comm; exact: mulrC. Qed.

Lemma prodrXl n I r (P : pred I) (F : I -> R) :
  \prod_(i <- r | P i) F i ^+ n = (\prod_(i <- r | P i) F i) ^+ n.
Proof. by rewrite (big_morph _ (exprMn n) (expr1n _ n)). Qed.

Lemma exprDn x y n :
  (x + y) ^+ n = \sum_(i < n.+1) (x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof. by rewrite exprDn_comm //; exact: mulrC. Qed.

Lemma exprBn x y n :
  (x - y) ^+ n =
     \sum_(i < n.+1) ((-1) ^+ i * x ^+ (n - i) * y ^+ i) *+ 'C(n, i).
Proof. by rewrite exprBn_comm //; exact: mulrC. Qed.

Lemma subrXX x y n :
  x ^+ n - y ^+ n = (x - y) * (\sum_(i < n) x ^+ (n.-1 - i) * y ^+ i).
Proof. by rewrite -subrXX_comm //; exact: mulrC. Qed.

Lemma sqrrD x y : (x + y) ^+ 2 = x ^+ 2 + x * y *+ 2 + y ^+ 2.
Proof. by rewrite exprDn !big_ord_recr big_ord0 /= add0r mulr1 mul1r. Qed.

Lemma sqrrB x y : (x - y) ^+ 2 = x ^+ 2 - x * y *+ 2 + y ^+ 2.
Proof. by rewrite sqrrD mulrN mulNrn sqrrN. Qed.

Lemma subr_sqr x y : x ^+ 2 - y ^+ 2 = (x - y) * (x + y).
Proof. by rewrite subrXX !big_ord_recr big_ord0 /= add0r mulr1 mul1r. Qed.

Lemma subr_sqrDB x y : (x + y) ^+ 2 - (x - y) ^+ 2 = x * y *+ 4.
Proof.
rewrite sqrrD sqrrB -!(addrAC _ (y ^+ 2)) opprB.
by rewrite addrC addrA subrK -mulrnDr.
Qed.

Section FrobeniusAutomorphism.

Variables (p : nat) (charRp : p \in [char R]).

Lemma Frobenius_aut_is_rmorphism : rmorphism (Frobenius_aut charRp).
Proof.
split=> [x y|]; first exact: Frobenius_autB_comm (mulrC _ _).
split=> [x y|]; first exact: Frobenius_autM_comm (mulrC _ _).
exact: Frobenius_aut1.
Qed.

Canonical Frobenius_aut_additive := Additive Frobenius_aut_is_rmorphism.
Canonical Frobenius_aut_rmorphism := RMorphism Frobenius_aut_is_rmorphism.

End FrobeniusAutomorphism.

Lemma exprDn_char x y n : [char R].-nat n -> (x + y) ^+ n = x ^+ n + y ^+ n.
Proof.
pose p := pdiv n; have [|n_gt1 charRn] := leqP n 1; first by case: (n) => [|[]].
have charRp: p \in [char R] by rewrite (pnatPpi charRn) ?pi_pdiv.
have{charRn} /p_natP[e ->]: p.-nat n by rewrite -(eq_pnat _ (charf_eq charRp)).
by elim: e => // e IHe; rewrite !expnSr !exprM IHe -(Frobenius_autE charRp) rmorphD.
Qed.

Lemma rmorph_comm (S : ringType) (f : {rmorphism R -> S}) x y : 
  comm (f x) (f y).
Proof. by red; rewrite -!rmorphM mulrC. Qed.

Section ScaleLinear.

Variables (U V : lmodType R) (b : R) (f : {linear U -> V}).

Lemma scale_is_scalable : scalable ( *:%R b : V -> V).
Proof. by move=> a v /=; rewrite !scalerA mulrC. Qed.
Canonical scale_linear := AddLinear scale_is_scalable.

Lemma scale_fun_is_scalable : scalable (b \*: f).
Proof. by move=> a v /=; rewrite !linearZ. Qed.
Canonical scale_fun_linear := AddLinear scale_fun_is_scalable.

End ScaleLinear.

End ComRingTheory.

Module Algebra.

Section Mixin.

Variables (R : ringType) (A : lalgType R).

Definition axiom := forall k (x y : A), k *: (x * y) = x * (k *: y).

Lemma comm_axiom : phant A -> commutative (@mul A) -> axiom.
Proof. by move=> _ commA k x y; rewrite commA scalerAl commA. Qed.

End Mixin.

Section ClassDef.

Variable R : ringType.

Record class_of (T : Type) : Type := Class {
  base : Lalgebra.class_of R T; 
  mixin : axiom (Lalgebra.Pack _ base T)
}.
Local Coercion base : class_of >-> Lalgebra.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (ax0 : @axiom R b0) :=
  fun bT b & phant_id (@Lalgebra.class R phR bT) b =>
  fun   ax & phant_id ax0 ax => Pack phR (@Class T b ax) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition lmodType := @Lmodule.Pack R phR cT xclass xT.
Definition lalgType := @Lalgebra.Pack R phR cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lalgebra.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Notation algType R := (type (Phant R)).
Notation AlgType R A ax := (@pack _ (Phant R) A _ ax _ _ id _ id).
Notation CommAlgType R A := (AlgType R A (comm_axiom (Phant A) (@mulrC _))).
Notation "[ 'algType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'algType'  R  'of'  T  'for'  cT ]")
  : form_scope.
Notation "[ 'algType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'algType'  R  'of'  T ]") : form_scope.
End Exports.

End Algebra.
Import Algebra.Exports.

Section AlgebraTheory.

Variables (R : comRingType) (A : algType R).
Implicit Types (k : R) (x y : A).

Lemma scalerAr k x y : k *: (x * y) = x * (k *: y).
Proof. by case: A k x y => T []. Qed.

Lemma scalerCA k x y : k *: x * y = x * (k *: y).
Proof. by rewrite -scalerAl scalerAr. Qed.

Lemma mulr_algr a x : x * a%:A = a *: x.
Proof. by rewrite -scalerAr mulr1. Qed.

Lemma exprZn k x n : (k *: x) ^+ n = k ^+ n *: x ^+ n.
Proof. 
elim: n => [|n IHn]; first by rewrite !expr0 scale1r.
by rewrite !exprS IHn -scalerA scalerAr scalerAl.
Qed.

Lemma scaler_prod I r (P : pred I) (F : I -> R) (G : I -> A) :
  \prod_(i <- r | P i) (F i *: G i) =
    \prod_(i <- r | P i) F i *: \prod_(i <- r | P i) G i.
Proof.
elim/big_rec3: _ => [|i x a _ _ ->]; first by rewrite scale1r.
by rewrite -scalerAl -scalerAr scalerA.
Qed.

Lemma scaler_prodl (I : finType) (S : pred I) (F : I -> A) k :
  \prod_(i in S) (k *: F i)  = k ^+ #|S| *: \prod_(i in S) F i.
Proof. by rewrite scaler_prod prodr_const. Qed.

Lemma scaler_prodr (I : finType) (S : pred I) (F : I -> R) x :
  \prod_(i in S) (F i *: x)  = \prod_(i in S) F i *: x ^+ #|S|.
Proof. by rewrite scaler_prod prodr_const. Qed.

Canonical regular_comRingType := [comRingType of R^o].
Canonical regular_algType := CommAlgType R R^o.

Variables (U : lmodType R) (a : A) (f : {linear U -> A}).

Lemma mull_fun_is_scalable : scalable (a \*o f).
Proof. by move=> k x /=; rewrite linearZ scalerAr. Qed.
Canonical mull_fun_linear := AddLinear mull_fun_is_scalable.

End AlgebraTheory.

Module UnitRing.

Record mixin_of (R : ringType) : Type := Mixin {
  unit : pred R;
  inv : R -> R;
  _ : {in unit, left_inverse 1 inv *%R};
  _ : {in unit, right_inverse 1 inv *%R};
  _ : forall x y, y * x = 1 /\ x * y = 1 -> unit x;
  _ : {in [predC unit], inv =1 id}
}.

Definition EtaMixin R unit inv mulVr mulrV unitP inv_out :=
  let _ := @Mixin R unit inv mulVr mulrV unitP inv_out in
  @Mixin (Ring.Pack (Ring.class R) R) unit inv mulVr mulrV unitP inv_out.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : Ring.class_of R;
  mixin : mixin_of (Ring.Pack base R)
}.
Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Ring.Pack T b0 T)) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Notation unitRingType := type.
Notation UnitRingType T m := (@pack T _ m _ _ id _ id).
Notation UnitRingMixin := EtaMixin.
Notation "[ 'unitRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'unitRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'unitRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'unitRingType'  'of'  T ]") : form_scope.
End Exports.

End UnitRing.
Import UnitRing.Exports.

Definition unit {R : unitRingType} :=
  [qualify a u : R | UnitRing.unit (UnitRing.class R) u].
Fact unit_key R : pred_key (@unit R). Proof. by []. Qed.
Canonical unit_keyed R := KeyedQualifier (@unit_key R).
Definition inv {R : unitRingType} : R -> R := UnitRing.inv (UnitRing.class R).

Local Notation "x ^-1" := (inv x).
Local Notation "x / y" := (x * y^-1).
Local Notation "x ^- n" := ((x ^+ n)^-1).

Section UnitRingTheory.

Variable R : unitRingType.
Implicit Types x y : R.

Lemma divrr : {in unit, right_inverse 1 (@inv R) *%R}.
Proof. by case: R => T [? []]. Qed.
Definition mulrV := divrr.

Lemma mulVr : {in unit, left_inverse 1 (@inv R) *%R}.
Proof. by case: R => T [? []]. Qed.

Lemma invr_out x : x \isn't a unit -> x^-1 = x.
Proof. by case: R x => T [? []]. Qed.

Lemma unitrP x : reflect (exists y, y * x = 1 /\ x * y = 1) (x \is a unit).
Proof.
apply: (iffP idP) => [Ux | []]; last by case: R x => T [? []].
by exists x^-1; rewrite divrr ?mulVr.
Qed.

Lemma mulKr : {in unit, left_loop (@inv R) *%R}.
Proof. by move=> x Ux y; rewrite mulrA mulVr ?mul1r. Qed.

Lemma mulVKr : {in unit, rev_left_loop (@inv R) *%R}.
Proof. by move=> x Ux y; rewrite mulrA mulrV ?mul1r. Qed.

Lemma mulrK : {in unit, right_loop (@inv R) *%R}.
Proof. by move=> x Ux y; rewrite -mulrA divrr ?mulr1. Qed.

Lemma mulrVK : {in unit, rev_right_loop (@inv R) *%R}.
Proof. by move=> x Ux y; rewrite -mulrA mulVr ?mulr1. Qed.
Definition divrK := mulrVK.

Lemma mulrI : {in @unit R, right_injective *%R}.
Proof. by move=> x Ux; exact: can_inj (mulKr Ux). Qed.

Lemma mulIr : {in @unit R, left_injective *%R}.
Proof. by move=> x Ux; exact: can_inj (mulrK Ux). Qed.

Lemma commrV x y : comm x y -> comm x y^-1.
Proof.
have [Uy cxy | /invr_out-> //] := boolP (y \in unit).
by apply: (canLR (mulrK Uy)); rewrite -mulrA cxy mulKr.
Qed.

Lemma unitrE x : (x \is a unit) = (x / x == 1).
Proof.
apply/idP/eqP=> [Ux | xx1]; first exact: divrr.
by apply/unitrP; exists x^-1; rewrite -commrV.
Qed.

Lemma invrK : involutive (@inv R).
Proof.
move=> x; case Ux: (x \in unit); last by rewrite !invr_out ?Ux.
rewrite -(mulrK Ux _^-1) -mulrA commrV ?mulKr //.
by apply/unitrP; exists x; rewrite divrr ?mulVr.
Qed.

Lemma invr_inj : injective (@inv R).
Proof. exact: inv_inj invrK. Qed.

Lemma unitrV x : (x^-1 \in unit) = (x \in unit).
Proof. by rewrite !unitrE invrK commrV. Qed.

Lemma unitr1 : 1 \in @unit R.
Proof. by apply/unitrP; exists 1; rewrite mulr1. Qed.

Lemma invr1 : 1^-1 = 1 :> R.
Proof. by rewrite -{2}(mulVr unitr1) mulr1. Qed.

Lemma div1r x : 1 / x = x^-1. Proof. by rewrite mul1r. Qed.
Lemma divr1 x : x / 1 = x. Proof. by rewrite invr1 mulr1. Qed.

Lemma natr_div m d :
  d %| m -> d%:R \is a @unit R -> (m %/ d)%:R = m%:R / d%:R :> R.
Proof.
by rewrite dvdn_eq => /eqP def_m unit_d; rewrite -{2}def_m natrM mulrK.
Qed.

Lemma unitr0 : (0 \is a @unit R) = false.
Proof.
by apply/unitrP=> [[x [_]]]; apply/eqP; rewrite mul0r eq_sym oner_neq0.
Qed.

Lemma invr0 : 0^-1 = 0 :> R.
Proof. by rewrite invr_out ?unitr0. Qed.

Lemma unitrN1 : -1 \is a @unit R.
Proof. by apply/unitrP; exists (-1); rewrite mulrNN mulr1. Qed.

Lemma invrN1 : (-1)^-1 = -1 :> R.
Proof. by rewrite -{2}(divrr unitrN1) mulN1r opprK. Qed.

Lemma invr_sign n : ((-1) ^- n) = (-1) ^+ n :> R.
Proof. by rewrite -signr_odd; case: (odd n); rewrite (invr1, invrN1). Qed.

Lemma unitrMl x y : y \is a unit -> (x * y \is a unit) = (x \is a unit).
Proof.
move=> Uy; wlog Ux: x y Uy / x \is a unit => [WHxy|].
  by apply/idP/idP=> Ux; first rewrite -(mulrK Uy x); rewrite WHxy ?unitrV.
rewrite Ux; apply/unitrP; exists (y^-1 * x^-1).
by rewrite -!mulrA mulKr ?mulrA ?mulrK ?divrr ?mulVr.
Qed.

Lemma unitrMr x y : x \is a unit -> (x * y \is a unit) = (y \is a unit).
Proof.
move=> Ux; apply/idP/idP=> [Uxy | Uy]; last by rewrite unitrMl.
by rewrite -(mulKr Ux y) unitrMl ?unitrV.
Qed.

Lemma invrM : {in unit &, forall x y, (x * y)^-1 = y^-1 * x^-1}.
Proof.
move=> x y Ux Uy; have Uxy: (x * y \in unit) by rewrite unitrMl.
by apply: (mulrI Uxy); rewrite divrr ?mulrA ?mulrK ?divrr.
Qed.

Lemma unitrM_comm x y :
  comm x y -> (x * y \is a unit) = (x \is a unit) && (y \is a unit).
Proof.
move=> cxy; apply/idP/andP=> [Uxy | [Ux Uy]]; last by rewrite unitrMl.
suffices Ux: x \in unit by rewrite unitrMr in Uxy.
apply/unitrP; case/unitrP: Uxy => z [zxy xyz]; exists (y * z).
rewrite mulrA xyz -{1}[y]mul1r -{1}zxy cxy -!mulrA (mulrA x) (mulrA _ z) xyz.
by rewrite mul1r -cxy.
Qed.

Lemma unitrX x n : x \is a unit -> x ^+ n \is a unit.
Proof.
by move=> Ux; elim: n => [|n IHn]; rewrite ?unitr1 // exprS unitrMl.
Qed.

Lemma unitrX_pos x n : n > 0 -> (x ^+ n \in unit) = (x \in unit).
Proof.
case: n => // n _; rewrite exprS unitrM_comm; last exact: commrX.
by case Ux: (x \is a unit); rewrite // unitrX.
Qed.

Lemma exprVn x n : x^-1 ^+ n = x ^- n.
Proof.
elim: n => [|n IHn]; first by rewrite !expr0 ?invr1.
case Ux: (x \is a unit); first by rewrite exprSr exprS IHn -invrM // unitrX.
by rewrite !invr_out ?unitrX_pos ?Ux.
Qed.

Lemma exprB m n x : n <= m -> x \is a unit -> x ^+ (m - n) = x ^+ m / x ^+ n.
Proof. by move/subnK=> {2}<- Ux; rewrite exprD mulrK ?unitrX. Qed.

Lemma invr_neq0 x : x != 0 -> x^-1 != 0.
Proof.
move=> nx0; case Ux: (x \is a unit); last by rewrite invr_out ?Ux.
by apply/eqP=> x'0; rewrite -unitrV x'0 unitr0 in Ux.
Qed.

Lemma invr_eq0 x : (x^-1 == 0) = (x == 0).
Proof. by apply: negb_inj; apply/idP/idP; move/invr_neq0; rewrite ?invrK. Qed.

Lemma invr_eq1 x : (x^-1 == 1) = (x == 1).
Proof. by rewrite (inv_eq invrK) invr1. Qed.

Lemma rev_unitrP (x y : R^c) : y * x = 1 /\ x * y = 1 -> x \is a unit.
Proof. by case=> [yx1 xy1]; apply/unitrP; exists y. Qed.

Definition converse_unitRingMixin :=
  @UnitRing.Mixin _ ((unit : pred_class) : pred R^c) _
     mulrV mulVr rev_unitrP invr_out.
Canonical converse_unitRingType := UnitRingType R^c converse_unitRingMixin.
Canonical regular_unitRingType := [unitRingType of R^o].

Section ClosedPredicates.

Variables S : predPredType R.

Definition invr_closed := {in S, forall x, x^-1 \in S}.
Definition divr_2closed := {in S &, forall x y, x / y \in S}.
Definition divr_closed := 1 \in S /\ divr_2closed.
Definition sdivr_closed := -1 \in S /\ divr_2closed.
Definition divring_closed := [/\ 1 \in S, subr_2closed S & divr_2closed].

Lemma divr_closedV : divr_closed -> invr_closed.
Proof. by case=> S1 Sdiv x Sx; rewrite -[x^-1]mul1r Sdiv. Qed.

Lemma divr_closedM : divr_closed -> mulr_closed S.
Proof.
by case=> S1 Sdiv; split=> // x y Sx Sy; rewrite -[y]invrK -[y^-1]mul1r !Sdiv.
Qed.

Lemma sdivr_closed_div : sdivr_closed -> divr_closed.
Proof. by case=> SN1 Sdiv; split; rewrite // -(divrr unitrN1) Sdiv. Qed.

Lemma sdivr_closedM : sdivr_closed -> smulr_closed S.
Proof.
by move=> Sdiv; have [_ SM] := divr_closedM (sdivr_closed_div Sdiv); case: Sdiv.
Qed.

Lemma divring_closedBM : divring_closed -> subring_closed S.
Proof. by case=> S1 SB Sdiv; split=> //; case: divr_closedM. Qed.

Lemma divring_closed_div : divring_closed -> sdivr_closed.
Proof.
case=> S1 SB Sdiv; split; rewrite ?zmod_closedN //.
exact/subring_closedB/divring_closedBM.
Qed.

End ClosedPredicates.

End UnitRingTheory.

Implicit Arguments invr_inj [[R] x1 x2].

Section UnitRingMorphism.

Variables (R S : unitRingType) (f : {rmorphism R -> S}).

Lemma rmorph_unit x : x \in unit -> f x \in unit.
Proof.
case/unitrP=> y [yx1 xy1]; apply/unitrP.
by exists (f y); rewrite -!rmorphM // yx1 xy1 rmorph1.
Qed.

Lemma rmorphV : {in unit, {morph f: x / x^-1}}.
Proof.
move=> x Ux; rewrite /= -[(f x)^-1]mul1r.
by apply: (canRL (mulrK (rmorph_unit Ux))); rewrite -rmorphM mulVr ?rmorph1.
Qed.

Lemma rmorph_div x y : y \in unit -> f (x / y) = f x / f y.
Proof. by move=> Uy; rewrite rmorphM rmorphV. Qed.

End UnitRingMorphism.

Module ComUnitRing.

Section Mixin.

Variables (R : comRingType) (unit : pred R) (inv : R -> R).
Hypothesis mulVx : {in unit, left_inverse 1 inv *%R}.
Hypothesis unitPl : forall x y, y * x = 1 -> unit x.

Fact mulC_mulrV : {in unit, right_inverse 1 inv *%R}.
Proof. by move=> x Ux /=; rewrite mulrC mulVx. Qed.

Fact mulC_unitP x y : y * x = 1 /\ x * y = 1 -> unit x.
Proof. case=> yx _; exact: unitPl yx. Qed.

Definition Mixin := UnitRingMixin mulVx mulC_mulrV mulC_unitP.

End Mixin.

Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : ComRing.class_of R;
  mixin : UnitRing.mixin_of (Ring.Pack base R)
}.
Local Coercion base : class_of >-> ComRing.class_of.
Definition base2 R m := UnitRing.Class (@mixin R m).
Local Coercion base2 : class_of >-> UnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (ComRing.class bT) (b : ComRing.class_of T) =>
  fun mT m & phant_id (UnitRing.class mT) (@UnitRing.Class T b m) =>
  Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition comRingType := @ComRing.Pack cT xclass xT.
Definition unitRingType := @UnitRing.Pack cT xclass xT.
Definition com_unitRingType := @UnitRing.Pack comRingType xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> ComRing.class_of.
Coercion mixin : class_of >-> UnitRing.mixin_of.
Coercion base2 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Canonical com_unitRingType.
Notation comUnitRingType := type.
Notation ComUnitRingMixin := Mixin.
Notation "[ 'comUnitRingType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'comUnitRingType'  'of'  T ]") : form_scope.
End Exports.

End ComUnitRing.
Import ComUnitRing.Exports.

Module UnitAlgebra.

Section ClassDef.

Variable R : ringType.

Record class_of (T : Type) : Type := Class {
  base : Algebra.class_of R T; 
  mixin : GRing.UnitRing.mixin_of (Ring.Pack base T)
}.
Definition base2 R m := UnitRing.Class (@mixin R m).
Local Coercion base : class_of >-> Algebra.class_of.
Local Coercion base2 : class_of >-> UnitRing.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (@Algebra.class R phR bT) (b : Algebra.class_of R T) =>
  fun mT m & phant_id (UnitRing.mixin (UnitRing.class mT)) m =>
  Pack (Phant R) (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition unitRingType := @UnitRing.Pack cT xclass xT.
Definition lmodType := @Lmodule.Pack R phR cT xclass xT.
Definition lalgType := @Lalgebra.Pack R phR cT xclass xT.
Definition algType := @Algebra.Pack R phR cT xclass xT.
Definition lmod_unitRingType := @Lmodule.Pack R phR unitRingType xclass xT.
Definition lalg_unitRingType := @Lalgebra.Pack R phR unitRingType xclass xT.
Definition alg_unitRingType := @Algebra.Pack R phR unitRingType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Algebra.class_of.
Coercion base2 : class_of >-> UnitRing.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> Algebra.type.
Canonical algType.
Canonical lmod_unitRingType.
Canonical lalg_unitRingType.
Canonical alg_unitRingType.
Notation unitAlgType R := (type (Phant R)).
Notation "[ 'unitAlgType' R 'of' T ]" := (@pack _ (Phant R) T _ _ id _ _ id)
  (at level 0, format "[ 'unitAlgType'  R  'of'  T ]") : form_scope.
End Exports.

End UnitAlgebra.
Import UnitAlgebra.Exports.

Section ComUnitRingTheory.

Variable R : comUnitRingType.
Implicit Types x y : R.

Lemma unitrM x y : (x * y \in unit) = (x \in unit) && (y \in unit).
Proof. by apply: unitrM_comm; exact: mulrC. Qed.

Lemma unitrPr x : reflect (exists y, x * y = 1) (x \in unit).
Proof.
by apply: (iffP (unitrP x)) => [[y []] | [y]]; exists y; rewrite // mulrC.
Qed.

Lemma expr_div_n x y n : (x / y) ^+ n = x ^+ n / y ^+ n.
Proof. by rewrite exprMn exprVn. Qed.

Canonical regular_comUnitRingType := [comUnitRingType of R^o].
Canonical regular_unitAlgType := [unitAlgType R of R^o].

End ComUnitRingTheory.

Section UnitAlgebraTheory.

Variable (R : comUnitRingType) (A : unitAlgType R).
Implicit Types (k : R) (x y : A).

Lemma scaler_injl : {in unit, @right_injective R A A *:%R}.
Proof.
move=> k Uk x1 x2 Hx1x2.
by rewrite -[x1]scale1r -(mulVr Uk) -scalerA Hx1x2 scalerA mulVr // scale1r.
Qed.

Lemma scaler_unit k x : k \in unit -> (k *: x \in unit) = (x \in unit).
Proof.
move=> Uk; apply/idP/idP=> [Ukx | Ux]; apply/unitrP; last first.
  exists (k^-1 *: x^-1).
  by rewrite -!scalerAl -!scalerAr !scalerA !mulVr // !mulrV // scale1r.
exists (k *: (k *: x)^-1); split.
  apply: (mulrI Ukx).
  by rewrite mulr1 mulrA -scalerAr mulrV // -scalerAl mul1r.
apply: (mulIr Ukx).
by rewrite mul1r -mulrA -scalerAl mulVr // -scalerAr mulr1.
Qed.
 
Lemma invrZ k x : k \in unit -> x \in unit -> (k *: x)^-1 = k^-1 *: x^-1.
Proof.
move=> Uk Ux; have Ukx: (k *: x \in unit) by rewrite scaler_unit.
apply: (mulIr Ukx).
by rewrite mulVr // -scalerAl -scalerAr scalerA !mulVr // scale1r.
Qed.

Section ClosedPredicates.

Variables S : predPredType A.

Definition divalg_closed := [/\ 1 \in S, linear_closed S & divr_2closed S].

Lemma divalg_closedBdiv : divalg_closed -> divring_closed S.
Proof. by case=> S1 /linear_closedB. Qed.

Lemma divalg_closedZ : divalg_closed -> subalg_closed S.
Proof. by case=> S1 Slin Sdiv; split=> //; have [] := @divr_closedM A S. Qed.

End ClosedPredicates.

End UnitAlgebraTheory.

(* Interface structures for algebraically closed predicates. *)
Module Pred.

Structure opp V S := Opp {opp_key : pred_key S; _ : @oppr_closed V S}.
Structure add V S := Add {add_key : pred_key S; _ : @addr_closed V S}.
Structure mul R S := Mul {mul_key : pred_key S; _ : @mulr_closed R S}.
Structure zmod V S := Zmod {zmod_add : add S; _ : @oppr_closed V S}.
Structure semiring R S := Semiring {semiring_add : add S; _ : @mulr_closed R S}.
Structure smul R S := Smul {smul_opp : opp S; _ : @mulr_closed R S}.
Structure div R S := Div {div_mul : mul S; _ : @invr_closed R S}.
Structure submod R V S :=
  Submod {submod_zmod : zmod S; _ : @scaler_closed R V S}.
Structure subring R S := Subring {subring_zmod : zmod S; _ : @mulr_closed R S}.
Structure sdiv R S := Sdiv {sdiv_smul : smul S; _ : @invr_closed R S}.
Structure subalg (R : ringType) (A : lalgType R) S :=
  Subalg {subalg_ring : subring S; _ : @scaler_closed R A S}.
Structure divring R S :=
  Divring {divring_ring : subring S; _ : @invr_closed R S}.
Structure divalg (R : ringType) (A : unitAlgType R) S :=
  Divalg {divalg_ring : divring S; _ : @scaler_closed R A S}.

Section Subtyping.

Ltac done := case=> *; assumption.
Fact zmod_oppr R S : @zmod R S -> oppr_closed S. Proof. by []. Qed.
Fact semiring_mulr R S : @semiring R S -> mulr_closed S. Proof. by []. Qed.
Fact smul_mulr R S : @smul R S -> mulr_closed S. Proof. by []. Qed.
Fact submod_scaler R V S : @submod R V S -> scaler_closed S. Proof. by []. Qed.
Fact subring_mulr R S : @subring R S -> mulr_closed S. Proof. by []. Qed.
Fact sdiv_invr R S : @sdiv R S -> invr_closed S. Proof. by []. Qed.
Fact subalg_scaler R A S : @subalg R A S -> scaler_closed S. Proof. by []. Qed.
Fact divring_invr R S : @divring R S -> invr_closed S. Proof. by []. Qed.
Fact divalg_scaler R A S : @divalg R A S -> scaler_closed S. Proof. by []. Qed.

Definition zmod_opp R S (addS : @zmod R S) :=
  Opp (add_key (zmod_add addS)) (zmod_oppr addS).
Definition semiring_mul R S (ringS : @semiring R S) :=
  Mul (add_key (semiring_add ringS)) (semiring_mulr ringS).
Definition smul_mul R S (mulS : @smul R S) :=
  Mul (opp_key (smul_opp mulS)) (smul_mulr mulS).
Definition subring_semi R S (ringS : @subring R S) :=
  Semiring (zmod_add (subring_zmod ringS)) (subring_mulr ringS).
Definition subring_smul R S (ringS : @subring R S) :=
  Smul (zmod_opp (subring_zmod ringS)) (subring_mulr ringS).
Definition sdiv_div R S (divS : @sdiv R S) :=
  Div (smul_mul (sdiv_smul divS)) (sdiv_invr divS).
Definition subalg_submod R A S (algS : @subalg R A S) :=
  Submod (subring_zmod (subalg_ring algS)) (subalg_scaler algS).
Definition divring_sdiv R S (ringS : @divring R S) :=
  Sdiv (subring_smul (divring_ring ringS)) (divring_invr ringS).
Definition divalg_alg R A S (algS : @divalg R A S) :=
  Subalg (divring_ring (divalg_ring algS)) (divalg_scaler algS).

End Subtyping.

Section Extensionality.
(* This could be avoided by exploiting the Coq 8.4 eta-convertibility.        *)

Lemma opp_ext (U : zmodType) S k (kS : @keyed_pred U S k) :
  oppr_closed kS -> oppr_closed S.
Proof. by move=> oppS x; rewrite -!(keyed_predE kS); apply: oppS. Qed.

Lemma add_ext (U : zmodType) S k (kS : @keyed_pred U S k) :
  addr_closed kS -> addr_closed S.
Proof.
by case=> S0 addS; split=> [|x y]; rewrite -!(keyed_predE kS) //; apply: addS.
Qed.

Lemma mul_ext (R : ringType) S k (kS : @keyed_pred R S k) :
  mulr_closed kS -> mulr_closed S.
Proof.
by case=> S1 mulS; split=> [|x y]; rewrite -!(keyed_predE kS) //; apply: mulS.
Qed.

Lemma scale_ext (R : ringType) (U : lmodType R) S k (kS : @keyed_pred U S k) :
  scaler_closed kS -> scaler_closed S.
Proof. by move=> linS a x; rewrite -!(keyed_predE kS); apply: linS. Qed.

Lemma inv_ext (R : unitRingType) S k (kS : @keyed_pred R S k) :
  invr_closed kS -> invr_closed S.
Proof. by move=> invS x; rewrite -!(keyed_predE kS); apply: invS. Qed.

End Extensionality.

Module Default.
Definition opp V S oppS := @Opp V S (DefaultPredKey S) oppS.
Definition add V S addS := @Add V S (DefaultPredKey S) addS.
Definition mul R S mulS := @Mul R S (DefaultPredKey S) mulS.
Definition zmod V S addS oppS := @Zmod V S (add addS) oppS.
Definition semiring R S addS mulS := @Semiring R S (add addS) mulS.
Definition smul R S oppS mulS := @Smul R S (opp oppS) mulS.
Definition div R S mulS invS := @Div R S (mul mulS) invS.
Definition submod R V S addS oppS linS := @Submod R V S (zmod addS oppS) linS.
Definition subring R S addS oppS mulS := @Subring R S (zmod addS oppS) mulS.
Definition sdiv R S oppS mulS invS := @Sdiv R S (smul oppS mulS) invS.
Definition subalg R A S addS oppS mulS linS :=
  @Subalg R A S (subring addS oppS mulS) linS.
Definition divring R S addS oppS mulS invS :=
  @Divring R S (subring addS oppS mulS) invS.
Definition divalg R A S addS oppS mulS invS linS :=
  @Divalg R A S (divring addS oppS mulS invS) linS.
End Default.

Module Exports.

Notation oppr_closed := oppr_closed.
Notation addr_closed := addr_closed.
Notation mulr_closed := mulr_closed.
Notation zmod_closed := zmod_closed.
Notation smulr_closed := smulr_closed.
Notation invr_closed := invr_closed.
Notation divr_closed := divr_closed.
Notation linear_closed := linear_closed.
Notation submod_closed := submod_closed.
Notation semiring_closed := semiring_closed.
Notation subring_closed := subring_closed.
Notation sdivr_closed := sdivr_closed.
Notation subalg_closed := subalg_closed.
Notation divring_closed := divring_closed.
Notation divalg_closed := divalg_closed.
 
Coercion zmod_closedD : zmod_closed >-> addr_closed.
Coercion zmod_closedN : zmod_closed >-> oppr_closed.
Coercion smulr_closedN : smulr_closed >-> oppr_closed.
Coercion smulr_closedM : smulr_closed >-> mulr_closed.
Coercion divr_closedV : divr_closed >-> invr_closed.
Coercion divr_closedM : divr_closed >-> mulr_closed.
Coercion submod_closedZ : submod_closed >-> scaler_closed.
Coercion submod_closedB : submod_closed >-> zmod_closed.
Coercion semiring_closedD : semiring_closed >-> addr_closed.
Coercion semiring_closedM : semiring_closed >-> mulr_closed.
Coercion subring_closedB : subring_closed >-> zmod_closed.
Coercion subring_closedM : subring_closed >-> smulr_closed.
Coercion subring_closed_semi : subring_closed >-> semiring_closed.
Coercion sdivr_closedM : sdivr_closed >-> smulr_closed.
Coercion sdivr_closed_div : sdivr_closed >-> divr_closed.
Coercion subalg_closedZ : subalg_closed >-> submod_closed.
Coercion subalg_closedBM : subalg_closed >-> subring_closed.
Coercion divring_closedBM : divring_closed >-> subring_closed.
Coercion divring_closed_div : divring_closed >-> sdivr_closed.
Coercion divalg_closedZ : divalg_closed >-> subalg_closed.
Coercion divalg_closedBdiv : divalg_closed >-> divring_closed.

Coercion opp_key : opp >-> pred_key.
Coercion add_key : add >-> pred_key.
Coercion mul_key : mul >-> pred_key.
Coercion zmod_opp : zmod >-> opp.
Canonical zmod_opp.
Coercion zmod_add : zmod >-> add.
Coercion semiring_add : semiring >-> add.
Coercion semiring_mul : semiring >-> mul.
Canonical semiring_mul.
Coercion smul_opp : smul >-> opp.
Coercion smul_mul : smul >-> mul.
Canonical smul_mul.
Coercion div_mul : div >-> mul.
Coercion submod_zmod : submod >-> zmod.
Coercion subring_zmod : subring >-> zmod.
Coercion subring_semi : subring >-> semiring.
Canonical subring_semi.
Coercion subring_smul : subring >-> smul.
Canonical subring_smul.
Coercion sdiv_smul : sdiv >-> smul.
Coercion sdiv_div : sdiv >-> div.
Canonical sdiv_div.
Coercion subalg_submod : subalg >-> submod.
Canonical subalg_submod.
Coercion subalg_ring : subalg >-> subring.
Coercion divring_ring : divring >-> subring.
Coercion divring_sdiv : divring >-> sdiv.
Canonical divring_sdiv.
Coercion divalg_alg : divalg >-> subalg.
Canonical divalg_alg.
Coercion divalg_ring : divalg >-> divring.

Notation opprPred := opp.
Notation addrPred := add.
Notation mulrPred := mul.
Notation zmodPred := zmod.
Notation semiringPred := semiring.
Notation smulrPred := smul.
Notation divrPred := div.
Notation submodPred := submod.
Notation subringPred := subring.
Notation sdivrPred := sdiv.
Notation subalgPred := subalg.
Notation divringPred := divring.
Notation divalgPred := divalg.

Definition OpprPred U S k kS NkS := Opp k (@opp_ext U S k kS NkS).
Definition AddrPred U S k kS DkS := Add k (@add_ext U S k kS DkS).
Definition MulrPred R S k kS MkS := Mul k (@mul_ext R S k kS MkS).
Definition ZmodPred U S k kS NkS := Zmod k (@opp_ext U S k kS NkS).
Definition SemiringPred R S k kS MkS := Semiring k (@mul_ext R S k kS MkS).
Definition SmulrPred R S k kS MkS := Smul k (@mul_ext R S k kS MkS).
Definition DivrPred R S k kS VkS := Div k (@inv_ext R S k kS VkS).
Definition SubmodPred R U S k kS ZkS := Submod k (@scale_ext R U S k kS ZkS).
Definition SubringPred R S k kS MkS := Subring k (@mul_ext R S k kS MkS).
Definition SdivrPred R S k kS VkS := Sdiv k (@inv_ext R S k kS VkS).
Definition SubalgPred (R : ringType) (A : lalgType R) S k kS ZkS :=
  Subalg k (@scale_ext R A S k kS ZkS).
Definition DivringPred R S k kS VkS := Divring k (@inv_ext R S k kS VkS).
Definition DivalgPred (R : ringType) (A : unitAlgType R) S k kS ZkS :=
  Divalg k (@scale_ext R A S k kS ZkS).

End Exports.

End Pred.
Import Pred.Exports.

Module DefaultPred.

Canonical Pred.Default.opp.
Canonical Pred.Default.add.
Canonical Pred.Default.mul.
Canonical Pred.Default.zmod.
Canonical Pred.Default.semiring.
Canonical Pred.Default.smul.
Canonical Pred.Default.div.
Canonical Pred.Default.submod.
Canonical Pred.Default.subring.
Canonical Pred.Default.sdiv.
Canonical Pred.Default.subalg.
Canonical Pred.Default.divring.
Canonical Pred.Default.divalg.

End DefaultPred.

Section ZmodulePred.

Variables (V : zmodType) (S : predPredType V).

Section Add.

Variables (addS : addrPred S) (kS : keyed_pred addS).

Lemma rpred0D : addr_closed kS.
Proof.
by split=> [|x y]; rewrite !keyed_predE; case: addS => _ [_]//; apply.
Qed.

Lemma rpred0 : 0 \in kS.
Proof. by case: rpred0D. Qed.

Lemma rpredD : {in kS &, forall u v, u + v \in kS}.
Proof. by case: rpred0D. Qed.

Lemma rpred_sum I r (P : pred I) F :
  (forall i, P i -> F i \in kS) -> \sum_(i <- r | P i) F i \in kS.
Proof. by move=> IH; elim/big_ind: _; [exact: rpred0 | exact: rpredD |]. Qed.

Lemma rpredMn n : {in kS, forall u, u *+ n \in kS}.
Proof. by move=> u Su; rewrite -(card_ord n) -sumr_const rpred_sum. Qed.

End Add.

Section Opp.

Variables (oppS : opprPred S) (kS : keyed_pred oppS).

Lemma rpredNr : oppr_closed kS.
Proof. by move=> x; rewrite !keyed_predE; case: oppS => _; apply. Qed.

Lemma rpredN : {mono -%R: u / u \in kS}.
Proof. by move=> u; apply/idP/idP=> /rpredNr; rewrite ?opprK; apply. Qed.

End Opp.

Section Sub.

Variables (subS : zmodPred S) (kS : keyed_pred subS).

Lemma rpredB : {in kS &, forall u v, u - v \in kS}.
Proof. by move=> u v Su Sv; rewrite /= rpredD ?rpredN. Qed.

Lemma rpredMNn n : {in kS, forall u, u *- n \in kS}.
Proof. by move=> u Su; rewrite /= rpredN rpredMn. Qed.

Lemma rpredDr x y : x \in kS -> (y + x \in kS) = (y \in kS).
Proof.
move=> Sx; apply/idP/idP=> [Sxy | /rpredD-> //].
by rewrite -(addrK x y) rpredB.
Qed.

Lemma rpredDl x y : x \in kS -> (x + y \in kS) = (y \in kS).
Proof. by rewrite addrC; apply: rpredDr. Qed.

Lemma rpredBr x y : x \in kS -> (y - x \in kS) = (y \in kS).
Proof. by rewrite -rpredN; apply: rpredDr. Qed.

Lemma rpredBl x y : x \in kS -> (x - y \in kS) = (y \in kS).
Proof. by rewrite -(rpredN _ y); apply: rpredDl. Qed.

End Sub.

End ZmodulePred.

Section RingPred.

Variables (R : ringType) (S : predPredType R).

Lemma rpredMsign (oppS : opprPred S) (kS : keyed_pred oppS) n x :
  ((-1) ^+ n * x \in kS) = (x \in kS).
Proof. by rewrite -signr_odd mulr_sign; case: ifP => // _; rewrite rpredN. Qed.

Section Mul.

Variables (mulS : mulrPred S) (kS : keyed_pred mulS).

Lemma rpred1M : mulr_closed kS.
Proof.
by split=> [|x y]; rewrite !keyed_predE; case: mulS => _ [_] //; apply.
Qed.

Lemma rpred1 : 1 \in kS.
Proof. by case: rpred1M. Qed.

Lemma rpredM : {in kS &, forall u v, u * v \in kS}.
Proof. by case: rpred1M. Qed.

Lemma rpred_prod I r (P : pred I) F :
  (forall i, P i -> F i \in kS) -> \prod_(i <- r | P i) F i \in kS.
Proof. by move=> IH; elim/big_ind: _; [exact: rpred1 | exact: rpredM |]. Qed.

Lemma rpredX n : {in kS, forall u, u ^+ n \in kS}.
Proof. by move=> u Su; rewrite -(card_ord n) -prodr_const rpred_prod. Qed.

End Mul.

Lemma rpred_nat (rngS : semiringPred S) (kS : keyed_pred rngS) n : n%:R \in kS.
Proof. by rewrite rpredMn ?rpred1. Qed.

Lemma rpredN1 (mulS : smulrPred S) (kS : keyed_pred mulS) : -1 \in kS.
Proof. by rewrite rpredN rpred1. Qed.

Lemma rpred_sign (mulS : smulrPred S) (kS : keyed_pred mulS) n :
  (-1) ^+ n \in kS.
Proof. by rewrite rpredX ?rpredN1. Qed.

End RingPred.

Section LmodPred.

Variables (R : ringType) (V : lmodType R) (S : predPredType V).

Lemma rpredZsign (oppS : opprPred S) (kS : keyed_pred oppS) n u :
  ((-1) ^+ n *: u \in kS) = (u \in kS).
Proof. by rewrite -signr_odd scaler_sign fun_if if_arg rpredN if_same. Qed.

Lemma rpredZnat (addS : addrPred S) (kS : keyed_pred addS) n :
  {in kS, forall u, n%:R *: u \in kS}.
Proof. by move=> u Su; rewrite /= scaler_nat rpredMn. Qed.

Lemma rpredZ (linS : submodPred S) (kS : keyed_pred linS) : scaler_closed kS.
Proof. by move=> a u; rewrite !keyed_predE; case: {kS}linS => _; apply. Qed.

End LmodPred.

Section UnitRingPred.

Variable R : unitRingType. 

Section Div.

Variables (S : predPredType R) (divS : divrPred S) (kS : keyed_pred divS).

Lemma rpredVr x : x \in kS -> x^-1 \in kS.
Proof. by rewrite !keyed_predE; case: divS x. Qed.

Lemma rpredV x : (x^-1 \in kS) = (x \in kS).
Proof. by apply/idP/idP=> /rpredVr; rewrite ?invrK; apply. Qed.

Lemma rpred_div : {in kS &, forall x y, x / y \in kS}.
Proof. by move=> x y Sx Sy; rewrite /= rpredM ?rpredV. Qed.

Lemma rpredXN n : {in kS, forall x, x ^- n \in kS}.
Proof. by move=> x Sx; rewrite /= rpredV rpredX. Qed.

Lemma rpredMl x y : x \in kS -> x \is a unit-> (x * y \in kS) = (y \in kS).
Proof.
move=> Sx Ux; apply/idP/idP=> [Sxy | /(rpredM Sx)-> //].
by rewrite -(mulKr Ux y); rewrite rpredM ?rpredV.
Qed.

Lemma rpredMr x y : x \in kS -> x \is a unit -> (y * x \in kS) = (y \in kS).
Proof.
move=> Sx Ux; apply/idP/idP=> [Sxy | /rpredM-> //].
by rewrite -(mulrK Ux y); rewrite rpred_div.
Qed.

Lemma rpred_divr x y : x \in kS -> x \is a unit -> (y / x \in kS) = (y \in kS).
Proof. by rewrite -rpredV -unitrV; apply: rpredMr. Qed.

Lemma rpred_divl x y : x \in kS -> x \is a unit -> (x / y \in kS) = (y \in kS).
Proof. by rewrite -(rpredV y); apply: rpredMl. Qed.

End Div.

Fact unitr_sdivr_closed : @sdivr_closed R unit.
Proof. by split=> [|x y Ux Uy]; rewrite ?unitrN1 // unitrMl ?unitrV. Qed.

Canonical unit_opprPred := OpprPred unitr_sdivr_closed.
Canonical unit_mulrPred := MulrPred unitr_sdivr_closed.
Canonical unit_divrPred := DivrPred unitr_sdivr_closed.
Canonical unit_smulrPred := SmulrPred unitr_sdivr_closed.
Canonical unit_sdivrPred := SdivrPred unitr_sdivr_closed.

Implicit Type x : R.

Lemma unitrN x : (- x \is a unit) = (x \is a unit). Proof. exact: rpredN. Qed.

Lemma invrN x : (- x)^-1 = - x^-1.
Proof.
have [Ux | U'x] := boolP (x \is a unit); last by rewrite !invr_out ?unitrN.
by rewrite -mulN1r invrM ?unitrN1 // invrN1 mulrN1.
Qed.

Lemma invr_signM n x : ((-1) ^+ n * x)^-1 = (-1) ^+ n * x^-1.
Proof. by rewrite -signr_odd !mulr_sign; case: ifP => // _; rewrite invrN. Qed.

Lemma divr_signM (b1 b2 : bool) x1 x2:
  ((-1) ^+ b1 * x1) / ((-1) ^+ b2 * x2) = (-1) ^+ (b1 (+) b2) * (x1 / x2).
Proof. by rewrite invr_signM mulr_signM. Qed.

End UnitRingPred.

(* Reification of the theory of rings with units, in named style  *)
Section TermDef.

Variable R : Type.

Inductive term : Type :=
| Var of nat
| Const of R
| NatConst of nat
| Add of term & term
| Opp of term
| NatMul of term & nat
| Mul of term & term
| Inv of term
| Exp of term & nat.

Inductive formula : Type :=
| Bool of bool
| Equal of term & term
| Unit of term
| And of formula & formula
| Or of formula & formula
| Implies of formula & formula
| Not of formula
| Exists of nat & formula
| Forall of nat & formula.

End TermDef.

Bind Scope term_scope with term.
Bind Scope term_scope with formula.
Arguments Scope Add [_ term_scope term_scope].
Arguments Scope Opp [_ term_scope].
Arguments Scope NatMul [_ term_scope nat_scope].
Arguments Scope Mul [_ term_scope term_scope].
Arguments Scope Mul [_ term_scope term_scope].
Arguments Scope Inv [_ term_scope].
Arguments Scope Exp [_ term_scope nat_scope].
Arguments Scope Equal [_ term_scope term_scope].
Arguments Scope Unit [_ term_scope].
Arguments Scope And [_ term_scope term_scope].
Arguments Scope Or [_ term_scope term_scope].
Arguments Scope Implies [_ term_scope term_scope].
Arguments Scope Not [_ term_scope].
Arguments Scope Exists [_ nat_scope term_scope].
Arguments Scope Forall [_ nat_scope term_scope].

Implicit Arguments Bool [R].
Prenex Implicits Const Add Opp NatMul Mul Exp Bool Unit And Or Implies Not.
Prenex Implicits Exists Forall.

Notation True := (Bool true).
Notation False := (Bool false).

Local Notation "''X_' i" := (Var _ i) : term_scope.
Local Notation "n %:R" := (NatConst _ n) : term_scope.
Local Notation "x %:T" := (Const x) : term_scope.
Local Notation "0" := 0%:R%T : term_scope.
Local Notation "1" := 1%:R%T : term_scope.
Local Infix "+" := Add : term_scope.
Local Notation "- t" := (Opp t) : term_scope.
Local Notation "t - u" := (Add t (- u)) : term_scope.
Local Infix "*" := Mul : term_scope.
Local Infix "*+" := NatMul : term_scope.
Local Notation "t ^-1" := (Inv t) : term_scope.
Local Notation "t / u" := (Mul t u^-1) : term_scope.
Local Infix "^+" := Exp : term_scope.
Local Infix "==" := Equal : term_scope.
Local Infix "/\" := And : term_scope.
Local Infix "\/" := Or : term_scope.
Local Infix "==>" := Implies : term_scope.
Local Notation "~ f" := (Not f) : term_scope.
Local Notation "x != y" := (Not (x == y)) : term_scope.
Local Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Local Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

Section Substitution.

Variable R : Type.

Fixpoint tsubst (t : term R) (s : nat * term R) :=
  match t with
  | 'X_i => if i == s.1 then s.2 else t
  | _%:T | _%:R => t
  | t1 + t2 => tsubst t1 s + tsubst t2 s
  | - t1 => - tsubst t1 s
  | t1 *+ n => tsubst t1 s *+ n
  | t1 * t2 => tsubst t1 s * tsubst t2 s
  | t1^-1 => (tsubst t1 s)^-1
  | t1 ^+ n => tsubst t1 s ^+ n
  end%T.

Fixpoint fsubst (f : formula R) (s : nat * term R) :=
  match f with
  | Bool _ => f
  | t1 == t2 => tsubst t1 s == tsubst t2 s
  | Unit t1 => Unit (tsubst t1 s)
  | f1 /\ f2 => fsubst f1 s /\ fsubst f2 s
  | f1 \/ f2 => fsubst f1 s \/ fsubst f2 s
  | f1 ==> f2 => fsubst f1 s ==> fsubst f2 s
  | ~ f1 => ~ fsubst f1 s
  | ('exists 'X_i, f1) => 'exists 'X_i, if i == s.1 then f1 else fsubst f1 s
  | ('forall 'X_i, f1) => 'forall 'X_i, if i == s.1 then f1 else fsubst f1 s
  end%T.

End Substitution.

Section EvalTerm.

Variable R : unitRingType.

(* Evaluation of a reified term into R a ring with units *)
Fixpoint eval (e : seq R) (t : term R) {struct t} : R :=
  match t with
  | ('X_i)%T => e`_i
  | (x%:T)%T => x
  | (n%:R)%T => n%:R
  | (t1 + t2)%T => eval e t1 + eval e t2
  | (- t1)%T => - eval e t1
  | (t1 *+ n)%T => eval e t1 *+ n
  | (t1 * t2)%T => eval e t1 * eval e t2
  | t1^-1%T => (eval e t1)^-1
  | (t1 ^+ n)%T => eval e t1 ^+ n
  end.

Definition same_env (e e' : seq R) := nth 0 e =1 nth 0 e'.

Lemma eq_eval e e' t : same_env e e' -> eval e t = eval e' t.
Proof. by move=> eq_e; elim: t => //= t1 -> // t2 ->. Qed.

Lemma eval_tsubst e t s :
  eval e (tsubst t s) = eval (set_nth 0 e s.1 (eval e s.2)) t.
Proof.
case: s => i u; elim: t => //=; do 2?[move=> ? -> //] => j.
by rewrite nth_set_nth /=; case: (_ == _).
Qed.

(* Evaluation of a reified formula *)
Fixpoint holds (e : seq R) (f : formula R) {struct f} : Type :=
  match f with
  | Bool b => b
  | (t1 == t2)%T => eval e t1 = eval e t2
  | Unit t1 => eval e t1 \in unit
  | (f1 /\ f2)%T => holds e f1 /\ holds e f2
  | (f1 \/ f2)%T => holds e f1 \/ holds e f2
  | (f1 ==> f2)%T => holds e f1 -> holds e f2
  | (~ f1)%T => ~ holds e f1
  | ('exists 'X_i, f1)%T => exists x, holds (set_nth 0 e i x) f1
  | ('forall 'X_i, f1)%T => forall x, holds (set_nth 0 e i x) f1
  end.

Lemma same_env_sym e e' : same_env e e' -> same_env e' e.
Proof. exact: fsym. Qed.

(* Extensionality of formula evaluation *)
Lemma eq_holds e e' f : same_env e e' -> holds e f -> holds e' f.
Proof.
pose sv := set_nth (0 : R).
have eq_i i v e1 e2: same_env e1 e2 -> same_env (sv e1 i v) (sv e2 i v).
  by move=> eq_e j; rewrite !nth_set_nth /= eq_e.
elim: f e e' => //=. (*
- by move=> t1 t2 e e' eq_e; rewrite !(eq_eval _ eq_e). 
- by move=> t e e' eq_e; rewrite (eq_eval _ eq_e).
- by move=> f1 IH1 f2 IH2 e e' eq_e; move/IH2: (eq_e); move/IH1: eq_e; tauto.
- by move=> f1 IH1 f2 IH2 e e' eq_e; move/IH2: (eq_e); move/IH1: eq_e; tauto.
- by move=> f1 IH1 f2 IH2 e e' eq_e f12; move/IH1: (same_env_sym eq_e); eauto.
- by move=> f1 IH1 e e'; move/same_env_sym; move/IH1; tauto.
- by move=> i f1 IH1 e e'; move/(eq_i i)=> eq_e [x f_ex]; exists x; eauto.
move=> i f1 IH1 e e' ?. move/(eq_i i); eauto. *) admit.
Qed.


(* assia : no tauto *)
(* Evaluation and substitution by a constant *)
Lemma holds_fsubst e f i v :
  holds e (fsubst f (i, v%:T)%T) <-> holds (set_nth 0 e i v) f.
Proof. (*
elim: f e => //=; do [
  by move=> *; rewrite !eval_tsubst
| move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto
| move=> f IHf e; move: (IHf e); tauto
| move=> j f IHf e].
- case eq_ji: (j == i); first rewrite (eqP eq_ji).
    by split=> [] [x f_x]; exists x; rewrite set_set_nth eqxx in f_x *.
  split=> [] [x f_x]; exists x; move: f_x; rewrite set_set_nth eq_sym eq_ji;
     have:= IHf (set_nth 0 e j x); tauto.
case eq_ji: (j == i); first rewrite (eqP eq_ji).
  by split=> [] f_ x; move: (f_ x); rewrite set_set_nth eqxx.
split=> [] f_ x; move: (IHf (set_nth 0 e j x)) (f_ x);
  by rewrite set_set_nth eq_sym eq_ji; tauto. *) admit.
Qed.


(* Boolean test selecting terms in the language of rings *)
Fixpoint rterm (t : term R) :=
  match t with
  | _^-1 => false
  | t1 + t2 | t1 * t2 => rterm t1 && rterm t2
  | - t1 | t1 *+ _ | t1 ^+ _ => rterm t1
  | _ => true
  end%T.

(* Boolean test selecting formulas in the theory of rings *)
Fixpoint rformula (f : formula R) :=
  match f with
  | Bool _ => true
  | t1 == t2 => rterm t1 && rterm t2
  | Unit t1 => false
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => rformula f1 && rformula f2
  | ~ f1 | ('exists 'X__, f1) | ('forall 'X__, f1) => rformula f1
  end%T.

(* Upper bound of the names used in a term *)
Fixpoint ub_var (t : term R) :=
  match t with
  | 'X_i => i.+1
  | t1 + t2 | t1 * t2 => maxn (ub_var t1) (ub_var t2)
  | - t1 | t1 *+ _ | t1 ^+ _ | t1^-1 => ub_var t1
  | _ => 0%N
  end%T.

(* Replaces inverses in the term t by fresh variables, accumulating the *)
(* substitution. *)
Fixpoint to_rterm (t : term R) (r : seq (term R)) (n : nat) {struct t} :=
  match t with
  | t1^-1 =>
    let: (t1', r1) := to_rterm t1 r n in
      ('X_(n + size r1), rcons r1 t1')
  | t1 + t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (t1' + t2', r2)
  | - t1 =>
   let: (t1', r1) := to_rterm t1 r n in
     (- t1', r1)
  | t1 *+ m =>
   let: (t1', r1) := to_rterm t1 r n in
     (t1' *+ m, r1)
  | t1 * t2 =>
    let: (t1', r1) := to_rterm t1 r n in
    let: (t2', r2) := to_rterm t2 r1 n in
      (Mul t1' t2', r2)
  | t1 ^+ m =>
       let: (t1', r1) := to_rterm t1 r n in
     (t1' ^+ m, r1)
  | _ => (t, r)
  end%T.

Lemma to_rterm_id t r n : rterm t -> to_rterm t r n = (t, r).
Proof.
elim: t r n => //.
- by move=> t1 IHt1 t2 IHt2 r n /= /andP[rt1 rt2]; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n /= rt; rewrite {}IHt.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
- by move=> t1 IHt1 t2 IHt2 r n /= /andP[rt1 rt2]; rewrite {}IHt1 // IHt2.
- by move=> t IHt r n m /= rt; rewrite {}IHt.
Qed.

(* A ring formula stating that t1 is equal to 0 in the ring theory. *)
(* Also applies to non commutative rings.                           *)
Definition eq0_rform t1 :=
  let m := ub_var t1 in
  let: (t1', r1) := to_rterm t1 [::] m in
  let fix loop r i := match r with
  | [::] => t1' == 0
  | t :: r' =>
    let f := 'X_i * t == 1 /\ t * 'X_i == 1 in
     'forall 'X_i, (f \/ 'X_i == t /\ ~ ('exists 'X_i,  f)) ==> loop r' i.+1
  end%T
  in loop r1 m.

(* Transformation of a formula in the theory of rings with units into an *)
(* equivalent formula in the sub-theory of rings.                        *)
Fixpoint to_rform f :=
  match f with
  | Bool b => f
  | t1 == t2 => eq0_rform (t1 - t2)
  | Unit t1 => eq0_rform (t1 * t1^-1 - 1)
  | f1 /\ f2 => to_rform f1 /\ to_rform f2
  | f1 \/ f2 =>  to_rform f1 \/ to_rform f2
  | f1 ==> f2 => to_rform f1 ==> to_rform f2
  | ~ f1 => ~ to_rform f1
  | ('exists 'X_i, f1) => 'exists 'X_i, to_rform f1
  | ('forall 'X_i, f1) => 'forall 'X_i, to_rform f1
  end%T.

(* The transformation gives a ring formula. *)
Lemma to_rform_rformula f : rformula (to_rform f).
Proof.
suffices eq0_ring t1: rformula (eq0_rform t1) by elim: f => //= => f1 ->.
rewrite /eq0_rform; move: (ub_var t1) => m; set tr := _ m.
suffices: all rterm (tr.1 :: tr.2).
  case: tr => {t1} t1 r /= /andP[t1_r].
  by elim: r m => [|t r IHr] m; rewrite /= ?andbT // => /andP[->]; exact: IHr.
have: all rterm [::] by [].
rewrite {}/tr; elim: t1 [::] => //=.
- move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {t2 r IHt2} t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
- by move=> t1 IHt1 r /IHt1; case: to_rterm.
- by move=> t1 IHt1 n r /IHt1; case: to_rterm.
- move=> t1 IHt1 t2 IHt2 r.
  move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /= /andP[t1_r].
  move/IHt2; case: to_rterm => {t2 r IHt2} t2 r /= /andP[t2_r].
  by rewrite t1_r t2_r.
- move=> t1 IHt1 r.
  by move/IHt1; case: to_rterm => {t1 r IHt1} t1 r /=; rewrite all_rcons.
- by move=> t1 IHt1 n r /IHt1; case: to_rterm.
Qed.

(* assia : no tauto *)
(* Correctness of the transformation. *)
Lemma to_rformP e f : holds e (to_rform f) <-> holds e f.
Proof. (*
suffices{e f} equal0_equiv e t1 t2:
  holds e (eq0_rform (t1 - t2)) <-> (eval e t1 == eval e t2).
- elim: f e => /=; try tauto.
  + move=> t1 t2 e.
    by split; [move/equal0_equiv/eqP | move/eqP/equal0_equiv].
  + move=> t1 e; rewrite unitrE; exact: equal0_equiv.
  + move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + move=> f1 IHf1 f2 IHf2 e; move: (IHf1 e) (IHf2 e); tauto.
  + move=> f1 IHf1 e; move: (IHf1 e); tauto.
  + by move=> n f1 IHf1 e; split=> [] [x] /IHf1; exists x.
  + by move=> n f1 IHf1 e; split=> Hx x; apply/IHf1.
rewrite -(add0r (eval e t2)) -(can2_eq (subrK _) (addrK _)).
rewrite -/(eval e (t1 - t2)); move: (t1 - t2)%T => {t1 t2} t.
have sub_var_tsubst s t0: s.1 >= ub_var t0 -> tsubst t0 s = t0.
  elim: t0 {t} => //=.
  - by move=> n; case: ltngtP.
  - by move=> t1 IHt1 t2 IHt2; rewrite geq_max => /andP[/IHt1-> /IHt2->].
  - by move=> t1 IHt1 /IHt1->.
  - by move=> t1 IHt1 n /IHt1->.
  - by move=> t1 IHt1 t2 IHt2; rewrite geq_max => /andP[/IHt1-> /IHt2->].
  - by move=> t1 IHt1 /IHt1->.
  - by move=> t1 IHt1 n /IHt1->.
pose fix rsub t' m r : term R :=
  if r is u :: r' then tsubst (rsub t' m.+1 r') (m, u^-1)%T else t'.
pose fix ub_sub m r : Type :=
  if r is u :: r' then ub_var u <= m /\ ub_sub m.+1 r' else true.
suffices{t} rsub_to_r t r0 m: m >= ub_var t -> ub_sub m r0 ->
  let: (t', r) := to_rterm t r0 m in
  [/\ take (size r0) r = r0,
      ub_var t' <= m + size r, ub_sub m r & rsub t' m r = t].
- have:= rsub_to_r t [::] _ (leqnn _); rewrite /eq0_rform.
  case: (to_rterm _ _ _) => [t1' r1] [//|_ _ ub_r1 def_t].
  rewrite -{2}def_t {def_t}.
  elim: r1 (ub_var t) e ub_r1 => [|u r1 IHr1] m e /= => [_|[ub_u ub_r1]].
    by split=> /eqP.
  rewrite eval_tsubst /=; set y := eval e u; split=> t_eq0.
    apply/IHr1=> //; apply: t_eq0.
    rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
    rewrite sub_var_tsubst //= -/y.
    case Uy: (y \in unit); [left | right]; first by rewrite mulVr ?divrr.
    split=> [|[z]]; first by rewrite invr_out ?Uy.
    rewrite nth_set_nth /= eqxx.
    rewrite -!(eval_tsubst _ _ (m, Const _)) !sub_var_tsubst // -/y => yz1.
    by case/unitrP: Uy; exists z.
  move=> x def_x; apply/IHr1=> //; suff ->: x = y^-1 by []; move: def_x.
  rewrite nth_set_nth /= eqxx -(eval_tsubst e u (m, Const _)).
  rewrite sub_var_tsubst //= -/y; case=> [[xy1 yx1] | [xy nUy]].
    by rewrite -[y^-1]mul1r -[1]xy1 mulrK //; apply/unitrP; exists x.
  rewrite invr_out //; apply/unitrP=> [[z yz1]]; case: nUy; exists z.
  rewrite nth_set_nth /= eqxx -!(eval_tsubst _ _ (m, _%:T)%T).
  by rewrite !sub_var_tsubst.
have rsub_id r t0 n: ub_var t0 <= n -> rsub t0 n r = t0.
  by elim: r n => //= t1 r IHr n let0n; rewrite IHr ?sub_var_tsubst ?leqW.
have rsub_acc r s t1 m1:
  ub_var t1 <= m1 + size r -> rsub t1 m1 (r ++ s) = rsub t1 m1 r.
  elim: r t1 m1 => [|t1 r IHr] t2 m1 /=; first by rewrite addn0; apply: rsub_id.
  by move=> letmr; rewrite IHr ?addSnnS.
elim: t r0 m => /=; try do [
  by move=> n r m hlt hub; rewrite take_size (ltn_addr _ hlt) rsub_id
| by move=> n r m hlt hub; rewrite leq0n take_size rsub_id
| move=> t1 IHt1 t2 IHt2 r m; rewrite geq_max; case/andP=> hub1 hub2 hmr;
  case: to_rterm {IHt1 hub1 hmr}(IHt1 r m hub1 hmr) => t1' r1;
  case=> htake1 hub1' hsub1 <-;
  case: to_rterm {IHt2 hub2 hsub1}(IHt2 r1 m hub2 hsub1) => t2' r2 /=;
  rewrite geq_max; case=> htake2 -> hsub2 /= <-;
  rewrite -{1 2}(cat_take_drop (size r1) r2) htake2; set r3 := drop _ _;
  rewrite size_cat addnA (leq_trans _ (leq_addr _ _)) //;
  split=> {hsub2}//;
   first by [rewrite takel_cat // -htake1 size_take geq_min leqnn orbT];
  rewrite -(rsub_acc r1 r3 t1') {hub1'}// -{htake1}htake2 {r3}cat_take_drop;
  by elim: r2 m => //= u r2 IHr2 m; rewrite IHr2
| do [ move=> t1 IHt1 r m; do 2!move/IHt1=> {IHt1}IHt1
     | move=> t1 IHt1 n r m; do 2!move/IHt1=> {IHt1}IHt1];
  case: to_rterm IHt1 => t1' r1 [-> -> hsub1 <-]; split=> {hsub1}//;
  by elim: r1 m => //= u r1 IHr1 m; rewrite IHr1].
move=> t1 IH r m letm /IH {IH} /(_ letm) {letm}.
case: to_rterm => t1' r1 /= [def_r ub_t1' ub_r1 <-].
rewrite size_rcons addnS leqnn -{1}cats1 takel_cat ?def_r; last first.
  by rewrite -def_r size_take geq_min leqnn orbT.
elim: r1 m ub_r1 ub_t1' {def_r} => /= [|u r1 IHr1] m => [_|[->]].
  by rewrite addn0 eqxx.
by rewrite -addSnnS => /IHr1 IH /IH[_ _ ub_r1 ->].*) admit.
Qed.


(* Boolean test selecting formulas which describe a constructible set, *)
(* i.e. formulas without quantifiers.                                  *)

(* The quantifier elimination check. *)
Fixpoint qf_form (f : formula R) :=
  match f with
  | Bool _ | _ == _ | Unit _ => true
  | f1 /\ f2 | f1 \/ f2 | f1 ==> f2 => qf_form f1 && qf_form f2
  | ~ f1 => qf_form f1
  | _ => false
  end%T.

(* Boolean holds predicate for quantifier free formulas *)
Definition qf_eval e := fix loop (f : formula R) : bool :=
  match f with
  | Bool b => b
  | t1 == t2 => (eval e t1 == eval e t2)%bool
  | Unit t1 => eval e t1 \in unit
  | f1 /\ f2 => loop f1 && loop f2
  | f1 \/ f2 => loop f1 || loop f2
  | f1 ==> f2 => (loop f1 ==> loop f2)%bool
  | ~ f1 => ~~ loop f1
  |_ => false
  end%T.

(* qf_eval is equivalent to holds *)
Lemma qf_evalP e f : qf_form f -> reflect (holds e f) (qf_eval e f).
Proof.
elim: f => //=; try by move=> *; exact: idP.
- move=> t1 t2 _; exact: eqP.
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1T]; last by right; case.
  by case/IHf2; [left | right; case].
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1F]; first by do 2 left.
  by case/IHf2; [left; right | right; case].
- move=> f1 IHf1 f2 IHf2 /= /andP[/IHf1[] f1T]; last by left.
  by case/IHf2; [left | right; move/(_ f1T)].
by move=> f1 IHf1 /IHf1[]; [right | left].
Qed.

Implicit Type bc : seq (term R) * seq (term R).

(* Quantifier-free formula are normalized into DNF. A DNF is *)
(* represented by the type seq (seq (term R) * seq (term R)), where we *)
(* separate positive and negative literals *)

(* DNF preserving conjunction *)
Definition and_dnf bcs1 bcs2 :=
  \big[cat/nil]_(bc1 <- bcs1)
     map (fun bc2 => (bc1.1 ++ bc2.1, bc1.2 ++ bc2.2)) bcs2.

(* Computes a DNF from a qf ring formula *)
Fixpoint qf_to_dnf (f : formula R) (neg : bool) {struct f} :=
  match f with
  | Bool b => if b (+) neg then [:: ([::], [::])] else [::]
  | t1 == t2 => [:: if neg then ([::], [:: t1 - t2]) else ([:: t1 - t2], [::])]
  | f1 /\ f2 => (if neg then cat else and_dnf) [rec f1, neg] [rec f2, neg]
  | f1 \/ f2 => (if neg then and_dnf else cat) [rec f1, neg] [rec f2, neg]
  | f1 ==> f2 => (if neg then and_dnf else cat) [rec f1, ~~ neg] [rec f2, neg]
  | ~ f1 => [rec f1, ~~ neg]
  | _ =>  if neg then [:: ([::], [::])] else [::]
  end%T where "[ 'rec' f , neg ]" := (qf_to_dnf f neg).

(* Conversely, transforms a DNF into a formula *)
Definition dnf_to_form :=
  let pos_lit t := And (t == 0) in let neg_lit t := And (t != 0) in 
  let cls bc := Or (foldr pos_lit True bc.1 /\ foldr neg_lit True bc.2) in
  foldr cls False.

(* Catenation of dnf is the Or of formulas *)
Lemma cat_dnfP e bcs1 bcs2 :
  qf_eval e (dnf_to_form (bcs1 ++ bcs2))
    = qf_eval e (dnf_to_form bcs1 \/ dnf_to_form bcs2).
Proof.
by elim: bcs1 => //= bc1 bcs1 IH1; rewrite -orbA; congr orb; rewrite IH1.
Qed.

(* and_dnf is the And of formulas *)
Lemma and_dnfP e bcs1 bcs2 :
  qf_eval e (dnf_to_form (and_dnf bcs1 bcs2))
   = qf_eval e (dnf_to_form bcs1 /\ dnf_to_form bcs2).
Proof.
elim: bcs1 => [|bc1 bcs1 IH1] /=; first by rewrite /and_dnf big_nil.
rewrite /and_dnf big_cons -/(and_dnf bcs1 bcs2) cat_dnfP  /=.
rewrite {}IH1 /= andb_orl; congr orb.
elim: bcs2 bc1 {bcs1} => [|bc2 bcs2 IH] bc1 /=; first by rewrite andbF.
rewrite {}IH /= andb_orr; congr orb => {bcs2}.
suffices aux (l1 l2 : seq (term R)) g : let redg := foldr (And \o g) True in
  qf_eval e (redg (l1 ++ l2)) = qf_eval e (redg l1 /\ redg l2)%T.
+ by rewrite 2!aux /= 2!andbA -andbA -andbCA andbA andbCA andbA.
by elim: l1 => [| t1 l1 IHl1] //=; rewrite -andbA IHl1.
Qed.

Lemma qf_to_dnfP e :
  let qev f b := qf_eval e (dnf_to_form (qf_to_dnf f b)) in
  forall f, qf_form f && rformula f -> qev f false = qf_eval e f.
Proof.
move=> qev; have qevT f: qev f true = ~~ qev f false.
  rewrite {}/qev; elim: f => //=; do [by case | move=> f1 IH1 f2 IH2 | ].
  - by move=> t1 t2; rewrite !andbT !orbF.
  - by rewrite and_dnfP cat_dnfP negb_and -IH1 -IH2.
  - by rewrite and_dnfP cat_dnfP negb_or -IH1 -IH2.
  - by rewrite and_dnfP cat_dnfP /= negb_or IH1 -IH2 negbK.
  by move=> t1 ->; rewrite negbK.
rewrite /qev; elim=> //=; first by case.
- by move=> t1 t2 _; rewrite subr_eq0 !andbT orbF.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite and_dnfP /= => /IH1-> /IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /= => /IH1-> => /IH2->.
- move=> f1 IH1 f2 IH2; rewrite andbCA -andbA andbCA andbA; case/andP.
  by rewrite cat_dnfP /= [qf_eval _ _]qevT -implybE => /IH1 <- /IH2->.
by move=> f1 IH1 /IH1 <-; rewrite -qevT.
Qed.

Lemma dnf_to_form_qf bcs : qf_form (dnf_to_form bcs).
Proof.
by elim: bcs => //= [[clT clF] _ ->] /=; elim: clT => //=; elim: clF.
Qed.

Definition dnf_rterm cl := all rterm cl.1 && all rterm cl.2.

Lemma qf_to_dnf_rterm f b : rformula f -> all dnf_rterm (qf_to_dnf f b).
Proof.
set ok := all dnf_rterm.
have cat_ok bcs1 bcs2: ok bcs1 -> ok bcs2 -> ok (bcs1 ++ bcs2).
  by move=> ok1 ok2; rewrite [ok _]all_cat; exact/andP.
have and_ok bcs1 bcs2: ok bcs1 -> ok bcs2 -> ok (and_dnf bcs1 bcs2).
  rewrite /and_dnf unlock; elim: bcs1 => //= cl1 bcs1 IH1; rewrite -andbA.
  case/and3P=> ok11 ok12 ok1 ok2; rewrite cat_ok ?{}IH1 {bcs1 ok1}//.
  elim: bcs2 ok2 => //= cl2 bcs2 IH2 /andP[ok2 /IH2->].
  by rewrite /dnf_rterm !all_cat ok11 ok12 /= !andbT.
elim: f b => //=; [ by do 2!case | | | | | by auto | | ];
  try by repeat case/andP || intro; case: ifP; auto.
by rewrite /dnf_rterm => ?? [] /= ->.
Qed.

Lemma dnf_to_rform bcs : rformula (dnf_to_form bcs) = all dnf_rterm bcs.
Proof.
elim: bcs => //= [[cl1 cl2] bcs ->]; rewrite {2}/dnf_rterm /=; congr (_ && _).
by congr andb; [elim: cl1 | elim: cl2] => //= t cl ->; rewrite andbT.
Qed.

Section If.

Variables (pred_f then_f else_f : formula R).

Definition If := (pred_f /\ then_f \/ ~ pred_f /\ else_f)%T.

Lemma If_form_qf :
  qf_form pred_f -> qf_form then_f -> qf_form else_f -> qf_form If.
Proof. by move=> /= -> -> ->. Qed.

Lemma If_form_rf :
  rformula pred_f -> rformula then_f -> rformula else_f -> rformula If.
Proof. by move=> /= -> -> ->. Qed.

Lemma eval_If e :
  let ev := qf_eval e in ev If = (if ev pred_f then ev then_f else ev else_f).
Proof. by rewrite /=; case: ifP => _; rewrite ?orbF. Qed. 

End If.

Section Pick.

Variables (I : finType) (pred_f then_f : I -> formula R) (else_f : formula R).

Definition Pick :=
  \big[Or/False]_(p : {ffun pred I})
    ((\big[And/True]_i (if p i then pred_f i else ~ pred_f i))
    /\ (if pick p is Some i then then_f i else else_f))%T.

Lemma Pick_form_qf :
   (forall i, qf_form (pred_f i)) ->
   (forall i, qf_form (then_f i)) ->
    qf_form else_f ->
  qf_form Pick.
Proof.
move=> qfp qft qfe; have mA := (big_morph qf_form) true andb.
rewrite mA // big1 //= => p _.
rewrite mA // big1 => [|i _]; first by case: pick.
by rewrite fun_if if_same /= qfp.
Qed.

Lemma eval_Pick e (qev := qf_eval e) :
  let P i := qev (pred_f i) in
  qev Pick = (if pick P is Some i then qev (then_f i) else qev else_f).
Proof.
move=> P; rewrite ((big_morph qev) false orb) //= big_orE /=.
apply/existsP/idP=> [[p] | true_at_P].
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  case/andP=> /forallP eq_p_P.
  rewrite (@eq_pick _ _ P) => [|i]; first by case: pick.
  by move/(_ i): eq_p_P => /=; case: (p i) => //=; move/negbTE.
exists [ffun i => P i] => /=; apply/andP; split.
  rewrite ((big_morph qev) true andb) //= big_andE /=.
  by apply/forallP=> i; rewrite /= ffunE; case Pi: (P i) => //=; apply: negbT.
rewrite (@eq_pick _ _ P) => [|i]; first by case: pick true_at_P.
by rewrite ffunE.
Qed.

End Pick.

Section MultiQuant.

Variable f : formula R.
Implicit Types (I : seq nat) (e : seq R).

Lemma foldExistsP I e :
  (exists2 e', {in [predC I], same_env e e'} & holds e' f)
    <-> holds e (foldr Exists f I).
Proof.
elim: I e => /= [|i I IHi] e.
  by split=> [[e' eq_e] |]; [apply: eq_holds => i; rewrite eq_e | exists e].
split=> [[e' eq_e f_e'] | [x]]; last set e_x := set_nth 0 e i x.
  exists e'`_i; apply/IHi; exists e' => // j.
  by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP => // ->.
case/IHi=> e' eq_e f_e'; exists e' => // j.
by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP.
Qed.

Lemma foldForallP I e :
  (forall e', {in [predC I], same_env e e'} -> holds e' f)
    <-> holds e (foldr Forall f I).
Proof.
elim: I e => /= [|i I IHi] e.
  by split=> [|f_e e' eq_e]; [exact | apply: eq_holds f_e => i; rewrite eq_e].
split=> [f_e' x | f_e e' eq_e]; first set e_x := set_nth 0 e i x.
  apply/IHi=> e' eq_e; apply: f_e' => j.
  by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP.
move/IHi: (f_e e'`_i); apply=> j.
by have:= eq_e j; rewrite nth_set_nth /= !inE; case: eqP => // ->.
Qed.


End MultiQuant.

End EvalTerm.

Prenex Implicits dnf_rterm.

Module IntegralDomain.

Definition axiom (R : ringType) :=
  forall x y : R, x * y = 0 -> (x == 0) || (y == 0).

Section ClassDef.

Record class_of (R : Type) : Type :=
  Class {base : ComUnitRing.class_of R; mixin : axiom (Ring.Pack base R)}.
Local Coercion base : class_of >-> ComUnitRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : axiom (@Ring.Pack T b0 T)) :=
  fun bT b & phant_id (ComUnitRing.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition comRingType := @ComRing.Pack cT xclass xT.
Definition unitRingType := @UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @ComUnitRing.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> ComUnitRing.class_of.
Implicit Arguments mixin [R x y].
Coercion mixin : class_of >-> axiom.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Notation idomainType := type.
Notation IdomainType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'idomainType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'idomainType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'idomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'idomainType'  'of'  T ]") : form_scope.
End Exports.

End IntegralDomain.
Import IntegralDomain.Exports.

Section IntegralDomainTheory.

Variable R : idomainType.
Implicit Types x y : R.

Lemma mulf_eq0 x y : (x * y == 0) = (x == 0) || (y == 0).
Proof.
apply/eqP/idP; first by case: R x y => T [].
by case/pred2P=> ->; rewrite (mulr0, mul0r).
Qed.

Lemma prodf_eq0 (I : finType) (P : pred I) (F : I -> R) :
  reflect (exists2 i, P i & (F i == 0)) (\prod_(i | P i) F i == 0).
Proof.
apply: (iffP idP) => [|[i Pi /eqP Fi0]]; last first.
  by rewrite (bigD1 i) //= Fi0 mul0r.
elim: (index_enum _) => [|i r IHr]; first by rewrite big_nil oner_eq0.
rewrite big_cons /=; have [Pi | _] := ifP; last exact: IHr.
by rewrite mulf_eq0; case/orP=> // Fi0; exists i.
Qed.

Lemma prodf_seq_eq0 I r (P : pred I) (F : I -> R) :
  (\prod_(i <- r | P i) F i == 0) = has (fun i => P i && (F i == 0)) r.
Proof. by rewrite (big_morph _ mulf_eq0 (oner_eq0 _)) big_has_cond. Qed.

Lemma mulf_neq0 x y : x != 0 -> y != 0 -> x * y != 0.
Proof. move=> x0 y0; rewrite mulf_eq0; exact/norP. Qed.

Lemma prodf_neq0 (I : finType) (P : pred I) (F : I -> R) :
  reflect (forall i, P i -> (F i != 0)) (\prod_(i | P i) F i != 0).
Proof.
by rewrite (sameP (prodf_eq0 _ _) exists_inP) negb_exists_in; exact: forall_inP.
Qed.

Lemma prodf_seq_neq0 I r (P : pred I) (F : I -> R) :
  (\prod_(i <- r | P i) F i != 0) = all (fun i => P i ==> (F i != 0)) r.
Proof.
rewrite prodf_seq_eq0 -all_predC; apply: eq_all => i /=.
by rewrite implybE negb_and.
Qed.

Lemma expf_eq0 x n : (x ^+ n == 0) = (n > 0) && (x == 0).
Proof.
elim: n => [|n IHn]; first by rewrite oner_eq0.
by rewrite exprS mulf_eq0 IHn andKb.
Qed.

Lemma sqrf_eq0 x : (x ^+ 2 == 0) = (x == 0). Proof. exact: expf_eq0. Qed.

Lemma expf_neq0 x m : x != 0 -> x ^+ m != 0.
Proof. by move=> x_nz; rewrite expf_eq0; apply/nandP; right. Qed.

Lemma natf_neq0 n : (n%:R != 0 :> R) = [char R]^'.-nat n.
Proof.
have [-> | /prod_prime_decomp->] := posnP n; first by rewrite eqxx.
rewrite !big_seq; elim/big_rec: _ => [|[p e] s /=]; first by rewrite oner_eq0.
case/mem_prime_decomp=> p_pr _ _; rewrite pnat_mul pnat_exp eqn0Ngt orbC => <-.
by rewrite natrM natrX mulf_eq0 expf_eq0 negb_or negb_and pnatE ?inE p_pr.
Qed.

Lemma natf0_char n : n > 0 -> n%:R == 0 :> R -> exists p, p \in [char R].
Proof.
elim: {n}_.+1 {-2}n (ltnSn n) => // m IHm n; rewrite ltnS => le_n_m.
rewrite leq_eqVlt -pi_pdiv mem_primes; move: (pdiv n) => p.
case/predU1P=> [<-|/and3P[p_pr n_gt0 /dvdnP[n']]]; first by rewrite oner_eq0.
move=> def_n; rewrite def_n muln_gt0 andbC prime_gt0 // in n_gt0 *.
rewrite natrM mulf_eq0 orbC; case/orP; first by exists p; exact/andP.
by apply: IHm (leq_trans _ le_n_m) _; rewrite // def_n ltn_Pmulr // prime_gt1.
Qed.

Lemma charf'_nat n : [char R]^'.-nat n = (n%:R != 0 :> R).
Proof.
have [-> | n_gt0] := posnP n; first by rewrite eqxx.
apply/idP/idP => [|nz_n]; last first.
  by apply/pnatP=> // p p_pr p_dvd_n; apply: contra nz_n => /dvdn_charf <-.
apply: contraL => n0; have [// | p charRp] := natf0_char _ n0.
have [p_pr _] := andP charRp; rewrite (eq_pnat _ (eq_negn (charf_eq charRp))).
by rewrite p'natE // (dvdn_charf charRp) n0.
Qed.

Lemma charf0P : [char R] =i pred0 <-> (forall n, (n%:R == 0 :> R) = (n == 0)%N).
Proof.
split=> charF0 n; last by rewrite !inE charF0 andbC; case: eqP => // ->.
have [-> | n_gt0] := posnP; first exact: eqxx.
by apply/negP; case/natf0_char=> // p; rewrite charF0.
Qed.

Lemma eqf_sqr x y : (x ^+ 2 == y ^+ 2) = (x == y) || (x == - y).
Proof. by rewrite -subr_eq0 subr_sqr mulf_eq0 subr_eq0 addr_eq0. Qed.

Lemma mulfI x : x != 0 -> injective ( *%R x).
Proof.
move=> nz_x y z; rewrite -[x * z]add0r; move/(canLR (addrK _))/eqP.
rewrite -mulrN -mulrDr mulf_eq0 (negbTE nz_x) /=.
by move/eqP/(canRL (subrK _)); rewrite add0r.
Qed.

Lemma mulIf x : x != 0 -> injective ( *%R^~ x).
Proof. by move=> nz_x y z; rewrite -!(mulrC x); exact: mulfI. Qed.

Lemma sqrf_eq1 x : (x ^+ 2 == 1) = (x == 1) || (x == -1).
Proof. by rewrite -subr_eq0 subr_sqr_1 mulf_eq0 subr_eq0 addr_eq0. Qed.

Lemma expfS_eq1 x n :
  (x ^+ n.+1 == 1) = (x == 1) || (\sum_(i < n.+1) x ^+ i == 0).
Proof. by rewrite -![_ == 1]subr_eq0 subrX1 mulf_eq0. Qed.

Lemma lregP x : reflect (lreg x) (x != 0).
Proof. by apply: (iffP idP) => [/mulfI | /lreg_neq0]. Qed.

Lemma rregP x : reflect (rreg x) (x != 0).
Proof. by apply: (iffP idP) => [/mulIf | /rreg_neq0]. Qed.

Canonical regular_idomainType := [idomainType of R^o].

End IntegralDomainTheory.

Implicit Arguments lregP [[R] [x]].
Implicit Arguments rregP [[R] [x]].

Module Field.

Definition mixin_of (F : unitRingType) := forall x : F, x != 0 -> x \in unit.

Lemma IdomainMixin R : mixin_of R -> IntegralDomain.axiom R.
Proof.
move=> m x y xy0; apply/norP=> [[]] /m Ux /m.
by rewrite -(unitrMr _ Ux) xy0 unitr0.
Qed.

Section Mixins.

Variables (R : comRingType) (inv : R -> R).

Definition axiom := forall x, x != 0 -> inv x * x = 1.
Hypothesis mulVx : axiom.
Hypothesis inv0 : inv 0 = 0.

Fact intro_unit (x y : R) : y * x = 1 -> x != 0.
Proof.
by move=> yx1; apply: contraNneq (oner_neq0 R) => x0; rewrite -yx1 x0 mulr0.
Qed.

Fact inv_out : {in predC (predC1 0), inv =1 id}.
Proof. by move=> x /negbNE/eqP->. Qed.

Definition UnitMixin := ComUnitRing.Mixin mulVx intro_unit inv_out.

Lemma Mixin : mixin_of (UnitRing.Pack (UnitRing.Class UnitMixin) R).
Proof. by []. Qed.

End Mixins.

Section ClassDef.

Record class_of (F : Type) : Type := Class {
  base : IntegralDomain.class_of F;
  mixin : mixin_of (UnitRing.Pack base F)
}.
Local Coercion base : class_of >-> IntegralDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@UnitRing.Pack T b0 T)) :=
  fun bT b & phant_id (IntegralDomain.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition comRingType := @ComRing.Pack cT xclass xT.
Definition unitRingType := @UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @ComUnitRing.Pack cT xclass xT.
Definition idomainType := @IntegralDomain.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> IntegralDomain.class_of.
Implicit Arguments mixin [F x].
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> IntegralDomain.type.
Canonical idomainType.
Notation fieldType := type.
Notation FieldType T m := (@pack T _ m _ _ id _ id).
Notation FieldUnitMixin := UnitMixin.
Notation FieldIdomainMixin := IdomainMixin.
Notation FieldMixin := Mixin.
Notation "[ 'fieldType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'fieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'fieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'fieldType'  'of'  T ]") : form_scope.
End Exports.

End Field.
Import Field.Exports.

Section FieldTheory.

Variable F : fieldType.
Implicit Types x y : F.

Lemma unitfE x : (x \in unit) = (x != 0).
Proof.
apply/idP/idP=> [Ux |]; last by case: F x => T [].
by apply/eqP=> x0; rewrite x0 unitr0 in Ux.
Qed.

Lemma mulVf x : x != 0 -> x^-1 * x = 1.
Proof. by rewrite -unitfE; exact: mulVr. Qed.
Lemma divff x : x != 0 -> x / x = 1.
Proof. by rewrite -unitfE; exact: divrr. Qed.
Definition mulfV := divff.
Lemma mulKf x : x != 0 -> cancel ( *%R x) ( *%R x^-1).
Proof. by rewrite -unitfE; exact: mulKr. Qed.
Lemma mulVKf x : x != 0 -> cancel ( *%R x^-1) ( *%R x).
Proof. by rewrite -unitfE; exact: mulVKr. Qed.
Lemma mulfK x : x != 0 -> cancel ( *%R^~ x) ( *%R^~ x^-1).
Proof. by rewrite -unitfE; exact: mulrK. Qed.
Lemma mulfVK x : x != 0 -> cancel ( *%R^~ x^-1) ( *%R^~ x).
Proof. by rewrite -unitfE; exact: divrK. Qed.
Definition divfK := mulfVK.

Lemma invfM : {morph @inv F : x y / x * y}.
Proof.
move=> x y; case: (eqVneq x 0) => [-> |nzx]; first by rewrite !(mul0r, invr0).
case: (eqVneq y 0) => [-> |nzy]; first by rewrite !(mulr0, invr0).
by rewrite mulrC invrM ?unitfE.
Qed.

Lemma expfB_cond m n x : (x == 0) + n <= m -> x ^+ (m - n) = x ^+ m / x ^+ n.
Proof.
move/subnK=> <-; rewrite addnA addnK !exprD.
have [-> | nz_x] := altP eqP; first by rewrite !mulr0 !mul0r.
by rewrite mulfK ?expf_neq0.
Qed.

Lemma expfB m n x : n < m -> x ^+ (m - n) = x ^+ m / x ^+ n.
Proof. by move=> lt_n_m; apply: expfB_cond; case: eqP => // _; apply: ltnW. Qed.

Lemma prodf_inv I r (P : pred I) (E : I -> F) :
  \prod_(i <- r | P i) (E i)^-1 = (\prod_(i <- r | P i) E i)^-1.
Proof. by rewrite (big_morph _ invfM (invr1 _)). Qed.

Lemma addf_div x1 y1 x2 y2 :
  y1 != 0 -> y2 != 0 -> x1 / y1 + x2 / y2 = (x1 * y2 + x2 * y1) / (y1 * y2).
Proof. by move=> nzy1 nzy2; rewrite invfM mulrDl !mulrA mulrAC !mulfK. Qed.

Lemma mulf_div x1 y1 x2 y2 : (x1 / y1) * (x2 / y2) = (x1 * x2) / (y1 * y2).
Proof. by rewrite mulrACA -invfM. Qed.

Lemma char0_natf_div :
  [char F] =i pred0 -> forall m d, d %| m -> (m %/ d)%:R = m%:R / d%:R :> F.
Proof.
move/charf0P=> char0F m [|d] d_dv_m; first by rewrite divn0 invr0 mulr0.
by rewrite natr_div // unitfE char0F.
Qed.

Section FieldMorphismInj.

Variables (R : ringType) (f : {rmorphism F -> R}).

Lemma fmorph_eq0 x : (f x == 0) = (x == 0).
Proof.
have [-> | nz_x] := altP (x =P _); first by rewrite rmorph0 eqxx.
apply/eqP; move/(congr1 ( *%R (f x^-1)))/eqP.
by rewrite -rmorphM mulVf // mulr0 rmorph1 ?oner_eq0.
Qed.

Lemma fmorph_inj : injective f.
Proof.
move=> x y eqfxy; apply/eqP; rewrite -subr_eq0 -fmorph_eq0 rmorphB //.
by rewrite eqfxy subrr.
Qed.

Lemma fmorph_eq1 x : (f x == 1) = (x == 1).
Proof. by rewrite -(inj_eq fmorph_inj) rmorph1. Qed.

Lemma fmorph_char : [char R] =i [char F].
Proof. by move=> p; rewrite !inE -fmorph_eq0 rmorph_nat. Qed.

End FieldMorphismInj.

Section FieldMorphismInv.

Variables (R : unitRingType) (f : {rmorphism F -> R}).

Lemma fmorph_unit x : (f x \in unit) = (x != 0).
Proof.
have [-> |] := altP (x =P _); first by rewrite rmorph0 unitr0.
by rewrite -unitfE; exact: rmorph_unit.
Qed.

Lemma fmorphV : {morph f: x / x^-1}.
Proof.
move=> x; have [-> | nz_x] := eqVneq x 0; first by rewrite !(invr0, rmorph0).
by rewrite rmorphV ?unitfE.
Qed.

Lemma fmorph_div : {morph f : x y / x / y}.
Proof. by move=> x y; rewrite rmorphM fmorphV. Qed.

End FieldMorphismInv.

Canonical regular_fieldType := [fieldType of F^o].

Section ModuleTheory.

Variable V : lmodType F.
Implicit Types (a : F) (v : V).

Lemma scalerK a : a != 0 -> cancel ( *:%R a : V -> V) ( *:%R a^-1).
Proof. by move=> nz_a v; rewrite scalerA mulVf // scale1r. Qed.

Lemma scalerKV a : a != 0 -> cancel ( *:%R a^-1 : V -> V) ( *:%R a).
Proof. by rewrite -invr_eq0 -{3}[a]invrK; exact: scalerK. Qed.

Lemma scalerI a : a != 0 -> injective ( *:%R a : V -> V).
Proof. move=> nz_a; exact: can_inj (scalerK nz_a). Qed.

Lemma scaler_eq0 a v : (a *: v == 0) = (a == 0) || (v == 0).
Proof.
have [-> | nz_a] := altP (a =P _); first by rewrite scale0r eqxx.
by rewrite (can2_eq (scalerK nz_a) (scalerKV nz_a)) scaler0.
Qed.

Lemma rpredZeq S (modS : submodPred S) (kS : keyed_pred modS) a v :
  (a *: v \in kS) = (a == 0) || (v \in kS).
Proof.
have [-> | nz_a] := altP eqP; first by rewrite scale0r rpred0.
by apply/idP/idP; first rewrite -{2}(scalerK nz_a v); apply: rpredZ.
Qed.

End ModuleTheory.

Section Predicates.

Context (S : pred_class) (divS : @divrPred F S) (kS : keyed_pred divS).

Lemma fpredMl x y : x \in kS -> x != 0 -> (x * y \in kS) = (y \in kS).
Proof. by rewrite -!unitfE; exact: rpredMl. Qed.

Lemma fpredMr x y : x \in kS -> x != 0 -> (y * x \in kS) = (y \in kS).
Proof. by rewrite -!unitfE; exact: rpredMr. Qed.

Lemma fpred_divl x y : x \in kS -> x != 0 -> (x / y \in kS) = (y \in kS).
Proof. by rewrite -!unitfE; exact: rpred_divl. Qed.

Lemma fpred_divr x y : x \in kS -> x != 0 -> (y / x \in kS) = (y \in kS).
Proof. by rewrite -!unitfE; exact: rpred_divr. Qed.

End Predicates.

End FieldTheory.

Implicit Arguments fmorph_inj [[F] [R] x1 x2].

Module DecidableField.

Definition axiom (R : unitRingType) (s : seq R -> pred (formula R)) :=
  forall e f, reflect (holds e f) (s e f).

Record mixin_of (R : unitRingType) : Type :=
  Mixin { sat : seq R -> pred (formula R); satP : axiom sat}.

Section ClassDef.

Record class_of (F : Type) : Type :=
  Class {base : Field.class_of F; mixin : mixin_of (UnitRing.Pack base F)}.
Local Coercion base : class_of >-> Field.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@UnitRing.Pack T b0 T)) :=
  fun bT b & phant_id (Field.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition comRingType := @ComRing.Pack cT xclass xT.
Definition unitRingType := @UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @ComUnitRing.Pack cT xclass xT.
Definition idomainType := @IntegralDomain.Pack cT xclass xT.
Definition fieldType := @Field.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Field.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> IntegralDomain.type.
Canonical idomainType.
Coercion fieldType : type >-> Field.type.
Canonical fieldType.
Notation decFieldType := type.
Notation DecFieldType T m := (@pack T _ m _ _ id _ id).
Notation DecFieldMixin := Mixin.
Notation "[ 'decFieldType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'decFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'decFieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'decFieldType'  'of'  T ]") : form_scope.
End Exports.

End DecidableField.
Import DecidableField.Exports.

Section DecidableFieldTheory.

Variable F : decFieldType.

Definition sat := DecidableField.sat (DecidableField.class F).

Lemma satP : DecidableField.axiom sat.
Proof. exact: DecidableField.satP. Qed.


Fact sol_subproof n f :
  reflect (exists s, (size s == n) && sat s f)
          (sat [::] (foldr Exists f (iota 0 n))).
Proof.
apply: (iffP (satP _ _)) => [|[s]]; last first.
  case/andP=> /eqP sz_s /satP f_s; apply/foldExistsP.
  exists s => // i; rewrite !inE mem_iota -leqNgt add0n => le_n_i.
  by rewrite !nth_default ?sz_s.
case/foldExistsP=> e e0 f_e; set s := take n (set_nth 0 e n 0).
have sz_s: size s = n by rewrite size_take size_set_nth leq_max leqnn.
exists s; rewrite sz_s eqxx; apply/satP; apply: eq_holds f_e => i.
case: (leqP n i) => [le_n_i | lt_i_n].
  by rewrite -e0 ?nth_default ?sz_s // !inE mem_iota -leqNgt.
by rewrite nth_take // nth_set_nth /= eq_sym eqn_leq leqNgt lt_i_n.
Qed.

Definition sol n f :=
  if sol_subproof n f is ReflectT sP then xchoose sP else nseq n 0.

Lemma size_sol n f : size (sol n f) = n.
Proof.
rewrite /sol; case: sol_subproof => [sP | _]; last exact: size_nseq.
by case/andP: (xchooseP sP) => /eqP.
Qed.

Lemma solP n f : reflect (exists2 s, size s = n & holds s f) (sat (sol n f) f).
Proof.
rewrite /sol; case: sol_subproof => [sP | sPn].
  case/andP: (xchooseP sP) => _ ->; left.
  by case: sP => s; case/andP; move/eqP=> <-; move/satP; exists s.
apply: (iffP (satP _ _)); first by exists (nseq n 0); rewrite ?size_nseq.
by case=> s sz_s; move/satP=> f_s; case: sPn; exists s; rewrite sz_s eqxx.
Qed.

Lemma eq_sat f1 f2 :
  (forall e, holds e f1 <-> holds e f2) -> sat^~ f1 =1 sat^~ f2.
Proof. by move=> eqf12 e; apply/satP/satP; case: (eqf12 e). Qed.

Lemma eq_sol f1 f2 :
  (forall e, holds e f1 <-> holds e f2) -> sol^~ f1 =1 sol^~ f2.
Proof.
rewrite /sol => /eq_sat eqf12 n.
do 2![case: sol_subproof] => //= [f1s f2s | ns1 [s f2s] | [s f1s] []].
- by apply: eq_xchoose => s; rewrite eqf12.
- by case: ns1; exists s; rewrite -eqf12.
by exists s; rewrite eqf12.
Qed.

End DecidableFieldTheory.

Implicit Arguments satP [[F] [e] [f]].
Implicit Arguments solP [[F] [n] [f]].

Section QE_Mixin.

Variable F : Field.type.
Implicit Type f : formula F.

Variable proj : nat -> seq (term F) * seq (term F) -> formula F.
(* proj is the elimination of a single existential quantifier *)

(* The elimination projector is well_formed. *)
Definition wf_QE_proj :=
  forall i bc (bc_i := proj i bc),
  dnf_rterm bc -> qf_form bc_i && rformula bc_i.

(* The elimination projector is valid *)
Definition valid_QE_proj :=
  forall i bc (ex_i_bc := ('exists 'X_i, dnf_to_form [:: bc])%T) e,
  dnf_rterm bc -> reflect (holds e ex_i_bc) (qf_eval e (proj i bc)).

Hypotheses (wf_proj : wf_QE_proj) (ok_proj : valid_QE_proj).

Let elim_aux f n := foldr Or False (map (proj n) (qf_to_dnf f false)).

Fixpoint quantifier_elim f :=
  match f with
  | f1 /\ f2 => (quantifier_elim f1) /\ (quantifier_elim f2)
  | f1 \/ f2 => (quantifier_elim f1) \/ (quantifier_elim f2)
  | f1 ==> f2 => (~ quantifier_elim f1) \/ (quantifier_elim f2)
  | ~ f => ~ quantifier_elim f
  | ('exists 'X_n, f) => elim_aux (quantifier_elim f) n
  | ('forall 'X_n, f) => ~ elim_aux (~ quantifier_elim f) n
  | _ => f
  end%T.

Lemma quantifier_elim_wf f :
  let qf := quantifier_elim f in rformula f -> qf_form qf && rformula qf.
Proof.
suffices aux_wf f0 n : let qf := elim_aux f0 n in
  rformula f0 -> qf_form qf && rformula qf.
- by elim: f => //=; do ?[  move=> f1 IH1 f2 IH2;
                     case/andP=> rf1 rf2;
                     case/andP:(IH1 rf1)=> -> ->;
                     case/andP:(IH2 rf2)=> -> -> //
                  |  move=> n f1 IH rf1;
                     case/andP: (IH rf1)=> qff rf;
                     rewrite aux_wf ].
rewrite /elim_aux => rf.
suffices or_wf fs : let ofs := foldr Or False fs in 
  all (@qf_form F) fs && all (@rformula F) fs -> qf_form ofs && rformula ofs.
- apply: or_wf.
  suffices map_proj_wf bcs: let mbcs := map (proj n) bcs in
    all dnf_rterm bcs -> all (@qf_form _) mbcs && all (@rformula _) mbcs.
    by apply: map_proj_wf; exact: qf_to_dnf_rterm.
  elim: bcs => [|bc bcs ihb] bcsr //= /andP[rbc rbcs].
  by rewrite andbAC andbA wf_proj //= andbC ihb.
elim: fs => //= g gs ihg; rewrite -andbA => /and4P[-> qgs -> rgs] /=.
by apply: ihg; rewrite qgs rgs.
Qed.

Lemma quantifier_elim_rformP e f :
  rformula f -> reflect (holds e f) (qf_eval e (quantifier_elim f)).
Proof.
pose rc e n f := exists x, qf_eval (set_nth 0 e n x) f.
have auxP f0 e0 n0: qf_form f0 && rformula f0 ->
  reflect (rc e0 n0 f0) (qf_eval e0 (elim_aux f0 n0)).
+ rewrite /elim_aux => cf; set bcs := qf_to_dnf f0 false.
  apply: (@iffP (rc e0 n0 (dnf_to_form bcs))); last first.
  - by case=> x; rewrite -qf_to_dnfP //; exists x.
  - by case=> x; rewrite qf_to_dnfP //; exists x.
  have: all dnf_rterm bcs by case/andP: cf => _; exact: qf_to_dnf_rterm.
  elim: {f0 cf}bcs => [|bc bcs IHbcs] /=; first by right; case.
  case/andP=> r_bc /IHbcs {IHbcs}bcsP.
  have f_qf := dnf_to_form_qf [:: bc].
  case: ok_proj => //= [ex_x|no_x].
    left; case: ex_x => x /(qf_evalP _ f_qf); rewrite /= orbF => bc_x.
    by exists x; rewrite /= bc_x.
  apply: (iffP bcsP) => [[x bcs_x] | [x]] /=.
    by exists x; rewrite /= bcs_x orbT.
  case/orP => [bc_x|]; last by exists x.
  by case: no_x; exists x; apply/(qf_evalP _ f_qf); rewrite /= bc_x.
elim: f e => //.
- move=> b e _; exact: idP.
- move=> t1 t2 e _; exact: eqP.
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; last by right; case.
  by case/IH2; [left | right; case].
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; first by do 2!left.
  by case/IH2; [left; right | right; case].
- move=> f1 IH1 f2 IH2 e /= /andP[/IH1[] f1e]; last by left.
  by case/IH2; [left | right; move/(_ f1e)].
- by move=> f IHf e /= /IHf[]; [right | left].
- move=> n f IHf e /= rf; have rqf := quantifier_elim_wf rf.
  by apply: (iffP (auxP _ _ _ rqf)) => [] [x]; exists x; exact/IHf.
move=> n f IHf e /= rf; have rqf := quantifier_elim_wf rf.
case: auxP => // [f_x|no_x]; first by right=> no_x; case: f_x => x /IHf[].
by left=> x; apply/IHf=> //; apply/idPn=> f_x; case: no_x; exists x.
Qed.

Definition proj_sat e f := qf_eval e (quantifier_elim (to_rform f)).

Lemma proj_satP : DecidableField.axiom proj_sat.
Proof.
move=> e f; have fP := quantifier_elim_rformP e (to_rform_rformula f).
by apply: (iffP fP); move/to_rformP.
Qed.

Definition QEdecFieldMixin := DecidableField.Mixin proj_satP.

End QE_Mixin.

Module ClosedField.

(* Axiom == all non-constant monic polynomials have a root *)
Definition axiom (R : ringType) :=
  forall n (P : nat -> R), n > 0 ->
   exists x : R, x ^+ n = \sum_(i < n) P i * (x ^+ i).

Section ClassDef.

Record class_of (F : Type) : Type :=
  Class {base : DecidableField.class_of F; _ : axiom (Ring.Pack base F)}.
Local Coercion base : class_of >-> DecidableField.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : axiom (@Ring.Pack T b0 T)) :=
  fun bT b & phant_id (DecidableField.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

(* There should eventually be a constructor from polynomial resolution *)
(* that builds the DecidableField mixin using QE.                      *)

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition comRingType := @ComRing.Pack cT xclass xT.
Definition unitRingType := @UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @ComUnitRing.Pack cT xclass xT.
Definition idomainType := @IntegralDomain.Pack cT xclass xT.
Definition fieldType := @Field.Pack cT xclass xT.
Definition decFieldType := @DecidableField.Pack cT class xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> DecidableField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> IntegralDomain.type.
Canonical idomainType.
Coercion fieldType : type >-> Field.type.
Canonical fieldType.
Coercion decFieldType : type >-> DecidableField.type.
Canonical decFieldType.
Notation closedFieldType := type.
Notation ClosedFieldType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'closedFieldType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'closedFieldType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'closedFieldType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'closedFieldType'  'of'  T ]") : form_scope.
End Exports.

End ClosedField.
Import ClosedField.Exports.

Section ClosedFieldTheory.

Variable F : closedFieldType.

Lemma solve_monicpoly : ClosedField.axiom F.
Proof. by case: F => ? []. Qed.

End ClosedFieldTheory.

Module SubType.

Section Zmodule.

Variables (V : zmodType) (S : predPredType V).
Variables (subS : zmodPred S) (kS : keyed_pred subS).
Variable U : subType (mem kS).

Let inU v Sv : U := Sub v Sv.
Let zeroU := inU (rpred0 kS).

Let oppU (u : U) := inU (rpredNr (valP u)).
Let addU (u1 u2 : U) := inU (rpredD (valP u1) (valP u2)).

Fact addA : associative addU.
Proof. by move=> u1 u2 u3; apply: val_inj; rewrite !SubK addrA. Qed.
Fact addC : commutative addU.
Proof. by move=> u1 u2; apply: val_inj; rewrite !SubK addrC. Qed.
Fact add0 : left_id zeroU addU.
Proof. by move=> u; apply: val_inj; rewrite !SubK add0r. Qed.
Fact addN : left_inverse zeroU oppU addU.
Proof. by move=> u; apply: val_inj; rewrite !SubK addNr. Qed.

Definition zmodMixin of phant U := ZmodMixin addA addC add0 addN.

End Zmodule.

Section Ring.

Variables (R : ringType) (S : predPredType R).
Variables (ringS : subringPred S) (kS : keyed_pred ringS).

Definition cast_zmodType (V : zmodType) T (VeqT : V = T :> Type) :=
  let cast mV := let: erefl in _ = T := VeqT return Zmodule.class_of T in mV in
  Zmodule.Pack (cast (Zmodule.class V)) T.

Variable (T : subType (mem kS)) (V : zmodType) (VeqT: V = T :> Type).

Let inT x Sx : T := Sub x Sx.
Let oneT := inT (rpred1 kS).
Let mulT (u1 u2 : T) := inT (rpredM (valP u1) (valP u2)).
Let T' := cast_zmodType VeqT.

Hypothesis valM : {morph (val : T' -> R) : x y / x - y}.

Let val0 : val (0 : T') = 0.
Proof. by rewrite -(subrr (0 : T')) valM subrr. Qed.
Let valD : {morph (val : T' -> R): x y / x + y}.
Proof.
by move=> u v; rewrite -{1}[v]opprK -[- v]sub0r !valM val0 sub0r opprK.
Qed.

Fact mulA : @associative T' mulT.
Proof. by move=> u1 u2 u3; apply: val_inj; rewrite !SubK mulrA. Qed.
Fact mul1l : left_id oneT mulT.
Proof. by move=> u; apply: val_inj; rewrite !SubK mul1r. Qed.
Fact mul1r : right_id oneT mulT.
Proof. by move=> u; apply: val_inj; rewrite !SubK mulr1. Qed.
Fact mulDl : @left_distributive T' T' mulT +%R.
Proof. by move=> u1 u2 u3; apply: val_inj; rewrite !(SubK, valD) mulrDl. Qed.
Fact mulDr : @right_distributive T' T' mulT +%R.
Proof. by move=> u1 u2 u3; apply: val_inj; rewrite !(SubK, valD) mulrDr. Qed.
Fact nz1 : oneT != 0 :> T'.
Proof.
by apply: contraNneq (oner_neq0 R) => eq10; rewrite -val0 -eq10 SubK.
Qed.

Definition ringMixin := RingMixin mulA mul1l mul1r mulDl mulDr nz1.

End Ring.

Section Lmodule.

Variables (R : ringType) (V : lmodType R) (S : predPredType V).
Variables (linS : submodPred S) (kS : keyed_pred linS).
Variables (W : subType (mem kS)) (Z : zmodType) (ZeqW : Z = W :> Type).

Let scaleW a (w : W) := (Sub _ : _ -> W) (rpredZ a (valP w)).
Let W' := cast_zmodType ZeqW.

Hypothesis valD : {morph (val : W' -> V) : x y / x + y}.

Fact scaleA a b (w : W') : scaleW a (scaleW b w) = scaleW (a * b) w.
Proof. by apply: val_inj; rewrite !SubK scalerA. Qed.
Fact scale1 : left_id 1 scaleW.
Proof. by move=> w; apply: val_inj; rewrite !SubK scale1r. Qed.
Fact scaleDr : @right_distributive R W' scaleW +%R.
Proof. by move=> a w w2; apply: val_inj; rewrite !(SubK, valD) scalerDr. Qed.
Fact scaleDl w : {morph (scaleW^~ w : R -> W') : a b / a + b}.
Proof. by move=> a b; apply: val_inj; rewrite !(SubK, valD) scalerDl. Qed.

Definition lmodMixin := LmodMixin scaleA scale1 scaleDr scaleDl.

End Lmodule.

Lemma lalgMixin (R : ringType) (A : lalgType R) (B : lmodType R) (f : B -> A) :
     phant B -> injective f -> scalable f -> 
   forall mulB, {morph f : x y / mulB x y >-> x * y} -> Lalgebra.axiom mulB.
Proof.
by move=> _ injf fZ mulB fM a x y; apply: injf; rewrite !(fZ, fM) scalerAl.
Qed.

Lemma comRingMixin (R : comRingType) (T : ringType) (f : T -> R) :
  phant T -> injective f -> {morph f : x y / x * y} -> commutative (@mul T).
Proof. by move=> _ inj_f fM x y; apply: inj_f; rewrite !fM mulrC. Qed.

Lemma algMixin (R : comRingType) (A : algType R) (B : lalgType R) (f : B -> A) :
    phant B -> injective f -> {morph f : x y / x * y} -> scalable f ->
  @Algebra.axiom R B.
Proof.
by move=> _ inj_f fM fZ a x y; apply: inj_f; rewrite !(fM, fZ) scalerAr.
Qed.

Section UnitRing.

Definition cast_ringType (Q : ringType) T (QeqT : Q = T :> Type) :=
  let cast rQ := let: erefl in _ = T := QeqT return Ring.class_of T in rQ in
  Ring.Pack (cast (Ring.class Q)) T.

Variables (R : unitRingType) (S : predPredType R).
Variables (ringS : divringPred S) (kS : keyed_pred ringS).

Variables (T : subType (mem kS)) (Q : ringType) (QeqT : Q = T :> Type).

Let inT x Sx : T := Sub x Sx.
Let invT (u : T) := inT (rpredVr (valP u)).
Let unitT := [qualify a u : T | val u \is a unit].
Let T' := cast_ringType QeqT.

Hypothesis val1 : val (1 : T') = 1.
Hypothesis valM : {morph (val : T' -> R) : x y / x * y}.

Fact mulVr :
  {in (unitT : predPredType T'), left_inverse (1 : T') invT (@mul T')}.
Proof. by move=> u Uu; apply: val_inj; rewrite val1 valM SubK mulVr. Qed.

Fact mulrV : {in unitT, right_inverse (1 : T') invT (@mul T')}.
Proof. by move=> u Uu; apply: val_inj; rewrite val1 valM SubK mulrV. Qed.

Fact unitP (u v : T') : v * u = 1 /\ u * v = 1 -> u \in unitT.
Proof.
by case=> vu1 uv1; apply/unitrP; exists (val v); rewrite -!valM vu1 uv1.
Qed.

Fact unit_id : {in [predC unitT], invT =1 id}.
Proof. by move=> u /invr_out def_u1; apply: val_inj; rewrite SubK. Qed.

Definition unitRingMixin := UnitRingMixin mulVr mulrV unitP unit_id.

End UnitRing.

Lemma idomainMixin (R : idomainType) (T : ringType) (f : T -> R) :
    phant T -> injective f -> f 0 = 0 -> {morph f : u v / u * v} ->
  @IntegralDomain.axiom T.
Proof.
move=> _ injf f0 fM u v uv0.
by rewrite -!(inj_eq injf) !f0 -mulf_eq0 -fM uv0 f0.
Qed.

Lemma fieldMixin (F : fieldType) (K : unitRingType) (f : K -> F) : 
    phant K -> injective f -> f 0 = 0 -> {mono f : u / u \in unit} -> 
  @Field.mixin_of K.
Proof. by move=> _ injf f0 fU u; rewrite -fU unitfE -f0 inj_eq. Qed.

Module Exports.

Notation "[ 'zmodMixin' 'of' U 'by' <: ]" := (zmodMixin (Phant U))
  (at level 0, format "[ 'zmodMixin'  'of'  U  'by'  <: ]") : form_scope.
Notation "[ 'ringMixin' 'of' R 'by' <: ]" :=
  (@ringMixin _ _ _ _ _ _ (@erefl Type R%type) (rrefl _))
  (at level 0, format "[ 'ringMixin'  'of'  R  'by'  <: ]") : form_scope.
Notation "[ 'lmodMixin' 'of' U 'by' <: ]" :=
  (@lmodMixin _ _ _ _ _ _ _ (@erefl Type U%type) (rrefl _))
  (at level 0, format "[ 'lmodMixin'  'of'  U  'by'  <: ]") : form_scope.
Notation "[ 'lalgMixin' 'of' A 'by' <: ]" :=
  ((lalgMixin (Phant A) val_inj (rrefl _)) *%R (rrefl _))
  (at level 0, format "[ 'lalgMixin'  'of'  A  'by'  <: ]") : form_scope.
Notation "[ 'comRingMixin' 'of' R 'by' <: ]" :=
  (comRingMixin (Phant R) val_inj (rrefl _))
  (at level 0, format "[ 'comRingMixin'  'of'  R  'by'  <: ]") : form_scope.
Notation "[ 'algMixin' 'of' A 'by' <: ]" :=
  (algMixin (Phant A) val_inj (rrefl _) (rrefl _))
  (at level 0, format "[ 'algMixin'  'of'  A  'by'  <: ]") : form_scope.
Notation "[ 'unitRingMixin' 'of' R 'by' <: ]" :=
  (@unitRingMixin _ _ _ _ _ _ (@erefl Type R%type) (erefl _) (rrefl _))
  (at level 0, format "[ 'unitRingMixin'  'of'  R  'by'  <: ]") : form_scope.
Notation "[ 'idomainMixin' 'of' R 'by' <: ]" :=
  (idomainMixin (Phant R) val_inj (erefl _) (rrefl _))
  (at level 0, format "[ 'idomainMixin'  'of'  R  'by'  <: ]") : form_scope.
Notation "[ 'fieldMixin' 'of' F 'by' <: ]" :=
  (fieldMixin (Phant F) val_inj (erefl _) (frefl _))
  (at level 0, format "[ 'fieldMixin'  'of'  F  'by'  <: ]") : form_scope.

End Exports.

End SubType.

Module Theory.

Definition addrA := addrA.
Definition addrC := addrC.
Definition add0r := add0r.
Definition addNr := addNr.
Definition addr0 := addr0.
Definition addrN := addrN.
Definition subrr := subrr.
Definition addrCA := addrCA.
Definition addrAC := addrAC.
Definition addrACA := addrACA.
Definition addKr := addKr.
Definition addNKr := addNKr.
Definition addrK := addrK.
Definition addrNK := addrNK.
Definition subrK := subrK.
Definition addrI := @addrI.
Definition addIr := @addIr.
Implicit Arguments addrI [[V] x1 x2].
Implicit Arguments addIr [[V] x1 x2].
Definition opprK := opprK.
Definition oppr_inj := @oppr_inj.
Implicit Arguments oppr_inj [[V] x1 x2].
Definition oppr0 := oppr0.
Definition oppr_eq0 := oppr_eq0.
Definition opprD := opprD.
Definition opprB := opprB.
Definition subr0 := subr0.
Definition sub0r := sub0r.
Definition subr_eq := subr_eq.
Definition subr_eq0 := subr_eq0.
Definition addr_eq0 := addr_eq0.
Definition eqr_opp := eqr_opp.
Definition eqr_oppLR := eqr_oppLR.
Definition sumrN := sumrN.
Definition sumrB := sumrB.
Definition sumrMnl := sumrMnl.
Definition sumrMnr := sumrMnr.
Definition sumr_const := sumr_const.
Definition mulr0n := mulr0n.
Definition mulr1n := mulr1n.
Definition mulr2n := mulr2n.
Definition mulrS := mulrS.
Definition mulrSr := mulrSr.
Definition mulrb := mulrb.
Definition mul0rn := mul0rn.
Definition mulNrn := mulNrn.
Definition mulrnDl := mulrnDl.
Definition mulrnDr := mulrnDr.
Definition mulrnBl := mulrnBl.
Definition mulrnBr := mulrnBr.
Definition mulrnA := mulrnA.
Definition mulrnAC := mulrnAC.
Definition mulrA := mulrA.
Definition mul1r := mul1r.
Definition mulr1 := mulr1.
Definition mulrDl := mulrDl.
Definition mulrDr := mulrDr.
Definition oner_neq0 := oner_neq0.
Definition oner_eq0 := oner_eq0.
Definition mul0r := mul0r.
Definition mulr0 := mulr0.
Definition mulrN := mulrN.
Definition mulNr := mulNr.
Definition mulrNN := mulrNN.
Definition mulN1r := mulN1r.
Definition mulrN1 := mulrN1.
Definition mulr_suml := mulr_suml.
Definition mulr_sumr := mulr_sumr.
Definition mulrBl := mulrBl.
Definition mulrBr := mulrBr.
Definition mulrnAl := mulrnAl.
Definition mulrnAr := mulrnAr.
Definition mulr_natl := mulr_natl.
Definition mulr_natr := mulr_natr.
Definition natrD := natrD.
Definition natrB := natrB.
Definition natr_sum := natr_sum.
Definition natrM := natrM.
Definition natrX := natrX.
Definition expr0 := expr0.
Definition exprS := exprS.
Definition expr1 := expr1.
Definition expr2 := expr2.
Definition expr0n := expr0n.
Definition expr1n := expr1n.
Definition exprD := exprD.
Definition exprSr := exprSr.
Definition commr_sym := commr_sym.
Definition commr_refl := commr_refl.
Definition commr0 := commr0.
Definition commr1 := commr1.
Definition commrN := commrN.
Definition commrN1 := commrN1.
Definition commrD := commrD.
Definition commrMn := commrMn.
Definition commrM := commrM.
Definition commr_nat := commr_nat.
Definition commrX := commrX.
Definition exprMn_comm := exprMn_comm.
Definition commr_sign := commr_sign.
Definition exprMn_n := exprMn_n.
Definition exprM := exprM.
Definition exprAC := exprAC.
Definition expr_mod := expr_mod.
Definition expr_dvd := expr_dvd.
Definition signr_odd := signr_odd.
Definition signr_eq0 := signr_eq0.
Definition mulr_sign := mulr_sign.
Definition signr_addb := signr_addb.
Definition signrN := signrN.
Definition signrE := signrE.
Definition mulr_signM := mulr_signM.
Definition exprNn := exprNn.
Definition sqrrN := sqrrN.
Definition sqrr_sign := sqrr_sign.
Definition signrMK := signrMK.
Definition mulrI_eq0 := mulrI_eq0.
Definition lreg_neq0 := lreg_neq0.
Definition mulrI0_lreg := mulrI0_lreg.
Definition lregN := lregN.
Definition lreg1 := lreg1.
Definition lregM := lregM.
Definition lregX := lregX.
Definition lreg_sign := lreg_sign.
Definition lregP {R x} := @lregP R x.
Definition mulIr_eq0 := mulIr_eq0.
Definition mulIr0_rreg := mulIr0_rreg.
Definition rreg_neq0 := rreg_neq0.
Definition rregN := rregN.
Definition rreg1 := rreg1.
Definition rregM := rregM.
Definition revrX := revrX.
Definition rregX := rregX.
Definition rregP {R x} := @rregP R x.
Definition exprDn_comm := exprDn_comm.
Definition exprBn_comm := exprBn_comm.
Definition subrXX_comm := subrXX_comm.
Definition exprD1n := exprD1n.
Definition subrX1 := subrX1.
Definition sqrrD1 := sqrrD1.
Definition sqrrB1 := sqrrB1.
Definition subr_sqr_1 := subr_sqr_1.
Definition charf0 := charf0.
Definition charf_prime := charf_prime.
Definition mulrn_char := mulrn_char.
Definition dvdn_charf := dvdn_charf.
Definition charf_eq := charf_eq.
Definition bin_lt_charf_0 := bin_lt_charf_0.
Definition Frobenius_autE := Frobenius_autE.
Definition Frobenius_aut0 := Frobenius_aut0.
Definition Frobenius_aut1 := Frobenius_aut1.
Definition Frobenius_autD_comm := Frobenius_autD_comm.
Definition Frobenius_autMn := Frobenius_autMn.
Definition Frobenius_aut_nat := Frobenius_aut_nat.
Definition Frobenius_autM_comm := Frobenius_autM_comm.
Definition Frobenius_autX := Frobenius_autX.
Definition Frobenius_autN := Frobenius_autN.
Definition Frobenius_autB_comm := Frobenius_autB_comm.
Definition exprNn_char := exprNn_char.
Definition addrr_char2 := addrr_char2.
Definition oppr_char2 := oppr_char2.
Definition addrK_char2 := addrK_char2.
Definition addKr_char2 := addKr_char2.
Definition prodr_const := prodr_const.
Definition mulrC := mulrC.
Definition mulrCA := mulrCA.
Definition mulrAC := mulrAC.
Definition mulrACA := mulrACA.
Definition exprMn := exprMn.
Definition prodrXl := prodrXl.
Definition prodrXr := prodrXr.
Definition prodrN := prodrN.
Definition prodrMn := prodrMn.
Definition exprDn := exprDn.
Definition exprBn := exprBn.
Definition subrXX := subrXX.
Definition sqrrD := sqrrD.
Definition sqrrB := sqrrB.
Definition subr_sqr := subr_sqr.
Definition subr_sqrDB := subr_sqrDB.
Definition exprDn_char := exprDn_char.
Definition mulrV := mulrV.
Definition divrr := divrr.
Definition mulVr := mulVr.
Definition invr_out := invr_out.
Definition unitrP {R x} := @unitrP R x.
Definition mulKr := mulKr.
Definition mulVKr := mulVKr.
Definition mulrK := mulrK.
Definition mulrVK := mulrVK.
Definition divrK := divrK.
Definition mulrI := mulrI.
Definition mulIr := mulIr.
Definition commrV := commrV.
Definition unitrE := unitrE.
Definition invrK := invrK.
Definition invr_inj := @invr_inj.
Implicit Arguments invr_inj [[R] x1 x2].
Definition unitrV := unitrV.
Definition unitr1 := unitr1.
Definition invr1 := invr1.
Definition divr1 := divr1.
Definition div1r := div1r.
Definition natr_div := natr_div.
Definition unitr0 := unitr0.
Definition invr0 := invr0.
Definition unitrN1 := unitrN1.
Definition unitrN := unitrN.
Definition invrN1 := invrN1.
Definition invrN := invrN.
Definition invr_sign := invr_sign.
Definition unitrMl := unitrMl.
Definition unitrMr := unitrMr.
Definition invrM := invrM.
Definition invr_eq0 := invr_eq0.
Definition invr_eq1 := invr_eq1.
Definition invr_neq0 := invr_neq0.
Definition unitrM_comm := unitrM_comm.
Definition unitrX := unitrX.
Definition unitrX_pos := unitrX_pos.
Definition exprVn := exprVn.
Definition exprB := exprB.
Definition invr_signM := invr_signM.
Definition divr_signM := divr_signM.
Definition rpred0D := rpred0D.
Definition rpred0 := rpred0.
Definition rpredD := rpredD.
Definition rpredNr := rpredNr.
Definition rpred_sum := rpred_sum.
Definition rpredMn := rpredMn.
Definition rpredN := rpredN.
Definition rpredB := rpredB.
Definition rpredMNn := rpredMNn.
Definition rpredDr := rpredDr.
Definition rpredDl := rpredDl.
Definition rpredBr := rpredBr.
Definition rpredBl := rpredBl.
Definition rpredMsign := rpredMsign.
Definition rpred1M := rpred1M.
Definition rpred1 := rpred1.
Definition rpredM := rpredM.
Definition rpred_prod := rpred_prod.
Definition rpredX := rpredX.
Definition rpred_nat := rpred_nat.
Definition rpredN1 := rpredN1.
Definition rpred_sign := rpred_sign.
Definition rpredZsign := rpredZsign.
Definition rpredZnat := rpredZnat.
Definition rpredZ := rpredZ.
Definition rpredVr := rpredVr.
Definition rpredV := rpredV.
Definition rpred_div := rpred_div.
Definition rpredXN := rpredXN.
Definition rpredZeq := rpredZeq.
Definition rpredMr := rpredMr.
Definition rpredMl := rpredMl.
Definition rpred_divr := rpred_divr.
Definition rpred_divl := rpred_divl.
Definition eq_eval := eq_eval.
Definition eval_tsubst := eval_tsubst.
Definition eq_holds := eq_holds.
Definition holds_fsubst := holds_fsubst.
Definition unitrM := unitrM.
Definition unitrPr {R x} := @unitrPr R x.
Definition expr_div_n := expr_div_n.
Definition mulf_eq0 := mulf_eq0.
Definition prodf_eq0 := prodf_eq0.
Definition prodf_seq_eq0 := prodf_seq_eq0.
Definition mulf_neq0 := mulf_neq0.
Definition prodf_neq0 := prodf_neq0.
Definition prodf_seq_neq0 := prodf_seq_neq0.
Definition expf_eq0 := expf_eq0.
Definition sqrf_eq0 := sqrf_eq0.
Definition expf_neq0 := expf_neq0.
Definition natf_neq0 := natf_neq0.
Definition natf0_char := natf0_char.
Definition charf'_nat := charf'_nat.
Definition charf0P := charf0P.
Definition eqf_sqr := eqf_sqr.
Definition mulfI := mulfI.
Definition mulIf := mulIf.
Definition sqrf_eq1 := sqrf_eq1.
Definition expfS_eq1 := expfS_eq1.
Definition unitfE := unitfE.
Definition mulVf := mulVf.
Definition mulfV := mulfV.
Definition divff := divff.
Definition mulKf := mulKf.
Definition mulVKf := mulVKf.
Definition mulfK := mulfK.
Definition mulfVK := mulfVK.
Definition divfK := divfK.
Definition invfM := invfM.
Definition expfB_cond := expfB_cond.
Definition expfB := expfB.
Definition prodf_inv := prodf_inv.
Definition addf_div := addf_div.
Definition mulf_div := mulf_div.
Definition char0_natf_div := char0_natf_div.
Definition fpredMr := fpredMr.
Definition fpredMl := fpredMl.
Definition fpred_divr := fpred_divr.
Definition fpred_divl := fpred_divl.
Definition satP {F e f} := @satP F e f.
Definition eq_sat := eq_sat.
Definition solP {F n f} := @solP F n f.
Definition eq_sol := eq_sol.
Definition size_sol := size_sol.
Definition solve_monicpoly := solve_monicpoly.
Definition raddf0 := raddf0.
Definition raddf_eq0 := raddf_eq0.
Definition raddfN := raddfN.
Definition raddfD := raddfD.
Definition raddfB := raddfB.
Definition raddf_sum := raddf_sum.
Definition raddfMn := raddfMn.
Definition raddfMNn := raddfMNn.
Definition raddfMnat := raddfMnat.
Definition raddfMsign := raddfMsign.
Definition can2_additive := can2_additive.
Definition bij_additive := bij_additive.
Definition rmorph0 := rmorph0.
Definition rmorphN := rmorphN.
Definition rmorphD := rmorphD.
Definition rmorphB := rmorphB.
Definition rmorph_sum := rmorph_sum.
Definition rmorphMn := rmorphMn.
Definition rmorphMNn := rmorphMNn.
Definition rmorphismP := rmorphismP.
Definition rmorphismMP := rmorphismMP.
Definition rmorph1 := rmorph1.
Definition rmorph_eq1 := rmorph_eq1.
Definition rmorphM := rmorphM.
Definition rmorphMsign := rmorphMsign.
Definition rmorph_nat := rmorph_nat.
Definition rmorph_eq_nat := rmorph_eq_nat.
Definition rmorph_prod := rmorph_prod.
Definition rmorphX := rmorphX.
Definition rmorphN1 := rmorphN1.
Definition rmorph_sign := rmorph_sign.
Definition rmorph_char := rmorph_char.
Definition can2_rmorphism := can2_rmorphism.
Definition bij_rmorphism := bij_rmorphism.
Definition rmorph_comm := rmorph_comm.
Definition rmorph_unit := rmorph_unit.
Definition rmorphV := rmorphV.
Definition rmorph_div := rmorph_div.
Definition fmorph_eq0 := fmorph_eq0.
Definition fmorph_inj := @fmorph_inj.
Implicit Arguments fmorph_inj [[F] [R] x1 x2].
Definition fmorph_eq1 := fmorph_eq1.
Definition fmorph_char := fmorph_char.
Definition fmorph_unit := fmorph_unit.
Definition fmorphV := fmorphV.
Definition fmorph_div := fmorph_div.
Definition scalerA := scalerA.
Definition scale1r := scale1r.
Definition scalerDr := scalerDr.
Definition scalerDl := scalerDl.
Definition scaler0 := scaler0.
Definition scale0r := scale0r.
Definition scaleNr := scaleNr.
Definition scaleN1r := scaleN1r.
Definition scalerN := scalerN.
Definition scalerBl := scalerBl.
Definition scalerBr := scalerBr.
Definition scaler_nat := scaler_nat.
Definition scalerMnl := scalerMnl.
Definition scalerMnr := scalerMnr.
Definition scaler_suml := scaler_suml.
Definition scaler_sumr := scaler_sumr.
Definition scaler_eq0 := scaler_eq0.
Definition scalerK := scalerK.
Definition scalerKV := scalerKV.
Definition scalerI := scalerI.
Definition scalerAl := scalerAl.
Definition mulr_algl := mulr_algl.
Definition scaler_sign := scaler_sign.
Definition signrZK := signrZK.
Definition scalerCA := scalerCA.
Definition scalerAr := scalerAr.
Definition mulr_algr := mulr_algr.
Definition exprZn := exprZn.
Definition scaler_prodl := scaler_prodl.
Definition scaler_prodr := scaler_prodr.
Definition scaler_prod := scaler_prod.
Definition scaler_injl := scaler_injl.
Definition scaler_unit := scaler_unit.
Definition invrZ := invrZ.
Definition raddfZnat := raddfZnat.
Definition raddfZsign := raddfZsign.
Definition in_algE := in_algE.
Definition linear0 := linear0.
Definition linearN := linearN.
Definition linearD := linearD.
Definition linearB := linearB.
Definition linear_sum := linear_sum.
Definition linearMn := linearMn.
Definition linearMNn := linearMNn.
Definition linearP := linearP.
Definition linearZ_LR := linearZ_LR.
Definition linearZ := linearZ.
Definition linearPZ := linearPZ.
Definition linearZZ := linearZZ.
Definition scalarP := scalarP.
Definition scalarZ := scalarZ.
Definition can2_linear := can2_linear.
Definition bij_linear := bij_linear.
Definition rmorph_alg := rmorph_alg.
Definition lrmorphismP := lrmorphismP.
Definition can2_lrmorphism := can2_lrmorphism.
Definition bij_lrmorphism := bij_lrmorphism.

Notation null_fun V := (null_fun V) (only parsing).
Notation in_alg A := (in_alg_loc A).

End Theory.

Notation in_alg A := (in_alg_loc A).

End GRing.

Export Zmodule.Exports Ring.Exports Lmodule.Exports Lalgebra.Exports.
Export Additive.Exports RMorphism.Exports Linear.Exports LRMorphism.Exports.
Export ComRing.Exports Algebra.Exports UnitRing.Exports UnitAlgebra.Exports.
Export ComUnitRing.Exports IntegralDomain.Exports Field.Exports.
Export DecidableField.Exports ClosedField.Exports.
Export Pred.Exports SubType.Exports.
Notation QEdecFieldMixin := QEdecFieldMixin.

Notation "0" := (zero _) : ring_scope.
Notation "-%R" := (@opp _) : ring_scope.
Notation "- x" := (opp x) : ring_scope.
Notation "+%R" := (@add _).
Notation "x + y" := (add x y) : ring_scope.
Notation "x - y" := (add x (- y)) : ring_scope.
Notation "x *+ n" := (natmul x n) : ring_scope.
Notation "x *- n" := (opp (x *+ n)) : ring_scope.
Notation "s `_ i" := (seq.nth 0%R s%R i) : ring_scope.
Notation support := 0.-support.

Notation "1" := (one _) : ring_scope.
Notation "- 1" := (opp 1) : ring_scope.

Notation "n %:R" := (natmul 1 n) : ring_scope.
Notation "[ 'char' R ]" := (char (Phant R)) : ring_scope.
Notation Frobenius_aut chRp := (Frobenius_aut chRp).
Notation "*%R" := (@mul _).
Notation "x * y" := (mul x y) : ring_scope.
Notation "x ^+ n" := (exp x n) : ring_scope.
Notation "x ^-1" := (inv x) : ring_scope.
Notation "x ^- n" := (inv (x ^+ n)) : ring_scope.
Notation "x / y" := (mul x y^-1) : ring_scope.

Notation "*:%R" := (@scale _ _).
Notation "a *: m" := (scale a m) : ring_scope.
Notation "k %:A" := (scale k 1) : ring_scope.
Notation "\0" := (null_fun _) : ring_scope.
Notation "f \+ g" := (add_fun_head tt f g) : ring_scope.
Notation "f \- g" := (sub_fun_head tt f g) : ring_scope.
Notation "a \*: f" := (scale_fun_head tt a f) : ring_scope.
Notation "x \*o f" := (mull_fun_head tt x f) : ring_scope.
Notation "x \o* f" := (mulr_fun_head tt x f) : ring_scope.

Notation "\sum_ ( <- r | P ) F" :=
  (\big[+%R/0%R]_(<- r | P%B) F%R) : ring_scope.
Notation "\sum_ ( i <- r | P ) F" :=
  (\big[+%R/0%R]_(i <- r | P%B) F%R) : ring_scope.
Notation "\sum_ ( i <- r ) F" :=
  (\big[+%R/0%R]_(i <- r) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n | P ) F" :=
  (\big[+%R/0%R]_(m <= i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( m <= i < n ) F" :=
  (\big[+%R/0%R]_(m <= i < n) F%R) : ring_scope.
Notation "\sum_ ( i | P ) F" :=
  (\big[+%R/0%R]_(i | P%B) F%R) : ring_scope.
Notation "\sum_ i F" :=
  (\big[+%R/0%R]_i F%R) : ring_scope.
Notation "\sum_ ( i : t | P ) F" :=
  (\big[+%R/0%R]_(i : t | P%B) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i : t ) F" :=
  (\big[+%R/0%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\sum_ ( i < n | P ) F" :=
  (\big[+%R/0%R]_(i < n | P%B) F%R) : ring_scope.
Notation "\sum_ ( i < n ) F" :=
  (\big[+%R/0%R]_(i < n) F%R) : ring_scope.
Notation "\sum_ ( i 'in' A | P ) F" :=
  (\big[+%R/0%R]_(i in A | P%B) F%R) : ring_scope.
Notation "\sum_ ( i 'in' A ) F" :=
  (\big[+%R/0%R]_(i in A) F%R) : ring_scope.

Notation "\prod_ ( <- r | P ) F" :=
  (\big[*%R/1%R]_(<- r | P%B) F%R) : ring_scope.
Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%R/1%R]_(i <- r | P%B) F%R) : ring_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%R/1%R]_(i <- r) F%R) : ring_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%R/1%R]_(m <= i < n | P%B) F%R) : ring_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%R/1%R]_(m <= i < n) F%R) : ring_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%R/1%R]_(i | P%B) F%R) : ring_scope.
Notation "\prod_ i F" :=
  (\big[*%R/1%R]_i F%R) : ring_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%R/1%R]_(i : t | P%B) F%R) (only parsing) : ring_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%R/1%R]_(i : t) F%R) (only parsing) : ring_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%R/1%R]_(i < n | P%B) F%R) : ring_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%R/1%R]_(i < n) F%R) : ring_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%R/1%R]_(i in A | P%B) F%R) : ring_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%R/1%R]_(i in A) F%R) : ring_scope.

Canonical add_monoid.
Canonical add_comoid.
Canonical mul_monoid.
Canonical mul_comoid.
Canonical muloid.
Canonical addoid.

Canonical locked_additive.
Canonical locked_rmorphism.
Canonical locked_linear.
Canonical locked_lrmorphism.
Canonical idfun_additive.
Canonical idfun_rmorphism.
Canonical idfun_linear.
Canonical idfun_lrmorphism.
Canonical comp_additive.
Canonical comp_rmorphism.
Canonical comp_linear.
Canonical comp_lrmorphism.
Canonical opp_additive.
Canonical opp_linear.
Canonical scale_additive.
Canonical scale_linear.
Canonical null_fun_additive.
Canonical null_fun_linear.
Canonical scale_fun_additive.
Canonical scale_fun_linear.
Canonical add_fun_additive.
Canonical add_fun_linear.
Canonical sub_fun_additive.
Canonical sub_fun_linear.
Canonical mull_fun_additive.
Canonical mull_fun_linear.
Canonical mulr_fun_additive.
Canonical mulr_fun_linear.
Canonical Frobenius_aut_additive.
Canonical Frobenius_aut_rmorphism.
Canonical in_alg_additive.
Canonical in_alg_rmorphism.

Notation "R ^c" := (converse R) (at level 2, format "R ^c") : type_scope.
Canonical converse_eqType.
Canonical converse_choiceType.
Canonical converse_zmodType.
Canonical converse_ringType.
Canonical converse_unitRingType.

Notation "R ^o" := (regular R) (at level 2, format "R ^o") : type_scope.
Canonical regular_eqType.
Canonical regular_choiceType.
Canonical regular_zmodType.
Canonical regular_ringType.
Canonical regular_lmodType.
Canonical regular_lalgType.
Canonical regular_comRingType.
Canonical regular_algType.
Canonical regular_unitRingType.
Canonical regular_comUnitRingType.
Canonical regular_unitAlgType.
Canonical regular_idomainType.
Canonical regular_fieldType.

Canonical unit_keyed.
Canonical unit_opprPred.
Canonical unit_mulrPred.
Canonical unit_smulrPred.
Canonical unit_divrPred.
Canonical unit_sdivrPred.

Bind Scope term_scope with term.
Bind Scope term_scope with formula.

Notation "''X_' i" := (Var _ i) : term_scope.
Notation "n %:R" := (NatConst _ n) : term_scope.
Notation "0" := 0%:R%T : term_scope.
Notation "1" := 1%:R%T : term_scope.
Notation "x %:T" := (Const x) : term_scope.
Infix "+" := Add : term_scope.
Notation "- t" := (Opp t) : term_scope.
Notation "t - u" := (Add t (- u)) : term_scope.
Infix "*" := Mul : term_scope.
Infix "*+" := NatMul : term_scope.
Notation "t ^-1" := (Inv t) : term_scope.
Notation "t / u" := (Mul t u^-1) : term_scope.
Infix "^+" := Exp : term_scope.
Infix "==" := Equal : term_scope.
Notation "x != y" := (GRing.Not (x == y)) : term_scope.
Infix "/\" := And : term_scope.
Infix "\/" := Or : term_scope.
Infix "==>" := Implies : term_scope.
Notation "~ f" := (Not f) : term_scope.
Notation "''exists' ''X_' i , f" := (Exists i f) : term_scope.
Notation "''forall' ''X_' i , f" := (Forall i f) : term_scope.

(* Lifting Structure from the codomain of finfuns. *)
Section FinFunZmod.

Variable (aT : finType) (rT : zmodType).
Implicit Types f g : {ffun aT -> rT}.

Definition ffun_zero := [ffun a : aT => (0 : rT)].
Definition ffun_opp f := [ffun a => - f a].
Definition ffun_add f g := [ffun a => f a + g a].

Fact ffun_addA : associative ffun_add.
Proof. by move=> f1 f2 f3; apply/ffunP=> a; rewrite !ffunE addrA. Qed.
Fact ffun_addC : commutative ffun_add.
Proof. by move=> f1 f2; apply/ffunP=> a; rewrite !ffunE addrC. Qed.
Fact ffun_add0 : left_id ffun_zero ffun_add.
Proof. by move=> f; apply/ffunP=> a; rewrite !ffunE add0r. Qed.
Fact ffun_addN : left_inverse ffun_zero ffun_opp ffun_add.
Proof. by move=> f; apply/ffunP=> a; rewrite !ffunE addNr. Qed.

Definition ffun_zmodMixin :=
  Zmodule.Mixin ffun_addA ffun_addC ffun_add0 ffun_addN.
Canonical ffun_zmodType := Eval hnf in ZmodType _ ffun_zmodMixin.

Section Sum.

Variables (I : Type) (r : seq I) (P : pred I) (F : I -> {ffun aT -> rT}).

Lemma sum_ffunE x : (\sum_(i <- r | P i) F i) x = \sum_(i <- r | P i) F i x.
Proof. by elim/big_rec2: _ => // [|i _ y _ <-]; rewrite !ffunE. Qed.

Lemma sum_ffun :
  \sum_(i <- r | P i) F i = [ffun x => \sum_(i <- r | P i) F i x].
Proof. by apply/ffunP=> i; rewrite sum_ffunE ffunE. Qed.

End Sum.

Lemma ffunMnE f n x : (f *+ n) x = f x *+ n.
Proof. by rewrite -[n]card_ord -!sumr_const sum_ffunE. Qed.

End FinFunZmod.
Canonical exp_zmodType (M : zmodType) n := [zmodType of M ^ n].

Section FinFunRing.

(* As rings require 1 != 0 in order to lift a ring structure over finfuns     *)
(* we need evidence that the domain is non-empty.                             *)

Variable (aT : finType) (R : ringType) (a : aT).

Definition ffun_one : {ffun aT -> R} := [ffun => 1].
Definition ffun_mul (f g : {ffun aT -> R}) := [ffun x => f x * g x]. 

Fact ffun_mulA : associative ffun_mul.
Proof. by move=> f1 f2 f3; apply/ffunP=> i; rewrite !ffunE mulrA. Qed.
Fact ffun_mul_1l : left_id ffun_one ffun_mul.
Proof. by move=> f; apply/ffunP=> i; rewrite !ffunE mul1r. Qed.
Fact ffun_mul_1r : right_id ffun_one ffun_mul.
Proof. by move=> f; apply/ffunP=> i; rewrite !ffunE mulr1. Qed.
Fact ffun_mul_addl :  left_distributive ffun_mul (@ffun_add _ _).
Proof. by move=> f1 f2 f3; apply/ffunP=> i; rewrite !ffunE mulrDl. Qed.
Fact ffun_mul_addr :  right_distributive ffun_mul (@ffun_add _ _).
Proof. by move=> f1 f2 f3; apply/ffunP=> i; rewrite !ffunE mulrDr. Qed.
Fact ffun1_nonzero : ffun_one != 0.
Proof. by apply/eqP => /ffunP/(_ a)/eqP; rewrite !ffunE oner_eq0. Qed.

Definition ffun_ringMixin :=
  RingMixin ffun_mulA ffun_mul_1l ffun_mul_1r ffun_mul_addl ffun_mul_addr
            ffun1_nonzero.
Definition ffun_ringType :=
  Eval hnf in RingType {ffun aT -> R} ffun_ringMixin.

End FinFunRing.

Section FinFunComRing.

Variable (aT : finType) (R : comRingType) (a : aT).

Fact ffun_mulC : commutative (@ffun_mul aT R).
Proof. by move=> f1 f2; apply/ffunP=> i; rewrite !ffunE mulrC. Qed.

Definition ffun_comRingType :=
  Eval hnf in ComRingType (ffun_ringType R a) ffun_mulC.

End FinFunComRing.

Section FinFunLmod.

Variable (R : ringType) (aT : finType) (rT : lmodType R).

Implicit Types f g : {ffun aT -> rT}.

Definition ffun_scale k f := [ffun a => k *: f a].

Fact ffun_scaleA k1 k2 f : 
  ffun_scale k1 (ffun_scale k2 f) = ffun_scale (k1 * k2) f.
Proof. by apply/ffunP=> a; rewrite !ffunE scalerA. Qed.
Fact ffun_scale1 : left_id 1 ffun_scale.
Proof. by move=> f; apply/ffunP=> a; rewrite !ffunE scale1r. Qed.
Fact ffun_scale_addr k : {morph (ffun_scale k) : x y / x + y}.
Proof. by move=> f g; apply/ffunP=> a; rewrite !ffunE scalerDr. Qed.
Fact ffun_scale_addl u : {morph (ffun_scale)^~ u : k1 k2 / k1 + k2}.
Proof. by move=> k1 k2; apply/ffunP=> a; rewrite !ffunE scalerDl. Qed.

Definition ffun_lmodMixin := 
  LmodMixin ffun_scaleA ffun_scale1 ffun_scale_addr ffun_scale_addl.
Canonical ffun_lmodType :=
  Eval hnf in LmodType R {ffun aT -> rT} ffun_lmodMixin.

End FinFunLmod.
Canonical exp_lmodType (R : ringType) (M : lmodType R) n :=
  [lmodType R of M ^ n].

(* External direct product. *)
Section PairZmod.

Variables M1 M2 : zmodType.

Definition opp_pair (x : M1 * M2) := (- x.1, - x.2).
Definition add_pair (x y : M1 * M2) := (x.1 + y.1, x.2 + y.2).

Fact pair_addA : associative add_pair.
Proof. by move=> x y z; congr (_, _); apply: addrA. Qed.

Fact pair_addC : commutative add_pair.
Proof. by move=> x y; congr (_, _); apply: addrC. Qed.

Fact pair_add0 : left_id (0, 0) add_pair.
Proof. by case=> x1 x2; congr (_, _); apply: add0r. Qed.

Fact pair_addN : left_inverse (0, 0) opp_pair add_pair.
Proof. by move=> x; congr (_, _); apply: addNr. Qed.

Definition pair_zmodMixin := ZmodMixin pair_addA pair_addC pair_add0 pair_addN.
Canonical pair_zmodType := Eval hnf in ZmodType (M1 * M2) pair_zmodMixin.

End PairZmod.

Section PairRing.

Variables R1 R2 : ringType.

Definition mul_pair (x y : R1 * R2) := (x.1 * y.1, x.2 * y.2).

Fact pair_mulA : associative mul_pair.
Proof. by move=> x y z; congr (_, _); apply: mulrA. Qed.

Fact pair_mul1l : left_id (1, 1) mul_pair.
Proof. by case=> x1 x2; congr (_, _); apply: mul1r. Qed.

Fact pair_mul1r : right_id (1, 1) mul_pair.
Proof. by case=> x1 x2; congr (_, _); apply: mulr1. Qed.

Fact pair_mulDl : left_distributive mul_pair +%R.
Proof. by move=> x y z; congr (_, _); apply: mulrDl. Qed.

Fact pair_mulDr : right_distributive mul_pair +%R.
Proof. by move=> x y z; congr (_, _); apply: mulrDr. Qed.

Fact pair_one_neq0 : (1, 1) != 0 :> R1 * R2.
Proof. by rewrite xpair_eqE oner_eq0. Qed.

Definition pair_ringMixin :=
  RingMixin pair_mulA pair_mul1l pair_mul1r pair_mulDl pair_mulDr pair_one_neq0.
Canonical pair_ringType := Eval hnf in RingType (R1 * R2) pair_ringMixin.

End PairRing.

Section PairComRing.

Variables R1 R2 : comRingType.

Fact pair_mulC : commutative (@mul_pair R1 R2).
Proof. by move=> x y; congr (_, _); apply: mulrC. Qed.

Canonical pair_comRingType := Eval hnf in ComRingType (R1 * R2) pair_mulC.

End PairComRing.

Section PairLmod.

Variables (R : ringType) (V1 V2 : lmodType R).

Definition scale_pair a (v : V1 * V2) : V1 * V2 := (a *: v.1, a *: v.2).

Fact pair_scaleA a b u : scale_pair a (scale_pair b u) = scale_pair (a * b) u.
Proof. by congr (_, _); apply: scalerA. Qed.

Fact pair_scale1 u : scale_pair 1 u = u.
Proof. by case: u => u1 u2; congr (_, _); apply: scale1r. Qed.

Fact pair_scaleDr : right_distributive scale_pair +%R.
Proof. by move=> a u v; congr (_, _); apply: scalerDr. Qed.

Fact pair_scaleDl u : {morph scale_pair^~ u: a b / a + b}.
Proof. by move=> a b; congr (_, _); apply: scalerDl. Qed.

Definition pair_lmodMixin :=
  LmodMixin pair_scaleA pair_scale1 pair_scaleDr pair_scaleDl.
Canonical pair_lmodType := Eval hnf in LmodType R (V1 * V2) pair_lmodMixin.

End PairLmod.

Section PairLalg.

Variables (R : ringType) (A1 A2 : lalgType R).

Fact pair_scaleAl a (u v : A1 * A2) : a *: (u * v) = (a *: u) * v.
Proof. by congr (_, _); apply: scalerAl. Qed.
Canonical pair_lalgType :=  Eval hnf in LalgType R (A1 * A2) pair_scaleAl.

End PairLalg.

Section PairAlg.

Variables (R : comRingType) (A1 A2 : algType R).

Fact pair_scaleAr a (u v : A1 * A2) : a *: (u * v) = u * (a *: v).
Proof. by congr (_, _); apply: scalerAr. Qed.
Canonical pair_algType :=  Eval hnf in AlgType R (A1 * A2) pair_scaleAr.

End PairAlg.

Section PairUnitRing.

Variables R1 R2 : unitRingType.

Definition pair_unitr :=
  [qualify a x : R1 * R2 | (x.1 \is a GRing.unit) && (x.2 \is a GRing.unit)].
Definition pair_invr x :=
  if x \is a pair_unitr then (x.1^-1, x.2^-1) else x.

Lemma pair_mulVl : {in pair_unitr, left_inverse 1 pair_invr *%R}.
Proof.
rewrite /pair_invr=> x; case: ifP => // /andP[Ux1 Ux2] _.
by congr (_, _); apply: mulVr.
Qed.

Lemma pair_mulVr : {in pair_unitr, right_inverse 1 pair_invr *%R}.
Proof.
rewrite /pair_invr=> x; case: ifP => // /andP[Ux1 Ux2] _.
by congr (_, _); apply: mulrV.
Qed.

Lemma pair_unitP x y : y * x = 1 /\ x * y = 1 -> x \is a pair_unitr.
Proof.
case=> [[y1x y2x] [x1y x2y]]; apply/andP.
by split; apply/unitrP; [exists y.1 | exists y.2].
Qed.

Lemma pair_invr_out : {in [predC pair_unitr], pair_invr =1 id}.
Proof. by rewrite /pair_invr => x /negPf/= ->. Qed.

Definition pair_unitRingMixin :=
  UnitRingMixin pair_mulVl pair_mulVr pair_unitP pair_invr_out.
Canonical pair_unitRingType :=
  Eval hnf in UnitRingType (R1 * R2) pair_unitRingMixin.

End PairUnitRing.

Canonical pair_comUnitRingType (R1 R2 : comUnitRingType) :=
  Eval hnf in [comUnitRingType of R1 * R2].

Canonical pair_unitAlgType (R : comUnitRingType) (A1 A2 : unitAlgType R) :=
  Eval hnf in [unitAlgType R of A1 * A2].

(* begin hide *)

(* Testing subtype hierarchy
Section Test0.

Variables (T : choiceType) (S : predPredType T).

Inductive B := mkB x & x \in S.
Definition vB u := let: mkB x _ := u in x.

Canonical B_subType := [subType for vB].
Definition B_eqMixin := [eqMixin of B by <:].
Canonical B_eqType := EqType B B_eqMixin.
Definition B_choiceMixin := [choiceMixin of B by <:].
Canonical B_choiceType := ChoiceType B B_choiceMixin.

End Test0.

Section Test1.

Variables (R : unitRingType) (S : pred R).
Variables (ringS : divringPred S) (kS : keyed_pred ringS).

Definition B_zmodMixin := [zmodMixin of B kS by <:].
Canonical B_zmodType := ZmodType (B kS) B_zmodMixin.
Definition B_ringMixin := [ringMixin of B kS by <:].
Canonical B_ringType := RingType (B kS) B_ringMixin.
Definition B_unitRingMixin := [unitRingMixin of B kS by <:].
Canonical B_unitRingType := UnitRingType (B kS) B_unitRingMixin.

End Test1.

Section Test2.

Variables (R : comUnitRingType) (A : unitAlgType R) (S : pred A).
Variables (algS : divalgPred S) (kS : keyed_pred algS).

Definition B_lmodMixin := [lmodMixin of B kS by <:].
Canonical B_lmodType := LmodType R (B kS) B_lmodMixin.
Definition B_lalgMixin := [lalgMixin of B kS by <:].
Canonical B_lalgType := LalgType R (B kS) B_lalgMixin.
Definition B_algMixin := [algMixin of B kS by <:].
Canonical B_algType := AlgType R (B kS) B_algMixin.
Canonical B_unitAlgType := [unitAlgType R of B kS].

End Test2.

Section Test3.

Variables (F : fieldType) (S : pred F).
Variables (ringS : divringPred S) (kS : keyed_pred ringS).

Definition B_comRingMixin := [comRingMixin of B kS by <:].
Canonical B_comRingType := ComRingType (B kS) B_comRingMixin.
Canonical B_comUnitRingType := [comUnitRingType of B kS].
Definition B_idomainMixin := [idomainMixin of B kS by <:].
Canonical B_idomainType := IdomainType (B kS) B_idomainMixin.
Definition B_fieldMixin := [fieldMixin of B kS by <:].
Canonical B_fieldType := FieldType (B kS) B_fieldMixin.

End Test3.

*)

(* end hide *)
