(* -*- mode: coq; mode: visual-line -*-  *)
(** * Connectedness *)

Require Import Overture Trunc Equivalences types.Paths.
Local Open Scope equiv_scope.

(** There is a slight controversy of indexing for connectedness — in particular, how the indexing for maps shoud relate to the indexing for types.  One may reasonably take the connectedness of a map to correspond either to that of its *fibers*, or of its *cofiber*; these differ by 1.  The traditional topological indexing uses the cofiber.  We use the fiber, as does Lurie in [HTT]; but we choose to agree with the traditional indexing on types, while Lurie agrees with it on maps.

Currently, the translation is therefore as follows:

       HoTT              Traditional       Lurie

Map    (n-1)-connected   n-connected       n-connective
Type   n-connected       n-connected       (n+1)-connective
 *)
