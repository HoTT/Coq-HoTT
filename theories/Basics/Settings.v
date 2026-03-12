(** * General Settings *)

(** This file contains all the tweaks and settings we make to Coq. *)

(** ** Plugins *)

(** Load the Ltac plugin. This is the tactic language we use for proofs. *)
Declare ML Module "ltac_plugin:rocq-runtime.plugins.ltac".
(** Load the number string notation plugin. Allowing us to write numbers like [1234]. *)
Declare ML Module "number_string_notation_plugin:rocq-runtime.plugins.number_string_notation".

(** ** Proofs *)

(** Activate the Ltac tactics language for proofs. *)
Global Set Default Proof Mode "Classic".

(** Force use of bullets in proofs. *)
Global Set Default Goal Selector "!".

(** ** Universes *)

(** Activate universe polymorphism everywhere. This means that whenever you see a [Type], it's actually a [Type@{i}] for some universe level [i]. This allows us to reuse definitions for each universe level without having to redefine them. *)
Global Set Universe Polymorphism.

(** This command makes it so that you don't have to declare universes explicitly when mentioning them in the type.  (Without this command, if you want to say [Definition foo := Type@{i}.], you must instead say [Definition foo@{i} := Type@{i}.]. *)
Global Unset Strict Universe Declaration.

(** This command makes it so that when we say something like [IsHSet nat] we get [IsHSet@{i} nat] instead of [IsHSet@{Set} nat]. *)
Global Unset Universe Minimization ToSet.

(** ** Primitive Projections *)

Global Set Primitive Projections.
Global Set Nonrecursive Elimination Schemes.

(** Currently Coq doesn't print equivalences correctly (8.6). This fixes that. See https://github.com/HoTT/HoTT/issues/1000 *)
Global Set Printing Primitive Projection Parameters.

(** ** Pattern Matching *)

(** This flag removes parameters from constructors in patterns that appear in a match statement. *)
Global Set Asymmetric Patterns.

(** ** Unification *)

(** This command changes Coq's subterm selection to always use full conversion after finding a subterm whose head/key matches the key of the term we're looking for.  This applies to [rewrite] and higher-order unification in [apply]/[elim]/[destruct].  Again, if you don't know what that means, ignore it. *)
Global Set Keyed Unification.

(** ** Typeclasses and Hint settings *)

(** This tells Coq that when we [Require] a module without [Import]ing it, typeclass instances defined in that module should also not be imported.  In other words, the only effect of [Require] without [Import] is to make qualified names available. *)
Global Set Loose Hint Behavior "Strict".

Create HintDb rewrite discriminated.
#[export] Hint Variables Opaque : rewrite.
Create HintDb typeclass_instances discriminated.

(** ** Reversible Coercions *)

(** Coercions in Coq since 8.16 have the ability to be reversible. These are coercions that are not regular functions but rely on some meta-procedure like typeclass resolution to fill in missing pieces. Examples include marking fields of a record with [:>] which allows Coq to elaborate the projected term to the original term.

This behaviour can have some surprising effects in some places, where you might not expect a term to be elaborated. When inspecting proofs with [Set Printing All] you will not be able to see the reversible coercion. In order to help with inspecting such situations, Coq exposes a register for a dummy term called [reverse_coercion] which gets inserted during an application of a reversible coercion. This way you can see the application clearly in a proof term.

We register this here. This is standard from the Coq Stdlib prelude.*)
#[universes(polymorphic=yes)] Definition ReverseCoercionSource (T : Type) := T.
#[universes(polymorphic=yes)] Definition ReverseCoercionTarget (T : Type) := T.
#[warning="-uniform-inheritance", reversible=no, universes(polymorphic=yes)]
Coercion reverse_coercion {T' T} (x' : T') (x : ReverseCoercionSource T)
  : ReverseCoercionTarget T' := x'.
Register reverse_coercion as core.coercion.reverse_coercion.

(** ** Search Settings *)

(** Keywords for blacklisting from search function *)
Add Search Blacklist "_admitted" "_subproof" "Private_".
