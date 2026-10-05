(** * Power-set truncation inference with an individual-file import *)

(** Do not import [Universes.TruncType] here: importing [Sets.Powers] must expose the replacement truncation hints on its own. *)
Require Import HoTT.Basics HoTT.Types HoTT.Sets.Powers.

Definition powers_only `{Univalence} (X : HSet)
  : IsHSet (X -> HProp) := _.

Definition arbitrary_power_domain `{Univalence} (X : Type)
  : IsHSet (X -> HProp) := _.

Definition iterated_powers_only `{Univalence} (X : HSet) (n : nat)
  : IsHSet (power_iterated X n) := _.

(** Instance search must also respect an explicitly fixed [HProp] universe. *)
Definition powers_only_universe@{a i j | a <= j, i < j}
  `{Univalence} (X : Type@{a})
  : IsTrunc_internal@{j} (X -> HProp@{i}) 0.
Proof.
  rapply istrunc_arrow@{a j j}.
Defined.
