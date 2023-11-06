From HoTT Require Import Basics.Overture.

(** When [rewrite] is first used, it defines helper lemmas.  If the first use is in a Section that has universe variables, then these lemmas get unnecessary universe variables.  Overture uses [rewrite] outside of a section to ensure that they have the expected number of universe variables, and we test that here. *)

Check internal_paths_rew@{u1 u2}.
Check internal_paths_rew_r@{u1 u2}.
