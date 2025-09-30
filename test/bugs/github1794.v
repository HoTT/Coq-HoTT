From HoTT Require Import Basics.Overture.


(** After PR#21098, helper lemmas are not generated as rewrite now relies on typeclass instances *)

(*
Check internal_paths_rew@{u1 u2}.
Check internal_paths_rew_r@{u1 u2}.
*)