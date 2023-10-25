From HoTT Require Import WildCat Join.

(** PR #1791 reduced the number of universe variables for several definitions.  These tests ensure that they remain reduced. *)

(** WildCat/Square.v: *)

Check is0functor_idmap@{u1 u2}.
Check vinverse@{u1 u2 u3 u4 u5}.
Check transpose@{u1 u2 u3}.

(** WildCat/Yoneda.v: *)

Check opyon_equiv_0gpd@{u1 u2 u3 u4 u5 u6 u7 u8 u9}.

(** Join/Core.v: *)

Check equiv_join_sym@{u1 u2 u3 u4}.

(** Join/JoinAssoc.v: *)

Check join_assoc@{u1 u2 u3 u4 u5 u6 u7 u8}.
