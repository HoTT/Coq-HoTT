From HoTT.Modalities Require Import Localization.

(** [ExtendableAlong_Over] takes 5 universe parameters:
    - size of A
    - size of B
    - size of C
    - size of D
    - size of result (>= A,B,C,D) *)
Check ExtendableAlong_Over@{a b c d m}.

(** Universe parameters are the same as for [ExtendableAlong_Over]. *)
Check ooExtendableAlong_Over@{a b c d m}.
