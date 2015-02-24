Require Import HoTT.

Fail Check Type0 : Type0.
Check Susp nat : Type0.
Fail Check Susp Type0 : Type0.

Fail Check (fun (P : interval -> Type) (a : P Interval.zero) (b : P Interval.one)
                (p p' : seg # a = b)
            => idpath : interval_ind P a b p = interval_rect P a b p').

Local Open Scope nat_scope.
Fail Check Lift nat : Type0.
Check 1 : Lift nat.

Check lift'@{i j}.
Check lower'@{i j}.
Check isequiv_lift'@{i j}.

(** Check that [ispointed_susp] doesn't require just a [Set] *)
Check (fun A : Type => _ : IsPointed (Susp A)).
Check (@ispointed_susp Type).
Check (@ispointed_susp Set).

(** Check that nested sigma-type notation didn't get clobbered by surreal cuts *)
Check ({ l : Unit & { n : Unit & Unit }}).
