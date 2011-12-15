Ltac quantified_simple_match :=
  match goal with
    | |- forall x, ?Q x => idtac "Quantified simple match succeeded, found predicate " Q
    | _ => idtac "Quantified simple match failed."
  end.

Ltac quantified_second_order_match :=
  match goal with
    | |- forall x, @?Q x => idtac "Quantified second-order match succeeded, found predicate " Q
    | _ => idtac "Quantified second-order match failed."
  end.

Variable A : Type.
Variable P : A -> Type.

Goal forall x:A, P x.
  quantified_simple_match. (* succeeds *)
  quantified_second_order_match. (* succeeds *)
Abort.

Goal forall x:A, P x -> P x.
  quantified_simple_match.  (* fails, since [P x -> P x] is not literally written as the application of a predicate to P*)
  quantified_second_order_match. (* succeeds, generates [(fun x : A => P x -> P x)] *)
Abort.

Ltac open_simple_match x :=
  match goal with
    | |- ?Q x => idtac "Quantified simple match succeeded, found predicate " Q
    | _ => idtac "Quantified simple match failed."
  end.

Ltac open_second_order_match  x :=
  match goal with
    | |- @?Q x => idtac "Quantified second-order match succeeded, found predicate " Q
    | _ => idtac "Quantified second-order match failed."
  end.

Variable a:A.

Goal P a.
  open_simple_match a. (* succeeds *)
  open_second_order_match a. (* fails! I don’t understand why. *)
Abort.

Goal P a -> P a.
  quantified_simple_match.  (* fails *)
  quantified_second_order_match. (* fails!  Again, I don’t understand this. *)
Abort.
