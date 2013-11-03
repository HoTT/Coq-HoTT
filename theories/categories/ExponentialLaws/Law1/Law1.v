(** ** Laws about the terminal category *)
(** We prove:

    - x¹ ≅ x
    - 1ˣ ≅ 1
 *)
Require ExponentialLaws.Law1.Functors.
Require ExponentialLaws.Law1.Law.

Include ExponentialLaws.Law1.Functors.
Include ExponentialLaws.Law1.Law.
