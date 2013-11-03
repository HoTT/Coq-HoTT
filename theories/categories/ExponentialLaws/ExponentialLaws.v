Module Law0.
  (** ** Laws about the initial category *)
  (** We prove:

      - x⁰ ≅ 1
      - 0ˣ ≅ 0 if x ≠ 0
  *)
  Require ExponentialLaws.Law0.
  Include ExponentialLaws.Law0.
End Law0.

Module Law1.
  (** ** Laws about the terminal category *)
  (** We prove:

      - x¹ ≅ x
      - 1ˣ ≅ 1
   *)
  Require ExponentialLaws.Law1.Law1.
  Include ExponentialLaws.Law1.Law1.
End Law1.

Module Law2.
  (** ** The law that a sum in an exponent is a product *)
  (** We prove:

      - yⁿ⁺ᵐ ≅ yⁿ × yᵐ
   *)
  Require ExponentialLaws.Law2.Law2.
  Include ExponentialLaws.Law2.Law2.
End Law2.

Module Law3.
  (** ** The law that exponentiation distributes over product *)
  (** We prove:

      - (y × z)ⁿ ≅ yⁿ × zⁿ
   *)
  Require ExponentialLaws.Law3.Law3.
  Include ExponentialLaws.Law3.Law3.
End Law3.

Module Law4.
  (** ** Currying *)
  (** We prove:

      - (yⁿ)ᵐ ≅ yⁿᵐ
   *)
  Require ExponentialLaws.Law4.Law4.
  Include ExponentialLaws.Law4.Law4.
End Law4.
