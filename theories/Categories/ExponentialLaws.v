(** * Exponential Laws *)
(** We want to have the following as subdirectories/modules, not at top level.  Unfortunately, namespacing in Coq is kind-of broken (see, e.g., https://coq.inria.fr/bugs/show_bug.cgi?id=3676), so we don't get the ability to rename subfolders by [Including] into other modules. *)
(** ** Laws about the initial category *)
(** *** [x⁰ ≅ 1] *)
(** *** [0ˣ ≅ 0] if [x ≠ 0] *)
Require ExponentialLaws.Law0.

(** ** Laws about the terminal category *)
(** *** [x¹ ≅ x] *)
(** *** [1ˣ ≅ 1] *)
Require ExponentialLaws.Law1.

(** ** The law that a sum in an exponent is a product *)
(** *** [yⁿ⁺ᵐ ≅ yⁿ × yᵐ] *)
Require ExponentialLaws.Law2.

(** ** The law that exponentiation distributes over product *)
(** *** [(y × z)ⁿ ≅ yⁿ × zⁿ] *)
Require ExponentialLaws.Law3.

(** ** Currying *)
(** *** [(yⁿ)ᵐ ≅ yⁿᵐ] *)
Require ExponentialLaws.Law4.


Require ExponentialLaws.Tactics.
Include ExponentialLaws.Tactics.
