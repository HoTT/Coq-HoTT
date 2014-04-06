(** * Grothendieck Construction *)
(** ** of a functor to Set *)
Module ToSet.
  Require Grothendieck.ToSet.
  Include Grothendieck.ToSet.
End ToSet.

(** ** of a pseudofunctor to Cat *)
Module PseudofunctorToCat.
  Require Grothendieck.PseudofunctorToCat.
  Include Grothendieck.PseudofunctorToCat.
End PseudofunctorToCat.

(** ** of a functor to Cat *)
Module ToCat.
  Require Grothendieck.ToCat.
  Include Grothendieck.ToCat.
End ToCat.
