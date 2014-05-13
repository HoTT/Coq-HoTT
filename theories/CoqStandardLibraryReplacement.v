(** * Replacements for broken things in the standard library. *)
(** We redefine a number of constants from the standard library, to eliminate [Prop] and make them universe polymorphic.  We maintain compatibility as much as possible, except where it conflicts with the above goals.  (We may later add "taking advantage of eta for records and primitive projections" to this list.) *)
Global Set Universe Polymorphism.
Global Set Asymmetric Patterns.
Local Set Implicit Arguments.
Local Set Record Elimination Schemes.

Module Export Coq.
  (** ** Type classes *)
  Module Export Relations.
    Module Export Relation_Definitions.
      Definition relation (A : Type) := A -> A -> Type.
    End Relation_Definitions.
  End Relations.

  Module Export Classes.
    Module Export RelationClasses.
      Class Reflexive {A} (R : relation A) :=
        reflexivity : forall x : A, R x x.

      Class Symmetric {A} (R : relation A) :=
        symmetry : forall x y, R x y -> R y x.

      Class Transitive {A} (R : relation A) :=
        transitivity : forall x y z, R x y -> R y z -> R x z.

      (** A [PreOrder] is both Reflexive and Transitive. *)
      Class PreOrder {A} (R : relation A) :=
        { PreOrder_Reflexive :> Reflexive R | 2 ;
          PreOrder_Transitive :> Transitive R | 2 }.

      Tactic Notation "etransitivity" open_constr(y) :=
        let R := match goal with |- ?R ?x ?z => constr:(R) end in
        let x := match goal with |- ?R ?x ?z => constr:(x) end in
        let z := match goal with |- ?R ?x ?z => constr:(z) end in
        refine (@transitivity _ R _ x y z _ _).

      Tactic Notation "etransitivity" := etransitivity _.

      (** We would like to redefine [symmetry], which is too smart for its own good, as follows:

<<
Ltac symmetry := refine (@symmetry _ _ _ _ _ _).
>>

But this gives "Error: in Tacinterp.add_tacdef: Reserved Ltac name symmetry.".  This might be fixed with https://coq.inria.fr/bugs/show_bug.cgi?id=3113.  For now, you can [apply symmetry] or [eapply symmetry].  (Note that we can get around this error message by using [Tactic Notation "symmetry"], but, confusingly, this tactic notation never gets called. *)
    End RelationClasses.
  End Classes.

  Module Export Init.
    Module Export Datatypes.
      (** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

      Inductive sum (A B:Type) : Type :=
      | inl : A -> sum A B
      | inr : B -> sum A B.

      Notation "x + y" := (sum x y) : type_scope.

      Arguments inl {A B} _ , [A] B _.
      Arguments inr {A B} _ , A [B] _.

      (** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

      Record prod (A B:Type) : Type := pair { fst : A; snd : B }.

      Add Printing Let prod.

      Notation "x * y" := (prod x y) : type_scope.
      Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

      Arguments pair {A B} _ _.
      Arguments fst {A B} _.
      Arguments snd {A B} _.

      Hint Resolve pair inl inr: core.
    End Datatypes.

    Module Export Specif.
      (** Subsets and Sigma-types *)

      (** [(sig A P)], or more suggestively [{x:A | P x}], denotes the subset
    of elements of the type [A] which satisfy the predicate [P].
    Similarly [(sig2 A P Q)], or [{x:A | P x & Q x}], denotes the subset
    of elements of the type [A] which satisfy both [P] and [Q]. *)

      (** [(sigT A P)], or more suggestively [{x:A & (P x)}] is a Sigma-type.
    Similarly for [(sigT2 A P Q)], also written [{x:A & (P x) & (Q x)}]. *)

      Record sigT A (P : A -> Type) := existT { projT1 : A; projT2 : P projT1 }.
      Inductive sigT2 (A:Type) (P Q:A -> Type) : Type :=
        existT2 : forall x:A, P x -> Q x -> sigT2 P Q.

      Notation sig := sigT (only parsing).
      Notation sig2 := sigT2 (only parsing).
      Notation exist := existT (only parsing).
      Notation exist2 := existT2 (only parsing).
      Notation proj1_sig := projT1 (only parsing).
      Notation proj2_sig := projT2 (only parsing).

      Arguments sigT (A P)%type.
      Arguments sigT2 (A P Q)%type.

      Notation "{ x  |  P }" := (sig (fun x => P)) : type_scope.
      Notation "{ x  |  P  & Q }" := (sig2 (fun x => P) (fun x => Q)) : type_scope.
      Notation "{ x : A  |  P }" := (sig (A:=A) (fun x => P)) : type_scope.
      Notation "{ x : A  |  P  & Q }" := (sig2 (A:=A) (fun x => P) (fun x => Q)) :
                                           type_scope.
      Notation "{ x : A  & P }" := (sigT (A:=A) (fun x => P)) : type_scope.

      Add Printing Let sigT.
      Add Printing Let sigT2.

      (** [sumbool] is a boolean type equipped with the justification of
    their value.  Since we don't care about [Prop], we use [Type].
    (Maybe we should use [hProp]?) *)

      Notation sumbool := sum (only parsing).
      Notation "{ A } + { B }" := (sumbool A B) (only parsing) : type_scope.
      Notation left := inl (only parsing).
      Notation right := inr (only parsing).

      (** [sumor] is an option type equipped with the justification of why
    it may not be a regular value *)

      Notation sumor := sum (only parsing).
      Notation "A + { B }" := (sumor A B) (only parsing) : type_scope.
      Notation inleft := inl (only parsing).
      Notation inright := inr (only parsing).
    End Specif.

    Module Export Logic.
      (********************************************************************)
      (** * Datatypes with zero and one element *)

      Notation False := Empty_set (only parsing).
      Notation False_rect := Empty_set_rect (only parsing).
      Notation False_rec := Empty_set_rec (only parsing).
      Notation False_ind := Empty_set_ind (only parsing).

      Notation True := unit (only parsing).
      Notation True_rect := unit_rect (only parsing).
      Notation True_rec := unit_rec (only parsing).
      Notation True_ind := unit_ind (only parsing).

      (** [not A], written [~A], is the negation of [A] *)
      Definition not (A:Type) := A -> False.

      Notation "~ x" := (not x) : type_scope.


      (** [and A B], written [A /\ B], is the conjunction of [A] and [B]

      [conj p q] is a proof of [A /\ B] as soon as
      [p] is a proof of [A] and [q] a proof of [B]

      [proj1] and [proj2] are first and second projections of a conjunction *)

      Notation and := prod (only parsing).
      Notation conj := pair (only parsing).
      Notation "A /\ B" := (and A B) (only parsing) : type_scope.
      Notation proj1 := fst (only parsing).
      Notation proj2 := snd (only parsing).

      (** [or A B], written [A \/ B], is the disjunction of [A] and [B] *)

      Notation or := sum (only parsing).
      Notation or_introl := inl (only parsing).
      Notation or_intror := inr (only parsing).
      Notation "A \/ B" := (or A B) : type_scope.

      (** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

      Definition iff (A B:Type) := (A -> B) /\ (B -> A).

      Notation "A <-> B" := (iff A B) : type_scope.

      (** * First-order quantifiers *)

      (** [ex P], or simply [exists x, P x], or also [exists x:A, P x],
    expresses the existence of an [x] of some type [A] in [Set] which
    satisfies the predicate [P].  This is existential quantification.

    [ex2 P Q], or simply [exists2 x, P x & Q x], or also
    [exists2 x:A, P x & Q x], expresses the existence of an [x] of
    type [A] which satisfies both predicates [P] and [Q].

    Universal quantification is primitively written [forall x:A, Q]. By
    symmetry with existential quantification, the construction [all P]
    is provided too.
       *)

      Notation ex := sigT (only parsing).
      Notation ex_intro := existT (only parsing).
      Notation ex2 := sigT2 (only parsing).
      Notation ex2_intro := existT2 (only parsing).

      (* Rule order is important to give printing priority to fully typed exists *)

      Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
                                          (at level 200, x binder, right associativity,
                                           format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
                                        : type_scope.

      Notation "'exists2' x , p & q" := (ex2 (fun x => p) (fun x => q))
                                          (at level 200, x ident, p at level 200, right associativity) : type_scope.
      Notation "'exists2' x : t , p & q" := (ex2 (fun x:t => p) (fun x:t => q))
                                              (at level 200, x ident, t at level 200, p at level 200, right associativity,
                                               format "'[' 'exists2'  '/  ' x  :  t ,  '/  ' '[' p  &  '/' q ']' ']'")
                                            : type_scope.

      Hint Resolve I conj or_introl or_intror : core.
      Hint Resolve ex_intro ex_intro2: core.
    End Logic.
  End Init.
End Coq.
