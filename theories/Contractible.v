Require Import ssreflect ssrfun ssrbool eqtype.
Require Import Paths (* Fibrations*).
(* assia : in fact we do not rely on the file about fibrations. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import PathNotations.
Open Scope path_scope.

(** A space [A] is contractible if there is a point [x : A] and a
   (pointwise) homotopy connecting the identity on [A] to the constant
   map at [x].  Thus an element of [is_contr A] is a pair whose
   first component is a point [x] and the second component is a
   pointwise retraction of [A] to [x]. *)

(* assia : contractible means two things that are encapsulated in the sigma*)
(* type : a witness of the fiber being inhabited and a function which builds*)
(* the path connecting an arbitrary inhabitant of the contractible type*)
(* to the previous witness. We are going to use a record instead of a sigma*)
(* type, so that the access to each of these information gets eased : we will*)
(* no more need to traverse too many boxes to access the datas we want to*)
(* work with.*)
(* Also, this will allow us to benefit from some type inference mechanism *)
(* in order to automate proof that a certain type in contractible.*)

(* But first we start with a small gadget which we hope will prove convenient*)
(* in the sequel: a structure for inhabited types. The purpose of this structure*)
(* is this time only to have the system keep track for oureselves that, given *)
(* that we already have inhabited some types, more complex ones constructed *)
(* from these ones remain inhabited. This is only very preliminary and we should *)
(* feel free to remove it but it seems to be a natural need. However, we use this*)
(* simple example of structure to provide some hints about canonical structures*)

(* Being inhabited is just displaying a witness inhabitant of the type *)

Definition is_inhab (A : Type) : Type := A.

(* Now we build an interface for inhabited types. It is just a pair of the type*)
(* together with the inhabitant. One can access to the type using the *)
(* inhab_sort field of the record, and the witness itself is stored in the *)
(* second projection. *)
(* Gory details you can safely skip:*)
(* It can be surprising that we do not give a name to this second projection.*)
(* We actually do not because it will never be used to trigger canonical *)
(* structure (CS) inference but would be stored in the CS database anyway if *)
(* named it, which would pollute both the database and the answer displayed by*)
(* the "Print Canonical Projections" vernac command. But it is very simple to*)
(* have a posterior definition of this function which is a simple case analysis*)
(* See the definition of inhab_class below.*)

Record inhabType := InhabPack {
  inhab_sort :> Type;
  _ : is_inhab inhab_sort
}.

(* Definition inhab_pack T c := @InhabPack T c T. *)

(* let: InhabPack _ x  := A is an ssreflect syntax for match A with *)
(* | InhabPack _ x since we have a single constructor for the inductive*)
(* type of A *)

Definition inhab_class (A : inhabType) : is_inhab A :=
  let: InhabPack _ x := A in x.

(* Now we do something slightly more complicated. The aim of the game *)
(* is to work with say the type unit and never to see typset 'unit_inhabType' *)
(* (= the instance of inhabType with unit as inhab_sort) *)
(* as soon as we have proved that unit can be equipped with such a structure*)
(* of inhabType. Hence we need to have Coq guess that it has an instance*)
(* of inhabType stored in its database even if we never provide by hand*)
(* this 'unit_inhabType' instance (or whatever it may be called) but ony 'unit'.*)
(* But how to build a function which, when given only 'unit' as argument*)
(* can provide the canonical witness declared in the instance of inhabType*)
(* we have stored? We use a very generic trick here, called phantom type*)
(* We first define a new version of inhab_class, with a weird second argument*)
(* which seems useless at first sight.*)

Definition elt (A : inhabType) (phA : phant (inhab_sort A)) : inhab_sort A := inhab_class A.

Arguments elt : simpl never.

(* Now this is the function which does the job we wanted : when typing the term*)
(* {elt unit}, which de-sugars to (@elt _ (Phant unit)), Coq has to unify the *)
(* type of (Phant unit) which is (phant unit) with a type of the form *)
(* phant (inhab_sort ?) as prescribed by the definition of elt and the type of its *)
(* second argument. And eventually the solution of this problem should go in the*)
(* hole we left for the first argument of elt in (@elt _ (Phant unit)) *)
(* So now Coq faces the unification problem (unit = inhab_sort ?) and this is *)
(* exactly the shape of problems solved by CS, coq looks up in its databases and *)
(* finds the unit_inhabType we have once stored there, inserts it at the ? place *)
(* and we are done.*)

Notation "{elt A }" := (@elt _ (Phant A)) (format "{elt  A }").
Notation "[ 'inhabType' 'of' T 'for' C ]" := (@InhabPack T C)
  (at level 0, format "[ 'inhabType'  'of'  T  'for'  C ]") : form_scope.

(* We can use a similar trick if we really want to retrieve an instance of inhabType*)
(* for a certain type in a context where no natural unification problem can *)
(* trigger the inference*)

Definition inhab_clone T (iT : inhabType) :=
  fun (x : is_inhab T) & (iT -> T)
      & phant_id (@InhabPack T x) iT => @InhabPack T x.

Notation "[ 'inhabType' 'of' T ]" := (@inhab_clone T _ _ idfun id)
  (at level 0, format "[ 'inhabType'  'of'  T ]") : form_scope.

(* Just for name policy consistency reasons *)
Notation InhabType T c := (@InhabPack T c).

(* The first obvious instance is unit *)
Canonical unit_inhabType := InhabType unit tt. 

(* Sanity check *)
Check ({elt unit} : unit).

(* The product of two inhabited types is inhabited. *)
Canonical prod_inhabType (A B : inhabType) := 
  InhabType (A * B)%type (inhab_class A, inhab_class B).

(* Sanity check *)
Check ({elt (unit * unit * (unit * unit))%type}).

Record is_contr (A : Type) := IsContr {
  contr_elt : A;
  contr_eltE : forall a : A, contr_elt = a
}.

Arguments contr_eltE {A} i a.
Arguments contr_elt {A} i.

Lemma is_contr_eq (A : Type) : is_contr A -> forall x y : A, x = y.
Proof. by move=> [a Ha] x y; rewrite -[x]Ha -[y]Ha. Qed.

Lemma is_contrE (A : inhabType) : is_contr A -> all_equal_to {elt A}.
Proof. by move=> A_is_contr a; apply: is_contr_eq. Qed.

Lemma inhab_contr (A : inhabType) : (forall x, {elt A} = x) -> is_contr A.
Proof. exact: IsContr. Qed. (* Cyril: move/IsContr does not work, why ???? *) 

Lemma unit_is_contr : is_contr unit. Proof. by exists tt; case. Qed.

Definition UIP (A : Type) := forall (x y : A) (p q : x = y), p = q.

Section ContrTheory.

Variables (A : Type).
Hypothesis A_is_contr : is_contr A.

(* Was: contr_path2 *)
Lemma is_contr_UIP :  UIP A.
Proof.
move=> x y p q; have cE := contr_eltE A_is_contr.
suff {p q} cst t : t = (cE x)^-1 * (cE y) by rewrite [p]cst [q]cst.
by case t; rewrite mulVp.
Qed.

Variables (x y : A).

(* Was: contr_pathcontr *)
Lemma is_contr_eq_is_contr : is_contr (x = y).
Proof. rewrite -[y](is_contr_eq _ x) //; exists 1; exact: is_contr_UIP. Qed.

(* Was: pathspace_contr *)
Lemma is_contr_sig_eqr_is_contr : is_contr {y : A & x = y}.
Proof. exists (existT _ x 1); case=> [z p]; case p; exact 1. Qed.


(* Was: pathspace_contr_opp *)
Lemma is_contr_sig_eql_is_contr : is_contr {y : A & y = x}.
Proof.
exists (existT (fun y => y = x) _ 1). 
case=> [z p]; case p; exact 1. 
Qed.

End ContrTheory.

Definition funext_dep := forall A P (B1 B2 : forall a : A, P a), 
  (forall x, B1 x = B2 x) -> B1 = B2.

Section FunExtImpliesIsContrIsContr.
 
Variable A : Type.
Hypothesis A_is_contr : is_contr A.

Hypothesis FexDep: funext_dep.

Lemma is_contr_is_contr : is_contr (is_contr A).
Proof.
apply: (@IsContr _ A_is_contr) => [[a1 cA1]].
case: A_is_contr => a2. rewrite -[a2]cA1 => cA2.
apply resp.
apply: FexDep=> ?; exact: is_contr_UIP.
Qed.

End FunExtImpliesIsContrIsContr.