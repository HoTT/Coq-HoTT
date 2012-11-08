Require Import ssreflect ssrfun ssrbool.
Require Import Paths (* Fibrations*).
(* assia : in fact we do not rely on the file aubout fibrations. *)

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
(* Gory detail you can safely skip:*)
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

(* This definition was already present in the original version of the *)
(* file. *)
Definition is_contr A := {x : A & forall y : A, y = x}.

(* If we knew that the contractible type is inhabited (which it is necessarily),*)
(* we could use the default inhabitant as the hub: *)
Definition contr_axiom (A : inhabType) := forall y : A, y = {elt A}. 

(* And know this is the way we craft an interface for contractible: a type *)
(* with an inhabitant, and a function providing paths from any point of the *)
(* space to this hub.*)
Record contr_class_of (A : Type) := ContrClass {
  contr_base :> is_inhab A;
  contr_mixin :> contr_axiom (InhabType _ contr_base)
}.

Record contrType := ContrPack {
  contr_sort :> Type;
  _ : contr_class_of contr_sort
}.

Section ContrTypeTechDefs.

Variable (T : Type) (cT : contrType).

Definition contr_class :=
  let: ContrPack _ c := cT return contr_class_of cT in c.

Definition contr_clone c of phant_id contr_class c := @ContrPack T c.

Definition contr_pack x (m : contr_axiom (InhabType T x)) :=
  fun (iT : inhabType) b2 & phant_id (inhab_class iT) b2 =>
  fun                  m' & phant_id m m' =>
    @ContrPack T (@ContrClass T b2 m').

Let xT := let: ContrPack T _ := cT in T.
Notation xclass := (contr_class : contr_class_of xT).

Definition contr_inhabType := @InhabPack cT xclass.

End ContrTypeTechDefs.

Notation hContr := contrType.
Notation ContrType T m := (@contr_pack T _ m _ _ id _ id).
Notation "[ 'hContr' 'of' T 'for' C ]" := (@inhab_clone T C _ idfun)
  (at level 0, format "[ 'hContr'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'hContr' 'of' T ]" := (@inhab_clone T _ _ idfun)
  (at level 0, format "[ 'hContr'  'of'  T ]") : form_scope.
Coercion contr_inhabType : hContr >-> inhabType.
Canonical contr_inhabType.

Section ContrTheory.

(* The inhab slice (we call it a mixin) of a type which satisfies is_contr *)
Coercion inhab_elt_of_is_contr A (cA : is_contr A) : is_inhab A := projT1 cA.

(* How to obtain a contr slice from an inhabType which satisfies is_contr *)
Lemma ContrMixin (A : inhabType) (cA : is_contr A) : contr_axiom A.
Proof. by case: cA => [x Hx] y; rewrite [y]Hx [{elt _}]Hx. Qed.

Lemma hContrE (A : hContr) : all_equal_to {elt A}.
Proof. by case: A => A /= [hA h] y; rewrite (h y). Qed.

Lemma hContrP (A : hContr) (x : A) : {elt A} = x.
Proof. by rewrite hContrE. Qed.

(* Was : contr_path *)
Lemma hContr_path (A : hContr) (x y : A) : x = y.
Proof. apply: identity_trans (hContrP y); symmetry; exact: hContrP. Qed.

(* Was: contr_path2 *)
Lemma hContr_irrelevance (A : hContr) {x y : A} (p q : x = y) : p = q.
Proof.
suff {p q} cst t  : t = (hContrP x)^-1 * (hContrP y)  by rewrite (cst p) (cst q).
by case t; rewrite mulVp.
Qed.

Section EqHContr.

Variables (A : hContr) (x y : A).

(* Was: contr_pathcontr *)
Lemma eq_hContr_is_contr : is_contr (x = y).
Proof. by rewrite !hContrE; exists 1 => p; apply: hContr_irrelevance. Qed.

Canonical eq_hContr_inhabType := InhabType (x = y) eq_hContr_is_contr.
 
Definition eq_hContr_contrMixin := ContrMixin eq_hContr_is_contr.

Canonical eq_hContr_hContr := ContrType (x = y) eq_hContr_contrMixin.

(* Was: pathspace_contr *)
Lemma sig_eqr_hContr_is_contr : is_contr {y : A & x = y}.
Proof. exists (existT _ x 1); case=> [z p]; case p; exact 1. Qed.


(* Was: pathspace_contr_opp *)
Lemma sig_eql_hContr_is_contr : is_contr {y : A & y = x}.
Proof.
exists (existT (fun y => y = x) _ 1). 
case=> [z p]; case p; exact 1. 
Qed.

(* BUT we cannot declare canonical structure on these sigma types *)
(* because they expose the same value (A) in from of the sigT *)
(* projection in the unification problem triggering the inference of *)
(* canonical instance. And the CS mechanism*)
(* does not allow to register several instances of a same interface *)
(* keyed by the same value. *)

End EqHContr.

(* Was: unit_contr *)
Lemma unit_contrMixin : contr_axiom [inhabType of unit]. Proof. by case. Qed.

Canonical unit_hContr := ContrType unit unit_contrMixin.

End ContrTheory.

Arguments hContrP {A} _.


