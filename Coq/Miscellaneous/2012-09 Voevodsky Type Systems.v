(** Notes from Voevodsky’s series of lectures on Type Systems 
    Intended to be read in an h-set interpretation, i.e. with
    proof-irrelevant equality. *)

(* Terminology: “category” means a category up to equivalence;
   but we want to consider “contextual categories” up to 
   *isomorphism*, so we call them C-structures instead. *)

Record Cat := mkCat
  { Cat_ob : Set ;
    Cat_mor : Cat_ob -> Cat_ob -> Set }.

Coercion Cat_ob : Cat >-> Sortclass.

Record CStructure := mkCStrux
  { C_cat : Cat ;
    C_length : C_cat -> nat ;
    C_pt : C_cat ;
    C_ft : C_cat -> C_cat ;
    C_proj : forall X:C_cat, Cat_mor C_cat X (C_ft X) }.

(* OK, live coq'ing is not a feasible goal.  Dammit…  OK; I know what a contextual category is… *)

(* Note on the definition of B(X), after the definition of a contextual cat:

given as B(X) = { Y | ft Y = X }.

for X = pt, presumably we want B(X) to exclude pt itself.

(Or else we take the approach that ft(X) is defined only when l(X) > 0. *)