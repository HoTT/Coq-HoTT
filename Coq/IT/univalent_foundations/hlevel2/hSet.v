(** * Generalities on [ hSet ] .  Vladimir Voevodsky. Feb. - Sep. 2011 

In this file we introduce the type [ hSet ] of h-sets i.e. of types of h-level 2 as well as a number of constructions such as type of (monic) subtypes, images, surjectivity etc. which, while they formally apply to functions between arbitrary types actually only depend on the behavior of the function on the sets of connected componenets of these types. 

While it is possible to write a part of this file in a form which does not require RR1 it seems like a waste of effort since it would require to repeat a lot of things twice. Accordingly we assume RR1 from the start in dealing with sets. The drawback is that all the subsequent files will not compile at the moment without the Type in Type patch.

*)



(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)


(** Imports *)

Require Export hProp .


(** ** The type of sets i.e. of types of h-level 2 in [ UU ] *) 

Definition hSet:= total2 (fun X : UU => isaset X) .
Definition hSetpair := tpair (fun X : UU => isaset X).
Definition pr1hSet:= @pr1 UU (fun X : UU => isaset X) : hSet -> Type.
Coercion pr1hSet: hSet >-> Sortclass.

Definition eqset { X : hSet } ( x x' : X ) : hProp := hProppair _ ( pr2 X x x' ) . 

Definition setproperty ( X : hSet ) := pr2 X . 

Definition setdirprod ( X Y : hSet ) : hSet .
Proof . intros . split with ( dirprod X Y ) . apply ( isofhleveldirprod 2 ) .  apply ( pr2 X ) . apply ( pr2 Y ) . Defined . 

(** [ hProp ] as a set *)

Definition hPropset : hSet := tpair _ hProp isasethProp .  
Canonical Structure hPropset. 


(** Booleans as a set *)

Definition boolset : hSet := hSetpair bool isasetbool .
Canonical Structure boolset .  


(** ** Types [ X ] which satisfy " weak " axiom of choice for all families [ P : X -> UU0 ] 

Weak axiom of choice for [ X ] is the condition that for any family [ P : X -> UU0 ] over [ X ] such that all members of the family are inhabited the space of sections of the family is inhabited . Equivalently one can formulate it as an assertion that for any surjection ( see below ) [ p : Y -> X ] the space of sections of this surjection i.e. functions [ s : X -> Y ] together with a homotopy from [ funcomp s p ] to [ idfun X ] is inhabited . It does not provide a choice of a section for such a family or a surjection . In topos-theoretic semantics this condition corresponds to " local projectivity " of [ X ] . It automatically holds for the point [ unit ] but need not hold for sub-objects of [ unit ] i.e. for types of h-level 1 ( propositions ) . In particular it does not have to hold for general types with decidable equality . 

Intuition based on standard univalent models suggests that any type satisfying weak axiom of choice is a set . Indeed it seems to be possible to show that if both a type and the set of connected components of this type ( see below ) satisfy weak  axiom of choice then the type is a set . In particular , if one imposes weak axiom of choice for sets as an axiom then it would follow that every type satisfying weak axiom of choice is a set . I do not know however if there are models which would validate a possibility of types other than sets to satisfy weak axiom of choice . 


*)

Definition ischoicebase_uu1 ( X : UU0 ) := forall P : X -> UU0 , ( forall x : X , ishinh ( P x ) ) -> ishinh ( forall x : X , P x ) .

Lemma isapropischoicebase ( X : UU0 ) : isaprop ( ischoicebase_uu1 X ) .  (** Uses RR1 *)
Proof .  intro . apply impred . intro P .  apply impred . intro fs . apply ( pr2 ( ishinh _ ) ) .  Defined . 

Definition ischoicebase ( X : UU0 ) : hProp := hProppair _ ( isapropischoicebase X ) . 


Lemma ischoicebaseweqf { X Y : UU0 } ( w : weq X Y ) ( is : ischoicebase X ) : ischoicebase Y .
Proof . intros . unfold ischoicebase . intros Q fs . apply ( hinhfun ( invweq ( weqonsecbase Q w ) ) ) .   apply ( is ( funcomp w Q ) ( fun x : X => fs ( w x ) ) ) .  Defined . 

Lemma ischoicebaseweqb { X Y : UU0 } ( w : weq X Y ) ( is : ischoicebase Y ) : ischoicebase X .
Proof . intros . apply ( ischoicebaseweqf ( invweq w ) is ) . Defined . 

Lemma ischoicebaseunit : ischoicebase unit .
Proof . unfold ischoicebase . intros P fs .  apply ( hinhfun ( tosecoverunit P ) ) .  apply ( fs tt ) .  Defined .

Lemma ischoicebasecontr { X : UU0 } ( is : iscontr X ) : ischoicebase X .
Proof . intros . apply ( ischoicebaseweqb ( weqcontrtounit is )  ischoicebaseunit ) . Defined . 

Lemma ischoicebaseempty : ischoicebase empty .
Proof . unfold ischoicebase . intros P fs .  apply ( hinhpr _ ( fun x : empty => fromempty x ) ) .  Defined .

Lemma ischoicebaseempty2 { X : UU0 } ( is : neg X ) : ischoicebase X .
Proof . intros . apply ( ischoicebaseweqb ( weqtoempty is ) ischoicebaseempty ) . Defined .

Lemma ischoicebasecoprod { X Y : UU0 } ( isx : ischoicebase X ) ( isy : ischoicebase Y ) :  ischoicebase ( coprod X Y ) .
Proof . intros .  unfold ischoicebase .  intros P fs .  apply ( hinhfun ( invweq ( weqsecovercoprodtoprod P ) ) ) .  apply hinhand . apply ( isx _ ( fun x : X => fs ( ii1 x ) ) ) . apply ( isy _ ( fun y : Y => fs ( ii2 y ) ) ) .  Defined . 








(** ** The type of monic sybtypes of a type (subsets of the set of connected components) *)


(** *** Genneral definitions *)

Definition hsubtypes ( X : UU0 ) :=  X -> hProp .
Identity Coercion id_hsubtypes :  hsubtypes >-> Funclass . 
Definition carrier { X : UU0 } ( A : hsubtypes X ) := total2 A.
Coercion carrier : hsubtypes >-> Sortclass. 
Definition carrierpair { X : UU0 } ( A : hsubtypes X ) := tpair A.
Definition pr1carrier { X:UU0 } ( A : hsubtypes X ) := @pr1 _ _  : carrier A -> X .

Lemma isinclpr1carrier { X : UU0 } ( A : hsubtypes X ) : isincl ( @pr1carrier X A ) .
Proof . intros . apply ( isinclpr1 A ( fun x : _ => pr2 ( A x ) ) ) . Defined . 

Lemma isasethsubtypes (X:UU0): isaset (hsubtypes X).
Proof. intro . change ( isofhlevel 2 ( hsubtypes X ) ) .  apply impred . intro. apply isasethProp. Defined.

Definition totalsubtype ( X : UU0 ) : hsubtypes X := fun x => htrue .

Definition weqtotalsubtype ( X : UU0 ) : weq ( totalsubtype X ) X .
Proof . intro . apply weqpr1 .   intro . apply iscontrunit .  Defined . 


(** *** Direct product of two subtypes *)

Definition subtypesdirprod { X Y : UU0 } ( A : hsubtypes X ) ( B : hsubtypes Y ) : hsubtypes ( dirprod X Y ) := fun xy : _ => hconj ( A ( pr1 xy ) ) ( B ( pr2 xy ) ) .

Definition fromdsubtypesdirprodcarrier { X Y : UU0 } ( A : hsubtypes X ) ( B : hsubtypes Y ) ( xyis : subtypesdirprod A B ) : dirprod A B .
Proof . intros . set ( xy := pr1 xyis ) . set ( is := pr2 xyis ) .  set ( x := pr1 xy ) . set ( y := pr2 xy ) . simpl in is . simpl in y . apply ( dirprodpair ( tpair A x ( pr1 is ) ) ( tpair B y ( pr2 is ) ) ) . Defined .

Definition tosubtypesdirprodcarrier { X Y : UU0 } ( A : hsubtypes X ) ( B : hsubtypes Y ) ( xisyis : dirprod A B ) : subtypesdirprod A B . 
Proof . intros . set ( xis := pr1 xisyis ) . set ( yis := pr2 xisyis ) . set ( x := pr1 xis ) . set ( isx := pr2 xis ) . set ( y := pr1 yis ) . set ( isy := pr2 yis ) . simpl in isx . simpl in isy . apply ( tpair ( subtypesdirprod A B ) ( dirprodpair x y ) ( dirprodpair isx isy ) ) .  Defined .  

Lemma weqsubtypesdirprod { X Y : UU0 } ( A : hsubtypes X ) ( B : hsubtypes Y ) : weq ( subtypesdirprod A B ) ( dirprod A B ) .
Proof . intros .  set ( f := fromdsubtypesdirprodcarrier A B ) . set ( g :=  tosubtypesdirprodcarrier A B ) . split with f .
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro a . destruct a as [ xy is ] . destruct xy as [ x y ] . destruct is as [ isx isy ] . apply idpath . 
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro a . destruct a as [ xis yis ] . destruct xis as [ x isx ] . destruct yis as [ y isy ] . apply idpath .
apply ( gradth _ _ egf efg ) . Defined .  

Lemma ishinhsubtypesdirprod  { X Y : UU0 } ( A : hsubtypes X ) ( B : hsubtypes Y ) ( isa : ishinh A ) ( isb : ishinh B ) : ishinh ( subtypesdirprod A B ) .  
Proof . intros . apply ( hinhfun ( invweq ( weqsubtypesdirprod A B ) ) ) .  apply hinhand .  apply isa . apply isb . Defined . 



(** *** A a subtype of with a paths between any every two elements is an h-prop. *)


Lemma isapropsubtype { X : UU0 } ( A : hsubtypes X ) ( is : forall ( x1 x2 : X ) , A x1 -> A x2 -> paths x1 x2 ) : isaprop ( carrier A ) . 
Proof. intros.  apply invproofirrelevance. intros x x' .  
assert ( isincl ( @pr1 _ A )).  apply isinclpr1. intro x0. apply ( pr2 ( A x0 )).  
apply ( invmaponpathsincl ( @pr1 _ A ) X0 ). destruct x as [ x0 is0 ]. destruct x' as [ x0' is0' ] . simpl. apply is. assumption. assumption. Defined. 


(* End of " the type of monic subtypes of a type " . *)







(** ** Relations on types ( or equivalently relations on the sets of connected components) *)


(** *** Relations and boolean relations *)

Definition hrel ( X : UU0 ) := X -> X -> hProp.
Identity Coercion idhrel : hrel >-> Funclass .  

Definition brel ( X : UU0 ) := X -> X -> bool .
Identity Coercion idbrel : brel >-> Funclass . 

(** *** Standard properties of relations *)



Definition istrans { X : UU0 } ( R : hrel X ) := forall ( x1 x2 x3 : X ) ( r12 : R x1 x2 ) ( r23 : R x2 x3 ) , R x1 x3.

Definition isrefl { X : UU0 } ( R : hrel X ) := forall x : X , R x x.

Definition issymm { X : UU0 } ( R : hrel X ) := forall ( x1 x2 : X ) ( r12 : R x1 x2 ) , R x2 x1 .

Definition ispo { X : UU0 } ( R : hrel X ) := dirprod ( istrans R ) ( isrefl R ) .

Definition iseqrel { X : UU0 } ( R : hrel X ) := dirprod ( ispo R ) ( issymm R ) .
Definition iseqrelconstr { X : UU0 } { R : hrel X } ( trans0 : istrans R ) ( refl0 : isrefl R ) ( symm0 : issymm R ) : iseqrel R := dirprodpair ( dirprodpair trans0 refl0 ) symm0 .

Definition isirrefl { X : UU0 } ( R : hrel X ) := forall  x : X , neg ( R x x ) . 

Definition isasymm { X : UU0 } ( R : hrel X ) := forall ( x1 x2 : X ) ( r12 : R x1 x2 ) ( r21 : R x2 x1 ) , empty . 

Definition iscoasymm { X : UU0 } ( R : hrel X ) := forall x1 x2 , neg ( R x1 x2 ) -> R x2 x1 .

Definition istotal { X : UU0 } ( R : hrel X ) := forall x1 x2 , hdisj ( R x1 x2 ) ( R x2 x1 ) .

Definition iscotrans { X : UU0 } ( R : hrel X ) := forall x1 x2 x3 , R x1 x3 -> hdisj ( R x1 x2 ) ( R x2 x3 ) .

Definition isdecrel { X : UU0 } ( R : hrel X ) := forall x1 x2 , coprod ( R x1 x2 ) ( neg ( R x1 x2 ) ) .

Definition isnegrel { X : UU0 } ( R : hrel X ) := forall x1 x2 , neg ( neg ( R x1 x2 ) ) -> R x1 x2 .

(** Note that the property of being (co-)antisymmetric is different from other properties of relations which we consider due to the presence of [ paths ] in its formulation . As a consequence it behaves differently relative to the quotients of types - the quotient relation can be (co-)antisymmetric while the original relation was not . *) 

Definition isantisymm { X : UU0 } ( R : hrel X ) := forall ( x1 x2 : X ) ( r12 : R x1 x2 ) ( r21 : R x2 x1 ) , paths x1 x2 .

Definition isantisymmneg { X : UU0 } ( R : hrel X ) := forall ( x1 x2 : X ) ( nr12 : neg ( R x1 x2 ) ) ( nr21 : neg ( R x2 x1 ) ) , paths x1 x2 .

Definition iscoantisymm { X : UU0 } ( R : hrel X ) := forall x1 x2 , neg ( R x1 x2 ) -> coprod ( R x2 x1 ) ( paths x1 x2 ) .

(** Note that the following condition on a relation is different from all the other which we have considered since it is not a property but a structure, i.e. it is in general unclear whether [ isaprop ( neqchoice R ) ] is provable. *)

Definition neqchoice { X : UU0 } ( R : hrel X ) := forall x1 x2 , neg ( paths x1 x2 ) -> coprod ( R x1 x2 ) ( R x2 x1 ) .



(** *** Elementary implications between properties of relations *)

Lemma istransandirrefltoasymm { X : UU0 } { R : hrel X } ( is1 : istrans R ) ( is2 : isirrefl R ) : isasymm R .
Proof . intros .  intros a b rab rba . apply ( is2 _ ( is1 _ _ _ rab rba ) ) .  Defined . 

Lemma istotaltoiscoasymm { X : UU0 } { R : hrel X } ( is : istotal R ) : iscoasymm R .
Proof . intros .  intros x1 x2 . apply ( hdisjtoimpl ( is _ _ ) ) . Defined . 

Lemma isdecreltoisnegrel { X : UU0 } { R : hrel X } ( is : isdecrel R ) : isnegrel R .
Proof . intros .  intros x1 x2 .  destruct ( is x1 x2 ) as [ r | nr ] . intro . apply r . intro nnr . destruct ( nnr nr ) .  Defined . 

Lemma isantisymmnegtoiscoantisymm { X : UU0 } { R : hrel X } ( isdr : isdecrel R ) ( isr : isantisymmneg R ) : iscoantisymm R . 
Proof . intros . intros x1 x2 nrx12 . destruct ( isdr x2 x1 ) as [ r | nr ] . apply ( ii1 r ) .  apply ii2 . apply ( isr _ _ nrx12 nr ) .  Defined . 



(** *** Standard properties of relations and logical equivalences *)

Definition hrellogeq { X : UU0 } ( L R : hrel X ) := forall x1 x2 , ( L x1 x2 <-> R x1 x2 ) .

Definition istranslogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : istrans L ) : istrans R .
Proof . intros . intros x1 x2 x3 r12 r23 .   apply ( ( pr1 ( lg _ _ ) ) ( isl _ _ _ ( ( pr2 ( lg _ _ ) ) r12 ) ( ( pr2 ( lg _ _ ) ) r23 ) ) ) . Defined . 

Definition isrefllogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : isrefl L ) : isrefl R . 
Proof . intros . intro x . apply ( pr1 ( lg _ _ ) ( isl x ) ) .  Defined . 

Definition issymmlogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : issymm L ) : issymm R . 
Proof . intros . intros x1 x2 r12 . apply ( pr1 ( lg _ _ ) ( isl _ _ ( pr2 ( lg _ _ ) r12 ) ) ) . Defined .  

Definition ispologeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : ispo L ) : ispo R . 
Proof . intros . apply ( dirprodpair ( istranslogeqf lg ( pr1 isl ) ) ( isrefllogeqf lg ( pr2 isl ) ) ) . Defined . 

Definition iseqrellogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : iseqrel L ) : iseqrel R . 
Proof . intros . apply ( dirprodpair ( ispologeqf lg ( pr1 isl ) ) ( issymmlogeqf lg ( pr2 isl ) ) ) . Defined . 

Definition isirrefllogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : isirrefl L ) : isirrefl R .
Proof . intros . intros x r . apply ( isl _ ( pr2 ( lg x x ) r ) ) . Defined .   

Definition isasymmlogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : isasymm L ) : isasymm R . 
Proof . intros . intros x1 x2 r12 r21 . apply ( isl _ _ ( pr2 ( lg _ _ ) r12 ) ( pr2 ( lg _ _ ) r21 ) )   . Defined . 

Definition iscoasymmlogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : iscoasymm L ) : iscoasymm R . 
Proof . intros . intros x1 x2 r12 . apply ( ( pr1 ( lg _ _ ) ) ( isl _ _ ( negf ( pr1 ( lg _ _ ) ) r12 ) ) ) . Defined . 

Definition istotallogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : istotal L ) : istotal R . 
Proof . intros . intros x1 x2 . set ( int := isl x1 x2 ) .  generalize int . clear int . simpl .  apply hinhfun .  apply ( coprodf ( pr1 ( lg x1 x2 ) ) ( pr1 ( lg x2 x1 ) ) ) .  Defined . 

Definition iscotranslogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : iscotrans L ) : iscotrans R . 
Proof . intros . intros x1 x2 x3 r13 . set ( int := isl x1 x2 x3 ( pr2 ( lg _ _ ) r13 ) ) .  generalize int . clear int . simpl .  apply hinhfun .  apply ( coprodf ( pr1 ( lg x1 x2 ) ) ( pr1 ( lg x2 x3 ) ) ) .  Defined .

Definition isdecrellogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : isdecrel L ) : isdecrel R . 
Proof . intros . intros x1 x2 . destruct ( isl x1 x2 ) as [ l | nl ] . apply ( ii1 ( pr1 ( lg _ _ ) l ) ) . apply ( ii2 ( negf ( pr2 ( lg _ _ ) ) nl ) ) . Defined . 

Definition isnegrellogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : isnegrel L ) : isnegrel R . 
Proof . intros . intros x1 x2 nnr . apply ( ( pr1 ( lg _ _ ) ) ( isl _ _ ( negf ( negf ( pr2 ( lg _ _ ) ) ) nnr ) ) ) . Defined . 

Definition isantisymmlogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : isantisymm L ) : isantisymm R .
Proof . intros . intros x1 x2 r12 r21 . apply ( isl _ _ ( pr2 ( lg _ _ ) r12 ) ( pr2 ( lg _ _ ) r21 ) )   . Defined .  

Definition isantisymmneglogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : isantisymmneg L ) : isantisymmneg R .
Proof . intros . intros x1 x2 nr12 nr21 . apply ( isl _ _ ( negf ( pr1 ( lg _ _ ) ) nr12 ) ( negf ( pr1 ( lg _ _ ) ) nr21 ) )   . Defined .  

Definition iscoantisymmlogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : iscoantisymm L ) : iscoantisymm R .
Proof . intros . intros x1 x2 r12 . set ( int := isl _ _ ( negf ( pr1 ( lg _ _ ) ) r12 ) ) . generalize int .  clear int .  simpl . apply ( coprodf ( pr1 ( lg _ _ ) ) ( idfun _ ) ) . Defined . 

Definition neqchoicelogeqf { X : UU0 } { L R : hrel X } ( lg : forall x1 x2 , L x1 x2 <-> R x1 x2 ) ( isl : neqchoice L ) : neqchoice R .
Proof . intros . intros x1 x2  ne .  apply ( coprodf ( pr1 ( lg x1 x2 ) ) ( pr1 ( lg x2 x1 ) ) ( isl _ _ ne ) ) . Defined . 



(** *** Preorderings and associated types . *)

Definition po ( X : UU0 ) := total2 ( fun R : hrel X => ispo R ) .
Definition popair { X : UU0 } ( R : hrel X ) ( is : ispo R ) : po X := tpair ( fun R : hrel X => ispo R ) R is .
Definition carrierofpo ( X : UU0 ) :  po X  -> ( X -> X -> hProp ) :=  @pr1 _ ( fun R : hrel X => ispo R ) .
Coercion carrierofpo : po >-> Funclass  . 

Definition Poset := total2 ( fun X : hSet => po X ) .
Definition Posetpair ( X : hSet ) ( R : po X ) : Poset := tpair ( fun X : hSet => po X ) X R .
Definition carrierofposet : Poset -> hSet := @pr1 _ _ .
Coercion carrierofposet : Poset >-> hSet . 

Definition isaposetmorphism { X Y : Poset } ( f : X -> Y ) := forall x x' : X , ( pr1 ( pr2 X ) x x' ) -> ( pr1 ( pr2 Y ) ( f x ) ( f x' ) ) .
Definition posetmorphism ( X Y : Poset ) := total2 ( fun f : X -> Y => isaposetmorphism f ) .
Definition posetmorphismpair ( X Y : Poset ) := tpair ( fun f : X -> Y => isaposetmorphism f ) .
Definition carrierofposetmorphism ( X Y : Poset ) : posetmorphism X Y -> ( X -> Y ) := @pr1 _ _ .
Coercion  carrierofposetmorphism : posetmorphism >-> Funclass . 


(** *** Eqivalence relations and associated types . *)

Definition eqrel ( X : UU0 ) := total2 ( fun R : hrel X => iseqrel R ) .
Definition eqrelpair { X : UU0 } ( R : hrel X ) ( is : iseqrel R ) : eqrel X := tpair ( fun R : hrel X => iseqrel R ) R is .
Definition eqrelconstr { X : UU0 } ( R : hrel X ) ( is1 : istrans R ) ( is2 : isrefl R ) ( is3 : issymm R ) : eqrel X := eqrelpair R ( dirprodpair ( dirprodpair is1 is2 ) is3 ) .  
Definition pr1eqrel ( X : UU0 ) : eqrel X -> ( X -> ( X -> hProp ) ) := @pr1 _ _ .
Coercion pr1eqrel : eqrel >-> Funclass . 

Definition eqreltrans { X : UU0 } ( R : eqrel X ) : istrans R := pr1 ( pr1 ( pr2 R ) ) . 
Definition eqrelrefl { X : UU0 } ( R : eqrel X ) : isrefl R := pr2 ( pr1 ( pr2 R ) ) . 
Definition eqrelsymm { X : UU0 } ( R : eqrel X ) : issymm R := pr2 ( pr2 R )  . 



(** *** Direct product of two relations *)

Definition hreldirprod { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) : hrel ( dirprod X Y ) := fun xy xy' : dirprod X Y => hconj ( RX ( pr1 xy ) ( pr1 xy' ) ) ( RY ( pr2 xy ) ( pr2 xy' ) ) .

Definition istransdirprod { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) ( isx : istrans RX ) ( isy : istrans RY ) : istrans ( hreldirprod RX RY ) := fun xy1 xy2 xy3 : _ => fun is12 : _  => fun is23 : _ => dirprodpair ( isx _ _ _ ( pr1 is12 ) ( pr1 is23 ) ) ( isy _ _ _ ( pr2 is12 ) ( pr2 is23 ) ) . 

Definition isrefldirprod { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) ( isx : isrefl RX ) ( isy : isrefl RY ) : isrefl ( hreldirprod RX RY ) := fun xy : _ => dirprodpair ( isx _ ) ( isy _ ) .

Definition   issymmdirprod { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) ( isx : issymm RX ) ( isy : issymm RY ) : issymm ( hreldirprod RX RY ) :=  fun xy1 xy2 : _ => fun is12 : _ => dirprodpair ( isx _ _ ( pr1 is12 ) ) ( isy _ _ ( pr2 is12 ) ) . 

Definition eqreldirprod { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) : eqrel ( dirprod X Y ) := eqrelconstr ( hreldirprod RX RY ) ( istransdirprod _ _ ( eqreltrans RX ) ( eqreltrans RY ) ) ( isrefldirprod  _ _ ( eqrelrefl RX ) ( eqrelrefl RY ) ) ( issymmdirprod  _ _ ( eqrelsymm RX ) ( eqrelsymm RY ) ) .


(** *** Negation of a relation and its properties *)

Definition negrel { X : UU0 } ( R : hrel X ) : hrel X := fun x x' => hProppair _ ( isapropneg ( R x x' ) ) .

Lemma istransnegrel { X : UU0 } ( R : hrel X  ) ( isr : iscotrans R ) : istrans ( negrel R ) .  
Proof . intros . intros x1 x2 x3 r12 r23 .  apply ( negf ( isr x1 x2 x3 ) ) .  apply ( toneghdisj ( dirprodpair r12 r23 ) ) . Defined . 

Lemma isasymmnegrel { X : UU0 } ( R : hrel X  ) ( isr : iscoasymm R ) : isasymm ( negrel R ) .  
Proof . intros . intros x1 x2 r12 r21 . apply ( r21 ( isr _ _ r12 ) ) .   Defined . 

Lemma iscoasymmgenrel { X : UU0 } ( R : hrel X  ) ( isr : isasymm R ) : iscoasymm ( negrel R ) .  
Proof . intros . intros x1 x2 nr12 . apply ( negf ( isr _ _ ) nr12 ) .  Defined . 

Lemma isdecnegrel { X : UU0 } ( R : hrel X  ) ( isr : isdecrel R ) : isdecrel ( negrel R ) .
Proof . intros . intros x1 x2 . destruct ( isr x1 x2 ) as [ r | nr ] . apply ii2 .   apply ( todneg _ r ) .  apply ( ii1 nr ) . Defined . 

Lemma isnegnegrel { X : UU0 } ( R : hrel X ) : isnegrel ( negrel R ) .
Proof . intros .   intros x1 x2 .  apply ( negf ( todneg ( R x1 x2 ) ) ) . Defined . 

Lemma isantisymmnegrel { X : UU0 } ( R : hrel X  ) ( isr : isantisymmneg R ) : isantisymm ( negrel R ) . 
Proof . intros . apply isr .  Defined . 

(** *** Boolean representation of decidable equality *)

Definition eqh { X : UU } ( is : isdeceq X ) : hrel X := fun x x' => eqset ( booleq is x x' ) true .

Definition neqh { X : UU } ( is : isdeceq X ) : hrel X := fun x x' => eqset ( booleq is x x' ) false .

Lemma isrefleqh { X : UU } ( is : isdeceq X ) : isrefl ( eqh is ) . 
Proof . intros .  unfold eqh .  unfold booleq . intro x .  destruct ( is x x ) as [ e | ne ] . simpl .  apply idpath .  destruct ( ne ( idpath x ) ) .  Defined . 

Definition weqeqh { X : UU } ( is : isdeceq X ) ( x x' : X ) : weq ( paths x x' ) ( eqh is x x' ) .
Proof . intros . apply weqimplimpl .  intro e .  destruct e . apply isrefleqh . intro e . unfold eqh in e . unfold booleq in e . destruct ( is x x' ) as [ e' | ne' ] .   apply e' .  destruct ( nopathsfalsetotrue e ) . apply ( isasetifdeceq X is x x' ) . unfold eqh . simpl . apply ( isasetbool _ true ) . Defined . 

Definition weqneqh { X : UU0 } ( is : isdeceq X ) ( x x' : X ) : weq ( neg ( paths x x' ) ) ( neqh is x x' ) .
Proof . intros .  unfold neqh . unfold booleq . apply weqimplimpl . destruct ( is x x' ) as [ e | ne ] .  intro ne . destruct ( ne e ) . intro ne' . simpl . apply idpath . destruct ( is x x' ) as [ e | ne ] . intro tf . destruct ( nopathstruetofalse tf ) . intro . exact ne .  apply ( isapropneg ) . simpl . apply ( isasetbool _ false ) . Defined .


 

(** *** Boolean representation of decidable relations *)


Definition decrel ( X : UU ) := total2 ( fun R : hrel X => isdecrel R ) .
Definition pr1decrel ( X : UU ) : decrel X -> hrel X := @pr1 _ _ .  
Definition decrelpair { X : UU } { R : hrel X } ( is : isdecrel R ) : decrel X := tpair _ R is .  
Coercion pr1decrel : decrel >-> hrel . 

Definition decreltobrel { X : UU0 } ( R : decrel X ) : brel X .
Proof . intros . intros x x' . destruct ( ( pr2 R ) x x' ) . apply true . apply false . Defined .

Definition breltodecrel { X : UU0 } ( B : brel X ) : decrel X := @decrelpair _ ( fun x x' => hProppair ( paths ( B x x' ) true ) ( isasetbool _ _ ) ) ( fun x x' => ( isdeceqbool _ _ ) ) .  
 
Definition pathstor { X : UU } ( R : decrel X ) ( x x' : X ) ( e : paths ( decreltobrel R x x' ) true ) : R x x' .
Proof . unfold decreltobrel . intros .  destruct ( pr2 R x x' ) as [ e' | ne ]  .  apply e' . destruct ( nopathsfalsetotrue e ) . Defined .  

Definition rtopaths  { X : UU } ( R : decrel X ) ( x x' : X ) ( r : R x x' ) : paths ( decreltobrel R x x' ) true  .
Proof . unfold decreltobrel .  intros . destruct ( ( pr2 R ) x x' ) as [ r' | nr ] . apply idpath .  destruct ( nr r ) . Defined .   

Definition pathstonegr { X : UU } ( R : decrel X ) ( x x' : X ) ( e : paths ( decreltobrel R x x' ) false ) : neg ( R x x' ) .
Proof . unfold decreltobrel . intros .  destruct ( pr2 R x x' ) as [ e' | ne ] .  destruct ( nopathstruetofalse e ) . apply ne .  Defined . 

Definition negrtopaths { X : UU } ( R : decrel X ) ( x x' : X ) ( nr : neg ( R x x' ) ) : paths ( decreltobrel R x x' ) false .
Proof . unfold decreltobrel . intros .   destruct ( pr2 R x x' ) as [ r | nr' ] . destruct ( nr r ) . apply idpath. Defined .   


(** The following construction of "ct" ( "canonical term" ) is inspired by the ideas of George Gonthier. The expression [ ct ( R , x , y ) ] where [ R ] is in [ hrel X ] for some [ X ] and has a canonical structure of a decidable relation and [ x, y ] are closed terms of type [ X ] such that [ R x y ] is inhabited is the term of type [ R x y ] which relizes the canonical term in [ isdecrel R x y ] . *) 

Definition pathstor_comp { X : UU } ( R : decrel X ) ( x x' : X ) ( u : Phant ( ( pr1 R ) x x' ) ) ( e : paths ( decreltobrel R x x' ) true ) : R x x' .
Proof . unfold decreltobrel . intros .  destruct ( pr2 R x x' ) as [ e' | ne ]  .  apply e' . destruct ( nopathsfalsetotrue e ) . Defined .  

Notation " 'ct' ( R , x , y ) " := ( ( pathstor_comp _ x y ( phant ( R x y ) ) ( idpath true ) ) : R x y ) (at level 70 ) .



(** **** Restriction of a relation to a subtype *)

Definition resrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) : hrel P := fun p1 p2 => L ( pr1 p1 ) ( pr1 p2 ) .

Definition istransresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : istrans L ) : istrans ( resrel L P ) .
Proof . intros . intros x1 x2 x3 r12 r23 . apply ( isl _ ( pr1 x2 ) _ r12 r23 ) . Defined . 

Definition isreflresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X )  ( isl : isrefl L ) : isrefl ( resrel L P ) . 
Proof . intros . intro x . apply isl . Defined . 

Definition issymmresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : issymm L ) : issymm ( resrel L P ) . 
Proof . intros . intros x1 x2 r12 . apply isl . apply r12 .  Defined .  

Definition isporesrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : ispo L ) : ispo ( resrel L P ) . 
Proof . intros . apply ( dirprodpair ( istransresrel L P ( pr1 isl ) ) ( isreflresrel L P ( pr2 isl ) ) ) . Defined . 

Definition iseqrelresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : iseqrel L ) : iseqrel ( resrel L P ) . 
Proof . intros . apply ( dirprodpair ( isporesrel L P ( pr1 isl ) ) ( issymmresrel L P ( pr2 isl ) ) ) . Defined . 

Definition isirreflresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : isirrefl L ) : isirrefl ( resrel L P ) .
Proof . intros . intros x r . apply ( isl _ r ) . Defined .   

Definition isasymmresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : isasymm L ) : isasymm ( resrel L P ) . 
Proof . intros . intros x1 x2 r12 r21 . apply ( isl _ _ r12 r21 ) .  Defined . 

Definition iscoasymmresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : iscoasymm L ) : iscoasymm ( resrel L P ) . 
Proof . intros . intros x1 x2 r12 . apply ( isl _ _ r12 ) . Defined . 

Definition istotalresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : istotal L ) : istotal ( resrel L P ) . 
Proof . intros . intros x1 x2 . apply isl . Defined . 

Definition iscotransresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : iscotrans L ) : iscotrans ( resrel L P ) . 
Proof . intros . intros x1 x2 x3 r13 . apply ( isl _ _ _ r13 ) .  Defined .

Definition isdecrelresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : isdecrel L ) : isdecrel ( resrel L P ) . 
Proof . intros . intros x1 x2 . apply isl . Defined . 

Definition isnegrelresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : isnegrel L ) : isnegrel ( resrel L P ) . 
Proof . intros . intros x1 x2 nnr . apply ( isl _ _ nnr ) . Defined . 

Definition isantisymmresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : isantisymm L ) : isantisymm ( resrel L P ) .
Proof . intros . intros x1 x2 r12 r21 . apply ( invmaponpathsincl _ ( isinclpr1carrier _ ) _ _ ( isl _ _ r12 r21  ) ) . Defined .  

Definition isantisymmnegresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : isantisymmneg L ) : isantisymmneg ( resrel L P ) .
Proof . intros . intros x1 x2 nr12 nr21 . apply (  invmaponpathsincl _ ( isinclpr1carrier _ ) _ _ ( isl _ _ nr12 nr21 ) ) . Defined .  

Definition iscoantisymmresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : iscoantisymm L ) : iscoantisymm ( resrel L P ) .
Proof . intros . intros x1 x2 r12 . destruct ( isl _ _ r12 ) as [ l | e ] . apply ( ii1 l ) .  apply ii2 .  apply (  invmaponpathsincl _ ( isinclpr1carrier _ ) _ _ e ) . Defined . 

Definition  neqchoiceresrel { X : UU0 } ( L : hrel X ) ( P : hsubtypes X ) ( isl : neqchoice L ) : neqchoice ( resrel L P ) .
Proof . intros . intros x1 x2 ne .  set ( int := negf ( invmaponpathsincl _ ( isinclpr1carrier P ) _ _ ) ne ) . apply ( isl _ _ int ) . Defined . 



(** *** Equivalence classes with respect to a given relation *)



Definition iseqclass { X : UU0 } ( R : hrel X ) ( A : hsubtypes X ) := dirprod ( ishinh ( carrier A ) ) ( dirprod ( forall x1 x2 : X , R x1 x2 -> A x1 -> A x2 ) ( forall x1 x2 : X, A x1 ->  A x2 -> R x1 x2 ) ).
Definition iseqclassconstr { X : UU0 } ( R : hrel X ) { A : hsubtypes X } ( ax0 : ishinh ( carrier A ) ) ( ax1 : forall x1 x2 : X , R x1 x2 -> A x1 -> A x2 ) ( ax2 : forall x1 x2 : X, A x1 ->  A x2 -> R x1 x2 ) : iseqclass R A := dirprodpair ax0 ( dirprodpair ax1 ax2 ) . 

Definition eqax0 { X : UU0 } { R : hrel X } { A : hsubtypes X }  : iseqclass R A -> ishinh ( carrier A ) := fun is : iseqclass R A =>  pr1 is .
Definition eqax1 { X : UU0 } { R : hrel X } { A : hsubtypes X } : iseqclass R A ->  forall x1 x2 : X,  R x1 x2 -> A x1 -> A x2 := fun is: iseqclass R A => pr1 ( pr2 is) .
Definition eqax2 { X : UU0 } { R : hrel X } { A : hsubtypes X } : iseqclass R A ->  forall x1 x2 : X,  A x1 -> A x2 -> R x1 x2 := fun is: iseqclass R A => pr2 ( pr2 is) .

Lemma isapropiseqclass  { X : UU0 } ( R : hrel X ) ( A : hsubtypes X ) : isaprop ( iseqclass R A ) .
Proof. intros. unfold iseqclass. apply isofhleveldirprod. apply (isapropishinh (carrier A)). apply isofhleveldirprod. apply impredtwice. intros t t' . apply impred. intro. apply impred.  intro.  
apply (pr2 (A t')).  apply impredtwice. intros. apply impred. intro. apply impred.  intro.  apply (pr2 (R t t')).  Defined. 


(** *** Direct product of equivalence classes *)

Lemma iseqclassdirprod { X Y : UU0 } { R : hrel X } { Q : hrel Y } { A : hsubtypes X } { B : hsubtypes Y } ( isa : iseqclass R A ) ( isb : iseqclass Q B ) : iseqclass ( hreldirprod R Q ) ( subtypesdirprod A B ) .
Proof . intros . set ( XY := dirprod X Y ) . set ( AB := subtypesdirprod A B ) . set ( RQ := hreldirprod R Q ) . 
set ( ax0 := ishinhsubtypesdirprod  A B ( eqax0 isa ) ( eqax0 isb ) ) .
assert ( ax1 : forall xy1 xy2 : XY , RQ xy1 xy2 -> AB xy1 -> AB xy2 ) . intros xy1 xy2 rq ab1 . apply ( dirprodpair ( eqax1 isa _ _ ( pr1 rq ) ( pr1 ab1 ) ) ( eqax1 isb _ _ ( pr2 rq ) ( pr2 ab1 ) ) ) .    
assert ( ax2 : forall xy1 xy2 : XY ,  AB xy1 -> AB xy2 -> RQ xy1 xy2 ) . intros xy1 xy2 ab1 ab2 . apply ( dirprodpair ( eqax2 isa _ _ ( pr1 ab1 ) ( pr1 ab2 ) ) ( eqax2 isb _ _ ( pr2 ab1 ) ( pr2 ab2 ) ) ) .
apply ( iseqclassconstr _ ax0 ax1 ax2 ) . Defined .     







(** ** Images and surjectivity for functions between types (both depend only on the behavior of the corresponding function between the sets of connected components) **)

Definition image { X Y : UU0 } ( f : X -> Y ) := total2 ( fun y : Y => ishinh ( hfiber f y ) ) .
Definition imagepair { X Y : UU0 } (f: X -> Y) := tpair ( fun y : Y => ishinh ( hfiber f y ) ) .
Definition pr1image { X Y : UU0 } ( f : X -> Y ) := @pr1 _  ( fun y : Y => ishinh ( hfiber f y ) ) .


Definition prtoimage { X Y : UU0 } (f : X -> Y) : X -> image f.
Proof. intros X Y f X0. apply (imagepair _ (f X0) (hinhpr _ (hfiberpair f X0 (idpath _ )))). Defined. 

Definition issurjective { X Y : UU0 } (f : X -> Y ) := forall y:Y, ishinh (hfiber f y). 

Lemma isapropissurjective { X Y : UU0 } ( f : X -> Y) : isaprop (issurjective f).
Proof. intros.  apply impred. intro t. apply  (pr2 (ishinh (hfiber f t))). Defined. 

Lemma isinclpr1image { X Y : UU0 } (f:X -> Y): isincl (pr1image f).
Proof. intros. apply isofhlevelfpr1. intro. apply ( pr2 ( ishinh ( hfiber f x ) ) ) . Defined.

Lemma issurjprtoimage { X Y : UU0 } ( f : X -> Y) : issurjective (prtoimage f ).
Proof. intros. intro z.  set (f' := prtoimage f ). set (g:= pr1image f ). set (gf':= fun x:_ => g ( f' x )).
assert (e: paths f gf'). apply etacorrection .  
assert (ff: hfiber gf' (pr1 z) -> hfiber f' z).   apply ( invweq ( samehfibers _ _ ( isinclpr1image f ) z ) ) .  
assert (is2: ishinh (hfiber gf' (pr1 z))). destruct e.  apply (pr2 z). 
apply (hinhfun ff is2). Defined. 


(** *** Surjections to sets are epimorphisms  *)

Theorem surjectionisepitosets { X Y Z : UU0 } ( f : X -> Y ) ( g1 g2 : Y -> Z ) ( is1 : issurjective f ) ( is2 : isaset Z ) ( isf : forall x : X , paths ( g1 ( f x ) ) ( g2 ( f x ) ) ) : forall y : Y , paths ( g1 y ) ( g2 y ) .
Proof. intros . set (P1:= hProppair (paths (g1 y) (g2 y)) (is2 (g1 y) (g2 y))). unfold issurjective in is1. 
assert (s1: (hfiber f y)-> paths (g1 y) (g2 y)). intro X1. destruct X1 as [t x ]. induction x. apply (isf t). 
assert (s2: ishinh (paths (g1 y) (g2 y))). apply (hinhfun s1 (is1 y)).  
set (is3:= is2 (g1 y) (g2 y)). simpl in is3. apply (@hinhuniv (paths (g1 y) (g2 y)) (hProppair _ is3)). intro X1.  assumption. assumption. Defined. 

(** *** The two-out-of-three properties of surjections *)

Lemma issurjcomp { X Y Z : UU0 } ( f : X -> Y ) ( g : Y -> Z ) ( isf : issurjective f ) ( isg : issurjective g ) : issurjective ( funcomp f g ) .
Proof . intros . unfold issurjective .  intro z . apply ( fun ff => hinhuniv ff ( isg z ) ) . intro ye .  apply ( hinhfun ( hfibersftogf f g z ye ) ) .  apply ( isf ) .   Defined . 

Notation issurjtwooutof3c := issurjcomp . 

Lemma issurjtwooutof3b { X Y Z : UU0 } ( f : X -> Y ) ( g : Y -> Z ) ( isgf : issurjective ( funcomp f g ) ) : issurjective g .  
Proof . intros . unfold issurjective .  intro z .  apply ( hinhfun ( hfibersgftog f g z ) ( isgf z ) ) .  Defined . 

(** *** A function between hsets which is an inclusion and a surjection is a weak equivalence *)

Lemma isweqinclandsurj { X Y : hSet } ( f : X -> Y ) ( is1 : isincl f ) ( is1 : issurjective f ) : isweq f .
Proof . intros . unfold isweq . intro y . 

assert ( isp : isaprop ( hfiber f y ) ) . apply ( is1 y ) .
apply iscontraprop1 . apply isp . apply ( @hinhuniv _ ( hProppair _ isp ) ( idfun _ ) ( is0 y ) ) .  Defined .


 




(** ** Set quotients of types. 

In this file we study the set quotients of types by equivalence relations. While the general notion of a quotient of a type by a relation is complicated due to the existence of different kinds of quotients (e.g. homotopy quotients or categorical quotients in the homotopy category which are usually different from each other) there is one particular class of quotients which is both very important for applications and semantically straightforward. These quotients are the universal functions from a type to an hset which respect a given relation. Some of the proofs in this section depend on the proerties of the hinhabited construction and some also depend on the univalence axiom for [ hProp ] which allows us to prove that the type of monic subtypes of a type is a set. 

Our main construction is analogous to the usual construction of quotient as a set of equivalence classes. Wev also consider another construction of [ setquot ] which is analogous ( on the next h-level ) to our construction of [ ishinh ] . Both have generalizations to the "higher" quotients (i.e. groupoid quotients etc.) which will be considered separately. In particular, the quotients the next h-level appear to be closely related to the localizations of categories and will be considered in the section about types of h-level 3.  


*)



(** ** Setquotient defined in terms of equivalence classes *)


Definition setquot { X : UU0 } ( R : hrel X ) := total2 ( fun A : _ => iseqclass R A ) .
Definition setquotpair { X : UU0 } ( R : hrel X ) ( A : hsubtypes X ) ( is : iseqclass R A ) := tpair _ A is .
Definition pr1setquot { X : UU0 } ( R : hrel X ) : setquot R -> ( hsubtypes X ) := @pr1 _ ( fun A : _ => iseqclass R A ) .
Coercion pr1setquot : setquot >-> hsubtypes . 

Lemma isinclpr1setquot { X : UU0 } ( R : hrel X ) : isincl ( pr1setquot R ) .
Proof . intros . apply isinclpr1.  intro x0. apply isapropiseqclass. Defined .  

Definition setquottouu0 { X : UU0 } ( R : hrel X ) ( a : setquot R )  := carrier ( pr1 a ).
Coercion setquottouu0 : setquot >-> Sortclass.


Theorem isasetsetquot { X : UU0 } ( R : hrel X ) : isaset ( setquot R ) .
Proof. intros.  apply ( isasetsubset ( @pr1 _ _ )  ( isasethsubtypes X )  ) . apply isinclpr1.  intro.  apply isapropiseqclass.  Defined. 

Definition setquotinset { X : UU0 } ( R : hrel X ) : hSet := hSetpair _ ( isasetsetquot R ) . 

Theorem setquotpr { X : UU0 } ( R : eqrel X ) : X -> setquot R.
Proof. intros X R X0. set ( rax:= eqrelrefl R ). set ( sax := eqrelsymm R  ) . set (tax:= eqreltrans R ). split with (fun x:X =>  R X0 x). split with (hinhpr _ (tpair _ X0 (rax X0))).  
assert (a1: (forall x1 x2 : X, R x1 x2 -> R X0 x1 -> R X0 x2)). intros x1 x2 X1 X2.  apply (tax X0 x1 x2 X2 X1). split with a1.
assert (a2: (forall x1 x2 : X, R X0 x1 -> R X0 x2 -> R x1 x2)). intros x1 x2 X1 X2. apply (tax x1 X0 x2 (sax X0 x1 X1) X2). 
assumption. Defined. 

Lemma setquotl0 { X : UU0 } ( R : eqrel X ) ( c : setquot R ) ( x : c ) : paths ( setquotpr R ( pr1 x ) ) c .
Proof . intros . apply ( invmaponpathsincl _ ( isinclpr1setquot R ) ) .  simpl . apply funextsec . intro x0 . destruct c as [ A iseq ] .  destruct x as [ x is ] .  simpl in is . simpl .  apply uahp . intro r . apply ( eqax1 iseq _ _ r is ) .  intro a . apply ( eqax2 iseq _ _ is a ) .  Defined . 



Theorem issurjsetquotpr { X : UU0 } ( R : eqrel X)  : issurjective (setquotpr R ).
Proof. intros. unfold issurjective. intro c.   apply ( @hinhuniv ( carrier ( pr1 c ) ) ) .  intro x . apply hinhpr .  split with ( pr1 x ) . apply setquotl0 .  apply ( eqax0 ( pr2 c ) ) .  
Defined . 

Lemma iscompsetquotpr { X : UU0 } ( R : eqrel X ) ( x x' : X ) ( a : R x x' ) : paths ( setquotpr R x ) ( setquotpr R x' ) .
Proof. intros. apply ( invmaponpathsincl _ ( isinclpr1setquot R ) ) . simpl . apply funextsec . intro x0 . apply uahp .  intro r0 . apply ( eqreltrans R _ _ _ ( eqrelsymm R _ _ a ) r0 ) .  intro x0' . apply ( eqreltrans R _ _ _ a x0' ) . Defined .  





(** *** Universal property of [ seqtquot R ] for functions to sets satisfying compatibility condition [ iscomprelfun ] *)


Definition iscomprelfun { X Y : UU0 } ( R : hrel X ) ( f : X -> Y ) := forall x x' : X , R x x' -> paths ( f x ) ( f x' ) .

Lemma iscomprelfunlogeqf { X Y : UU0 } { R L : hrel X } ( lg : hrellogeq L R ) ( f : X -> Y ) ( is : iscomprelfun L f ) : iscomprelfun R f .
Proof . intros . intros x x' r . apply ( is _ _ ( pr2 ( lg  _ _ ) r ) ) . Defined . 

Lemma isapropimeqclass { X : UU0 } ( R : hrel X ) ( Y : hSet ) ( f : X -> Y ) ( is : iscomprelfun R f ) ( c : setquot R ) : isaprop ( image ( fun x : c => f ( pr1 x ) ) ) .
Proof. intros. apply isapropsubtype .  intros y1 y2 . simpl . apply ( @hinhuniv2 _ _ ( hProppair ( paths y1 y2 ) ( pr2 Y y1 y2 ) ) ) .  intros x1 x2 . simpl . destruct c as [ A iseq ] . destruct x1 as [ x1 is1 ] . destruct x2 as [ x2 is2 ] . destruct x1 as [ x1 is1' ] . destruct x2 as [ x2 is2' ] . simpl in is1 .  simpl in is2 . simpl in is1' .  simpl in is2' .  assert ( r : R x1 x2 ) . apply ( eqax2 iseq _ _ is1' is2' ) .  apply ( pathscomp0 ( pathsinv0 is1 )  ( pathscomp0 ( is _ _ r ) is2 ) ) .  Defined .  


Theorem setquotuniv  { X : UU0 } ( R : hrel X ) ( Y : hSet ) ( f : X -> Y ) ( is : iscomprelfun R f ) ( c : setquot R ) : Y .
Proof. intros.   apply ( pr1image ( fun x : c => f ( pr1 x ) ) ) . apply ( @hinhuniv ( pr1 c ) ( hProppair _ ( isapropimeqclass R Y f is c ) ) ( prtoimage ( fun x : c => f ( pr1 x ) ) ) ) .  apply ( eqax0 ( pr2 c ) ) .  Defined . 


(** Note: the axioms rax, sax and trans are not used in the proof of setquotuniv. If we consider a relation which is not an equivalence relation then setquot will still be the set of subsets which are equivalence classes. Now however such subsets need not to cover all of the type. In fact their set can be empty. Nevertheless setquotuniv will apply. *)


Theorem setquotunivcomm  { X : UU0 } ( R : eqrel X ) ( Y : hSet ) ( f : X -> Y ) ( is : iscomprelfun R f ) : forall x : X , paths ( setquotuniv R Y f is ( setquotpr R x ) )  ( f x ) .
Proof. intros. unfold setquotuniv . unfold setquotpr .  simpl .  apply idpath .  Defined.


Theorem weqpathsinsetquot { X : UU0 } ( R : eqrel X ) ( x x' : X ) : weq ( R x x' ) ( paths ( setquotpr R x ) ( setquotpr R x' ) ) .
Proof .  intros . split with ( iscompsetquotpr R x x' ) .  apply isweqimplimpl .  intro e .  set ( e' := maponpaths ( pr1setquot R ) e ) .  unfold pr1setquot in e' . unfold setquotpr in e' . simpl in e' . assert ( e'' := maponpaths ( fun f : _ => f x' ) e' ) .  simpl in e'' . apply ( eqweqmaphProp ( pathsinv0 e'' ) ( eqrelrefl R x' ) ) .  apply ( pr2 ( R x x' ) ) .  set ( int := isasetsetquot R (setquotpr R x) (setquotpr R x') ) .  assumption . Defined .



(** *** Functoriality of [ setquot ] for functions mapping one relation to another *)


Definition iscomprelrelfun { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) ( f : X -> Y ) := forall x x' : X , RX x x' -> RY ( f x ) ( f x' ) .

Lemma iscomprelfunlogeqf1 { X Y : UU0 }  { LX RX : hrel X } ( RY : hrel Y ) ( lg : hrellogeq LX RX ) ( f : X -> Y ) ( is : iscomprelrelfun LX RY f ) : iscomprelrelfun RX RY f .
Proof . intros . intros x x' r . apply ( is _ _ ( pr2 ( lg  _ _ ) r ) ) . Defined . 

Lemma iscomprelfunlogeqf2 { X Y : UU0 }  ( RX : hrel X ) { LY RY : hrel Y } ( lg : hrellogeq LY RY ) ( f : X -> Y ) ( is : iscomprelrelfun RX LY f ) : iscomprelrelfun RX RY f .
Proof . intros . intros x x' r . apply ( ( pr1 ( lg _ _ ) ) ( is _ _ r ) ) . Defined . 

Definition  setquotfun  { X Y : UU0 } ( RX : hrel X ) ( RY : eqrel Y ) ( f : X -> Y ) ( is : iscomprelrelfun RX RY f ) ( cx : setquot RX ) : setquot RY .
Proof . intros . set ( ff := funcomp f ( setquotpr RY ) ) . assert ( isff : iscomprelfun RX ff ) .  intros x x' .  intro r .  apply ( weqpathsinsetquot RY ( f x ) ( f x' ) ) .  apply is . apply r . apply ( setquotuniv RX ( setquotinset RY ) ff isff cx) .  Defined . 

Definition setquotfuncomm  { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : X -> Y ) ( is : iscomprelrelfun RX RY f ) : forall x : X , paths ( setquotfun RX RY f is ( setquotpr RX x ) ) ( setquotpr RY ( f x ) ) .
Proof . intros . simpl . apply idpath .  Defined . 



(** *** Universal property of [ setquot ] for predicates of one and several variables *)


Theorem setquotunivprop { X : UU0 } ( R : eqrel X ) ( P : setquot R -> hProp ) ( is : forall x : X , P ( setquotpr R x ) ) : forall c : setquot R ,  P c .
Proof . intros . apply ( @hinhuniv ( carrier ( pr1 c ) ) ( P c ) ) .  intro x .  set ( e := setquotl0 R c x ) .  apply ( eqweqmaphProp ( maponpaths P e ) ) .   apply ( is ( pr1 x ) ) .  apply ( eqax0 ( pr2 c ) ) .  Defined . 


Theorem setquotuniv2prop { X : UU0 } ( R : eqrel X ) ( P : setquot R -> setquot R -> hProp ) ( is : forall x x' : X ,  P ( setquotpr R x ) ( setquotpr R x' ) ) : forall c c' : setquot R ,  P c c' .
Proof . intros . assert ( int1 : forall c0' : _ , P c c0' ) .  apply ( setquotunivprop R ( fun c0' => P c c0' ) ) .  intro x . apply ( setquotunivprop R ( fun c0 : _ => P c0 ( setquotpr R x ) ) ) .  intro x0 . apply ( is x0 x ) . apply ( int1 c' ) .  Defined . 

Theorem setquotuniv3prop { X : UU0 } ( R : eqrel X ) ( P : setquot R -> setquot R -> setquot R -> hProp ) ( is : forall x x' x'' : X ,  P  ( setquotpr R x ) ( setquotpr R x' ) ( setquotpr R x'' ) ) : forall c c' c'' : setquot R , P c c' c''  .
Proof . intros . assert ( int1 : forall c0' c0'' : _ , P c c0' c0'' ) .  apply ( setquotuniv2prop R ( fun c0' c0'' => P c c0' c0'' ) ) .  intros x x' . apply ( setquotunivprop R ( fun c0 : _ => P c0 ( setquotpr R x ) ( setquotpr R x' ) ) ) .  intro x0 . apply ( is x0 x x' ) . apply ( int1 c' c'' ) .  Defined . 

Theorem setquotuniv4prop { X : UU0 } ( R : eqrel X ) ( P : setquot R -> setquot R ->  setquot R -> setquot R -> hProp ) ( is : forall x x' x'' x''' : X ,  P  ( setquotpr R x ) ( setquotpr R x' ) ( setquotpr R x'' ) ( setquotpr R x''' ) ) : forall c c' c'' c''' : setquot R , P c c' c'' c''' .
Proof . intros . assert ( int1 : forall c0 c0' c0'' : _ , P c c0 c0' c0'' ) .  apply ( setquotuniv3prop R ( fun c0 c0' c0'' => P c c0 c0' c0'' ) ) .  intros x x' x'' . apply ( setquotunivprop R ( fun c0 : _ => P c0 ( setquotpr R x ) ( setquotpr R x' ) ( setquotpr R x'' ) ) ) .  intro x0 . apply ( is x0 x x' x'' ) . apply ( int1 c' c'' c''' ) .  Defined . 




(** Important note : theorems proved above can not be used ( al least at the moment ) to construct terms whose complete normalization ( evaluation ) is important . For example they should not be used * directly * to construct [ isdeceq ] property of [ setquot ] since [ isdeceq ] is in turn used to construct boolean equality [ booleq ] and evaluation of [ booleq x y ] is important for computational purposes . Terms produced using these universality theorems will not fully normalize even in simple cases due to the following steps in the proof of [ setquotunivprop ] . As a part of the proof term of this theorem there appears the composition of an application of [ uahp ] , transfer of the resulting term of the identity type by [ maponpaths ] along [ P ] followed by the reconstruction of a equivalence ( two directional implication ) between the corresponding propositions through [  eqweqmaphProp ] . The resulting implications are " opaque " and the proofs of disjunctions [ P \/ Q ]  produced with the use of such implications can not be evaluated to one of the summands of the disjunction . An example is given by the following theorem [ isdeceqsetquot_non_constr ] which , as simple experiments show, can not be used to compute the value of [ isdeceqsetquot ] . Below we give another proof of [ isdeceq ( setquot R ) ] using the same assumptions which is " constructive " i.e. usable for the evaluation purposes . *)




(** *** The case when the function between quotients defined by [ setquotfunt ] is a surjection , inclusion or a weak equivalence  *)

Lemma issurjsetquotfun { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : X -> Y ) ( is : issurjective f ) ( is1 : iscomprelrelfun RX RY f ) : issurjective ( setquotfun RX RY f is1 ) .
Proof . intros . apply ( issurjtwooutof3b ( setquotpr RX ) ) . apply ( issurjcomp f ( setquotpr RY ) is ( issurjsetquotpr RY ) ) .   Defined . 


Lemma isinclsetquotfun { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : X -> Y ) ( is1 : iscomprelrelfun RX RY f  )  ( is2 : forall x x' : X , RY ( f x ) ( f x' ) -> RX x x' ) : isincl ( setquotfun RX RY f is1 ) .
Proof . intros . apply isinclbetweensets . apply isasetsetquot .   apply isasetsetquot .
assert ( is : forall x x' : setquot RX , isaprop ( paths (setquotfun RX RY f is1 x) (setquotfun RX RY f is1 x') -> paths x x' ) ) . intros . apply impred .  intro . apply isasetsetquot .  
apply ( setquotuniv2prop RX ( fun x x' => hProppair _ ( is x x' ) ) ) .  simpl . intros x x' .  intro e .  set ( e' := invweq ( weqpathsinsetquot RY ( f x ) ( f x' ) ) e ) .  apply ( weqpathsinsetquot RX _ _ ( is2 x x' e' ) ) .  Defined .

Definition setquotincl { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : X -> Y ) ( is1 : iscomprelrelfun RX RY f  )  ( is2 : forall x x' : X , RY ( f x ) ( f x' ) -> RX x x' ) := inclpair ( setquotfun RX RY f is1 ) ( isinclsetquotfun RX RY f is1 is2 ) . 

Definition  weqsetquotweq { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : weq X Y ) ( is1 : iscomprelrelfun RX RY f  )  ( is2 : forall x x' : X , RY ( f x ) ( f x' ) -> RX x x' ) : weq ( setquot RX ) ( setquot RY )  .
Proof . intros . set ( ff := setquotfun RX RY f is1 ) . split with ff .
assert ( is2' : forall y y' : Y , RY y y' -> RX ( invmap f y ) ( invmap f y' ) ) . intros y y' .  rewrite ( pathsinv0 ( homotweqinvweq f y ) ) .  rewrite ( pathsinv0 ( homotweqinvweq f y' ) ) .  rewrite ( homotinvweqweq f ( invmap f y ) ) . rewrite ( homotinvweqweq f ( invmap f y' ) ) .  apply ( is2 _ _ ) .  set ( gg := setquotfun RY RX ( invmap f ) is2' ) .

assert ( egf : forall a , paths ( gg ( ff a ) ) a ) . apply ( setquotunivprop RX ( fun a0 => hProppair _ ( isasetsetquot RX ( gg ( ff a0 ) ) a0 ) ) ) .    simpl .  intro x .  unfold ff . unfold gg .  apply ( maponpaths ( setquotpr RX ) ( homotinvweqweq f x ) ) . 

assert ( efg : forall a , paths ( ff ( gg a ) ) a ) . apply ( setquotunivprop RY ( fun a0 => hProppair _ ( isasetsetquot RY ( ff ( gg a0 ) ) a0 ) ) ) .    simpl .  intro x .  unfold ff . unfold gg .  apply ( maponpaths ( setquotpr RY ) ( homotweqinvweq f x ) ) .

apply ( gradth _ _ egf efg ) . Defined .

Definition weqsetquotsurj  { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : X -> Y ) ( is : issurjective f ) ( is1 : iscomprelrelfun RX RY f  )  ( is2 : forall x x' : X , RY ( f x ) ( f x' ) -> RX x x' ) : weq ( setquot RX ) ( setquot RY )  .
Proof . intros . set ( ff := setquotfun RX RY f is1 ) . split with ff .  apply ( @isweqinclandsurj ( setquotinset RX ) ( setquotinset RY ) ff ) .  apply ( isinclsetquotfun RX RY f is1 is2 ) .  apply ( issurjsetquotfun RX RY f is is1 ) .  Defined . 



(** *** [ setquot ] with respect to the product of two relations *)



Definition setquottodirprod { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( cc : setquot ( eqreldirprod RX RY ) ) : dirprod ( setquot RX ) ( setquot RY ) .
Proof . intros .  set ( RXY := eqreldirprod RX RY ) . apply ( dirprodpair ( setquotuniv RXY ( setquotinset RX ) ( funcomp ( @pr1 _ ( fun x : _ => Y ) ) ( setquotpr RX ) ) ( fun xy xy' : dirprod X Y => fun rr : RXY xy xy' => iscompsetquotpr RX _ _ ( pr1 rr ) ) cc )  ( setquotuniv RXY ( setquotinset RY ) ( funcomp ( @pr2 _ ( fun x : _ => Y ) ) ( setquotpr RY ) ) ( fun xy xy' : dirprod X Y => fun rr : RXY xy xy' =>  iscompsetquotpr RY _ _ ( pr2 rr ) ) cc ) )  . Defined .   

Definition dirprodtosetquot { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) (cd : dirprod ( setquot RX ) ( setquot RY ) ) : setquot ( hreldirprod RX RY ) := setquotpair _ _ ( iseqclassdirprod ( pr2 ( pr1 cd ) ) ( pr2 ( pr2 cd ) ) ) . 


Theorem weqsetquottodirprod { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) : weq ( setquot ( eqreldirprod RX RY ) ) ( dirprod ( setquot RX ) ( setquot RY ) ) .
Proof . intros . set ( f := setquottodirprod  RX RY ) . set ( g := dirprodtosetquot RX RY ) . split with f .

assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . apply ( setquotunivprop _ ( fun a : _ => ( hProppair _ ( isasetsetquot _ ( g ( f a ) ) a ) ) ) ) . intro xy . destruct xy as [ x y ] . simpl . apply ( invmaponpathsincl _ ( isinclpr1setquot _ ) ) . simpl . apply funextsec .  intro xy' .  destruct xy' as [ x' y' ] . apply idpath .

assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro a . destruct a as [ ax ay ] . apply pathsdirprod . generalize ax .  clear ax . apply ( setquotunivprop RX ( fun ax : _ => ( hProppair _ ( isasetsetquot _ _ _ ) ) ) ) . intro x . simpl .  generalize ay .  clear ay . apply ( setquotunivprop RY ( fun ay : _ => ( hProppair _ ( isasetsetquot _ _ _ ) ) ) ) . intro y . simpl .   apply ( invmaponpathsincl _ ( isinclpr1setquot _ ) ) . apply funextsec .  intro x0 . simpl . apply idpath . generalize ax .  clear ax . apply ( setquotunivprop RX ( fun ax : _ => ( hProppair _ ( isasetsetquot _ _ _ ) ) ) ) . intro x . simpl .  generalize ay .  clear ay . apply ( setquotunivprop RY ( fun ay : _ => ( hProppair _ ( isasetsetquot _ _ _ ) ) ) ) . intro y . simpl .   apply ( invmaponpathsincl _ ( isinclpr1setquot _ ) ) . apply funextsec .  intro x0 . simpl . apply idpath . 

apply ( gradth _ _ egf efg ) . Defined .  



(** *** Universal property of [ setquot ] for functions of two variables *) 

Definition iscomprelfun2 { X Y : UU0 } ( R : hrel X ) ( f : X -> X -> Y ) := forall x x' x0 x0' : X , R x x' ->  R x0 x0' ->  paths ( f x x0 ) ( f x' x0' ) .

Lemma iscomprelfun2if { X Y : UU0 } ( R : hrel X ) ( f : X -> X -> Y ) ( is1 : forall x x' x0 : X , R x x' -> paths ( f x x0 ) ( f x' x0 ) ) ( is2 : forall x x0 x0' : X , R x0 x0' -> paths ( f x x0 ) ( f x x0' ) ) : iscomprelfun2 R f .
Proof . intros . intros x x' x0 x0' .  intros r r' .  set ( e := is1 x x' x0 r ) . set ( e' := is2 x' x0 x0' r' ) . apply ( pathscomp0 e e' ) . Defined . 

Lemma iscomprelfun2logeqf { X Y : UU0 } { L R : hrel X } ( lg : hrellogeq L R ) ( f : X -> X -> Y ) ( is : iscomprelfun2 L f ) : iscomprelfun2 R f .
Proof . intros . intros x x' x0 x0' r r0 . apply ( is _ _ _ _ ( ( pr2 ( lg _ _ ) ) r )  ( ( pr2 ( lg _ _ ) ) r0 ) ) . Defined .     

Definition setquotuniv2  { X : UU0 } ( R : hrel X ) ( Y : hSet ) ( f : X -> X -> Y ) ( is : iscomprelfun2 R f ) ( c c0 : setquot R ) : Y .
Proof. intros .  set ( ff := fun xy : dirprod X X => f ( pr1 xy ) ( pr2 xy ) ) . set ( RR := hreldirprod R R ) . 
assert ( isff : iscomprelfun RR ff ) . intros xy x'y' . simpl . intro dp .  destruct dp as [ r r'] .  apply ( is _ _ _ _ r r' ) . apply ( setquotuniv RR Y ff isff ( dirprodtosetquot R R ( dirprodpair c c0 ) ) ) . Defined .   

Theorem setquotuniv2comm  { X : UU0 } ( R : eqrel X ) ( Y : hSet ) ( f : X -> X -> Y ) ( is : iscomprelfun2 R f ) : forall x x' : X , paths ( setquotuniv2 R Y f is ( setquotpr R x ) ( setquotpr R x' ) )  ( f x x' ) .
Proof. intros.   apply idpath .  Defined.



(** *** Functoriality of [ setquot ] for functions of two variables mapping one relation to another *)


Definition iscomprelrelfun2 { X Y : UU0 } ( RX : hrel X ) ( RY : hrel Y ) ( f : X -> X -> Y ) := forall x x' x0 x0' : X , RX x x' -> RX x0 x0' ->  RY ( f x x0 ) ( f x' x0' ) .

Lemma iscomprelrelfun2if { X Y : UU0 } ( RX : hrel X ) ( RY : eqrel Y ) ( f : X -> X -> Y ) ( is1 : forall x x' x0 : X , RX x x' -> RY ( f x x0 ) ( f x' x0 ) ) ( is2 : forall x x0 x0' : X , RX x0 x0' -> RY ( f x x0 ) ( f x x0' ) ) : iscomprelrelfun2 RX RY f .
Proof . intros . intros x x' x0 x0' .  intros r r' .  set ( e := is1 x x' x0 r ) . set ( e' := is2 x' x0 x0' r' ) . apply ( eqreltrans RY _ _ _ e e' ) . Defined . 

Lemma iscomprelrelfun2logeqf1 { X Y : UU0 } { LX RX : hrel X } ( RY : hrel Y ) ( lg : hrellogeq LX RX ) ( f : X -> X -> Y ) ( is : iscomprelrelfun2 LX RY f ) : iscomprelrelfun2 RX RY f .
Proof . intros . intros x x' x0 x0' r r0 . apply ( is _ _ _ _ ( ( pr2 ( lg _ _ ) ) r )  ( ( pr2 ( lg _ _ ) ) r0 ) ) . Defined .

Lemma iscomprelrelfun2logeqf2 { X Y : UU0 } ( RX : hrel X ) { LY RY : hrel Y } ( lg : hrellogeq LY RY ) ( f : X -> X -> Y ) ( is : iscomprelrelfun2 RX LY f ) : iscomprelrelfun2 RX RY f .
Proof . intros . intros x x' x0 x0' r r0 . apply ( ( pr1 ( lg _ _ ) ) ( is _ _ _ _ r r0 ) ) .  Defined .

Definition  setquotfun2  { X Y : UU0 } ( RX : hrel X ) ( RY : eqrel Y ) ( f : X -> X -> Y ) ( is : iscomprelrelfun2 RX RY f ) ( cx cx0 : setquot RX ) : setquot RY .
Proof . intros . set ( ff := fun x x0 : X => setquotpr RY ( f x x0 ) ) . assert ( isff : iscomprelfun2 RX ff ) .  intros x x' x0 x0' .  intros r r0  .  apply ( weqpathsinsetquot RY ( f x x0 ) ( f x' x0' ) ) .  apply is . apply r . apply r0 . apply ( setquotuniv2 RX ( setquotinset RY ) ff isff cx cx0 ) .  Defined . 

Theorem setquotfun2comm  { X Y : UU0 } ( RX : eqrel X ) ( RY : eqrel Y ) ( f : X -> X -> Y ) ( is : iscomprelrelfun2 RX RY f ) : forall x x' : X , paths ( setquotfun2 RX RY f is ( setquotpr RX x ) ( setquotpr RX x' ) )  ( setquotpr RY ( f x x' ) ) .
Proof. intros.   apply idpath .  Defined.



(** *** Set quotients with respect to decidable equivalence relations have decidable equality *)


Theorem isdeceqsetquot_non_constr { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) : isdeceq ( setquot R ) . 
Proof . intros .  apply isdeceqif . intros x x' .  apply ( setquotuniv2prop R ( fun x0 x0' => hProppair _ ( isapropisdecprop ( paths x0 x0' ) ) ) ) .  intros x0 x0' .  simpl .  apply ( isdecpropweqf ( weqpathsinsetquot R x0 x0' ) ( is x0 x0' ) ) .  Defined . 

Definition setquotbooleqint { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) ( x x' : X ) : bool .
Proof . intros . destruct ( pr1 ( is x x' ) ) . apply true . apply false . Defined .

Lemma  setquotbooleqintcomp { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) : iscomprelfun2 R ( setquotbooleqint R is ) .
Proof . intros . unfold iscomprelfun2 .    intros x x' x0 x0' r r0 .  unfold setquotbooleqint . destruct ( pr1 ( is x x0 ) ) as [ r1 | nr1 ]  .   destruct ( pr1 ( is x' x0' ) ) as [ r1' | nr1' ] . apply idpath . destruct ( nr1' ( eqreltrans R _ _ _ ( eqreltrans R _ _ _ ( eqrelsymm R _ _ r ) r1 ) r0 ) )  .   destruct ( pr1 ( is x' x0' ) ) as [ r1' | nr1' ] . destruct ( nr1 ( eqreltrans R _ _ _ r ( eqreltrans R _ _ _ r1' ( eqrelsymm R _ _ r0 ) ) ) ) . apply idpath .   Defined . 


Definition setquotbooleq { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) : setquot R -> setquot R -> bool := setquotuniv2 R ( hSetpair _ ( isasetbool ) ) ( setquotbooleqint R is ) ( setquotbooleqintcomp R is ) .

Lemma setquotbooleqtopaths  { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) ( x x' : setquot R ) : paths ( setquotbooleq R is x x' ) true  -> paths x x' . 
Proof . intros X R is . assert ( isp : forall x x' : setquot R , isaprop ( paths ( setquotbooleq R is x x' ) true  -> paths x x' ) ) . intros x x' . apply impred . intro . apply ( isasetsetquot R x x' ) .     apply ( setquotuniv2prop R ( fun x x' => hProppair _ ( isp x x' ) ) ) . simpl .    intros x x' .  change ( paths (setquotbooleqint R is x x' ) true -> paths (setquotpr R x) (setquotpr R x') ) . unfold setquotbooleqint .  destruct ( pr1 ( is x x' ) ) as [ i1 | i2 ] . intro .  apply ( weqpathsinsetquot R _ _ i1 ) .  intro H . destruct ( nopathsfalsetotrue H ) .  Defined .  

Lemma setquotpathstobooleq  { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) ( x x' : setquot R ) : paths x x' -> paths ( setquotbooleq R is x x' ) true .
Proof . intros X R is x x' e . destruct e . generalize x .  apply ( setquotunivprop R ( fun x => hProppair _ ( isasetbool (setquotbooleq R is x x) true ) ) ) .  simpl .  intro x0 .  change ( paths ( setquotbooleqint R is x0 x0 ) true ) .  unfold setquotbooleqint .  destruct ( pr1 ( is x0 x0 ) ) as [ i1 | i2 ] .  apply idpath .  destruct ( i2 ( eqrelrefl R x0 ) ) .  Defined . 

Definition  isdeceqsetquot { X : UU0 } ( R : eqrel X ) ( is : forall x x' : X , isdecprop ( R x x' ) ) : isdeceq ( setquot R ) .
Proof . intros . intros x x' .  destruct ( boolchoice ( setquotbooleq R is x x' ) ) as [ i | ni ] .  apply ( ii1 ( setquotbooleqtopaths R is x x' i ) ) . apply ii2 .   intro e .  destruct ( falsetonegtrue _ ni ( setquotpathstobooleq R is x x' e ) ) . Defined . 



(** *** Relations on quotient sets 

Note that all the properties of the quotient relations which we consider other than [ isantisymm ] are also inhereted in the opposite direction - if the quotent relation satisfies the property then the original relation does .  *)

Definition iscomprelrel { X : UU0 } ( R : hrel X ) ( L : hrel X ) := iscomprelfun2 R L .

Lemma iscomprelrelif { X : UU0 } { R : hrel X } ( L : hrel X ) ( isr : issymm R ) ( i1 : forall x x' y , R x x' -> L x y -> L x' y ) ( i2 : forall x y y' , R y y' -> L x y -> L x y' ) : iscomprelrel R L .
Proof . intros .  intros x x' y y' rx ry .  set ( rx' := isr _ _ rx ) . set ( ry' := isr _ _ ry ) . apply uahp .  intro lxy .  set ( int1 := i1 _ _ _ rx lxy ) . apply ( i2 _ _ _ ry int1 ) .  intro lxy' .  set ( int1 := i1 _ _ _ rx' lxy' ) .  apply ( i2 _ _ _ ry' int1 ) .  Defined . 

Lemma iscomprelrellogeqf1 { X : UU0 } { R R' : hrel X } ( L : hrel X ) ( lg : hrellogeq R R' ) ( is : iscomprelrel R L ) : iscomprelrel R' L .
Proof . intros . apply ( iscomprelfun2logeqf lg L is ) .  Defined .

Lemma iscomprelrellogeqf2 { X : UU0 } ( R : hrel X ) { L L' : hrel X } ( lg : hrellogeq L L' ) ( is : iscomprelrel R L ) : iscomprelrel R L' .
Proof . intros . intros x x' x0 x0' r r0 . assert ( e : paths ( L x x0 ) ( L' x x0 ) ) . apply uahp . apply ( pr1 ( lg _ _ ) ) .   apply ( pr2 ( lg _ _ ) ) .  assert ( e' : paths ( L x' x0' ) ( L' x' x0' ) ) . apply uahp . apply ( pr1 ( lg _ _ ) ) .   apply ( pr2 ( lg _ _ ) ) . destruct e .  destruct e' .  apply ( is _ _ _ _ r r0 ) . Defined . 

Definition quotrel  { X : UU0 } { R L : hrel X } ( is : iscomprelrel R L ) : hrel ( setquot R ) := setquotuniv2 R hPropset L is .

Lemma istransquotrel { X : UU0 } { R : eqrel X } { L : hrel X } ( is : iscomprelrel R L ) ( isl : istrans L ) : istrans ( quotrel is ) .
Proof . intros . unfold istrans.  assert ( int : forall x1 x2 x3 : setquot R , isaprop ( quotrel is x1 x2 -> quotrel is x2 x3 -> quotrel is x1 x3 ) ) .  intros x1 x2 x3 . apply impred . intro . apply impred . intro . apply ( pr2 ( quotrel is x1 x3 ) ) .  apply ( setquotuniv3prop R ( fun x1 x2 x3 => hProppair _ ( int x1 x2 x3 ) ) ) .  intros x x' x'' . intros r r' . apply ( isl x x' x'' r r' ) . Defined .   

Lemma issymmquotrel  { X : UU0 } { R : eqrel X } { L : hrel X } ( is : iscomprelrel R L ) ( isl : issymm L ) : issymm ( quotrel is ) .
Proof . intros . unfold issymm.  assert ( int : forall x1 x2 : setquot R , isaprop ( quotrel is x1 x2 -> quotrel is x2 x1 ) ) .  intros x1 x2 . apply impred . intro . apply ( pr2 ( quotrel is x2 x1 ) ) .  apply ( setquotuniv2prop R ( fun x1 x2 => hProppair _ ( int x1 x2 ) ) ) .  intros x x' . intros r . apply ( isl x x' r ) . Defined .

Lemma isreflquotrel { X : UU0 } { R : eqrel X } { L : hrel X } ( is : iscomprelrel R L ) ( isl : isrefl L ) : isrefl ( quotrel is ) .  
Proof . intros . unfold isrefl .  apply ( setquotunivprop R ) .   intro x .  apply ( isl x ) . Defined . 

Lemma ispoquotrel  { X : UU0 } { R : eqrel X } { L : hrel X } ( is : iscomprelrel R L ) ( isl : ispo L ) : ispo ( quotrel is ) .
Proof . intros . split with ( istransquotrel is ( pr1 isl ) ) .  apply ( isreflquotrel is ( pr2 isl ) ) .  Defined . 

Lemma iseqrelquotrel  { X : UU0 } { R : eqrel X } { L : hrel X } ( is : iscomprelrel R L ) ( isl : iseqrel L ) : iseqrel ( quotrel is ) .
Proof . intros . split with ( ispoquotrel is ( pr1 isl ) ) .  apply ( issymmquotrel is ( pr2 isl ) ) .  Defined . 

Lemma isirreflquotrel { X : UU0 } { R : eqrel X } { L : hrel X } ( is : iscomprelrel R L ) ( isl : isirrefl L ) : isirrefl ( quotrel is ) .  
Proof . intros . unfold isirrefl .  apply ( setquotunivprop R ( fun x => hProppair _ ( isapropneg (quotrel is x x) ) ) ) .   intro x .  apply ( isl x ) . Defined .   

Lemma isasymmquotrel { X : UU0 } { R : eqrel X } { L : hrel X } ( is : iscomprelrel R L ) ( isl : isasymm L ) : isasymm ( quotrel is ) .
Proof . intros . unfold isasymm.  assert ( int : forall x1 x2 : setquot R , isaprop ( quotrel is x1 x2 -> quotrel is x2 x1 -> empty ) ) .  intros x1 x2 . apply impred . intro . apply impred . intro . apply isapropempty .  apply ( setquotuniv2prop R ( fun x1 x2 => hProppair _ ( int x1 x2 ) ) ) .  intros x x' . intros r r' . apply ( isl x x' r r' ) . Defined .

Lemma iscoasymmquotrel { X : UU0 } { R : eqrel X } { L : hrel X } ( is : iscomprelrel R L ) ( isl : iscoasymm L ) : iscoasymm ( quotrel is ) .
Proof . intros . unfold iscoasymm.  assert ( int : forall x1 x2 : setquot R , isaprop ( neg ( quotrel is x1 x2 ) -> quotrel is x2 x1 ) ) .  intros x1 x2 . apply impred . intro . apply ( pr2 _ ) .  apply ( setquotuniv2prop R ( fun x1 x2 => hProppair _ ( int x1 x2 ) ) ) .  intros x x' . intros r . apply ( isl x x' r ) . Defined .

Lemma istotalquotrel { X : UU0 } { R : eqrel X } { L : hrel X } ( is : iscomprelrel R L ) ( isl : istotal L ) : istotal ( quotrel is ) .
Proof . intros .  unfold istotal . apply ( setquotuniv2prop R ( fun x1 x2 => hdisj _ _ ) ) .  intros x x' . intros r r' . apply ( isl x x' r r' ) . Defined .

Lemma iscotransquotrel { X : UU0 } { R : eqrel X } { L : hrel X } ( is : iscomprelrel R L ) ( isl : iscotrans L ) : iscotrans ( quotrel is ) .
Proof . intros .  unfold iscotrans . assert ( int : forall x1 x2 x3 : setquot R , isaprop ( quotrel is x1 x3 -> hdisj (quotrel is x1 x2) (quotrel is x2 x3) ) ) . intros . apply impred . intro . apply ( pr2 _ ) . apply ( setquotuniv3prop R ( fun x1 x2 x3 => hProppair  _ ( int x1 x2 x3 ) ) ) .  intros x x' x'' . intros r . apply ( isl x x' x'' r  ) . Defined .

Lemma isantisymmquotrel { X : UU0 } { R : eqrel X } { L : hrel X } ( is : iscomprelrel R L ) ( isl : isantisymm L ) : isantisymm ( quotrel is ) .
Proof . intros . unfold isantisymm.  assert ( int : forall x1 x2 : setquot R , isaprop ( quotrel is x1 x2 -> quotrel is x2 x1 -> paths x1 x2 ) ) .  intros x1 x2 . apply impred . intro . apply impred . intro . apply ( isasetsetquot R x1 x2 ) .  apply ( setquotuniv2prop R ( fun x1 x2 => hProppair _ ( int x1 x2 ) ) ) .  intros x x' . intros r r' . apply ( maponpaths ( setquotpr R ) ( isl x x' r r' ) ) . Defined .
 
Lemma isantisymmnegquotrel { X : UU0 } { R : eqrel X } { L : hrel X } ( is : iscomprelrel R L ) ( isl : isantisymmneg L ) : isantisymmneg ( quotrel is ) .
Proof . intros . unfold isantisymmneg.  assert ( int : forall x1 x2 : setquot R , isaprop ( neg ( quotrel is x1 x2 ) -> neg ( quotrel is x2 x1 ) -> paths x1 x2 ) ) .  intros x1 x2 . apply impred . intro . apply impred . intro . apply ( isasetsetquot R x1 x2 ) .  apply ( setquotuniv2prop R ( fun x1 x2 => hProppair _ ( int x1 x2 ) ) ) .  intros x x' . intros r r' . apply ( maponpaths ( setquotpr R ) ( isl x x' r r' ) ) . Defined .

(** We do not have a lemma for [ neqchoicequotrel ] since [ neqchoice ] is not a property and since even when it is a property such as under the additional condition [ isasymm ] on the relation it still carrier computational content (similarly to [ isdec ]) which would be lost under our current approach of taking quotients. How to best define [neqchoicequotrel] remains at the moment an open question.*)


Lemma quotrelimpl { X : UU0 } { R : eqrel X } { L L' : hrel X } ( is : iscomprelrel R L ) ( is' : iscomprelrel R L' ) ( impl : forall x x' , L x x' -> L' x x' ) ( x x' : setquot R ) ( ql : quotrel is x x' ) : quotrel is' x x'  .
Proof . intros .  generalize x x' ql . assert ( int : forall x0 x0' , isaprop ( quotrel is x0 x0' -> quotrel is' x0 x0' ) ) . intros x0 x0' . apply impred . intro . apply ( pr2 _ ) . apply ( setquotuniv2prop _ ( fun x0 x0' => hProppair _ ( int x0 x0' ) ) ) . intros x0 x0' .  change ( L x0 x0' -> L' x0 x0' ) .  apply ( impl x0 x0' ) . Defined . 

Lemma quotrellogeq { X : UU0 } { R : eqrel X } { L L' : hrel X } ( is : iscomprelrel R L ) ( is' : iscomprelrel R L' ) ( lg : forall x x' , L x x' <-> L' x x' ) ( x x' : setquot R ) : ( quotrel is x x' ) <-> ( quotrel is' x x' ) .
Proof . intros . split . apply ( quotrelimpl is is' ( fun x0 x0' => pr1 ( lg x0 x0' ) ) x x' ) .  apply ( quotrelimpl is' is ( fun x0 x0' => pr2 ( lg x0 x0' ) ) x x' ) . Defined . 


(** Constructive proof of decidability of the quotient relation *)


Definition quotdecrelint { X : UU0 } { R : hrel X } ( L : decrel X ) ( is : iscomprelrel R ( pr1 L ) )  : brel ( setquot R ) .
Proof .    intros .  set ( f := decreltobrel L ) .  unfold brel . apply ( setquotuniv2 R _ f ) . intros x x' x0 x0' r r0. unfold f . unfold decreltobrel in * .  destruct ( pr2 L x x0' ) as [ l | nl ] . destruct ( pr2 L x' x0' ) as [ l' | nl' ] .  destruct ( pr2 L x x0 ) as [ l'' | nl'' ] . apply idpath .  set ( e := is x x' x0 x0' r r0 ) . destruct e . destruct ( nl'' l' ) .   destruct ( pr2 L x x0 ) as [ l'' | nl'' ] .  set ( e := is x x' x0 x0' r r0 ) . destruct e . destruct ( nl' l'' ) .  apply idpath . destruct ( pr2 L x x0 ) as [ l' | nl' ] . destruct ( pr2 L x' x0' ) as [ l'' | nl'' ] .  apply idpath .  set ( e := is x x' x0 x0' r r0 ) . destruct e . destruct ( nl'' l' ) . destruct ( pr2 L x' x0' ) as [ l'' | nl'' ] .  set ( e := is x x' x0 x0' r r0 ) . destruct e . destruct ( nl' l'' ) .    apply idpath . Defined .

Definition quotdecrelintlogeq { X : UU0 } { R : eqrel X } ( L : decrel X ) ( is : iscomprelrel R ( pr1 L ) ) ( x x' : setquot R ) : breltodecrel ( quotdecrelint L is ) x x' <-> quotrel is x x' .
Proof . intros X R L is . assert ( int : forall x x' , isaprop ( paths ( quotdecrelint L is x x' ) true  <-> ( quotrel is x x' ) ) ) .  intros x x' . apply isapropdirprod .    apply impred . intro . apply ( pr2 ( quotrel _ _ _ ) ) . apply impred . intro . apply isasetbool .  apply ( setquotuniv2prop R ( fun x x' => hProppair _ ( int x x' ) ) ) . intros x x' .   simpl . split .  apply ( pathstor L x x' ) . apply ( rtopaths L x x' ) . Defined .

Lemma isdecquotrel { X : UU0 } { R : eqrel X } { L : hrel X } ( is : iscomprelrel R L ) ( isl : isdecrel L ) : isdecrel ( quotrel is ) .
Proof . intros . apply ( isdecrellogeqf ( quotdecrelintlogeq ( decrelpair isl ) is ) ( pr2 ( breltodecrel ( quotdecrelint ( decrelpair isl ) is ) ) ) ) .  Defined .   

Definition decquotrel  { X : UU0 } { R : eqrel X } ( L : decrel X ) ( is : iscomprelrel R L ) : decrel ( setquot R ) := decrelpair ( isdecquotrel is ( pr2 L ) ) . 



(** *** Subtypes of quotients and quotients of subtypes *)


Definition reseqrel { X : UU0 } ( R : eqrel X ) ( P : hsubtypes X ) : eqrel P := eqrelpair _ ( iseqrelresrel R P ( pr2 R ) ) . 

Lemma iseqclassresrel { X : UU0 } ( R : hrel X ) ( P Q : hsubtypes X ) ( is : iseqclass R Q ) ( is' : forall x , Q x -> P x ) : iseqclass ( resrel R P ) ( fun x : P => Q ( pr1 x ) ) .
Proof . intros . split .

set ( l1 := pr1 is ) . generalize l1 . clear l1 . simpl . apply hinhfun . intro q . split with ( carrierpair P ( pr1 q ) ( is' ( pr1 q ) ( pr2 q ) ) ) . apply ( pr2 q ) .  split . 

intros p1 p2 r12 q1 . apply ( ( pr1 ( pr2 is ) ) _ _ r12 q1 ) . 

intros p1 p2 q1 q2 . apply ( ( pr2 ( pr2 is ) ) _ _ q1 q2 ) . Defined . 

Definition fromsubquot { X : UU0 } ( R : eqrel X ) ( P : hsubtypes ( setquot R ) ) ( p : P )  : setquot ( resrel R ( funcomp ( setquotpr R ) P ) ) .
Proof . intros . split with ( fun rp : carrier (funcomp (setquotpr R) P) => ( pr1 p ) ( pr1 rp ) ) .  apply ( iseqclassresrel R ( funcomp ( setquotpr R ) P ) _ ( pr2 ( pr1 p ) ) ) . intros x px .  set ( e := setquotl0 R _ ( carrierpair _ x px ) ) .  (* *) simpl in e . unfold funcomp . rewrite e . apply ( pr2 p ) . Defined .  

Definition tosubquot { X : UU0 } ( R : eqrel X ) ( P : hsubtypes ( setquot R ) ) : setquot ( resrel R ( funcomp ( setquotpr R ) P ) ) -> P .
Proof . intros X R P . assert ( int : isaset P ) . apply ( isasetsubset ( @pr1 _ P ) ) . apply ( setproperty ( setquotinset R ) ) . apply isinclpr1carrier . apply ( setquotuniv _ ( hSetpair _ int ) ( fun xp => carrierpair P ( setquotpr R ( pr1 xp ) ) ( pr2 xp ) ) ) .  intros xp1 xp2 rp12 . apply ( invmaponpathsincl _ ( isinclpr1carrier P ) _ _ ) . simpl .  apply ( iscompsetquotpr ) . apply rp12 . Defined .  

Definition weqsubquot { X : UU0 } ( R : eqrel X ) ( P : hsubtypes ( setquot R ) ) : weq P ( setquot ( resrel R ( funcomp ( setquotpr R ) P ) ) ) .
Proof . intros . set ( f := fromsubquot R P ) . set ( g := tosubquot R P ) .  split with f .  assert ( int0 : isaset P ) . apply ( isasetsubset ( @pr1 _ P ) ) . apply ( setproperty ( setquotinset R ) ) . apply isinclpr1carrier .

assert ( egf : forall a , paths ( g ( f a ) ) a ) .  intros a .  destruct a as [ p isp ] . generalize isp . generalize p . clear isp . clear p .  assert ( int : forall p , isaprop ( forall isp : P p , paths (g (f {| pr1 := p; pr2 := isp |})) {| pr1 := p; pr2 := isp |} ) ) .  intro p . apply impred . intro . apply ( int0 _ _ ) . apply ( setquotunivprop _ ( fun a =>  hProppair _ ( int a ) ) ) .  simpl . intros x isp .  apply ( invmaponpathsincl _ ( isinclpr1carrier P ) _ _ ) .  apply idpath . 

assert ( efg : forall a , paths ( f ( g a ) ) a ) . assert ( int : forall a , isaprop ( paths ( f ( g a ) ) a ) ) . intro a . apply ( setproperty ( setquotinset (resrel R (funcomp (setquotpr R) P)) )  ) . set ( Q := reseqrel R (funcomp (setquotpr R) P) ) . apply ( setquotunivprop Q ( fun a : setquot (resrel R (funcomp (setquotpr R) P)) =>  hProppair _ ( int a ) ) ) .   intro a . simpl .  unfold f . unfold g . unfold fromsubquot . unfold tosubquot . simpl .  apply ( invmaponpathsincl _ ( isinclpr1 _ ( fun a => isapropiseqclass _ a ) ) ) .  apply idpath .  

apply ( gradth _ _ egf efg ) . Defined .

(** Comment: unfortunetely [ weqsubquot ] is not as useful as it should be at moment due to the failure of the following code to work: 

[ Lemma test ( X : UU0 ) ( R : eqrel X ) ( P : hsubtypes ( setquot R ) ) ( x : X ) ( is : P ( setquotpr R x ) ) : paths ( setquotpr ( reseqrel R (funcomp (setquotpr R) P) ) ( tpair _ x is ) ) ( fromsubquot R P ( tpair _ ( setquotpr R x ) is ) ) .  
Proof . intros . apply idpath . Defined . ]

As one of the consequences we are forced to use a "hack" in the definition of multiplicative inverses for rationals in [ hqmultinv ] .

The issue which arises here is the same one which arises in several other places in the work with quotients. It can be traced back first to the failure of [ invmaponpathsincl ] to map [ idpath ] to [ idpath ] and then to the fact that for [ ( X : UU ) ( is : isaprop X ) ] the term [ t := proofirrelevance is : forall x1 x2 : X , paths x1 x2 ] does not satisfy (definitionally) the condition [ t x x == idpath x ]. 

It can and probably should be fixed by the addition of a new componenet to CIC in the form of a term constructor:

tfc ( X : Type ) ( E : X -> Type ) ( is : forall x , iscontr ( E x ) ) ( x0 : X ) ( e0 : E x0 ) : forall x : X , E x . 

and a computation rule

tfc_comp ( tfc X E is x0 e0 x0 ) == e0 

(with both tfc and tfc_comp definable in an arbitrary context)

Such an extension will be compatible with the univalent models and should not, as far as I can see, provide any problems for normalization or for the decidability of typing. Using tfc one can give a construction of [ proofirrelevance ] as follows ( recall that [ isaprop := forall x1 x2 , iscontr ( paths x1 x2 ) ] ) :

Lemma proofirrelevance { X : UU } ( is : isaprop X ) : forall x1 x2 , paths x1 x2 .
Proof . intros X is x1 . apply ( tfc X ( fun x2 => paths x1 x2 ) is x1 ( idpath x1 ) ) . Defined . 

Defined in this way [ proofirrelevance ] will have the required property and will enable to define [ invmaponpathsincl ] in such a way that the existing proofs of [ setquotl0 ] and [ fromsubquot ] and [ weqsubquot ] will provide the desired behavior of [ fromsubquot ] on terms of the form [ ( tpair _ ( setquotpr R x ) is ) ]. *)




(** *** The set of connected components of type. *)



Definition pathshrel ( X : UU0 ) := fun x x' : X  =>  ishinh ( paths x x' )  .
Definition istranspathshrel ( X : UU0 ) : istrans ( pathshrel X ) := fun x x' x'' : _ => fun a : _ => fun b : _ =>  hinhfun2 (fun e1 : paths x x' => fun e2 : paths x' x'' => pathscomp0 e1 e2 ) a b .
Definition isreflpathshrel ( X : UU0 ) : isrefl ( pathshrel X ) := fun x : _ =>  hinhpr _ ( idpath x ) .
Definition issymmpathshrel ( X : UU0 ) : issymm ( pathshrel X ) := fun x x': _ => fun a : _ => hinhfun ( fun e : paths x x' => pathsinv0 e ) a . 

Definition pathseqrel ( X : UU0 ) := eqrelconstr ( pathshrel X ) ( istranspathshrel X ) ( isreflpathshrel X ) ( issymmpathshrel X ) . 

Definition pi0 ( X : UU0 ) := setquot ( pathshrel X ) . 
Definition pi0pr ( X : UU0 ) := setquotpr ( pathseqrel X ) .









(** **  Set quotients. Construction 2. 


****************** THIS SECTION IS UNFINISHED ******************


Another construction of the set quotient is based on the following idea. Let X be a set. Then we have the obvious "double evaluation map" from X to the product over all sets Y of the sets ((X -> Y) -> Y). This is always an inclusion and in particular X is isomorphic to the image of this map. Suppore now we have a relation (which need not be an equivalence relation) R on X. Then we know that (X/R -> Y) is a subset of (X -> Y) which consists of functions compatible with the relation even if we do not know what X/R is. Thus we may consider the image of X in the product over all Y of ((X/R -> Y) ->Y) and it must be isomorphic to X/R. This ideas are realized in the definitions given below. There are two advantages to this approach. One is that the relation need not be an equivalence relation. Another one is that it can be more easily generalized to the higher quotients of type.


We also show that two constructions of set-quotients of types - the one given in set_quotients and the one given here agree up to an isomorphism (weak equivalence). *)




(** *** Functions compatible with a relation *)




Definition compfun { X : UU0 }  ( R : hrel X ) ( S : UU0 ) : UU0 := total2  (fun F: X -> S => iscomprelfun R F ) . 
Definition compfunpair { X : UU0 }  ( R : hrel X ) { S : UU0 } ( f : X -> S ) ( is : iscomprelfun R f ) : compfun R S := tpair _ f is .
Definition pr1compfun ( X : UU0 )  ( R : hrel X ) ( S : UU0 ) : @compfun X R S -> ( X -> S ) := @pr1 _ _ .
Coercion pr1compfun : compfun >-> Funclass .   

Definition compevmapset { X : UU0 } ( R : hrel X ) : X -> forall S : hSet, ( compfun R S ) -> S := fun x : X => fun S : _ => fun f : compfun R S => pr1 f x.

Definition compfuncomp { X : UU0 }  ( R : hrel X ) { S S' : UU0 } ( f : compfun R S ) ( g : S -> S' ) : compfun R S' .
Proof . intros . split with ( funcomp f g ) . intros x x' r .  apply ( maponpaths g ( pr2 f x x' r ) ) . Defined . 


(** Tests 

Definition F ( X Y : UU ) ( R : hrel X ) := ( compfun R Y ) -> Y .

Definition Fi ( X Y : UU ) ( R : hrel X ) : X -> F X Y R := fun x => fun f => f x .

Lemma iscompFi { X Y : UU } ( R : hrel X ) : iscomprelfun R ( Fi X Y R ) .
Proof . intros . intros x x' r . unfold Fi . apply funextfun .  intro f . apply ( pr2 f x x' r ) .  Defined . 

Definition Fv { X Y : UU } ( R : hrel X ) ( f : compfun R Y ) ( phi : F X Y R ) : Y := phi f . 

Definition qeq { X Y : UU } ( R : hrel X ) := total2 ( fun phi : F X Y R => forall psi : F X Y R -> Y  , paths ( psi phi ) ( Fv R ( compfuncomp R ( compfunpair R _ ( iscompFi R ) ) psi ) phi ) ) .  

Lemma isinclpr1qeq { X : UU } ( R : hrel X ) ( Y : hSet ) : isincl ( @pr1 _ ( fun phi : F X Y R => forall psi : F X Y R -> Y  , paths ( psi phi ) ( Fv R ( compfuncomp R ( compfunpair R _ ( iscompFi R ) ) psi ) phi ) ) ) .
Proof . intros . apply isinclpr1 .  intro phi .  apply impred . intro psi .  apply ( pr2 Y ) . Defined.  

Definition toqeq { X Y : UU } ( R : hrel X ) ( x : X ) : @qeq X Y R .
Proof . intros . split with ( Fi X Y R x ) . intro psi. apply idpath . Defined . 

Lemma iscomptoqeq  { X : UU } ( Y : hSet ) ( R : hrel X ) : iscomprelfun R ( @toqeq X Y R ) .
Proof . intros . intros x x' r . unfold toqeq . apply ( invmaponpathsincl _ ( isinclpr1qeq R Y ) ) . apply (  @iscompFi X Y R x x' r ) . Defined . 

Definition qequniv { X : UU } ( Y : hSet ) ( R : hrel X ) ( f : compfun R Y ) ( phi : @qeq X Y R ) : Y .
Proof . intros . apply ( Fv R f ( pr1 phi ) ) . Defined.

Lemma qequnivandpr { X : UU } ( Y : hSet ) ( R : hrel X ) ( f : compfun R Y ) ( x : X ) : paths ( qequniv Y R f ( toqeq R x ) ) ( f x ) .
Proof . intros . apply idpath . Defined .  

Lemma etaqeq { X : UU } ( Y : hSet ) ( R : hrel X ) ( psi : qeq R -> Y ) ( phi : qeq R ) : paths ( psi phi ) ( qequniv Y R ( compfuncomp R ( compfunpair R _ ( iscomptoqeq Y R ) ) psi ) phi ) .  
Proof .  intros . apply ( pr2 phi psi ) .  




Definition Fd1 { X Y : UU } : F X Y R -> ( F ( F X Y ) Y ) := Fi ( F X Y ) Y . 

Definition Fd2 { X Y : UU } ( R : hrel X ) ( phi : F X Y R ) ( psi : F X Y R -> Y ) : Y := ( Fv R ( funcomp ( Fi X Y R ) psi ) phi ) . 

Definition Ffunct { X1 X2 : UU } ( f : X1 -> X2 ) ( Y : UU ) : F X1 Y -> F X2 Y := fun phi => fun g => phi ( funcomp f g ) . 



Lemma testd1 { X Y : UU } ( psi : F X Y -> Y ) ( phi : F X Y ) : paths ( psi phi ) ( Fd1 phi psi )  .  
Proof . intros . apply idpath . Defined . 

Lemma testd2 { X Y : UU } ( psi : F X Y -> Y ) ( phi : F X Y ) : paths ( Fv ( funcomp ( Fi X Y ) psi ) phi ) ( Fd2 phi psi )  .
Proof . intros . apply idpath . Defined .  

Definition F ( X Y : UU ) := ( X -> Y ) -> Y .

Definition Ffunct { X1 X2 : UU } ( f : X1 -> X2 ) ( Y : UU ) : F X1 Y -> F X2 Y := fun phi => fun g => phi ( funcomp f g ) . 

Definition Fi ( X Y : UU ) : X -> F X Y := fun x => fun f => f x .

Definition Fd1 { X Y : UU } : F X Y -> ( F ( F X Y ) Y ) := Fi ( F X Y ) Y . 

Definition Fd2 { X Y : UU } : F X Y -> ( F ( F X Y ) Y ) := Ffunct ( Fi X Y ) Y .

Definition Fv { X Y : UU } ( f : X -> Y ) ( phi : F X Y ) : Y := phi f .  

Lemma testd1 { X Y : UU } ( psi : F X Y -> Y ) ( phi : F X Y ) : paths ( psi phi ) ( Fd1 phi psi )  .  
Proof . intros . apply idpath . Defined . 

Lemma testd2 { X Y : UU } ( psi : F X Y -> Y ) ( phi : F X Y ) : paths ( Fv ( funcomp ( Fi X Y ) psi ) phi ) ( Fd2 phi psi )  .
Proof . intros . apply idpath . Defined .  





Lemma Xineq ( X Y : UU ) ( x : X ) : paths ( Fd1 ( Fi X Y x ) ) ( Fd2 ( Fi X Y x ) ) .
Proof . intros . apply idpath . Defined .   

Lemma test ( X Y : UU ) ( phi : F X Y ) ( f : X -> Y ) : paths ( Fd1 phi ( Fi ( X -> Y ) Y f ) ) ( Fd2 phi ( Fi ( X -> Y ) Y f ) ) .
Proof . intros . unfold Fd1 . unfold Fd2. unfold Fi . unfold Ffunct . unfold funcomp .    simpl .  apply ( maponpaths phi ) .  apply etacorrection . Defined . 

Inductive try0 ( T : Type ) ( t : T ) : forall ( t1 t2 : T ) ( e1 : paths t t1 ) ( e2 : paths t t2 ) , Type := idconstr : forall ( t' : T ) ( e' : paths t t' ) , try0 T t t' t' e' e' .

Definition try0map1 ( T : Type ) ( t : T ) ( t1 t2 : T ) ( e1 : paths t t1 ) ( e2 : paths t t2 ) ( X : try0 T t t1 t2 e1 e2 ) : paths t1 t2 .
Proof . intros . destruct  X . apply idpath . Defined . 

Definition try0map2  ( T : Type ) ( t : T ) ( t1 t2 : T ) ( e1 : paths t t1 ) ( e2 : paths t t2 ) : try0 T t t1 t2 e1 e2 .
Proof .     


Lemma test ( X : UU0 ) ( t : X ) : paths ( pr2 ( iscontrcoconustot X t ) (  pr1 ( iscontrcoconustot X t ) ) ) ( idpath _ ) .
Proof . intros . apply idpath . 


Lemma test { X : UU0 } ( is : iscontr X ) : paths ( pr2 ( iscontrcor is ) ( pr1 ( iscontrcor is ) ) ) ( idpath _ ) . 
Proof . intros . apply idpath . 




Lemma test { X : UU0 } ( R : eqrel X ) ( Y : hSet ) ( f : setquot R -> Y ) : paths f ( setquotuniv R Y ( funcomp ( setquotpr R ) f ) ( fun x x' : X => fun r : R x x' => maponpaths f ( iscompsetquotpr R x x' r ) ) ) .   
Proof . intros . apply funextfun .  intro c . simpl . destruct c as [ A iseq ] .  simpl .  *)






(** *** The quotient set of a type by a relation. *)

Definition setquot2 { X : UU0 } ( R : hrel X ) : UU0 := image  ( compevmapset R ) . 

Theorem isasetsetquot2 { X : UU0 } ( R : hrel X ) : isaset ( setquot2 R ) .
Proof. intros. 
assert (is1: isofhlevel 2 ( forall S: hSet, (compfun R S) -> S )).  apply impred.  intro.  apply impred.  intro X0.  apply (pr2 t).
apply (isasetsubset _ is1 (isinclpr1image _ )).  Defined.

Definition setquot2inset { X : UU0 } ( R : hrel X ) : hSet := hSetpair _ ( isasetsetquot2 R ) .  

(** We will be asuming below that setquot2 is in UU0.  In the future it should be proved using [ issurjsetquot2pr ] below and a resizing axiom. The appropriate resizing axiom for this should say that if X -> Y is a surjection, Y is an hset and X : UU then Y : UU . *)  

Definition setquot2pr { X : UU0 }  ( R : hrel X ) : X -> setquot2 R := fun x : X => imagepair ( compevmapset R ) _ ( hinhpr _ ( hfiberpair ( compevmapset R ) x ( idpath _ ) ) ) .

Lemma issurjsetquot2pr { X : UU0 } ( R : hrel X ) : issurjective ( setquot2pr R ) .
Proof. intros. apply issurjprtoimage. Defined.    

Lemma iscompsetquot2pr { X : UU0 } ( R : hrel X ) : iscomprelfun R ( setquot2pr R ) . 
Proof. intros.  intros x x' r . 
assert (e1: paths ( compevmapset R x ) ( compevmapset R x' ) ) .  apply funextsec. intro S.  apply funextsec.  intro f.   unfold compfun in f. apply ( pr2 f x x' r ) . 
apply ( invmaponpathsincl _ ( isinclpr1image ( compevmapset R ) ) ( setquot2pr R x ) ( setquot2pr R x' ) e1 ) . Defined . 


(** *** Universal property of [ seqtquot2 R ] for functions to sets satisfying compatibility condition [ iscomprelfun ] *)

Definition setquot2univ { X : UU0 } ( R : hrel X ) ( Y : hSet ) ( F : X -> Y ) (is : iscomprelfun R F ) ( c: setquot2 R ) : Y := pr1 c Y ( compfunpair _ F is ) .  

Theorem setquot2univcomm  { X : UU0 } ( R : hrel X ) ( Y : hSet ) ( F : X -> Y ) (iscomp : iscomprelfun R F ) ( x : X) : paths (setquot2univ _ _ F iscomp ( setquot2pr R x )) (F x) .  
Proof. intros. apply idpath. Defined.

(** *** Weak equivalence from [ R x x' ] to [ paths ( setquot2pr R x ) ( setquot2pr R x' ) ] *) 

Lemma weqpathssetquot2l1 { X : UU0 } ( R : eqrel X ) ( x : X ) : iscomprelfun R ( fun x' => R x x' ) . 
Proof . intros .  intros x' x'' .  intro r . apply uahp . intro r' .  apply ( eqreltrans R _ _ _ r' r ) . intro r'' .  apply ( eqreltrans R _ _ _ r'' ( eqrelsymm R _ _ r ) ) . Defined . 

Theorem weqpathsinsetquot2 { X : UU0 } ( R : eqrel X ) ( x x' : X ) : weq ( R x x' ) ( paths ( setquot2pr R x ) ( setquot2pr R x' ) ) .
Proof .  intros . apply weqimplimpl .  apply iscompsetquot2pr . set ( int := setquot2univ  R hPropset ( fun x'' => R x x'' ) ( weqpathssetquot2l1 R x ) ) .  intro e .  change ( pr1 ( int ( setquot2pr R x' ) ) ) . destruct e . change ( R x x ) . apply ( eqrelrefl R ) . apply ( pr2 ( R x x' ) ) . apply ( isasetsetquot2 ) .  Defined . 








(* *** Comparison of setquot2 and setquot.  *)



Definition setquottosetquot2 (X: UU0) (R: hrel X) (is: iseqrel R) : setquot R -> setquot2 R.
Proof. intros X R is X0. apply (setquotuniv R (hSetpair _ (isasetsetquot2 R)) (setquot2pr R) (iscompsetquot2pr R) X0).  Defined.










(* End of the file hSet.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)