(** * Algebra I. Part D.  Integral domains and fileds. Vladimir Voevodsky. Aug. 2011 - . 

*)



(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)


(** Imports *)

Require Export algebra1c .


(** To upstream files *)

(** To hSet *)

Lemma rtoneq { X : UU0 } { R : hrel X } ( is : isirrefl R ) { a b : X } ( r : R a b ) : neg ( paths a b ) .
Proof . intros . intro e . rewrite e in r . apply ( is b r ) . Defined .  

(** To one binary operation *)

Lemma islcancelableif { X : hSet } ( opp : binop X ) ( x : X ) ( is : forall a b : X , paths ( opp x a ) ( opp x b ) -> paths a b ) : islcancelable opp x . 
Proof . intros . apply isinclbetweensets . apply ( setproperty X ) . apply ( setproperty X ) . apply is .  Defined . 

Lemma isrcancelableif { X : hSet } ( opp : binop X ) ( x : X ) ( is : forall a b : X , paths ( opp a x ) ( opp b x ) -> paths a b ) : isrcancelable opp x . 
Proof . intros . apply isinclbetweensets . apply ( setproperty X ) . apply ( setproperty X ) . apply is .  Defined . 

Definition iscancelableif { X : hSet } ( opp : binop X ) ( x : X ) ( isl : forall a b : X , paths ( opp x a ) ( opp x b ) -> paths a b ) ( isr : forall a b : X , paths ( opp a x ) ( opp b x ) -> paths a b ) : iscancelable opp x := dirprodpair ( islcancelableif opp x isl ) ( isrcancelableif opp x isr ) . 


(** To monoids *)

Open Local Scope  multmonoid_scope. 

Definition linvpair ( X : monoid ) ( x : X ) := total2 ( fun x' : X => paths ( x' * x ) 1 ) .
Definition pr1linvpair ( X : monoid ) ( x : X ) : linvpair X x -> X := @pr1 _ _ .

Definition linvpairxy ( X : monoid ) ( x y : X ) ( x' : linvpair X x ) ( y' : linvpair X y ) : linvpair X ( x * y ) .
Proof . intros . split with ( ( pr1 y' ) * ( pr1 x' ) ) . rewrite ( assocax _ _ _ ( x * y ) ) .  rewrite ( pathsinv0 ( assocax _ _ x y ) ) . rewrite ( pr2 x' ) .  rewrite ( lunax _ y ) .  rewrite ( pr2 y' ) . apply idpath . Defined .   

Definition lcanfromlinv ( X : monoid ) ( a b c : X ) ( c' : linvpair X c ) ( e : paths ( c * a ) ( c * b ) ) : paths a b .
Proof . intros . assert ( e' := maponpaths ( fun x : X => ( pr1 c' ) * x ) e ) .  simpl in e' . rewrite ( pathsinv0 ( assocax X _ _ _ ) ) in e' .  rewrite ( pathsinv0 ( assocax X _ _ _ ) ) in e' . rewrite ( pr2 c' ) in e' .  rewrite ( lunax X a ) in e' .  rewrite ( lunax X b ) in e'. apply e' . Defined.


Definition rinvpair ( X : monoid ) ( x : X ) := total2 ( fun x' : X => paths ( x * x' ) 1 ) .
Definition pr1rinvpair ( X : monoid ) ( x : X ) : rinvpair X x -> X := @pr1 _ _ .

Definition rinvpairxy ( X : monoid ) ( x y : X ) ( x' : rinvpair X x ) ( y' : rinvpair X y ) : rinvpair X ( x * y ) .
Proof . intros . split with ( ( pr1 y' ) * ( pr1 x' ) ) . rewrite ( assocax _ x y _ ) .  rewrite ( pathsinv0 ( assocax _ y _ _ ) ) . rewrite ( pr2 y' ) .  rewrite ( lunax _ _ ) .  rewrite ( pr2 x' ) . apply idpath . Defined . 

Definition rcanfromrinv ( X : monoid ) ( a b c : X ) ( c' : rinvpair X c ) ( e : paths ( a * c  ) ( b * c ) ) : paths a b .
Proof . intros . assert ( e' := maponpaths ( fun x : X => x * ( pr1 c' ) ) e ) .  simpl in e' . rewrite ( assocax X _ _ _ )  in e' .  rewrite ( assocax X _ _ _ ) in e' . rewrite ( pr2 c' ) in e' .  rewrite ( runax X a ) in e' .  rewrite ( runax X b ) in e'. apply e' . Defined.

Lemma pathslinvtorinv ( X : monoid ) ( x : X ) ( x' : linvpair X x ) ( x'' : rinvpair X x ) : paths ( pr1 x' ) ( pr1 x'' ) .
Proof . intros .   destruct ( runax X ( pr1 x' ) ) . unfold p . destruct ( pr2 x'' ) . set ( int := x * pr1 x'' ) . change ( paths ( pr1 x' * int ) ( pr1 x'' ) ) .   destruct ( lunax X ( pr1 x'' ) ) . destruct ( pr2 x' ) .  unfold p1 . unfold int . apply ( pathsinv0 ( assocax X _ _ _ ) ) .  Defined . 

Definition invpair ( X : monoid ) ( x : X ) := total2 ( fun x' : X => dirprod ( paths ( x' * x ) 1 ) ( paths ( x * x' ) 1 ) ) .
Definition pr1invpair ( X : monoid ) ( x : X ) : invpair X x -> X := @pr1 _ _ .
Definition invtolinv ( X : monoid ) ( x : X ) ( x' : invpair X x ) : linvpair X x := tpair _ ( pr1 x' ) ( pr1 ( pr2 x' ) ) .
Definition invtorinv ( X : monoid ) ( x : X ) ( x' : invpair X x ) : rinvpair X x := tpair _ ( pr1 x' ) ( pr2 ( pr2 x' ) ) . 

Lemma isapropinvpair ( X : monoid ) ( x : X ) : isaprop ( invpair X x ) .
Proof . intros . apply invproofirrelevance . intros x' x'' . apply ( invmaponpathsincl _ ( isinclpr1 _ ( fun a => isapropdirprod _ _ ( setproperty X _ _ ) ( setproperty X _ _ ) ) ) ) .  apply ( pathslinvtorinv X x ( invtolinv X x x' ) ( invtorinv X x x'' ) ) . Defined. 

Definition invpairxy ( X : monoid ) ( x y : X ) ( x' : invpair X x ) ( y' : invpair X y ) : invpair X ( x * y ) .
Proof . intros . split with ( ( pr1 y' ) * ( pr1 x' ) ) . split .  apply ( pr2 ( linvpairxy _ x y ( invtolinv _ x x' ) ( invtolinv _ y y' ) ) ) .  apply ( pr2 ( rinvpairxy _ x y ( invtorinv _ x x' ) ( invtorinv _ y y' ) ) ) .  Defined . 


(** To groups *)

Lemma grfrompathsxy ( X : gr ) { a b : X } ( e : paths a b ) : paths ( op a ( grinv X b ) ) ( unel X ) .
Proof . intros .   assert  ( e' := maponpaths ( fun x : X => op x  ( grinv X b ) ) e ) . simpl in e' .  rewrite ( grrinvax X _ ) in e' .  apply e' . Defined .

Lemma grtopathsxy ( X : gr ) { a b : X } ( e : paths ( op a ( grinv X b ) ) ( unel X )  ) : paths a b  .
Proof . intros . assert ( e' := maponpaths ( fun x => op x b ) e ) . simpl in e' . rewrite ( assocax X ) in e' . rewrite ( grlinvax X ) in e' . rewrite ( lunax X ) in e' . rewrite ( runax X ) in e' . apply e' . Defined .    



(** To rigs *)

Definition multlinvpair ( X : rig ) ( x : X ) := linvpair ( rigmultmonoid X ) x .

Definition multrinvpair ( X : rig ) ( x : X ) := rinvpair ( rigmultmonoid X ) x .
 
Definition multinvpair ( X : rig ) ( x : X ) := invpair ( rigmultmonoid X ) x .

Definition rigneq0andmultlinv ( X : rig ) ( n m : X ) ( isnm : neg ( paths ( n * m ) 0 )%rig ) : neg ( paths n 0 )%rig .
Proof . intros . intro e .  rewrite e in isnm .  rewrite ( rigmult0x X ) in isnm .  destruct ( isnm ( idpath _ ) ) .  Defined . 

Definition rigneq0andmultrinv ( X : rig ) ( n m : X ) ( isnm : neg ( paths ( n * m ) 0 )%rig ) : neg ( paths m 0 )%rig .
Proof . intros . intro e .  rewrite e in isnm .  rewrite ( rigmultx0 _ ) in isnm .  destruct ( isnm ( idpath _ ) ) .  Defined . 



(** To rings *)

Local Open Scope rng_scope.

Definition rngneq0andmultlinv ( X : rng ) ( n m : X ) ( isnm : neg ( paths ( n * m ) 0 ) ) : neg ( paths n 0 ) .
Proof . intros . intro e .  rewrite e in isnm .  rewrite ( rngmult0x X ) in isnm .  destruct ( isnm ( idpath _ ) ) .  Defined . 

Definition rngneq0andmultrinv ( X : rng ) ( n m : X ) ( isnm : neg ( paths ( n * m ) 0 ) ) : neg ( paths m 0 ) .
Proof . intros . intro e .  rewrite e in isnm .  rewrite ( rngmultx0 _ ) in isnm .  destruct ( isnm ( idpath _ ) ) .  Defined . 


Definition rngpossubmonoid ( X : rng ) { R : hrel X } ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) : @submonoids ( rngmultmonoid X ) .
Proof . intros . split with ( fun x => R x 0 ) . split .  intros x1 x2 . apply is1 . apply ( pr2 x1 ) .  apply ( pr2 x2 ) .  apply is2 . Defined . 

Lemma isinvrngmultgtif ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( nc : neqchoice R ) ( isa : isasymm R ) : isinvrngmultgt X R .  
Proof . intros . split . 

intros a b rab0 ra0 . assert ( int : neg ( paths b 0 ) ) . intro e .  rewrite e in rab0 .  rewrite ( rngmultx0 X _ ) in rab0 .  apply ( isa _ _ rab0 rab0 ) . destruct ( nc _ _ int ) as [ g | l ] . apply g . set ( int' := rngmultgt0lt0 X is0 is1 ra0 l ) .  destruct ( isa _ _ rab0 int' ) .  

intros a b rab0 rb0 . assert ( int : neg ( paths a 0 ) ) . intro e .  rewrite e in rab0 .  rewrite ( rngmult0x X _ ) in rab0 .  apply ( isa _ _ rab0 rab0 ) . destruct ( nc _ _ int ) as [ g | l ] . apply g . set ( int' := rngmultlt0gt0 X is0 is1 l rb0 ) .  destruct ( isa _ _ rab0 int' ) .  Defined .




(** ** Standard Algebraic Structures (cont.) Integral domains and Fileds. 

Some of the notions condidered in this section were introduced in  C. Mulvey "Intuitionistic algebra and representations of rings". See also P.T. Johnstone "Rings, fields and spectra". We only consider here the strongest ("geometric") forms of the conditions of integrality and of being a field. In particular all our fileds have decidable equality and p-adic numbers or reals are not fileds in the sense of the definitions considered here.   *)

Local Open Scope rng_scope.


(** *** Integral domains *)

(** **** General definitions *)

Definition isnonzerorng ( X : rng ) := neg ( @paths X 1 0 ) .

Lemma isnonzerolinvel ( X : rng ) ( is : isnonzerorng X ) ( x : X ) ( x' : multlinvpair X x ) : neg ( paths ( pr1 x' ) 0 ) .
Proof . intros . apply ( negf ( maponpaths ( fun a : X => a * x ) ) ) .  assert ( e := pr2 x' ) . change ( paths ( pr1 x' * x ) 1 ) in e . change ( neg ( paths ( pr1 x' * x ) ( 0 * x ) ) ) .   rewrite e . rewrite ( rngmult0x X _ ) . apply is . Defined .     

Lemma isnonzerorinvel ( X : rng ) ( is : isnonzerorng X ) ( x : X ) ( x' : multrinvpair X x ) : neg ( paths ( pr1 x' ) 0 ) .
Proof . intros . apply ( negf ( maponpaths ( fun a : X => x * a ) ) ) .  assert ( e := pr2 x' ) . change ( paths ( x * pr1 x' ) 1 ) in e . change ( neg ( paths ( x * pr1 x' ) ( x * 0 ) ) ) .   rewrite e . rewrite ( rngmultx0 X _ ) . apply is . Defined .  

Lemma isnonzerofromlinvel ( X : rng ) ( is : isnonzerorng X ) ( x : X ) ( x' : multlinvpair X x ) : neg ( paths x 0 ) .
Proof .  intros .   apply ( negf ( maponpaths ( fun a : X => ( pr1 x' ) * a ) ) ) .  assert ( e := pr2 x' ) . change ( paths ( pr1 x' * x ) 1 ) in e . change ( neg ( paths ( pr1 x' * x ) ( ( pr1 x' ) * 0 ) ) ) .   rewrite e . rewrite ( rngmultx0 X _ ) . apply is . Defined .

Lemma isnonzerofromrinvel ( X : rng ) ( is : isnonzerorng X ) ( x : X ) ( x' : multrinvpair X x ) : neg ( paths x 0 ) .
Proof .  intros .   apply ( negf ( maponpaths ( fun a : X => a * ( pr1 x' ) ) ) ) .  assert ( e := pr2 x' ) . change ( paths ( x * pr1 x' ) 1 ) in e . change ( neg ( paths ( x * pr1 x' ) ( 0 * ( pr1 x' ) ) ) ) .   rewrite e . rewrite ( rngmult0x X _ ) . apply is . Defined .
 
Definition isintdom ( X : commrng ) := dirprod ( isnonzerorng X ) ( forall a1 a2 : X , paths ( a1 * a2 ) 0 -> hdisj ( eqset a1 0 ) ( eqset a2 0 ) ) .  

Definition intdom := total2 ( fun X : commrng => isintdom X ) .
Definition pr1intdom : intdom -> commrng := @pr1 _ _ .
Coercion pr1intdom : intdom >-> commrng .

Definition nonzeroax ( X : intdom ) : neg ( @paths X 1 0 ) := pr1 ( pr2 X ) .   
Definition intdomax ( X : intdom ) : forall a1 a2 : X , paths ( a1 * a2 ) 0 -> hdisj ( eqset a1 0 ) ( eqset a2 0 )  := pr2 ( pr2 X ) . 

(** **** Computational lemmas for integral domains *)

Lemma intdomax2l ( X : intdom ) ( x y : X ) ( is : paths ( x * y ) 0 ) ( ne : neg ( paths x 0 ) ) : paths y 0 .
Proof . intros .  assert ( int := intdomax X _ _ is ) .  generalize ne .  assert ( int' : isaprop ( neg (paths x 0) -> paths y 0 ) ) . apply impred . intro . apply ( setproperty X _ _ ) .  generalize int .  simpl .  apply ( @hinhuniv _ ( hProppair _ int' ) ) .  intro ene . destruct ene as [ e'' | ne' ] .  destruct ( ne e'' ) . intro .  apply ne' .  Defined .  

Lemma intdomax2r ( X : intdom ) ( x y : X ) ( is : paths ( x * y ) 0 ) ( ne : neg ( paths y 0 ) ) : paths x 0 .
Proof . intros .  assert ( int := intdomax X _ _ is ) .  generalize ne .  assert ( int' : isaprop ( neg (paths y 0) -> paths x 0 ) ) . apply impred . intro . apply ( setproperty X _ _ ) .  generalize int .  simpl .  apply ( @hinhuniv _ ( hProppair _ int' ) ) .  intro ene . destruct ene as [ e'' | ne' ] .   intro .  apply e'' . destruct ( ne ne' ) .  Defined .  


Definition intdomneq0andmult ( X : intdom ) ( n m : X ) ( isn : neg ( paths n 0 ) ) ( ism : neg ( paths m 0 ) ) : neg ( paths ( n * m ) 0 ) .
Proof . intros . intro e . destruct ( ism ( intdomax2l X n m e isn  ) ) .  Defined . 






Lemma intdomlcan ( X : intdom ) : forall a b c : X , neg ( paths c 0 ) -> paths ( c * a ) ( c * b ) -> paths a b .
Proof . intros X a b c ne e . apply ( @grtopathsxy ( rngaddabgr X ) a b ) . change ( paths ( a - b ) 0 ) . assert ( e' := grfrompathsxy ( rngaddabgr X ) e ) .  change ( paths ( ( c * a ) - ( c * b ) ) 0 ) in e' .  rewrite ( pathsinv0 ( rngrmultminus X _ _ ) ) in e' .  rewrite ( pathsinv0 ( rngldistr X _ _ c ) ) in e' . assert ( int := intdomax X _ _ e' ) .  generalize ne .  assert ( int' : isaprop ( neg (paths c 0) -> paths (a - b) 0 ) ) . apply impred . intro . apply ( setproperty X _ _ ) .  generalize int .  simpl .  apply ( @hinhuniv _ ( hProppair _ int' ) ) .  intro ene . destruct ene as [ e'' | ne' ] .  destruct ( ne e'' ) . intro .  apply ne' .  Defined . 

Opaque intdomlcan .

Lemma intdomrcan ( X : intdom ) : forall a b c : X , neg ( paths c 0 ) -> paths ( a * c ) ( b * c ) -> paths a b .
Proof . intros X a b c ne e . apply ( @grtopathsxy ( rngaddabgr X ) a b ) . change ( paths ( a - b ) 0 ) . assert ( e' := grfrompathsxy ( rngaddabgr X ) e ) .  change ( paths ( ( a * c ) - ( b * c ) ) 0 ) in e' .  rewrite ( pathsinv0 ( rnglmultminus X _ _ ) ) in e' .  rewrite ( pathsinv0 ( rngrdistr X _ _ c ) ) in e' . assert ( int := intdomax X _ _ e' ) .  generalize ne .  assert ( int' : isaprop ( neg (paths c 0) -> paths (a - b) 0 ) ) . apply impred . intro . apply ( setproperty X _ _ ) .  generalize int .  simpl .  apply ( @hinhuniv _ ( hProppair _ int' ) ) .  intro ene . destruct ene as [ e'' | ne' ] .  intro .  apply e'' .  destruct ( ne ne' ) .  Defined . 

Opaque intdomrcan .


Lemma intdomiscancelable ( X : intdom ) ( x : X ) ( is : neg ( paths x 0 ) ) : iscancelable ( @op2 X ) x . 
Proof . intros . apply iscancelableif .  intros a b . apply ( intdomlcan X a b x is ) .  intros a b . apply ( intdomrcan X a b x is ) . Defined .  



(** **** Multiplicative submonoid of non-zero elements *)


Definition intdomnonzerosubmonoid ( X : intdom ) : @subabmonoids ( rngmultabmonoid X ) .  
Proof . intros . split with ( fun x : X => hProppair _ ( isapropneg ( paths x 0 ) ) ) . split . 

intros a b . simpl in * .  intro e . set ( int := intdomax X ( pr1 a ) ( pr1 b ) e ) . clearbody int . generalize int . apply ( toneghdisj ) .  apply ( dirprodpair ( pr2 a ) ( pr2 b ) ) . 

simpl .  apply ( nonzeroax X ) . Defined .




(** **** Relations similar to "greater" on integral domains *)


Definition intdomnonzerotopos ( X : intdom ) ( R : hrel X ) ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) ( x : intdomnonzerosubmonoid X ) : rngpossubmonoid X is1 is2 .
Proof . intros . destruct ( nc ( pr1 x ) 0 ( pr2 x ) ) as [ g | l ] . apply ( tpair _ ( pr1 x ) g ) . split with ( - ( pr1 x ) ) .  simpl . apply rngtogt0 . apply is0 .  rewrite ( rngminusminus X _ ) .  apply l . Defined .





(** *** Ring units ( i.e. multilicatively invertible elements ) *)







(** *** Fields *)

(** **** Main definitions *)

Definition isafield ( X : commrng ) := dirprod ( isnonzerorng X ) ( forall x : X , coprod ( multinvpair X x ) ( paths x 0 ) ) . 

Definition fld := total2 ( fun X : commrng => isafield X ) .  
Definition fldpair ( X : commrng ) ( is : isafield X ) : fld := tpair _ X is . 
Definition pr1fld : fld -> commrng := @pr1 _ _ .

Definition fldtointdom ( X : fld ) : intdom .
Proof . intro . split with ( pr1 X ) .  split with ( pr1 ( pr2 X ) ) . intros a1 a2 . destruct ( pr2 ( pr2 X ) a1 ) as [ a1' | e0 ] . 

intro e12 . rewrite ( pathsinv0 ( rngmultx0 ( pr1 X ) a1 ) ) in e12 . set ( e2 := lcanfromlinv _ _ _ _ ( invtolinv _ _ a1' ) e12 ) .  apply ( hinhpr _ ( ii2 e2 ) ) .      

intro e12 . apply ( hinhpr _ ( ii1 e0 ) ) . Defined .  

Coercion fldtointdom : fld >-> intdom . 

Definition fldchoice { X : fld } ( x : X ) : coprod ( multinvpair X x ) ( paths x 0 ) := pr2 ( pr2 X ) x.

Definition fldmultinvpair ( X : fld ) ( x : X ) ( ne : neg ( paths x 0 ) ) : multinvpair X x .
Proof . intros . destruct ( fldchoice x ) as [ ne0 | e0 ] . apply ne0 . destruct ( ne e0 ) . Defined . 

Definition fldmultinv { X : fld } ( x : X ) ( ne : neg ( paths x 0 ) ) : X := pr1 ( fldmultinvpair X x ne ) .  


(** **** Field of fractions of an integral domain with decidable equality *)

Definition fldfracmultinvint ( X : intdom ) ( is : isdeceq X ) ( xa : dirprod X ( intdomnonzerosubmonoid X ) ) : dirprod X ( intdomnonzerosubmonoid X ) .
Proof .  intros . destruct ( is ( pr1 xa ) 0 ) as [ e0 | ne0 ] . apply ( dirprodpair 1 ( tpair ( fun x => neg ( paths x 0 ) ) 1 ( nonzeroax X ) ) ) . apply ( dirprodpair ( pr1 ( pr2 xa ) ) ( tpair ( fun x => neg ( paths x 0 ) ) ( pr1 xa ) ne0 ) ) .  Defined . 

(** Note: we choose a strange from the mathematicians perspective approach to the definition of the multiplicative inverse on non-zero elements of a field due to the current, somewhat less than satisfactory, situation with computational behavior of our construction of set-quotients. The particular problem is that the weak equivalence between "quotient of subtype" and "subtype of a quotient" is not isomorphism in the syntactic category. This can be corrected by extension of the type system with tfc-terms. See discussion in hSet.v *)

Lemma fldfracmultinvintcomp  ( X : intdom ) ( is : isdeceq X ) : iscomprelrelfun ( eqrelcommrngfrac X ( intdomnonzerosubmonoid X ) ) ( eqrelcommrngfrac X ( intdomnonzerosubmonoid X ) ) ( fldfracmultinvint X is ) .
Proof . intros .  intros xa1 xa2 .  set ( x1 := pr1 xa1 ) . set ( aa1 := pr2 xa1 ) . set ( a1 := pr1 aa1 ) . set ( x2 := pr1 xa2 ) . set ( aa2 := pr2 xa2 ) . set ( a2 := pr1 aa2 ) .  simpl .  apply hinhfun . intro t2 .  unfold fldfracmultinvint .  destruct ( is (pr1 xa1) 0 ) as [ e1 | ne1 ] . destruct ( is (pr1 xa2) 0 ) as [ e2 | ne2 ] . 

simpl .  split with ( tpair ( fun x => neg ( paths x 0 ) ) 1 ( nonzeroax X ) ) . apply idpath . 

simpl . set ( aa0 := pr1 t2 ) . set ( a0 := pr1 aa0 ) . assert ( e := pr2 t2 ) . change ( paths ( x1 * a2 * a0 ) ( x2 * a1 * a0 ) ) in e .  change ( paths x1 0 ) in e1 . rewrite e1 in e . rewrite ( rngmult0x X _ ) in e .   rewrite ( rngmult0x X _ ) in e . assert ( e' := intdomax2r X _ _ ( pathsinv0 e ) ( pr2 aa0 ) ) .   assert ( e'' := intdomax2r X _ _ e' ( pr2 aa1 ) ) . destruct ( ne2 e'' ) .  destruct ( is (pr1 xa2) 0 ) as [ e2 | ne2 ] .

simpl . set ( aa0 := pr1 t2 ) . set ( a0 := pr1 aa0 ) . assert ( e := pr2 t2 ) . change ( paths ( x1 * a2 * a0 ) ( x2 * a1 * a0 ) ) in e .  change ( paths x2 0 ) in e2 . rewrite e2 in e . rewrite ( rngmult0x X _ ) in e .   rewrite ( rngmult0x X _ ) in e . assert ( e' := intdomax2r X _ _  e ( pr2 aa0 ) ) .   assert ( e'' := intdomax2r X _ _ e' ( pr2 aa2 ) ) . destruct ( ne1 e'' ) .  

simpl .  set ( aa0 := pr1 t2 ) . set ( a0 := pr1 aa0 ) . assert ( e := pr2 t2 ) . split with aa0 . change ( paths ( a1 * x2 * a0 ) ( a2 * x1 * a0 ) ) .  change ( paths ( x1 * a2 * a0 ) ( x2 * a1 * a0 ) ) in e . rewrite ( rngcomm2 X a1 x2 ) .  rewrite ( rngcomm2 X a2 x1 ) .  apply ( pathsinv0 e ) .  Defined . 

Opaque fldfracmultinvintcomp .

 
Definition fldfracmultinv0 ( X : intdom ) ( is : isdeceq X ) ( x : commrngfrac X ( intdomnonzerosubmonoid X ) ) : commrngfrac X ( intdomnonzerosubmonoid X ) := setquotfun _ _ _ ( fldfracmultinvintcomp X is ) x . 


Lemma nonzeroincommrngfrac ( X : commrng ) ( S : @submonoids ( rngmultmonoid X ) ) ( xa : dirprod X S ) ( ne : neg ( paths ( setquotpr ( eqrelcommrngfrac X S ) xa ) ( setquotpr _ ( dirprodpair 0 ( unel S ) ) ) ) ) : neg ( paths ( pr1 xa ) 0 ) . 
Proof . intros . set ( x := pr1 xa ) . set ( aa := pr2 xa ) .  assert ( e' := negf ( weqpathsinsetquot ( eqrelcommrngfrac X S ) _ _ ) ne ) . simpl in e' . generalize e' .   apply negf .  intro e .  apply hinhpr .  split with ( unel S ) .  change ( paths ( x * 1 * 1 ) ( 0 * ( pr1 aa ) * 1 ) ) . rewrite e . rewrite ( rngmult0x X _ ) .  rewrite ( rngmult0x X _ ) .   rewrite ( rngmult0x X _ ) .  rewrite ( rngmult0x X _ ) . apply idpath . Defined . 

Opaque nonzeroincommrngfrac .

Lemma zeroincommrngfrac ( X : intdom ) ( S : @submonoids ( rngmultmonoid X ) ) ( is : forall s : S , neg ( paths ( pr1 s ) 0 ) ) ( x : X ) ( aa : S ) ( e : paths ( setquotpr ( eqrelcommrngfrac X S ) ( dirprodpair x aa ) ) ( setquotpr _ ( dirprodpair 0 ( unel S ) ) ) )  : paths x 0 . 
Proof . intros . assert ( e' := invweq ( weqpathsinsetquot _ _ _ ) e ) .  simpl in e' .  generalize e' .  apply ( @hinhuniv _ ( hProppair _ ( setproperty X _ _ ) ) ) . intro t2 . simpl . set ( aa0 := pr1 t2 ) . set ( a0 := pr1 aa0 ) . assert ( e2 := pr2 t2 ) . set ( a := pr1 aa ) .  simpl in e2 . change ( paths ( x * 1 * a0 ) ( 0 * a * a0 ) ) in e2 . rewrite ( rngmult0x X _ ) in e2 .  rewrite ( rngmult0x X _ ) in e2 . rewrite ( rngrunax2 X _ ) in e2 . apply ( intdomax2r X x a0 e2 ( is aa0 ) ) . Defined .    

Opaque zeroincommrngfrac . 


Lemma isdeceqfldfrac  ( X : intdom ) ( is : isdeceq X ) : isdeceq ( commrngfrac X ( intdomnonzerosubmonoid X ) ) . 
Proof . intros . apply isdeceqcommrngfrac .  intro a . apply isrcancelableif . intros b0 b1 e . apply ( intdomrcan X _ _ ( pr1 a ) ( pr2 a ) e ) .  apply is . Defined . 

Lemma islinvinfldfrac ( X : intdom ) ( is : isdeceq X ) ( x : commrngfrac X ( intdomnonzerosubmonoid X ) ) ( ne : neg ( paths x 0 ) ) : paths ( ( fldfracmultinv0 X is x ) * x ) 1 .
Proof . intros X is . assert ( int : forall x0 , isaprop ( neg ( paths x0 0 ) ->  paths ( ( fldfracmultinv0 X is x0 ) * x0 ) 1 ) ) . intro x0 . apply impred. intro . apply ( setproperty _ _ _ ) . apply ( setquotunivprop _ ( fun x0 => hProppair _ ( int x0 ) ) ) .  simpl . intros xa ne .  change ( paths ( setquotpr (eqrelcommrngfrac X (intdomnonzerosubmonoid X)) ( dirprodpair ( ( pr1 ( fldfracmultinvint X is xa ) ) * ( pr1 xa ) ) ( @op ( intdomnonzerosubmonoid X ) ( pr2 ( fldfracmultinvint X is xa ) ) ( pr2 xa ) ) ) ) ( setquotpr _ ( dirprodpair 1 ( tpair _ 1 ( nonzeroax X ) ) ) ) )  . apply ( weqpathsinsetquot ) .  unfold fldfracmultinvint . simpl . destruct ( is (pr1 xa) 0  ) as [ e0 | ne0' ] .

destruct ( nonzeroincommrngfrac X ( intdomnonzerosubmonoid X ) xa ne e0 ) .

apply hinhpr .  split with ( tpair ( fun a => neg ( paths a 0 ) ) 1 ( nonzeroax X ) ) .  set ( x := ( pr1 xa ) : X ) . set ( aa := pr2 xa ) . set ( a := ( pr1 aa ) : X ) . simpl .  change ( paths ( a * x * 1  * 1 ) ( 1 * ( x * a ) * 1 ) ) .  rewrite ( rngcomm2 X a x ) .  rewrite ( rngrunax2 X _ ) .  rewrite ( rngrunax2 X _ ) .  rewrite ( rngrunax2 X _ ) . rewrite ( rnglunax2 X _ ) .    apply idpath . Defined .  

Opaque islinvinfldfrac . 

Lemma isrinvinfldfrac ( X : intdom ) ( is : isdeceq X ) ( x : commrngfrac X ( intdomnonzerosubmonoid X ) ) ( ne : neg ( paths x 0 ) ) : paths ( x * ( fldfracmultinv0 X is x ) ) 1 .
Proof . intros. rewrite ( rngcomm2 _ _ _ ) . apply islinvinfldfrac . apply ne . Defined .   


Definition fldfrac ( X : intdom ) ( is : isdeceq X ) : fld .
Proof . intros . split with ( commrngfrac X ( intdomnonzerosubmonoid X ) ) . split .    

intro e . assert ( e' := zeroincommrngfrac X ( intdomnonzerosubmonoid X ) ( fun a : ( intdomnonzerosubmonoid X ) => pr2 a ) 1 ( unel ( intdomnonzerosubmonoid X ) ) e ) . apply ( nonzeroax X e' ) . 

intro x .  destruct ( isdeceqfldfrac X is x 0 ) as [ e | ne ] .

apply ( ii2 e ) .

apply ii1 . split with ( fldfracmultinv0 X is x ) . split . apply ( islinvinfldfrac X is x ne )  .   apply ( isrinvinfldfrac X is x ne ) .  Defined .



(** **** Canonical homomorphism to the field of fractions *)

Definition tofldfrac ( X : intdom ) ( is : isdeceq X ) ( x : X ) : fldfrac X is := setquotpr _ ( dirprodpair x ( tpair ( fun x => neg ( paths x 0 ) ) 1 ( nonzeroax X ) ) ) .

Definition isbinop1funtofldfrac ( X : intdom ) ( is : isdeceq X ) : @isbinopfun ( rngaddabgr X ) ( rngaddabgr ( fldfrac X is ) ) ( tofldfrac X is ) :=  isbinop1funtocommrngfrac X _ .   

Lemma isunital1funtofldfrac ( X : intdom ) ( is : isdeceq X ) : paths ( tofldfrac X is 0 ) 0 .
Proof . intros. apply idpath . Defined .

Definition isaddmonoidfuntofldfrac ( X : intdom ) ( is : isdeceq X ) : @ismonoidfun  ( rngaddabgr X ) ( rngaddabgr ( fldfrac X is ) ) ( tofldfrac X is ) := dirprodpair ( isbinop1funtofldfrac X is ) ( isunital1funtofldfrac X is ) . 

Definition tofldfracandminus0 ( X : intdom ) ( is : isdeceq X ) ( x : X ) : paths ( tofldfrac X is ( - x ) ) ( - tofldfrac X is x ) := tocommrngfracandminus0 _ _ x  . 

Definition tofldfracandminus ( X : intdom ) ( is : isdeceq X ) ( x y : X ) : paths ( tofldfrac X is ( x - y ) ) ( tofldfrac X is x - tofldfrac X is y ) := tocommrngfracandminus _ _ x y . 

Definition isbinop2funtofldfrac  ( X : intdom ) ( is : isdeceq X ) : @isbinopfun ( rngmultmonoid X ) ( rngmultmonoid ( fldfrac X is ) ) ( tofldfrac X is ) := isbinopfuntoabmonoidfrac ( rngmultabmonoid X ) ( intdomnonzerosubmonoid X ) . 

Opaque isbinop2funtofldfrac .

Lemma isunital2funtofldfrac  ( X : intdom ) ( is : isdeceq X ) : paths ( tofldfrac X is 1 ) 1 .
Proof . intros. apply idpath . Defined .

Opaque isunital2funtofldfrac .   

Definition ismultmonoidfuntofldfrac  ( X : intdom ) ( is : isdeceq X ) : @ismonoidfun  ( rngmultmonoid X ) ( rngmultmonoid ( fldfrac X is ) ) ( tofldfrac X is ) := dirprodpair ( isbinop2funtofldfrac X is ) ( isunital2funtofldfrac X is ) . 

Definition isrngfuntofldfrac ( X : intdom ) ( is : isdeceq X ) : @isrngfun X ( fldfrac X is ) ( tofldfrac X is ) := dirprodpair ( isaddmonoidfuntofldfrac X is ) ( ismultmonoidfuntofldfrac X is ) .

Definition isincltofldfrac ( X : intdom ) ( is : isdeceq X ) : isincl ( tofldfrac X is ) := isincltocommrngfrac X ( intdomnonzerosubmonoid X ) ( fun x : _ =>  pr2 ( intdomiscancelable X ( pr1 x ) ( pr2 x ) ) ) .




 




(** *** Relations similar to "greater" on fields of fractions 

Our approach here is slightly different from the tranditional one used for example in Bourbaki Algebra II , Ch. VI , Section 2 where one starts with a total ordering on a ring and extends it to its field of fractions. This situation woud be exemplified by the extension of "greater or equal" from integers to rationals. We have chosen to use instead as our archetypical example the extension of "greater" from integers to rationals. There is no particular difference between the two choices for types with decidable equality but in the setting of general rings in constructive mathematics the relations such as "greater" appear to be more fundamental than relations such as "greater or equal". For example, "greater or equal" on constructive real numbers can be obtained from "greater" but not vice versa.  *)






(** **** Description of the field of fractions as the ring of fractions with respect to the submonoid of "positive" elements *)


Definition weqfldfracgtint_f ( X : intdom ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) ( xa : dirprod X ( intdomnonzerosubmonoid X ) ) : dirprod X ( rngpossubmonoid X is1 is2 ) .
Proof . intros . destruct ( nc ( pr1 ( pr2 xa ) ) 0 ( pr2 ( pr2 xa ) ) ) as [ g | l ] .  apply ( dirprodpair ( pr1 xa ) ( tpair _ ( pr1 ( pr2 xa ) ) g ) ) . split with ( - ( pr1 xa ) ) .  split with ( - ( pr1 ( pr2 xa ) ) ) .  simpl . apply ( rngfromlt0 X is0 l ) . Defined . 


Lemma weqfldfracgtintcomp_f ( X : intdom ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) : iscomprelrelfun ( eqrelcommrngfrac X ( intdomnonzerosubmonoid X ) ) ( eqrelcommrngfrac X ( rngpossubmonoid X is1 is2 ) ) ( weqfldfracgtint_f X is0 is1 is2 nc ) . 
Proof . intros . intros xa1 xa2 . simpl . set ( x1 := pr1 xa1 ) . set ( aa1 := pr2 xa1 ) . set ( a1 := pr1 aa1 ) . set ( x2 := pr1 xa2 ) . set ( aa2 := pr2 xa2 ) . set ( a2 := pr1 aa2 ) . apply hinhfun .  intro t2 . split with ( tpair ( fun x => R x 0 ) 1 is2 ) .  set ( aa0 := pr1 t2 ) . set ( a0 := pr1 aa0 ) . assert ( e := pr2 t2 ) . change ( paths ( x1 * a2 * a0 ) ( x2 * a1 * a0 ) ) in e .  unfold weqfldfracgtint_f . destruct ( nc (pr1 (pr2 xa1)) 0 (pr2 (pr2 xa1)) ) as [ g1 | l1 ] .  destruct ( nc (pr1 (pr2 xa2)) 0 (pr2 (pr2 xa2)) ) as [ g2 | l2 ] . 

simpl .  rewrite ( rngrunax2 X _ ) . rewrite ( rngrunax2 X _ ) . apply ( intdomrcan X _ _ _ ( pr2 aa0 ) e ) . 

simpl .   rewrite ( rngrunax2 X _ ) . rewrite ( rngrunax2 X _ ) . rewrite (rngrmultminus X _ _ ) . rewrite ( rnglmultminus X _ _ ) . apply ( maponpaths ( fun x : X => - x ) ) .  apply ( intdomrcan X _ _ _ ( pr2 aa0 ) e ) .  destruct ( nc (pr1 (pr2 xa2)) 0 (pr2 (pr2 xa2)) ) as [ g2 | l2 ] .

simpl .   rewrite ( rngrunax2 X _ ) . rewrite ( rngrunax2 X _ ) . rewrite (rngrmultminus X _ _ ) . rewrite ( rnglmultminus X _ _ ) . apply ( maponpaths ( fun x : X => - x ) ) .  apply ( intdomrcan X _ _ _ ( pr2 aa0 ) e ) .

simpl .    rewrite ( rngrunax2 X _ ) . rewrite ( rngrunax2 X _ ) . rewrite (rngrmultminus X _ _ ) . rewrite ( rnglmultminus X _ _ ) .  rewrite (rngrmultminus X _ _ ) . rewrite ( rnglmultminus X _ _ ) . apply ( maponpaths ( fun x : X => - - x ) ) .  apply ( intdomrcan X _ _ _ ( pr2 aa0 ) e ) . Defined .  

Opaque weqfldfracgtintcomp_f . 

Definition weqfldfracgt_f ( X : intdom ) ( is : isdeceq X ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) : fldfrac X is -> commrngfrac X ( rngpossubmonoid X is1 is2 ) := setquotfun _ _ _ ( weqfldfracgtintcomp_f X is0 is1 is2 nc ) .   

Definition weqfldfracgtint_b ( X : intdom ) { R : hrel X } ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( ir : isirrefl R ) ( xa : dirprod X ( rngpossubmonoid X is1 is2 ) ) : dirprod X ( intdomnonzerosubmonoid X ) := dirprodpair ( pr1 xa ) ( tpair _ ( pr1 ( pr2 xa ) ) ( rtoneq ir ( pr2 ( pr2 xa ) ) ) ) . 


Lemma weqfldfracgtintcomp_b ( X : intdom ) { R : hrel X } ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( ir : isirrefl R ) : iscomprelrelfun ( eqrelcommrngfrac X ( rngpossubmonoid X is1 is2 ) ) ( eqrelcommrngfrac X ( intdomnonzerosubmonoid X ) ) ( weqfldfracgtint_b X is1 is2 ir ) .
Proof . intros . intros xa1 xa2 . simpl .  apply hinhfun .  intro t2 . split with ( tpair _ ( pr1 ( pr1 t2 ) ) ( rtoneq ir ( pr2 ( pr1 t2 ) ) ) ) .   apply ( pr2 t2 ) .  Defined . 


Definition weqfldfracgt_b ( X : intdom ) ( is : isdeceq X ) { R : hrel X } ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( ir : isirrefl R ) : commrngfrac X ( rngpossubmonoid X is1 is2 ) -> fldfrac X is := setquotfun _ _ _ ( weqfldfracgtintcomp_b X is1 is2 ir ) .


Definition weqfldfracgt ( X : intdom ) ( is : isdeceq X ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) ( ir : isirrefl R ) : weq ( fldfrac X is ) ( commrngfrac X ( rngpossubmonoid X is1 is2 ) ) .
Proof . intros . set ( f := weqfldfracgt_f X is is0 is1 is2 nc ) . set ( g := weqfldfracgt_b X is is1 is2 ir ) .  split with f . 

assert ( egf : forall a , paths ( g ( f a ) ) a ) .  unfold fldfrac. simpl . apply ( setquotunivprop _ ( fun a => hProppair _ ( isasetsetquot _ ( g ( f a ) ) a  ) ) ) . intro xa .  simpl . change ( paths ( setquotpr (eqrelcommrngfrac X (intdomnonzerosubmonoid X)) ( weqfldfracgtint_b X is1 is2 ir ( weqfldfracgtint_f X is0 is1 is2 nc xa ) ) ) ( setquotpr (eqrelcommrngfrac X (intdomnonzerosubmonoid X)) xa ) ) . apply ( weqpathsinsetquot ) . simpl . apply hinhpr . split with ( tpair ( fun x => neg ( paths x 0 ) ) 1 ( nonzeroax X ) ) . simpl . unfold weqfldfracgtint_f .  destruct ( nc (pr1 (pr2 xa)) 0 (pr2 (pr2 xa)) ) as [ g' | l' ] . 

simpl . apply idpath .

simpl .  rewrite (rngrmultminus X _ _ ) . rewrite ( rnglmultminus X _ _ ) . apply idpath .   

assert ( efg : forall a , paths ( f ( g a ) ) a ) .  unfold fldfrac. simpl . apply ( setquotunivprop _ ( fun a => hProppair _ ( isasetsetquot _ ( f ( g a ) ) a  ) ) ) . intro xa .  simpl .
change ( paths ( setquotpr _ ( weqfldfracgtint_f X is0 is1 is2 nc ( weqfldfracgtint_b X is1 is2 ir xa ) ) ) ( setquotpr (eqrelcommrngfrac X (rngpossubmonoid X is1 is2)) xa ) ) . apply weqpathsinsetquot . simpl . apply hinhpr .  split with ( tpair ( fun x => R x 0 ) 1 is2 ) .  unfold weqfldfracgtint_f .   unfold weqfldfracgtint_b . simpl . set ( int := nc (pr1 (pr2 xa)) 0 (rtoneq ir (pr2 (pr2 xa)))  ). change ( nc (pr1 (pr2 xa)) 0 (rtoneq ir (pr2 (pr2 xa))) ) with int . destruct int as [ g' | l' ] . 

simpl . apply idpath . 

simpl .   rewrite (rngrmultminus X _ _ ) . rewrite ( rnglmultminus X _ _ ) . apply idpath .

apply ( gradth _ _ egf efg ) . Defined .


Lemma isrngfunweqfldfracgt_b ( X : intdom ) ( is : isdeceq X ) { R : hrel X } ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( ir : isirrefl R ) : isrngfun ( weqfldfracgt_b X is is1 is2 ir ) .
Proof . intros . set ( g :=  weqfldfracgt_b X is is1 is2 ir ) . set ( g0 := weqfldfracgtint_b X is1 is2 ir ) . split . 

split .   

unfold isbinopfun . change ( forall x x' : commrngfrac X ( rngpossubmonoid X is1 is2 )  , paths ( g ( x + x' ) ) ( ( g x ) + ( g x' ) ) ) .  apply ( setquotuniv2prop _ ( fun x x' : commrngfrac X ( rngpossubmonoid X is1 is2 ) => hProppair _ ( setproperty _ ( g ( x + x' ) ) ( ( g x ) + ( g x' ) ) ) ) ) . intros xa1 xa2 .  change ( paths ( setquotpr (eqrelcommrngfrac X ( intdomnonzerosubmonoid X ) ) ( g0 ( commrngfracop1int X (rngpossubmonoid X is1 is2) xa1 xa2 ) ) ) ( setquotpr (eqrelcommrngfrac X ( intdomnonzerosubmonoid X )) ( commrngfracop1int  X ( intdomnonzerosubmonoid X ) ( g0 xa1 ) ( g0 xa2 ) ) ) )  . apply ( maponpaths ( setquotpr _ ) ) .  unfold g0 .  unfold weqfldfracgtint_b . unfold commrngfracop1int . simpl . apply ( pathsdirprod ) .  apply idpath . destruct xa1 as [ x1 aa1 ] .   destruct xa2 as [ x2 aa2 ] .  simpl . destruct aa1 as [ a1 ia1 ] . destruct aa2 as [ a2 ia2 ] . simpl .  apply ( invmaponpathsincl ( @pr1 _ _ ) ( isinclpr1 _ ( fun a => ( isapropneg ( paths a 0 ) ) ) ) {| pr1 := a1 * a2; pr2 := rtoneq ir (is1 a1 a2 ia1 ia2) |} (carrierpair
        (fun x : pr1 X =>
         hProppair (paths x 0 -> empty) (isapropneg (paths x 0))) 
        (a1 * a2)
        (fun e : paths (a1 * a2) 0 =>
         toneghdisj (dirprodpair (rtoneq ir ia1) (rtoneq ir ia2))
           (intdomax X a1 a2 e))) ( idpath _ ) ) .

change ( paths ( setquotpr (eqrelcommrngfrac X ( intdomnonzerosubmonoid X )) ( g0 ( dirprodpair 0 ( tpair _ 1 is2 ) ) ) ) ( setquotpr _ ( dirprodpair 0 ( tpair _ 1 ( nonzeroax X ) ) ) ) ) . apply ( maponpaths ( setquotpr _ ) ) .  unfold g0 .  unfold weqfldfracgtint_b . simpl . apply pathsdirprod . apply idpath .  apply ( invmaponpathsincl ( @pr1 _ _ ) ( isinclpr1 _ ( fun a => ( isapropneg ( paths a 0 ) ) ) ) {| pr1 := 1; pr2 := rtoneq ir is2 |} {| pr1 := 1; pr2 := nonzeroax X |} ) .  simpl . apply idpath .

split .  

unfold isbinopfun . change ( forall x x' : commrngfrac X ( rngpossubmonoid X is1 is2 )  , paths ( g ( x * x' ) ) ( ( g x ) * ( g x' ) ) ) .  apply ( setquotuniv2prop _ ( fun x x' : commrngfrac X ( rngpossubmonoid X is1 is2 ) => hProppair _ ( setproperty _ ( g ( x * x' ) ) ( ( g x ) * ( g x' ) ) ) ) ) . intros xa1 xa2 .  change ( paths ( setquotpr (eqrelcommrngfrac X ( intdomnonzerosubmonoid X ) ) ( g0 ( commrngfracop2int X (rngpossubmonoid X is1 is2) xa1 xa2 ) ) ) ( setquotpr (eqrelcommrngfrac X ( intdomnonzerosubmonoid X )) ( commrngfracop2int  X ( intdomnonzerosubmonoid X ) ( g0 xa1 ) ( g0 xa2 ) ) ) )  . apply ( maponpaths ( setquotpr _ ) ) .  unfold g0 .  unfold weqfldfracgtint_b . unfold commrngfracop2int . unfold abmonoidfracopint .  simpl . apply ( pathsdirprod ) .  apply idpath . destruct xa1 as [ x1 aa1 ] .   destruct xa2 as [ x2 aa2 ] .  simpl . destruct aa1 as [ a1 ia1 ] . destruct aa2 as [ a2 ia2 ] . simpl .  apply ( invmaponpathsincl ( @pr1 _ _ ) ( isinclpr1 _ ( fun a => ( isapropneg ( paths a 0 ) ) ) ) {| pr1 := a1 * a2; pr2 := rtoneq ir (is1 a1 a2 ia1 ia2) |} (carrierpair
        (fun x : pr1 X =>
         hProppair (paths x 0 -> empty) (isapropneg (paths x 0))) 
        (a1 * a2)
        (fun e : paths (a1 * a2) 0 =>
         toneghdisj (dirprodpair (rtoneq ir ia1) (rtoneq ir ia2))
           (intdomax X a1 a2 e))) ( idpath _ ) ) .

change ( paths ( setquotpr (eqrelcommrngfrac X ( intdomnonzerosubmonoid X )) ( g0 ( dirprodpair 1 ( tpair _ 1 is2 ) ) ) ) ( setquotpr _ ( dirprodpair 1 ( tpair _ 1 ( nonzeroax X ) ) ) ) ) . apply ( maponpaths ( setquotpr _ ) ) .  unfold g0 .  unfold weqfldfracgtint_b . simpl . apply pathsdirprod . apply idpath .  apply ( invmaponpathsincl ( @pr1 _ _ ) ( isinclpr1 _ ( fun a => ( isapropneg ( paths a 0 ) ) ) ) {| pr1 := 1; pr2 := rtoneq ir is2 |} {| pr1 := 1; pr2 := nonzeroax X |} ) .  simpl . apply idpath . Defined . 

Opaque isrngfunweqfldfracgt_b .

  
Lemma isrngfunweqfldfracgt_f ( X : intdom ) ( is : isdeceq X ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) ( ir : isirrefl R ) : isrngfun ( weqfldfracgt_f X is is0 is1 is2 nc ) .
Proof . intros .  set ( int := rngisopair ( invweq ( weqfldfracgt X is is0 is1 is2 nc ir ) ) ( isrngfunweqfldfracgt_b X is is1 is2 ir ) ) . change ( isrngfun ( invmap int ) ) .  apply isrngfuninvmap . Defined . 

Opaque isrngfunweqfldfracgt_f . 








(** **** Definition and properties of "greater" on the field of fractions *)

Definition fldfracgt ( X : intdom ) ( is : isdeceq X )  { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) : hrel ( fldfrac X is ) := fun a b => commrngfracgt X ( rngpossubmonoid X is1 is2 ) is0 is1 ( fun c r => r )  ( weqfldfracgt_f X is is0 is1 is2 nc a ) ( weqfldfracgt_f X is is0 is1 is2 nc b ) .  

Lemma isrngmultfldfracgt ( X : intdom ) ( is : isdeceq X )  { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) ( ir : isirrefl R ) : isrngmultgt ( fldfrac X is ) ( fldfracgt X is is0 is1 is2 nc ) .
Proof . intros . apply ( rngmultgtandfun ( rngfunconstr  ( isrngfunweqfldfracgt_f X is is0 is1 is2 nc ir ) ) ) .  apply isrngmultcommrngfracgt . Defined .  

Opaque isrngmultfldfracgt .

Lemma isrngaddfldfracgt ( X : intdom ) ( is : isdeceq X )  { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) ( ir : isirrefl R ) : @isbinophrel ( rngaddabgr ( fldfrac X is ) ) ( fldfracgt X is is0 is1 is2 nc ) .
Proof . intros . apply ( rngaddhrelandfun ( rngfunconstr  ( isrngfunweqfldfracgt_f X is is0 is1 is2 nc ir ) ) ) .  apply isrngaddcommrngfracgt . Defined . 

Opaque isrngaddfldfracgt . 

Lemma istransfldfracgt ( X : intdom ) ( is : isdeceq X )  { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) ( isr : istrans R ) : istrans ( fldfracgt X is is0 is1 is2 nc ) .
Proof . intros . intros a b c . unfold fldfracgt .  apply istransabmonoidfracrel .  apply isr . Defined . 

Opaque istransfldfracgt . 

Lemma isirreflfldfracgt ( X : intdom ) ( is : isdeceq X )  { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) ( isr : isirrefl R ) : isirrefl ( fldfracgt X is is0 is1 is2 nc ) .
Proof . intros .   intros a .  unfold fldfracgt  . apply isirreflabmonoidfracrel . apply isr .  Defined .

Opaque isirreflfldfracgt .

Lemma isasymmfldfracgt ( X : intdom ) ( is : isdeceq X )  { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) ( isr : isasymm R ) : isasymm ( fldfracgt X is is0 is1 is2 nc ) .
Proof . intros .  intros a b .  unfold fldfracgt  . apply isasymmabmonoidfracrel . apply isr . Defined .

Opaque  isasymmfldfracgt .

Lemma iscotransfldfracgt ( X : intdom ) ( is : isdeceq X )  { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) ( isr : iscotrans R ) : iscotrans ( fldfracgt X is is0 is1 is2 nc ) .
Proof . intros . intros a b c .  unfold fldfracgt  . apply iscotransabmonoidfracrel . apply isr . Defined .

Opaque iscotransfldfracgt . 

Lemma isantisymmnegfldfracgt  ( X : intdom ) ( is : isdeceq X )  { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) ( ir : isirrefl R ) ( isr : isantisymmneg R ) : isantisymmneg ( fldfracgt X is is0 is1 is2 nc ) .
Proof . intros .  assert ( int : isantisymmneg ( commrngfracgt X ( rngpossubmonoid X is1 is2 ) is0 is1 ( fun c r => r ) ) ) . unfold commrngfracgt . apply ( isantisymmnegabmonoidfracrel (rngmultabmonoid X) (rngpossubmonoid X is1 is2)
        (ispartbinopcommrngfracgt X (rngpossubmonoid X is1 is2) is0 is1
           (fun (c : X) (r : (rngpossubmonoid X is1 is2) c) => r))). apply isr . 

intros a b n1 n2 . set ( e := int _ _ n1 n2 ) .  apply ( invmaponpathsweq ( weqfldfracgt X is is0 is1 is2 nc ir )  _ _ e ) . Defined .

Opaque isantisymmnegfldfracgt . 


Definition isdecfldfracgt ( X : intdom ) ( is : isdeceq X )  { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is1 : isrngmultgt X R ) ( is2 : R 1 0 ) ( nc : neqchoice R ) ( isa : isasymm R ) ( isr : isdecrel R ) : isdecrel ( fldfracgt X is is0 is1 is2 nc ) .  
Proof . intros .  unfold fldfracgt . intros a b . apply isdecabmonoidfracrel .   apply ( pr1 ( isinvrngmultgtaspartinvbinophrel X R is0 ) ) .  apply isinvrngmultgtif . apply is0 . apply is1 . apply nc .  apply isa .  apply isr .  Defined . 





(** **** Realations and the canonical homomorphism to the field of fractions *)


Definition iscomptofldfrac ( X : intdom ) ( is : isdeceq X ) { L : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) L ) ( is1 : isrngmultgt X L )  ( is2 : L 1 0 ) ( nc : neqchoice L ) ( isa : isasymm L ) : iscomprelrelfun L ( fldfracgt X is is0 is1 is2 nc ) ( tofldfrac X is ) .
Proof . intros . intros x1 x2 l . assert ( int := iscomptocommrngfrac X ( rngpossubmonoid X is1 is2 ) is0 is1 ( fun c r => r )  ) . simpl in int .  unfold fldfracgt . unfold iscomprelrelfun in int .  assert ( ee : forall x : X , paths (tocommrngfrac X (rngpossubmonoid X is1 is2) x) (weqfldfracgt_f X is is0 is1 is2 nc (tofldfrac X is x)) ) .  intros x .  change (tocommrngfrac X (rngpossubmonoid X is1 is2) x) with (  setquotpr (eqrelcommrngfrac X (rngpossubmonoid X is1 is2)) ( dirprodpair x ( tpair ( fun a => L a 0 ) _ is2 ) ) ) . change (weqfldfracgt_f X is is0 is1 is2 nc (tofldfrac X is x)) with (  setquotpr (eqrelcommrngfrac X (rngpossubmonoid X is1 is2)) ( weqfldfracgtint_f X is0 is1 is2 nc ( dirprodpair x ( tpair ( fun a => neg ( paths a 0 ) ) 1 ( nonzeroax X ) ) ) ) ) . apply ( maponpaths ( setquotpr (eqrelcommrngfrac X (rngpossubmonoid X is1 is2)) ) ) . unfold weqfldfracgtint_f .  simpl . destruct ( nc 1 0 (nonzeroax X)  ) as [ l' | nl ] . 

apply pathsdirprod .  apply idpath .  apply ( invmaponpathsincl _ ( isinclpr1 _ ( fun a => ( pr2 ( L a 0 ) ) ) ) ) . apply idpath .  

destruct ( isa _ _ is2 nl ) . 

assert  ( int' := int x1 x2 ) .   rewrite ( ee x1 ) in int' .   rewrite ( ee x2 ) in int' . apply int' .  apply l . Defined .

Opaque iscomptofldfrac . 
 





(* End of the file algebra1d.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)