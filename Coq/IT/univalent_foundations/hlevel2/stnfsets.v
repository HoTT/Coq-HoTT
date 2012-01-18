(** * Standard finite sets . Vladimir Voevodsky . Apr. - Sep. 2011 .

This file contains main constructions related to the standard finite sets defined as the initial intervals of [ nat ] and their properties . *)




(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)



(** Imports. *)


Require Export hnat .


(* To up-steram files *)







(** ** Standard finite sets [ stn ] . *)



Definition stn ( n : nat ) := total2 ( fun m : nat => natlth m n ) .
Definition stnpair ( n : nat ) := tpair ( fun m : nat => natlth m n ) .
Definition stntonat ( n : nat ) : stn n -> nat := @pr1 _ _ .
Coercion stntonat : stn >-> nat .


Lemma isinclstntonat ( n : nat ) : isincl ( stntonat n ) .
Proof. intro .  apply isinclpr1 .  intro x .  apply ( pr2 ( natlth x n ) ) .  Defined.

Lemma isdecinclstntonat ( n : nat ) : isdecincl ( stntonat n ) .
Proof. intro . apply isdecinclpr1 .  intro x . apply isdecpropif . apply ( pr2 _ ) .   apply isdecrelnatgth .  Defined . 

Lemma neghfiberstntonat ( n m : nat ) ( is : natgeh m n ) : neg ( hfiber ( stntonat n ) m ) .
Proof. intros . intro h . destruct h as [ j e ] .  destruct j as [ j is' ] .  simpl in e .  rewrite e in is' .  apply ( natgehtonegnatlth _ _ is is' ) . Defined .

Lemma iscontrhfiberstntonat ( n m : nat ) ( is : natlth m n ) : iscontr ( hfiber ( stntonat n ) m ) .
Proof. intros .  apply ( iscontrhfiberofincl ( stntonat n ) ( isinclstntonat n ) ( stnpair n m is ) ) .  Defined . 

Lemma isisolatedinstn { n : nat } ( x : stn n ) : isisolated _ x.
Proof. intros . apply ( isisolatedinclb ( stntonat n ) ( isinclstntonat n ) x ( isisolatedn x ) ) .  Defined. 

Corollary isdeceqstn ( n : nat ) : isdeceq (stn n).
Proof. intro.  unfold isdeceq. intros x x' . apply (isisolatedinstn x x' ). Defined.

Definition weqisolatedstntostn ( n : nat ) : weq ( isolated ( stn n ) ) ( stn n ) .
Proof . intro . apply weqpr1 . intro x .   apply iscontraprop1 .  apply ( isapropisisolated ) . set ( int := isdeceqstn n x  ) . assumption .  Defined . 


Corollary isasetstn ( n : nat ) : isaset ( stn n ) .
Proof. intro . apply ( isasetifdeceq _ ( isdeceqstn n ) ) . Defined . 

Definition lastelement ( n : nat ) : stn ( S n ) .
Proof. intro .   split with n .  apply ( natgthsnn ( S n ) ) .  Defined . 

Definition stnmtostnn ( m n : nat ) (isnatleh: natleh m n ) : stn m -> stn n := fun x : stn m => match x with tpair i is => stnpair _ i ( natlthlehtrans i m n is isnatleh ) end .  




(** ** "Boundary" maps [ dni : stn n -> stn ( S n ) ] and their properties . *) 



Definition dni ( n : nat ) ( i : stn ( S n ) ) : stn n -> stn ( S n ) .
Proof. intros n i x .  destruct ( natlthorgeh x i ) . apply ( stnpair ( S n ) x ( natgthtogths _ _ ( pr2 x ) ) ) .  apply ( stnpair ( S n ) ( S x ) ( pr2 x ) ) .  Defined.  

Lemma dnicommsq ( n : nat ) ( i : stn ( S n ) ) : commsqstr ( di i ) ( stntonat ( S n ) ) ( stntonat n ) ( dni n i ) .
Proof. intros . intro x . unfold dni . unfold di . destruct ( natlthorgeh x i ) .  simpl .  apply idpath . simpl .  apply idpath . Defined . 

Theorem dnihfsq ( n : nat ) ( i : stn ( S n ) ) : hfsqstr ( di i ) ( stntonat ( S n ) ) ( stntonat n ) ( dni n i ) .
Proof. intros . apply ( ishfsqweqhfibersgtof' ( di i ) ( stntonat ( S n ) ) ( stntonat n ) ( dni n i ) ( dnicommsq _ _  ) ) . intro x . destruct ( natlthorgeh x n ) as [ g | l ] . 

assert ( is1 : iscontr ( hfiber ( stntonat n ) x ) ) . apply iscontrhfiberstntonat . assumption .
assert ( is2 : iscontr ( hfiber ( stntonat ( S n ) ) ( di i x )  ) ) .    apply iscontrhfiberstntonat . apply ( natlehlthtrans _ ( S x ) ( S n ) ( natlehdinsn i x ) g ) .  
apply isweqcontrcontr . assumption . assumption . 

assert ( is1 : neg ( hfiber ( stntonat ( S n ) ) ( di i x ) ) ) . apply neghfiberstntonat . unfold di .   destruct ( natlthorgeh x i ) as [ l'' | g' ] .  destruct ( natgehchoice2 _ _ l ) as [ g' | e ] .   apply g' .  rewrite e in l'' .  set ( int := natlthtolehsn _ _ l'' ) .  destruct ( int ( pr2 i ) ) .  apply l .  apply ( isweqtoempty2 _ is1 ) .
Defined . 



Lemma weqhfiberdnihfiberdi ( n : nat ) ( i j : stn ( S n ) ) : weq ( hfiber ( dni n i ) j ) ( hfiber ( di i ) j ) .
Proof.  intros . apply ( weqhfibersg'tof _ _ _ _ ( dnihfsq n i ) j ) . Defined .

Lemma neghfiberdni ( n : nat ) ( i : stn ( S n ) ) : neg ( hfiber ( dni n i ) i ) . 
Proof. intros . apply ( negf ( weqhfiberdnihfiberdi n i i ) ( neghfiberdi i ) ) . Defined .  

Lemma iscontrhfiberdni ( n : nat ) ( i j : stn ( S n ) ) ( ne : neg ( paths i j ) ) : iscontr ( hfiber ( dni n i ) j ) .
Proof . intros . set ( ne' := negf ( invmaponpathsincl _ ( isinclstntonat ( S n ) ) _ _ ) ne ) .  apply ( iscontrweqb ( weqhfiberdnihfiberdi n i j ) ( iscontrhfiberdi i j ne' ) ) .  Defined . 

Lemma isdecincldni ( n : nat ) ( i : stn ( S n ) ) : isdecincl ( dni n i ) .
Proof.  intros . intro j . destruct ( isdeceqstn _ i j ) . rewrite i0 .  apply ( isdecpropfromneg ( neghfiberdni n j ) ) . apply ( isdecpropfromiscontr ( iscontrhfiberdni _ _ _ e ) ) .  Defined . 
 
Lemma isincldni ( n : nat ) ( i : stn ( S n ) ) : isincl ( dni n i ) .
Proof. intros . apply ( isdecincltoisincl _  ( isdecincldni n i ) ) .  Defined . 






(** ** Weak equivalences between standard finite sets and constructions on these sets *)



(** *** The weak equivalence from [ stn n ] to the compl of a point [ j ] in [ stn ( S n ) ] defined by [ dni n j ] *)


Definition dnitocompl ( n : nat ) ( i : stn ( S n ) ) ( j : stn n ) : compl ( stn ( S n ) ) i .
Proof. intros . split with ( dni n i j ) .  intro e .  apply ( neghfiberdni n i ( hfiberpair _ j ( pathsinv0 e ) ) ) .  Defined .

Lemma isweqdnitocompl  ( n : nat ) ( i : stn ( S n ) ) : isweq ( dnitocompl n i ) .
Proof. intros . intro jni . destruct jni as [ j ni ] . set ( jni := complpair _ i j ni ) .  destruct ( isdeceqnat i j )  .  destruct ( ni ( invmaponpathsincl _ ( isinclstntonat _ ) _ _ i0 ) ) .  set ( w := samehfibers ( dnitocompl n i )  _ ( isinclpr1compl _ i ) jni ) .   simpl in w . assert ( is : iscontr (hfiber (fun x : stn n => dni n i x) j) ) . apply iscontrhfiberdni .  assumption . apply ( iscontrweqb w is ) .  Defined . 


Definition weqdnicompl ( n : nat ) ( i : stn ( S n ) ) := weqpair _ ( isweqdnitocompl n i ) . 




(** *** Weak equivalence from [ coprod ( stn n ) unit ] to [ stn ( S n ) ] defined by [ dni n i ] *)


Definition weqdnicoprod  ( n : nat ) ( j : stn ( S n ) ) : weq ( coprod ( stn n ) unit ) ( stn ( S n ) ) .
Proof . intros . apply ( weqcomp ( weqcoprodf ( weqdnicompl n j ) ( idweq unit ) ) ( weqrecompl ( stn ( S n ) ) j ( isdeceqstn ( S n ) j ) ) ) .  Defined . 




(** *** Weak equivalences from [ stn n ] for [ n = 0 , 1 , 2 ] to [ empty ] , [ unit ] and [ bool ] ( see also the section on [ nelstruct ] in finitesets.v ) . *)

Definition negstn0 : neg ( stn 0 ) .
Proof . intro x .  destruct x as [ a b ] .  apply ( negnatlthn0 _ b ) . Defined . 

Definition weqstn0toempty : weq ( stn 0 ) empty .
Proof .  apply weqtoempty . apply negstn0 . Defined .  

Definition weqstn1tounit : weq ( stn 1 ) unit .
Proof. set ( f := fun x : stn 1 => tt ) . apply weqcontrcontr .  split with ( lastelement 0 ) .   intro t .  destruct t as [ t l ] . set ( e := natlth1tois0 _ l ) .   apply ( invmaponpathsincl _ ( isinclstntonat 1 ) ( stnpair _ t l ) ( lastelement 0 ) e ) .  apply iscontrunit .  Defined .

Corollary iscontrstn1 : iscontr ( stn 1 ) .
Proof. apply iscontrifweqtounit . apply weqstn1tounit . Defined . 

Lemma isinclfromstn1 { X : UU0 } ( f : stn 1 -> X ) ( is : isaset X ) : isincl f .
Proof. intros . apply ( isinclbetweensets f ( isasetstn 1 ) is ) . intros x x' e . apply ( invmaponpathsweq weqstn1tounit x x' ( idpath tt ) )  .  Defined .    

Definition weqstn2tobool : weq ( stn 2 ) bool .
Proof. set ( f := fun j : stn 2 => match ( isdeceqnat j 0 ) with ii1 _ => false | ii2 _ => true end ) . set ( g := fun b : bool => match b with false => stnpair 2 0 ( idpath true ) | true => stnpair 2 1 ( idpath true ) end ) .  split with f . 
assert ( egf : forall j : _ , paths ( g ( f j ) ) j ) . intro j . unfold f .  destruct ( isdeceqnat j 0 ) as [ e | ne ] .  apply ( invmaponpathsincl _ ( isinclstntonat 2 ) ) . rewrite e .   apply idpath .  apply ( invmaponpathsincl _ ( isinclstntonat 2 ) ) . destruct j as [ j l ] . simpl . set ( l' := natlthtolehsn _ _ l ) .  destruct ( natlehchoice _ _ l' ) as [ l'' | e ] . simpl in ne . destruct  ( ne ( natlth1tois0 _ l'' ) ) .  apply ( pathsinv0 ( invmaponpathsS _ _ e ) ) .  
assert ( efg : forall b : _ , paths ( f ( g b ) ) b ) . intro b .  unfold g .  destruct b . apply idpath . apply idpath. 
apply ( gradth _ _ egf efg ) . Defined . 






(** ***  Weak equivalence between the coproduct of [ stn n ] and [ stn m ] and [ stn ( n + m ) ] *)

Theorem weqfromcoprodofstn ( n m : nat ) : weq ( coprod ( stn n ) ( stn m ) ) ( stn ( n + m ) ) .
Proof. intros . 

assert ( i1 : forall i : nat , natlth i n -> natlth i ( n + m ) ) . intros i1 l . apply ( natlthlehtrans _ _ _ l ( natlehnplusnm n m ) ) .    
assert ( i2 : forall i : nat , natlth i m -> natlth ( i + n ) ( n + m ) ) .  intros i2 l .  rewrite ( natpluscomm i2  n ) .  apply natgthandplusl . assumption . 
set ( f := fun ab : coprod ( stn n ) ( stn m ) => match ab with ii1 a =>  stnpair ( n + m ) a ( i1 a ( pr2 a ) ) | ii2 b => stnpair ( n + m ) ( b + n ) ( i2 b ( pr2 b ) ) end ) . 
split with f . 

assert ( is : isincl f ) .  apply  isinclbetweensets . apply ( isofhlevelssncoprod 0 _ _ ( isasetstn n ) ( isasetstn m ) ) .  apply ( isasetstn ( n + m ) ) .  intros x x' . intro e .   destruct x as [ xn | xm ] .

destruct x' as [ xn' | xm' ] . apply ( maponpaths (@ii1 _ _ ) ) .  apply ( invmaponpathsincl _ ( isinclstntonat n ) _ _ ) .  destruct xn as [ x ex ] . destruct xn' as [ x' ex' ] . simpl in e .  simpl .  apply ( maponpaths ( stntonat ( n + m ) ) e  )  .   destruct xn as [ x ex ] . destruct xm' as [ x' ex' ] . simpl in e . assert ( l : natleh n x ) . set ( e' := maponpaths ( stntonat _ ) e ) .   simpl in e' . rewrite e' .  apply ( natlehmplusnm x' n  ) . destruct ( natlehtonegnatgth _ _ l ex ) .  

destruct x' as [ xn' | xm' ] . destruct xm as [ x ex ] . destruct xn' as [ x' ex' ] . simpl in e .  assert ( e' := maponpaths ( stntonat _ ) e ) .  simpl in e' .  assert ( a : empty ) . clear e . rewrite ( pathsinv0 e' ) in ex' .  apply ( negnatgthmplusnm _ _ ex' )  .   destruct a . destruct xm as [ x ex ] . destruct xm' as [ x' ex' ] .  simpl in e .  apply ( maponpaths ( @ii2 _ _ ) ) .   simpl .  apply ( invmaponpathsincl _ ( isinclstntonat m ) _ _ ) .  simpl .  apply ( invmaponpathsincl _ ( isinclnatplusr n ) _ _ ( maponpaths ( stntonat _ ) e ) ) .  

intro jl . apply iscontraprop1 .  apply ( is jl ) .   destruct jl as [ j l ] . destruct ( natgthorleh n j ) as [ i | ni ] .
 
split with ( ii1 ( stnpair _ j i ) ) . simpl .   apply ( invmaponpathsincl _ ( isinclstntonat ( n + m ) )  (stnpair (n + m) j (i1 j i)) ( stnpair _ j l )  ( idpath j ) ) .

set ( jmn := pr1 ( iscontrhfibernatplusr n j ni ) ) .   destruct jmn as [ k e ] . assert ( is'' : natlth k m ) . rewrite ( pathsinv0 e ) in l .  rewrite ( natpluscomm k n ) in l .  apply ( natgthandpluslinv _ _ _ l ) . split with ( ii2 ( stnpair _ k is'' ) ) .  simpl .  apply ( invmaponpathsincl _ ( isinclstntonat _ ) (stnpair _ (k + n) (i2 k is'')) ( stnpair _ j l ) e ) . Defined .



(** *** Weak equivalence from the total space of a family [ stn ( f x ) ]  over [ stn n ] to [ stn ( stnsum n f ) ] *)

Definition stnsum { n : nat } ( f : stn n -> nat ) : nat .
Proof. intro n . induction n as [ | n IHn ] . intro. apply 0 . intro f . apply (  ( IHn ( fun i : stn n => f ( dni n ( lastelement n ) i ) ) ) + f ( lastelement n ) ) . Defined . 

Theorem weqstnsum { n : nat } ( P : stn n -> UU0 ) ( f : stn n -> nat ) ( ww : forall i : stn n , weq ( stn ( f i ) )  ( P i ) ) : weq ( total2 P ) ( stn ( stnsum f ) ) .
Proof . intro n . induction n as [ | n IHn ] . intros . simpl .  apply weqtoempty2 .  apply ( @pr1 _ _ ) .  apply negstn0 . intros .  simpl .  set ( a := stnsum (fun i : stn n => f (dni n (lastelement n) i)) ) . set ( b :=  f (lastelement n) ) . set ( w1 := invweq ( weqfp ( weqdnicoprod n ( lastelement n ) ) P ) ) . set ( w2 := weqcomp w1 ( weqtotal2overcoprod (fun x : coprod (stn n) unit => P ( weqdnicoprod n ( lastelement n )  x)) ) ) .  simpl in w2 . assert ( w3 : weq (total2 (fun x : stn n => P (dni n (lastelement n) x))) ( stn a ) ) .  assert ( int : forall x : stn n , weq  ( stn ( f ( dni n (lastelement n) x) ) ) ( P (dni n (lastelement n) x) ) ) .  intro x . apply ( ww ( dni n (lastelement n) x) ) .  apply ( IHn ( fun x : stn n => P (dni n (lastelement n) x)) ( fun x : stn n => f ( dni n (lastelement n) x ) ) int ) .  assert ( w4 : weq (total2 (fun _ : unit => P (lastelement n))) ( stn b) ) . apply ( weqcomp ( weqtotal2overunit (fun _ : unit => P (lastelement n)) ) ( invweq ( ww ( lastelement n ) ) ) ) .   apply ( weqcomp w2 ( weqcomp ( weqcoprodf w3 w4 ) ( weqfromcoprodofstn a b ) ) ) .  Defined . 


Corollary weqstnsum2 { X : UU0 } ( n : nat ) ( f : stn n -> nat ) ( g : X -> stn n ) ( ww : forall i : stn n , weq ( stn ( f i ) ) ( hfiber g i ) ) : weq X ( stn ( stnsum f ) ) .
Proof. intros . assert ( w : weq X ( total2 ( fun i : stn n => hfiber g i ) ) ) . apply weqtococonusf . apply ( weqcomp w ( weqstnsum ( fun i : stn n => hfiber g i ) f ww ) ) .   Defined . 



(** *** Weak equivalence between the direct product of [ stn n ] and [ stn m ] and [ stn n * m ] *)

Theorem weqfromprodofstn ( n m : nat ) : weq ( dirprod ( stn n ) ( stn m ) ) ( stn ( n * m ) ) .
Proof .  intros . destruct ( natgthorleh m 0 ) as [ is | i ] . 

assert ( i1 : forall i j : nat , natlth i n -> natlth j m ->  natlth ( j + i * m ) ( n * m ) ).  intros i j li lj . apply ( natlthlehtrans ( j + i * m ) ( ( S i ) * m ) ( n * m ) ( natgthandplusr m j ( i * m ) lj ) ( natlehandmultr ( S i ) n m ( natgthtogehsn _ _ li ) ) ) .     

set ( f := fun ij : dirprod ( stn n ) ( stn m ) => match ij with tpair i j => stnpair ( n * m ) ( j + i * m ) ( i1 i j ( pr2 i ) ( pr2 j ) ) end ) .  split with f . 

assert ( isinf : isincl f ) . apply isinclbetweensets . apply ( isofhleveldirprod 2 _ _ ( isasetstn n ) ( isasetstn m ) ) .  apply ( isasetstn ( n * m ) ) . intros ij ij' e .  destruct ij as [ i j ] . destruct ij' as [ i' j' ] .  destruct i as [ i li ] . destruct i' as [ i' li' ] .  destruct j as [ j lj ] . destruct j' as [ j' lj' ] . simpl in e . assert ( e' := maponpaths ( stntonat ( n * m ) ) e )  .   simpl in e' .
assert ( eei : paths i i' ) . apply ( pr1 ( natdivremunique m i j i' j' lj lj' ( maponpaths ( stntonat _ ) e ) ) ) .    
set ( eeis := invmaponpathsincl _ ( isinclstntonat _ ) ( stnpair _ i li ) ( stnpair _ i' li' ) eei ) .
assert ( eej : paths j j' ) . apply ( pr2 ( natdivremunique m i j i' j' lj lj' ( maponpaths ( stntonat _ ) e ) ) ) . 
set ( eejs := invmaponpathsincl _ ( isinclstntonat _ ) ( stnpair _ j lj ) ( stnpair _ j' lj' ) eej ) . apply ( pathsdirprod eeis eejs ) . 

intro xnm .  apply iscontraprop1 . apply ( isinf xnm ) . set ( e := pathsinv0 ( natdivremrule xnm m ( natgthtoneq _ _ is ) ) ) .  set ( i := natdiv xnm m ) .   set ( j := natrem xnm m ) . destruct xnm as [ xnm lxnm ] .   set ( li := natlthandmultrinv _ _ _ ( natlehlthtrans _ _ _ ( natlehmultnatdiv xnm m ( natgthtoneq _ _ is ) ) lxnm ) ) .  set ( lj := lthnatrem xnm m ( natgthtoneq _ _ is ) ) .  split with ( dirprodpair ( stnpair n i li ) ( stnpair m j lj ) ) .  simpl . apply ( invmaponpathsincl _ ( isinclstntonat _ ) _ _ ) .  simpl . apply e .

set ( e := natleh0tois0 _ i ) .  rewrite e .  rewrite ( natmultn0 n ) . split with ( @pr2 _ _ ) .   apply ( isweqtoempty2 _ ( weqstn0toempty ) ) . Defined . 


(** *** Weak equivalences between decidable subsets of [ stn n ] and [ stn x ] *)

Theorem weqfromdecsubsetofstn { n : nat } ( f : stn n -> bool ) : total2 ( fun x : nat => weq ( hfiber f true ) ( stn x ) ) .
Proof . intro . induction n as [ | n IHn ] . intros .    split with 0 .  assert ( g : ( hfiber f true ) -> ( stn 0 ) ) . intro hf . destruct hf as [ i e ] .  destruct ( weqstn0toempty i ) .  apply ( weqtoempty2 g weqstn0toempty ) . intro . set ( g := weqfromcoprodofstn 1 n ) .   change ( 1 + n ) with ( S n ) in g . 

set ( fl := fun i : stn 1 => f ( g ( ii1 i ) ) ) .   set ( fh := fun i : stn n => f ( g ( ii2 i ) ) ) . assert ( w : weq ( hfiber f true ) ( hfiber ( sumofmaps fl fh ) true ) ) .  set ( int := invweq ( weqhfibersgwtog g f true  ) ) .  assert ( h : forall x : _ , paths ( f ( g x ) ) ( sumofmaps fl fh x ) ) . intro . destruct x as [ x1 | xn ] . apply idpath . apply idpath .   apply ( weqcomp int ( weqhfibershomot _ _ h true ) ) .  set ( w' := weqcomp w ( invweq ( weqhfibersofsumofmaps fl fh true ) ) ) .  

set ( x0 := pr1 ( IHn fh ) ) . set ( w0 := pr2 ( IHn fh ) ) . simpl in w0 . destruct ( boolchoice ( fl ( lastelement 0 ) ) ) as [ i | ni ] .  

split with ( S x0 ) .  assert ( wi : weq ( hfiber fl true ) ( stn 1 ) ) . assert ( is : iscontr ( hfiber fl true ) ) . apply iscontraprop1 . apply ( isinclfromstn1 fl isasetbool true ) .  apply ( hfiberpair _ ( lastelement 0 ) i ) . apply ( weqcontrcontr is iscontrstn1 ) .  apply ( weqcomp ( weqcomp w' ( weqcoprodf wi w0 ) ) ( weqfromcoprodofstn 1 _ ) ) . 

split with x0 .  assert ( g' : neg ( hfiber fl true ) ) . intro hf . destruct hf as [ j e ] .  assert ( ee : paths j ( lastelement 0 ) ) . apply ( proofirrelevance _ ( isapropifcontr iscontrstn1 ) _ _ ) .  destruct ( nopathstruetofalse ( pathscomp0 ( pathscomp0 ( pathsinv0 e ) ( maponpaths fl ee ) ) ni ) ) .  apply ( weqcomp w' ( weqcomp ( invweq ( weqii2withneg _ g' ) ) w0 )  )  .  Defined . 

(** *** Weak equivalences between hfibers of functions from [ stn n ] over isolated points and [ stn x ] *)

Theorem weqfromhfiberfromstn { n : nat } { X : UU0 } ( x : X ) ( is : isisolated X x ) ( f : stn n -> X ) : total2 ( fun x0 : nat => weq ( hfiber f x ) ( stn x0 ) ) .
Proof . intros .  set ( t := weqfromdecsubsetofstn ( fun i : _ => eqbx X x is ( f i ) ) ) . split with ( pr1 t ) . apply ( weqcomp ( weqhfibertobhfiber f x is ) ( pr2 t ) ) .   Defined . 





(** *** Weak equivalence between [ stn n -> stn m ] and [ stn ( natpower m n ) ] ( uses functional extensionality ) *) 


Theorem weqfromfunstntostn ( n m : nat ) : weq ( stn n -> stn m ) ( stn ( natpower m n ) ) .
Proof. intro n . induction n as [ | n IHn ] . intro m .  apply weqcontrcontr . apply ( iscontrfunfromempty2 _ weqstn0toempty ) .  apply iscontrstn1 .
intro m . set ( w1 := weqfromcoprodofstn 1 n ) . assert ( w2 : weq ( stn ( S n ) -> stn m ) ( (coprod (stn 1) (stn n)) -> stn m ) ) .   apply ( weqbfun _ w1  ) .  set ( w3 := weqcomp w2 ( weqfunfromcoprodtoprod ( stn 1 ) ( stn n ) ( stn m ) ) ) .   set ( w4 := weqcomp w3 ( weqdirprodf ( weqfunfromcontr ( stn m ) iscontrstn1 ) ( IHn m ) ) ) .  apply ( weqcomp w4 ( weqfromprodofstn m ( natpower m n ) ) ) .  Defined . 





(** *** Weak equivalence from the space of functions of a family [ stn ( f x ) ]  over [ stn n ] to [ stn ( stnprod n f ) ] ( uses functional extensionality ) *)

Definition stnprod { n : nat } ( f : stn n -> nat ) : nat .
Proof. intro n . induction n as [ | n IHn ] . intro. apply 1 . intro f . apply (  ( IHn ( fun i : stn n => f ( dni n ( lastelement n ) i ) ) ) * f ( lastelement n ) ) . Defined . 

Theorem weqstnprod { n : nat } ( P : stn n -> UU0 ) ( f : stn n -> nat ) ( ww : forall i : stn n , weq ( stn ( f i ) )  ( P i ) ) : weq ( forall x : stn n , P x  ) ( stn ( stnprod f ) ) .
Proof . intro n . induction n as [ | n IHn ] . intros . simpl . apply ( weqcontrcontr ) .  apply ( iscontrsecoverempty2 _ ( negstn0 ) ) .   apply iscontrstn1 . intros .  set ( w1 := weqdnicoprod n ( lastelement n ) ) . set ( w2 := weqonsecbase P w1 ) .   set ( w3 := weqsecovercoprodtoprod ( fun x : _ => P ( w1 x ) ) ) .  set ( w4 := weqcomp w2 w3 ) .  set ( w5 := IHn ( fun x : stn n => P ( w1 ( ii1 x ) ) ) ( fun x : stn n => f ( w1 ( ii1 x ) ) ) ( fun i : stn n => ww ( w1 ( ii1 i ) ) ) ) . set ( w6 := weqcomp w4 ( weqdirprodf w5 ( weqsecoverunit _ ) ) ) .  simpl in w6 .  set ( w7 := weqcomp w6 ( weqdirprodf ( idweq _ ) ( invweq ( ww ( lastelement n ) ) ) ) ) .  apply ( weqcomp w7 ( weqfromprodofstn _ _ ) ) .   Defined . 




(** *** Weak equivalence between [ weq ( stn n ) ( stn n ) ] and [ stn ( factorial n ) ] ( uses functional extensionality ) *)

Theorem  weqweqstnsn ( n : nat ) : weq ( weq ( stn ( S n ) ) ( stn ( S n ) ) ) ( dirprod ( stn ( S n ) ) ( weq ( stn n ) ( stn n ) ) ) .
Proof . intro . set ( nn := lastelement n ) . set ( is := isdeceqstn _ nn ) . set ( w1 := weqcutonweq ( stn ( S n ) ) nn is ) . set ( w2 := weqisolatedstntostn ( S n ) ) .  set ( w3 := invweq ( weqdnicompl n nn ) ) .  apply ( weqcomp w1 ( weqdirprodf w2 ( weqcomp ( weqbweq _ ( invweq w3 )) ( weqfweq _ w3 ) ) ) ) .  Defined .   


Theorem weqfromweqstntostn ( n : nat ) : weq ( weq ( stn n ) ( stn n ) ) ( stn ( factorial n ) ) . 
Proof . intro . induction n as [ | n IHn ] . simpl . apply ( weqcontrcontr ) . apply ( iscontraprop1 ) .    apply ( isapropweqtoempty2 _ ( negstn0 ) ) .  apply idweq . apply iscontrstn1 . change ( factorial ( S n ) ) with ( ( S n ) * ( factorial n ) ) .   set ( w1 := weqweqstnsn n ) . apply ( weqcomp w1 ( weqcomp ( weqdirprodf ( idweq _ ) IHn ) ( weqfromprodofstn _ _ ) ) ) .  Defined . 


(* End of " weak equivalences between standard finite sets and constructions on these sets " . *)







(** ** Standard finite sets satisfy weak axiom of choice *)

Theorem ischoicebasestn ( n : nat ) : ischoicebase ( stn n ) .
Proof . intro . induction n as [ | n IHn ] .  apply ( ischoicebaseempty2 negstn0 ) .  apply ( ischoicebaseweqf ( weqdnicoprod n ( lastelement n ) ) ( ischoicebasecoprod IHn ischoicebaseunit ) ) .  Defined . 







(** ** Weak equivalence class of [ stn n ] determines [ n ] . *)


Lemma negweqstnsn0 (n:nat): neg (weq (stn (S n)) (stn O)).
Proof. unfold neg. intro. assert (lp: stn (S n)). apply lastelement.  intro X.  apply weqstn0toempty .  apply (pr1 X lp). Defined.

Lemma negweqstn0sn (n:nat): neg (weq (stn O) (stn (S n))).
Proof.  unfold neg. intro. assert (lp: stn (S n)). apply lastelement.  intro X.  apply weqstn0toempty .  apply (pr1 ( invweq X ) lp). Defined.

Lemma weqcutforstn ( n n' : nat ) ( w : weq (stn (S n)) (stn (S n')) ) : weq (stn n) (stn n').
Proof. intros. set ( nn := lastelement n  ) . set ( w1 := weqoncompl w nn ) .  set ( w2 := weqdnicompl n nn ) . set ( w3 := weqdnicompl n' ( w nn ) ) .   apply ( weqcomp w2 ( weqcomp w1 ( invweq w3 ) ) ) . Defined .   


Theorem weqtoeqstn ( n n' : nat ) ( w : weq (stn n) (stn n') ) : paths n n'.
Proof. intro. induction n as [ | n IHn ] . intro. destruct n' as [ | n' ] .  intros. apply idpath. intro X. apply (fromempty (negweqstn0sn  n' X)).  
 intro n'. destruct n' as [ | n' ] . intro X. set (int:= isdeceqnat (S n) 0 ).  destruct int as [ i | e ] .  assumption. apply (fromempty ( negweqstnsn0 n X)).  intro X. 
set (e:= IHn n' ( weqcutforstn _ _ X)). apply (maponpaths S e). Defined. 

Corollary stnsdnegweqtoeq ( n n' : nat ) ( dw : dneg (weq (stn n) (stn n')) ) : paths n n'.
Proof. intros n n' X. apply (eqfromdnegeq nat isdeceqnat _ _  (dnegf (@weqtoeqstn n n') X)). Defined. 




(** ** Some results on bounded quantification *)


Lemma weqforallnatlehn0 ( F : nat -> hProp ) : weq ( forall n : nat , natleh n 0 -> F n ) ( F 0 ) .
Proof . intros .  assert ( lg : ( forall n : nat , natleh n 0 -> F n ) <-> ( F 0 ) ) . split . intro f .  apply ( f 0 ( isreflnatleh 0 ) ) .  intros f0 n l .  set ( e := natleh0tois0 _ l ) .  rewrite e .  apply f0 . assert ( is1 : isaprop ( forall n : nat , natleh n 0 -> F n ) ) . apply impred . intro n . apply impred .   intro l .  apply ( pr2 ( F n ) ) .  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) is1 ( pr2 ( F 0 ) ) ) . Defined . 

Lemma weqforallnatlehnsn' ( n' : nat ) ( F : nat -> hProp ) : weq ( forall n : nat , natleh n ( S n' ) -> F n ) ( dirprod ( forall n : nat , natleh n n' -> F n ) ( F ( S n' ) ) ) . 
Proof . intros . assert ( lg : ( forall n : nat , natleh n ( S n' ) -> F n ) <-> dirprod ( forall n : nat , natleh n n' -> F n ) ( F ( S n' ) ) ) .  split . intro f.  apply ( dirprodpair ( fun n => fun l => ( f n ( natlehtolehs _ _ l ) ) ) ( f ( S n' ) ( isreflnatleh _ ) ) ) .  intro d2 . intro n .  intro l .  destruct ( natlehchoice2 _ _ l ) as [ h | e ] . simpl in h .  apply ( pr1 d2 n h ) . destruct d2 as [ f2 d2 ] .  rewrite e .  apply d2 . assert ( is1 : isaprop ( forall n : nat , natleh n ( S n' ) -> F n ) ) . apply impred . intro n . apply impred . intro l . apply ( pr2 ( F n ) ) . assert ( is2 : isaprop ( dirprod ( forall n : nat , natleh n n' -> F n ) ( F ( S n' ) ) ) ) . apply isapropdirprod . apply impred . intro n . apply impred . intro l . apply ( pr2 ( F n ) ) .   apply ( pr2 ( F ( S n' ) ) ) .  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) is1 is2 ) . Defined .

Lemma weqexistsnatlehn0 ( P : nat -> hProp  ) : weq ( hexists ( fun n : nat => dirprod ( natleh n 0 ) ( P n ) ) ) ( P 0 ) .
Proof . intro . assert ( lg : hexists ( fun n : nat => dirprod ( natleh n 0 ) ( P n ) ) <-> P 0  ) . split .  simpl . apply ( @hinhuniv _ ( P 0 ) ) .  intro t2 .  destruct t2 as [ n d2 ] . destruct d2 as [ l p ] . set ( e := natleh0tois0 _ l ) . clearbody e .  destruct e . apply p . intro p . apply hinhpr . split with 0 .  split with ( isreflnatleh 0 ) .  apply p . apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) ( pr2 _ ) ( pr2 _ ) ) .  Defined .

Lemma weqexistsnatlehnsn' ( n' : nat ) ( P : nat -> hProp  ) : weq ( hexists ( fun n : nat => dirprod ( natleh n ( S n' ) ) ( P n ) ) ) ( hdisj ( hexists ( fun n : nat => dirprod ( natleh n n' ) ( P n ) ) )  ( P ( S n' ) ) ) .
Proof . intros . assert ( lg : hexists ( fun n : nat => dirprod ( natleh n ( S n' ) ) ( P n ) )  <-> hdisj ( hexists ( fun n : nat => dirprod ( natleh n n' ) ( P n ) ) )  ( P ( S n' ) )  ) . split .  simpl . apply hinhfun .   intro t2 .  destruct t2 as [ n d2 ] . destruct d2 as [ l p ] . destruct ( natlehchoice2 _ _ l ) as [ h | nh ] . simpl in h . apply ii1 .  apply hinhpr . split with n .  apply ( dirprodpair h p ) . destruct nh .  apply ( ii2 p ) . simpl . apply ( @hinhuniv _ ( ishinh _ ) ) . intro c .  destruct c as [ t | p ] .  generalize t . simpl . apply hinhfun .  clear t . intro t . destruct t as [ n d2 ] . destruct d2 as [ l p ] . split with n .  split with ( natlehtolehs _ _ l ) .  apply p .  apply hinhpr . split with ( S n' ) .  split with ( isreflnatleh _ ) . apply p .  apply ( weqimplimpl ( pr1 lg ) ( pr2 lg ) ( pr2 _ ) ( pr2 _ ) ) .  Defined .  


Lemma isdecbexists ( n : nat ) ( P : nat -> UU ) ( is : forall n' , isdecprop ( P n' ) ) : isdecprop ( hexists ( fun n' => dirprod ( natleh n' n ) ( P n' ) ) ) .
Proof . intros .  set ( P' := fun n' : nat => hProppair _ ( is n' ) ) . induction n as [ | n IHn ] . apply ( isdecpropweqb ( weqexistsnatlehn0 P' ) ) . apply ( is 0 ) .   apply ( isdecpropweqb ( weqexistsnatlehnsn' _ P' ) ) . apply isdecprophdisj . apply IHn . apply ( is ( S n ) ) . Defined .   

Lemma isdecbforall ( n : nat ) ( P : nat -> UU ) ( is : forall n' , isdecprop ( P n' ) ) : isdecprop ( forall n' , natleh n' n -> P n' )  .
Proof . intros .  set ( P' := fun n' : nat => hProppair _ ( is n' ) ) . induction n as [ | n IHn ] . apply ( isdecpropweqb ( weqforallnatlehn0 P' ) ) . apply ( is 0 ) .   apply ( isdecpropweqb ( weqforallnatlehnsn' _ P' ) ) . apply isdecpropdirprod . apply IHn . apply ( is ( S n ) ) . Defined .   

 

(** The following lemma finds the largest [ n' ] such that [ neg ( P n' ) ] . It is a stronger form of ( neg forall ) -> ( exists neg ) in the case of bounded quantification of decidable propositions. *)

Lemma negbforalldectototal2neg ( n : nat ) ( P : nat -> UU ) ( is : forall n' : nat , isdecprop ( P n' ) ) : neg ( forall n' : nat , natleh n' n -> P n' ) -> total2 ( fun n' => dirprod ( natleh n' n ) ( neg ( P n' ) ) ) .
Proof . intros n P is . set ( P' := fun n' : nat => hProppair _ ( is n' ) ) . induction n as [ | n IHn ] . intro nf . set ( nf0 := negf ( invweq ( weqforallnatlehn0 P' ) ) nf ) . split with 0 . apply ( dirprodpair ( isreflnatleh 0 ) nf0 ) .   intro nf . set ( nf2 := negf ( invweq ( weqforallnatlehnsn' n P' ) ) nf ) . set ( nf3 := fromneganddecy ( is ( S n ) ) nf2 ) . destruct nf3 as [ f1 | f2 ] . set ( int := IHn f1 ) .  destruct int as [ n' d2 ] . destruct d2 as [ l np ] . split with n' .  split with ( natlehtolehs _ _ l ) .  apply np . split with ( S n ) . split with ( isreflnatleh _ ) . apply f2 .  Defined . 


(** ** Accesibility - the least element of an inhabited decidable subset of [nat] *)

Definition natdecleast ( F : nat -> UU ) ( is : forall n , isdecprop ( F n ) ) := total2 ( fun  n : nat => dirprod ( F n ) ( forall n' : nat , F n' -> natleh n n' ) ) .

Lemma isapropnatdecleast ( F : nat -> UU ) ( is : forall n , isdecprop ( F n ) ) : isaprop ( natdecleast F is ) .
Proof . intros . set ( P := fun n' : nat => hProppair _ ( is n' ) ) . assert ( int1 : forall n : nat, isaprop ( dirprod ( F n ) ( forall n' : nat , F n' -> natleh n n' ) ) ) .  intro n . apply isapropdirprod . apply ( pr2 ( P n ) ) .  apply impred . intro t .  apply impred .  intro .  apply ( pr2 ( natleh n t ) ) . set ( int2 := ( fun n : nat => hProppair _ ( int1 n ) ) : nat -> hProp ) .   change ( isaprop ( total2 int2 ) ) . apply isapropsubtype . intros x1 x2 .  intros c1 c2 . simpl in * . destruct c1 as [ e1 c1 ] . destruct c2 as [ e2 c2 ] . set ( l1 := c1 x2 e2 ) .  set ( l2 := c2 x1 e1 ) . apply ( isantisymmnatleh _ _ l1 l2 ) .  Defined .

Theorem accth ( F : nat -> UU ) ( is : forall n , isdecprop ( F n ) )  ( is' : hexists F ) : natdecleast F is .
Proof . intros F is . simpl . apply (@hinhuniv _ ( hProppair _ ( isapropnatdecleast F is ) ) ) . intro t2. destruct t2 as [ n l ] . simpl .

set ( F' := fun n' : nat => hexists ( fun n'' => dirprod ( natleh n'' n' ) ( F n'' ) ) ) .  assert ( X : forall n' , F' n' -> natdecleast F is ) .  intro n' .  simpl .    induction n' as [ | n' IHn' ] . apply ( @hinhuniv _  ( hProppair _ ( isapropnatdecleast F is ) ) ) . simpl .   intro t2 . destruct t2 as [ n'' is'' ] . destruct is'' as [ l'' d'' ] .  split with 0 .  split . set ( e := natleh0tois0 _ l'' ) . clearbody e . destruct e . apply d'' .  apply ( fun n' => fun f : _ => natleh0n n' ) .  apply ( @hinhuniv _  ( hProppair _ ( isapropnatdecleast F is ) ) ) . intro t2 .  destruct t2 as [ n'' is'' ] . set ( j := natlehchoice2 _ _ ( pr1 is'' ) ) .  destruct j as [ jl | je ] .  simpl .  apply ( IHn' ( hinhpr _ ( tpair _ n'' ( dirprodpair jl ( pr2 is'' ) ) ) ) ) .  simpl . rewrite je in is''  .  destruct is'' as [ nn is'' ] .  clear nn. clear je . clear n'' . 

assert ( is' : isdecprop ( F' n' ) ) . apply ( isdecbexists n' F is ) .   destruct ( pr1 is' ) as [ f | nf ] .  apply ( IHn'  f ) .  split with ( S n' ) .  split with is'' . intros n0 fn0 . destruct ( natlthorgeh n0 ( S n' ) )  as [ l' | g' ] .  set ( i' := natlthtolehsn _ _ l' ) .  destruct ( nf ( hinhpr _ ( tpair _ n0 ( dirprodpair i' fn0 ) ) ) ) .   apply g' . 

apply ( X n ( hinhpr _ ( tpair _ n ( dirprodpair ( isreflnatleh n ) l ) ) ) ) .  Defined . 


  









(* End of the file stnfsets.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)

