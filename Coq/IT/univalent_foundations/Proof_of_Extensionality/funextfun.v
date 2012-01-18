(** * Univalence axiom and functional extensionality.  Vladimir Voevodsky. Feb. 2010 - Sep. 2011 

This file contains the formulation of the univalence axiom and the proof that it implies functional extensionality for functions - Theorem funextfun.   
   
*)


(** *** Preamble. *)

Add Rec LoadPath "../Generalities".

(** *** Imports. *)

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)

Require Export uu0.


(** ** Univalence axiom. *)


Definition eqweqmap { T1 T2 : UU } ( e: paths T1 T2 ) : weq T1 T2 .
Proof. intros. destruct e . apply idweq. Defined. 

Axiom univalenceaxiom :  forall T1 T2 : UU ,  isweq ( @eqweqmap T1 T2 ).
 
Definition weqtopaths { T1 T2 : UU } ( w : weq T1 T2 ) : paths T1 T2  :=  invmap ( weqpair _ ( univalenceaxiom T1 T2 ) ) w.


Definition weqpathsweq { T1 T2 : UU } ( w : weq T1 T2 ) : paths ( eqweqmap ( weqtopaths w ) ) w  :=  homotweqinvweq ( weqpair _ ( univalenceaxiom T1 T2 ) ) w.

(** We show that [ univalenceaxiom ] is equivalent to the axioms [ weqtopaths0 ] and [ weqpathsweq0 ] stated below . *)


Axiom weqtopaths0 : forall ( T1 T2 : UU ) ( w : weq T1 T2 ) , paths T1 T2.

Axiom weqpathsweq0 : forall ( T1 T2 : UU ) ( w : weq T1 T2 ) ,  paths ( eqweqmap ( weqtopaths0 _ _ w ) ) w.

Theorem univfromtwoaxioms ( T1 T2 : UU ) : isweq ( @eqweqmap T1 T2 ).
Proof. intros. set ( P1 := fun XY : dirprod UU UU => ( match XY with  tpair X Y =>  paths X Y end ) ) . set ( P2 := fun XY :  dirprod UU UU => match XY with  tpair X Y => weq X Y end ) . set ( Z1 := total2 P1 ). set ( Z2 := total2 P2 ). set ( f := totalfun _ _ ( fun XY :  dirprod UU UU => match XY with  tpair X Y => @eqweqmap X Y end ) : Z1 -> Z2 ) . set ( g := totalfun _ _ ( fun XY : dirprod UU UU => match XY with  tpair X Y => weqtopaths0 X Y end ) : Z2 -> Z1 ) . set ( s1 := fun X Y  : UU => fun w : weq X Y =>  tpair P2 (  dirprodpair X Y ) w ) . set ( efg := fun a => match a as a' return (  paths ( f ( g a' ) ) a' ) with  tpair ( tpair X Y ) w => ( maponpaths ( s1 X Y ) ( weqpathsweq0 X Y w ) ) end ) . 

set ( h := fun a1 : Z1 =>  pr1 ( pr1 a1 ) ) .
assert ( egf0 : forall a1 : Z1 ,  paths ( pr1 ( g ( f a1 ) ) ) (  pr1 a1 ) ). intro. apply  idpath.  
assert ( egf1 : forall a1 a1' : Z1 ,  paths ( pr1 a1' ) (  pr1 a1 ) ->  paths a1' a1 ). intros.  set ( X' :=  maponpaths ( @pr1 _ _ ) X ). 
assert ( is : isweq h ).  apply isweqpr1pr1 . apply ( invmaponpathsweq ( weqpair h is ) _ _ X' ).
set ( egf := fun a1  => ( egf1 _ _ ( egf0 a1 ) ) ). 
set ( is2 := gradth _ _ egf efg ). 
apply ( isweqtotaltofib P1 P2  ( fun XY : dirprod UU UU => match XY with  tpair X Y => @eqweqmap X Y end ) is2 ( dirprodpair T1 T2 ) ). Defined. 


(** Conjecture :  the pair [weqtopaths0] and [weatopathsweq0] is well defined up to a canonical equality. **)






(** ** Transport theorem. 

Theorem saying that any general scheme to "transport" a structure along a weak equivalence which does not change the structure in the case of the identity equivalence is equivalent to the transport along the path which corresponds to a weak equivalence by the univalenceaxiom. As a corollary we conclude that for any such transport scheme the corresponding maps on spaes of structures are weak equivalences. *)


Lemma isweqtransportf10 { X : UU } ( P : X -> UU ) { x x' : X } ( e :  paths x x' ) : isweq ( transportf P e ).
Proof. intros. destruct e.  apply idisweq. Defined.

Lemma isweqtransportb10 { X : UU } ( P : X -> UU ) { x x' : X } ( e :  paths x x' ) : isweq ( transportb P e ).
Proof. intros. apply ( isweqtransportf10 _ ( pathsinv0 e ) ). Defined. 


Lemma l1  { X0 X0' : UU } ( ee : paths X0 X0' ) ( P : UU -> UU ) ( pp' : P X0' ) ( R : forall X X' : UU , forall w : weq X X' , P X' -> P X ) ( r : forall X : UU , forall p : P X , paths ( R X X ( idweq X ) p ) p ) : paths ( R X0 X0' ( eqweqmap ee ) pp' ) (  transportb P ee pp' ).
Proof. intro. intro. intro. intro. intro. destruct ee. simpl. intro. intro. apply r. Defined.


Theorem weqtransportb ( P : UU -> UU ) ( R : forall ( X X' : UU ) ( w :  weq X X' ) , P X' -> P X ) ( r : forall X : UU , forall p : P X , paths ( R X X ( idweq X ) p ) p ) :  forall ( X X' : UU ) ( w :  weq X X' ) ( p' : P X' ) , paths ( R X X' w p' ) (  transportb P ( weqtopaths w ) p' ).
Proof. intros. set ( uv := weqtopaths w ).   set ( v := eqweqmap uv ). 

assert ( e : paths v w ) . unfold weqtopaths in uv.  apply ( homotweqinvweq ( weqpair _ ( univalenceaxiom X X' ) ) w ).

assert ( ee : paths ( R X X' v p' ) ( R X X' w p' ) ) . set ( R' := fun vis : weq X X' => R X X' vis p' ). assert ( ee' : paths ( R' v ) ( R' w ) ). apply (  maponpaths R' e ). assumption.

destruct ee. apply l1. assumption. Defined.



Corollary isweqweqtransportb ( P : UU -> UU ) ( R :  forall ( X X' : UU ) ( w :  weq X X' ) , P X' -> P X ) ( r :  forall X : UU , forall p : P X , paths ( R X X ( idweq X ) p ) p ) :  forall ( X X' : UU ) ( w :  weq X X' ) , isweq ( fun p' :  P X' => R X X' w p' ).
Proof. intros. assert ( e : forall p' : P X' , paths ( R X X' w p' ) (  transportb P ( weqtopaths w ) p' ) ). apply weqtransportb. assumption. assert ( ee : forall p' : P X' , paths  ( transportb P ( weqtopaths w ) p' ) ( R X X' w p' ) ). intro.  apply ( pathsinv0 ( e p' ) ). clear e. 

assert ( is1 : isweq ( transportb P ( weqtopaths w ) ) ). apply isweqtransportb10.  
apply ( isweqhomot ( transportb P ( weqtopaths w ) ) ( fun p'  :  P X' => R X X' w p' ) ee is1 ).  Defined. 



    

(** Theorem saying that composition with a weak equivalence is a weak equivalence on function spaces. *)




Theorem isweqcompwithweq { X X' : UU } ( w : weq X X' ) ( Y : UU ) :  isweq ( fun f : X' -> Y => ( fun x : X => f ( w x ) ) ).
Proof. intros. 
set ( P := fun X0 : UU => ( X0 -> Y ) ). 
set ( R := fun X0 : UU => ( fun X0' : UU => ( fun w1 : X0 -> X0' =>  ( fun  f : P X0'  => ( fun x : X0 => f ( w1 x ) ) ) ) ) ). 
set ( r := fun X0 : UU => ( fun f : X0 -> Y => pathsinv0 ( etacor f ) ) ).
apply ( isweqweqtransportb P R r X X' w ). Defined.




(** ** Proof of the functional extensionality for functions *) 


Lemma eqcor0 { X X' : UU } ( w :  weq X X' ) ( Y : UU ) ( f1 f2 : X' -> Y ) : paths ( fun x : X => f1 ( w x ) )  ( fun x : X => f2 ( w x ) ) -> paths f1 f2. 
Proof. intros. apply ( invmaponpathsweq ( weqpair _ ( isweqcompwithweq w Y ) ) f1 f2 ). assumption.  Defined. 


Lemma apathpr1topr ( T : UU ) : paths ( fun z :  pathsspace T => pr1 z ) ( fun z : pathsspace T => pr1 ( pr2 z ) ).
Proof. intro. apply ( eqcor0  ( weqpair _ ( isweqdeltap T ) ) _ ( fun z :  pathsspace T => pr1 z ) ( fun z :  pathsspace T => pr1 ( pr2 z ) ) ( idpath ( idfun T ) ) ) . Defined.     


Theorem funextfun { X Y : UU } ( f1 f2 : X -> Y ) ( e :  forall x : X , paths ( f1 x ) ( f2 x ) ) : paths f1 f2.
Proof. intros. set ( f := fun x : X => pathsspacetriple Y ( e x ) ) .  set ( g1 := fun z : pathsspace Y => pr1 z ) . set ( g2 := fun z :  pathsspace Y => pr1 ( pr2 z ) ). assert ( e' : paths g1 g2 ). apply ( apathpr1topr Y ). assert ( ee : paths  ( fun x : X => f1 x ) ( fun x : X => f2 x ) ). change ( paths (fun x : X => g1 ( f x ) ) (fun x : X => g2 ( f x ) ) ) . destruct e' .  apply idpath .   apply etacoronpaths. apply ee . Defined. 

(* End of the file funextfun.v *)    







(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)




