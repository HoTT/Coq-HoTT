(** * Algebra I. Part C.  Rigs and rings. Vladimir Voevodsky. Aug. 2011 - . 

*)



(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)


(** Imports *)

Require Export algebra1b .


(** To upstream files *)


(** ** Standard Algebraic Structures (cont.) *)


(** *** Rigs - semirings with 1 , 0 and x*0 = 0*x=0 *)

(** **** General definitions *)



Definition rig := total2 ( fun X : setwith2binop =>  isrigops ( @op1 X ) ( @op2 X ) )  .
Definition rigpair { X : setwith2binop } ( is : isrigops ( @op1 X ) ( @op2 X ) ) : rig  := tpair ( fun X : setwith2binop =>  isrigops ( @op1 X ) ( @op2 X ) ) X is .
Definition pr1rig : rig -> setwith2binop := @pr1 _ ( fun X : setwith2binop =>  isrigops ( @op1 X ) ( @op2 X ) ) .
Coercion pr1rig : rig >-> setwith2binop . 

Definition rigaxs ( X : rig ) : isrigops ( @op1 X ) ( @op2 X ) := pr2 X . 

Definition rigop1axs ( X : rig ) : isabmonoidop ( @op1 X ) := rigop1axs_is ( pr2 X ) .
Definition rigassoc1 ( X : rig ) : isassoc ( @op1 X ) := assocax_is ( rigop1axs X ) . 
Definition rigunel1 { X : rig } : X := unel_is ( rigop1axs X ) . 
Definition riglunax1 ( X : rig ) : islunit op1 ( @rigunel1 X ) := lunax_is ( rigop1axs X ) .
Definition rigrunax1 ( X : rig ) : isrunit op1 ( @rigunel1 X ) := runax_is ( rigop1axs X ) .
Definition rigmult0x ( X : rig ) : forall x : X , paths ( op2 ( @rigunel1 X ) x ) ( @rigunel1 X ) := rigmult0x_is ( pr2 X ) . 
Definition rigmultx0 ( X : rig ) : forall x : X , paths ( op2 x ( @rigunel1 X ) ) ( @rigunel1 X ) := rigmultx0_is ( pr2 X ) . 
Definition rigcomm1 ( X : rig ) : iscomm ( @op1 X ) := commax_is ( rigop1axs X ) .
 

Definition rigop2axs ( X : rig ) : ismonoidop ( @op2 X ) := rigop2axs_is ( pr2 X ) .
Definition rigassoc2 ( X : rig ) : isassoc ( @op2 X ) := assocax_is ( rigop2axs X ) . 
Definition rigunel2 { X : rig } : X := unel_is ( rigop2axs X ) . 
Definition riglunax2 ( X : rig ) : islunit op2 ( @rigunel2 X ) := lunax_is ( rigop2axs X ) .
Definition rigrunax2 ( X : rig ) : isrunit op2 ( @rigunel2 X ) := runax_is ( rigop2axs X ) .


Definition rigdistraxs ( X : rig ) : isdistr ( @op1 X ) ( @op2 X ) := pr2 ( pr2 X ) .
Definition rigldistr ( X : rig ) : isldistr ( @op1 X ) ( @op2 X ) := pr1 ( pr2 ( pr2 X ) ) .
Definition rigrdistr ( X : rig ) : isrdistr ( @op1 X ) ( @op2 X ) := pr2 ( pr2 ( pr2 X ) ) .  

Definition rigconstr { X : hSet } ( opp1 opp2 : binop X ) ( ax11 : ismonoidop opp1 ) ( ax12 : iscomm opp1 ) ( ax2 : ismonoidop opp2 ) ( m0x : forall x : X , paths ( opp2 ( unel_is ax11 ) x ) ( unel_is ax11 ) ) ( mx0 : forall x : X , paths ( opp2 x ( unel_is ax11 ) ) ( unel_is ax11 ) ) ( dax : isdistr opp1 opp2 ) : rig .
Proof. intros. split with  ( setwith2binoppair X ( dirprodpair opp1 opp2 ) ) . split . split with ( dirprodpair ( dirprodpair ax11 ax12 ) ax2 ) . apply ( dirprodpair m0x mx0 ) . apply dax . Defined .  

Definition rigaddabmonoid ( X : rig ) : abmonoid := abmonoidpair ( setwithbinoppair X op1 ) ( rigop1axs X ) .
Definition rigmultmonoid ( X : rig ) : monoid := monoidpair  ( setwithbinoppair X op2 ) ( rigop2axs X ) .

Notation "x + y" := ( op1 x y ) : rig_scope .
Notation "x * y" := ( op2 x y ) : rig_scope . 
Notation "0" := ( rigunel1 ) : rig_scope .   
Notation "1" := ( rigunel2 ) : rig_scope .

Delimit Scope rig_scope with rig . 



  


(** **** Homomorphisms of rigs (rig functions) *)

Definition isrigfun { X Y : rig } ( f : X -> Y ) := dirprod ( @ismonoidfun ( rigaddabmonoid X ) ( rigaddabmonoid Y ) f ) ( @ismonoidfun ( rigmultmonoid X ) ( rigmultmonoid Y ) f ) .  

Definition rigfun ( X Y : rig ) := total2 ( fun f : X -> Y => isrigfun f ) .
Definition rigfunconstr { X Y : rig } { f : X -> Y } ( is : isrigfun f ) : rigfun X Y := tpair _ f is .   
Definition pr1rigfun ( X Y : rig ) : rigfun X Y  -> ( X -> Y ) := @pr1 _ _ .
Coercion pr1rigfun : rigfun >-> Funclass. 

Definition rigaddfun { X Y : rig } ( f : rigfun X Y ) : monoidfun ( rigaddabmonoid X ) ( rigaddabmonoid Y ) := monoidfunconstr ( pr1 ( pr2 f ) ) . 
Definition rigmultfun { X Y : rig } ( f : rigfun X Y ) : monoidfun ( rigmultmonoid X ) ( rigmultmonoid Y ) := monoidfunconstr ( pr2 ( pr2 f ) ) . 

Definition rigiso ( X Y : rig ) := total2 ( fun f : weq X Y => isrigfun f ) .   
Definition rigisopair { X Y : rig } ( f : weq X Y ) ( is : isrigfun f ) : rigiso X Y := tpair _  f is .
Definition pr1rigiso ( X Y : rig ) : rigiso X Y -> weq X Y := @pr1 _ _ .
Coercion pr1rigiso : rigiso >-> weq .

Definition rigaddiso { X Y : rig } ( f : rigiso X Y ) : monoidiso ( rigaddabmonoid X ) ( rigaddabmonoid Y ) := @monoidisopair ( rigaddabmonoid X ) ( rigaddabmonoid Y ) ( pr1 f ) ( pr1 ( pr2 f ) ) . 
Definition rigmultiso { X Y : rig } ( f : rigiso X Y ) : monoidiso ( rigmultmonoid X ) ( rigmultmonoid Y ) := @monoidisopair ( rigmultmonoid X )  ( rigmultmonoid Y ) ( pr1 f ) ( pr2 ( pr2 f ) ) . 

Lemma isrigfuninvmap { X Y : rig } ( f : rigiso X Y ) : isrigfun ( invmap f ) .
Proof . intros . split . apply ( ismonoidfuninvmap ( rigaddiso f ) ) . apply  ( ismonoidfuninvmap ( rigmultiso f ) ) . Defined .   



(** **** Relations similar to "greater" or "greater or equal" on rigs *)

Definition isrigmultgt ( X : rig ) ( R : hrel X ) :=  forall a b c d : X , R a b -> R c d -> R ( op1 ( op2 a c ) ( op2 b d ) ) ( op1 ( op2 a d ) ( op2 b c ) ) . 

Definition isinvrigmultgt ( X : rig ) ( R : hrel X ) := dirprod ( forall a b c d : X , R ( op1 ( op2 a c ) ( op2 b d ) ) ( op1 ( op2 a d ) ( op2 b c ) ) -> R a b -> R c d ) ( forall a b c d : X , R ( op1 ( op2 a c ) ( op2 b d ) ) ( op1 ( op2 a d ) ( op2 b c ) ) -> R c d -> R a b ) . 


(** **** Subobjects *)

Definition issubrig { X : rig } ( A : hsubtypes X ) := dirprod ( @issubmonoid ( rigaddabmonoid X ) A ) ( @issubmonoid ( rigmultmonoid X ) A ) . 

Lemma isapropissubrig { X : rig } ( A : hsubtypes X ) : isaprop ( issubrig A ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropissubmonoid . apply isapropissubmonoid . Defined . 

Definition subrigs ( X : rig ) := total2 ( fun  A : hsubtypes X => issubrig A ) .
Definition subrigpair { X : rig } := tpair ( fun  A : hsubtypes X => issubrig A ) .
Definition pr1subrig ( X : rig ) : @subrigs X -> hsubtypes X := @pr1 _ (fun  A : hsubtypes X => issubrig A ) .

Definition subrigtosubsetswith2binop ( X : rig ) : subrigs X -> @subsetswith2binop X := fun A : _ => subsetswith2binoppair ( pr1 A ) ( dirprodpair ( pr1 ( pr1 ( pr2 A ) ) ) ( pr1 ( pr2 ( pr2 A ) ) ) ) . 
Coercion subrigtosubsetswith2binop : subrigs >-> subsetswith2binop . 

Definition rigaddsubmonoid { X : rig } : subrigs X -> @subabmonoids ( rigaddabmonoid X ) := fun A : _ => @submonoidpair ( rigaddabmonoid X ) ( pr1 A ) ( pr1 ( pr2 A ) ) .
Definition rigmultsubmonoid { X : rig } : subrigs X -> @submonoids ( rigmultmonoid X ) := fun A : _ => @submonoidpair ( rigmultmonoid X ) ( pr1 A ) ( pr2 ( pr2 A ) ) .  

Lemma isrigcarrier { X : rig } ( A : subrigs X ) : isrigops ( @op1 A ) ( @op2 A ) .
Proof . intros . split . split with ( dirprodpair ( isabmonoidcarrier ( rigaddsubmonoid A ) ) ( ismonoidcarrier ( rigmultsubmonoid A ) ) ) . split . 

intro a . apply ( invmaponpathsincl _ ( isinclpr1carrier A ) ) . simpl . apply rigmult0x .   
intro a .  apply ( invmaponpathsincl _ ( isinclpr1carrier A ) ) . simpl . apply rigmultx0 .  split . 

intros a b c . apply ( invmaponpathsincl _ ( isinclpr1carrier A ) ) .  simpl . apply rigldistr .  
intros a b c . apply ( invmaponpathsincl _ ( isinclpr1carrier A ) ) .  simpl . apply rigrdistr . Defined .   

Definition carrierofasubrig ( X : rig ) ( A : subrigs X ) : rig .
Proof . intros . split with A . apply isrigcarrier .  Defined . 

Coercion carrierofasubrig : subrigs >-> rig .  


(** **** Quotient objects *) 


Definition rigeqrel { X : rig } := @twobinopeqrel X .
Identity Coercion id_rigeqrel : rigeqrel >-> twobinopeqrel .

Definition addabmonoideqrel { X : rig } ( R : @rigeqrel X ) : @binopeqrel ( rigaddabmonoid X ) := @binopeqrelpair ( rigaddabmonoid X ) ( pr1 R ) ( pr1 ( pr2 R ) ) .     

Definition multmonoideqrel { X : rig } ( R : @rigeqrel X ) : @binopeqrel ( rigmultmonoid X ) := @binopeqrelpair ( rigmultmonoid X ) ( pr1 R ) ( pr2 ( pr2 R ) ) .

Lemma isrigquot { X : rig } ( R : @rigeqrel X ) : isrigops ( @op1 ( setwith2binopquot R ) ) ( @op2 ( setwith2binopquot R ) ) . 
Proof . intros .  split . split with ( dirprodpair ( isabmonoidquot ( addabmonoideqrel R ) ) ( ismonoidquot ( multmonoideqrel R ) ) ) . set ( opp1 := @op1 ( setwith2binopquot R ) ) . set ( opp2 := @op2 ( setwith2binopquot R ) ) .  set ( zr := setquotpr R ( @rigunel1 X ) ) . split . 

apply  ( setquotunivprop R ( fun x  => hProppair _ ( setproperty ( setwith2binopquot R ) ( opp2 zr x ) zr ) ) ) .  intro x .   apply ( maponpaths ( setquotpr R ) ( rigmult0x X x ) ) .  
apply  ( setquotunivprop R ( fun x  => hProppair _ ( setproperty ( setwith2binopquot R ) ( opp2 x zr ) zr ) ) ) .  intro x .   apply ( maponpaths ( setquotpr R ) ( rigmultx0 X x ) ) .

set ( opp1 := @op1 ( setwith2binopquot R ) ) . set ( opp2 := @op2 ( setwith2binopquot R ) ) .  split . 


unfold isldistr . apply  ( setquotuniv3prop R ( fun x x' x''  => hProppair _ ( setproperty ( setwith2binopquot R ) ( opp2  x'' ( opp1 x x' ) ) ( opp1 ( opp2 x'' x ) ( opp2 x'' x' ) ) ) ) ) .  intros x x' x'' .   apply ( maponpaths ( setquotpr R ) ( rigldistr X x x' x'' ) ) .  

unfold isrdistr . apply  ( setquotuniv3prop R ( fun x x' x''  => hProppair _ ( setproperty ( setwith2binopquot R ) ( opp2  ( opp1 x x' ) x''  ) ( opp1 ( opp2 x x'' ) ( opp2 x' x'' ) ) ) ) ) .  intros x x' x'' .   apply ( maponpaths ( setquotpr R ) ( rigrdistr X x x' x'' ) ) .  Defined .

Definition rigquot { X : rig } ( R : @rigeqrel X ) : rig := @rigpair ( setwith2binopquot R ) ( isrigquot R ) .   



(** **** Direct products *)

Lemma isrigdirprod ( X Y : rig ) : isrigops ( @op1 ( setwith2binopdirprod X Y ) ) ( @op2 ( setwith2binopdirprod X Y ) ) .
Proof . intros . split .   split with ( dirprodpair ( isabmonoiddirprod ( rigaddabmonoid X ) ( rigaddabmonoid Y ) ) ( ismonoiddirprod ( rigmultmonoid X ) ( rigmultmonoid Y ) ) ) . simpl .  split . 

intro xy . unfold setwith2binopdirprod . unfold op1 . unfold op2 . unfold ismonoiddirprod . unfold unel_is .   simpl .  apply pathsdirprod .  apply ( rigmult0x X ) .  apply ( rigmult0x Y ) . 
intro xy . unfold setwith2binopdirprod . unfold op1 . unfold op2 . unfold ismonoiddirprod . unfold unel_is .   simpl .  apply pathsdirprod .  apply ( rigmultx0 X ) .  apply ( rigmultx0 Y ) . split . 

intros xy xy' xy'' . unfold setwith2binopdirprod . unfold op1 . unfold op2 .  simpl . apply pathsdirprod .  apply ( rigldistr X ) .  apply ( rigldistr Y ) . 
intros xy xy' xy'' . unfold setwith2binopdirprod . unfold op1 . unfold op2 .  simpl . apply pathsdirprod .  apply ( rigrdistr X ) .  apply ( rigrdistr Y ) .  Defined . 


Definition rigdirprod ( X Y : rig ) := @rigpair ( setwith2binopdirprod X Y ) ( isrigdirprod X Y ) . 





(** *** Commutative rigs *)

(** **** General definitions *)


Definition commrig := total2 ( fun X : setwith2binop => iscommrigops ( @op1 X ) ( @op2 X ) ) .
Definition commrigpair ( X : setwith2binop ) ( is : iscommrigops ( @op1 X ) ( @op2 X ) ) : commrig := tpair ( fun X : setwith2binop => iscommrigops ( @op1 X ) ( @op2 X ) ) X is .

Definition commrigconstr { X : hSet } ( opp1 opp2 : binop X ) ( ax11 : ismonoidop opp1 ) ( ax12 : iscomm opp1 ) ( ax2 : ismonoidop opp2 ) ( ax22 : iscomm opp2 ) ( m0x : forall x : X , paths ( opp2 ( unel_is ax11 ) x ) ( unel_is ax11 ) ) ( mx0 : forall x : X , paths ( opp2 x ( unel_is ax11 ) ) ( unel_is ax11 ) ) ( dax : isdistr opp1 opp2 ) : commrig .
Proof. intros. split with  ( setwith2binoppair X ( dirprodpair opp1 opp2 ) ) . split . split . split with ( dirprodpair ( dirprodpair ax11 ax12 ) ax2 ) . apply ( dirprodpair m0x mx0 ) . apply dax . apply ax22 . Defined . 

Definition commrigtorig : commrig -> rig := fun X : _ => @rigpair ( pr1 X ) ( pr1 ( pr2 X ) ) . 
Coercion commrigtorig : commrig >-> rig .

Definition rigcomm2 ( X : commrig ) : iscomm ( @op2 X ) := pr2 ( pr2 X ) . 
Definition commrigop2axs ( X : commrig ) : isabmonoidop ( @op2 X ) := tpair _ ( rigop2axs X ) ( rigcomm2 X ) . 


Definition commrigmultabmonoid ( X : commrig ) : abmonoid := abmonoidpair ( setwithbinoppair X op2 ) ( dirprodpair ( rigop2axs X ) ( rigcomm2 X ) ) .


 
(** **** Relations similar to "greater" on commutative rigs *)


Lemma isinvrigmultgtif ( X : commrig ) ( R : hrel X ) ( is2 : forall a b c d ,  R ( op1 ( op2 a c ) ( op2 b d ) ) ( op1 ( op2 a d ) ( op2 b c ) ) -> R a b -> R c d ) : isinvrigmultgt X R . 
Proof . intros . split .  apply is2 .  intros a b c d r rcd . rewrite ( rigcomm1 X ( op2 a d ) _ ) in r . rewrite ( rigcomm2 X a c ) in r . rewrite ( rigcomm2 X b d ) in r .     rewrite ( rigcomm2 X b c ) in r .  rewrite ( rigcomm2 X a d ) in r .  apply ( is2 _ _ _ _ r rcd ) . Defined . 



(** **** Subobjects *)

Lemma iscommrigcarrier { X : commrig } ( A : @subrigs X ) : iscommrigops ( @op1 A ) ( @op2 A ) .
Proof . intros . split with ( isrigcarrier A ) . apply ( pr2 ( @isabmonoidcarrier ( commrigmultabmonoid X ) ( rigmultsubmonoid A ) ) ) .  Defined . 

(* ??? slows down at the last [ apply ] and at [ Defined ] ( oct.16.2011 - does not slow down anymore with two Dan's patches ) *)

Definition carrierofasubcommrig { X : commrig } ( A : @subrigs X ) : commrig := commrigpair A ( iscommrigcarrier A ) . 


(** **** Quotient objects *)

Lemma iscommrigquot { X : commrig } ( R : @rigeqrel X ) : iscommrigops ( @op1 ( setwith2binopquot R ) ) ( @op2 ( setwith2binopquot R ) ) . 
Proof . intros . split with ( isrigquot R ) . apply ( pr2 ( @isabmonoidquot  ( commrigmultabmonoid X ) ( multmonoideqrel R ) ) ) .  Defined . 

Definition commrigquot { X : commrig } ( R : @rigeqrel X ) := commrigpair ( setwith2binopquot R ) ( iscommrigquot R ) . 




(** **** Direct products *)

Lemma iscommrigdirprod ( X Y : commrig ) : iscommrigops ( @op1 ( setwith2binopdirprod X Y ) ) ( @op2 ( setwith2binopdirprod X Y ) ) .
Proof . intros . split with ( isrigdirprod X Y ) . apply ( pr2 ( isabmonoiddirprod ( commrigmultabmonoid X ) ( commrigmultabmonoid Y ) ) ) . Defined . 

Definition commrigdirprod ( X Y : commrig ) := commrigpair ( setwith2binopdirprod X Y ) ( iscommrigdirprod X Y ) . 




(** *** Rings *)


(** **** General definitions *)


Definition rng := total2 ( fun X : setwith2binop =>  isrngops ( @op1 X ) ( @op2 X ) )  .
Definition rngpair { X : setwith2binop } ( is : isrngops ( @op1 X ) ( @op2 X ) ) : rng  := tpair ( fun X : setwith2binop =>  isrngops ( @op1 X ) ( @op2 X ) ) X is .
Definition pr1rng : rng -> setwith2binop := @pr1 _ ( fun X : setwith2binop =>  isrngops ( @op1 X ) ( @op2 X ) ) .
Coercion pr1rng : rng >-> setwith2binop .  


Definition rngaxs ( X : rng ) : isrngops ( @op1 X ) ( @op2 X ) := pr2 X . 

Definition rngop1axs ( X : rng ) : isabgrop ( @op1 X ) := pr1 ( pr1 ( pr2 X ) ) .
Definition rngassoc1 ( X : rng ) : isassoc ( @op1 X ) := assocax_is ( rngop1axs X ) . 
Definition rngunel1 { X : rng } : X := unel_is ( rngop1axs X ) . 
Definition rnglunax1 ( X : rng ) : islunit op1 ( @rngunel1 X ) := lunax_is ( rngop1axs X ) .
Definition rngrunax1 ( X : rng ) : isrunit op1 ( @rngunel1 X ) := runax_is ( rngop1axs X ) .
Definition rnginv1 { X : rng } : X -> X := grinv_is ( rngop1axs X ) .
Definition rnglinvax1 ( X : rng ) : forall x : X , paths ( op1 ( rnginv1 x ) x ) rngunel1 := grlinvax_is ( rngop1axs X ) .
Definition rngrinvax1 ( X : rng ) : forall x : X , paths ( op1 x ( rnginv1 x ) ) rngunel1 := grrinvax_is ( rngop1axs X ) . 
Definition rngcomm1 ( X : rng ) : iscomm ( @op1 X ) := commax_is ( rngop1axs X ) .
 

Definition rngop2axs ( X : rng ) : ismonoidop ( @op2 X ) := pr2 ( pr1 ( pr2 X ) ) .
Definition rngassoc2 ( X : rng ) : isassoc ( @op2 X ) := assocax_is ( rngop2axs X ) . 
Definition rngunel2 { X : rng } : X := unel_is ( rngop2axs X ) . 
Definition rnglunax2 ( X : rng ) : islunit op2 ( @rngunel2 X ) := lunax_is ( rngop2axs X ) .
Definition rngrunax2 ( X : rng ) : isrunit op2 ( @rngunel2 X ) := runax_is ( rngop2axs X ) .


Definition rngdistraxs ( X : rng ) : isdistr ( @op1 X ) ( @op2 X ) := pr2 ( pr2 X ) .
Definition rngldistr ( X : rng ) : isldistr ( @op1 X ) ( @op2 X ) := pr1 ( pr2 ( pr2 X ) ) .
Definition rngrdistr ( X : rng ) : isrdistr ( @op1 X ) ( @op2 X ) := pr2 ( pr2 ( pr2 X ) ) .  

Definition rngconstr { X : hSet } ( opp1 opp2 : binop X ) ( ax11 : isgrop opp1 ) ( ax12 : iscomm opp1 ) ( ax2 : ismonoidop opp2 ) ( dax : isdistr opp1 opp2 ) : rng := @rngpair ( setwith2binoppair X ( dirprodpair opp1 opp2 ) ) ( dirprodpair ( dirprodpair ( dirprodpair ax11 ax12 ) ax2 ) dax ) .   

Definition rngmultx0 ( X : rng ) : forall x : X , paths ( op2 x rngunel1 ) rngunel1 := rngmultx0_is ( rngaxs X ) .  
Definition rngmult0x ( X : rng ) : forall x : X , paths ( op2 rngunel1 x ) rngunel1 := rngmult0x_is ( rngaxs X ) .
Definition rngminus1 { X : rng } : X := rngminus1_is ( rngaxs X ) . 
Definition rngmultwithminus1 ( X : rng ) : forall x : X , paths ( op2 rngminus1 x ) ( rnginv1 x ) := rngmultwithminus1_is ( rngaxs X ) .
  

Definition rngaddabgr ( X : rng ) : abgr := abgrpair ( setwithbinoppair X op1 ) ( rngop1axs X ) .
Definition rngmultmonoid ( X : rng ) : monoid := monoidpair  ( setwithbinoppair X op2 ) ( rngop2axs X ) .

Notation "x + y" := ( op1 x y ) : rng_scope .
Notation "x - y" := ( op1 x ( rnginv1 y ) ) .
Notation "x * y" := ( op2 x y ) : rng_scope . 
Notation "0" := ( rngunel1 ) : rng_scope .   
Notation "1" := ( rngunel2 ) : rng_scope .
Notation "-1" := ( rngminus1 ) ( at level 0 ) : rng_scope . 
Notation " - x " := ( rnginv1 x ) : rng_scope .

Delimit Scope rng_scope with rng . 


Definition rngtorig ( X : rng ) : rig := @rigpair _ ( pr2 X ) . 
Coercion rngtorig : rng >-> rig .

(** **** Homomorphisms of rings *)

Definition isrngfun { X Y : rng } ( f : X -> Y ) := @isrigfun X Y f .  

Definition rngfun ( X Y : rng ) := rigfun X Y .
Definition rngfunconstr { X Y : rng } { f : X -> Y } ( is : isrngfun f ) : rngfun X Y := rigfunconstr is .   
Identity Coercion id_rngfun : rngfun >-> rigfun. 

Definition rngaddfun { X Y : rng } ( f : rngfun X Y ) : monoidfun ( rngaddabgr X ) ( rngaddabgr Y ) := monoidfunconstr ( pr1 ( pr2 f ) ) . 
Definition rngmultfun { X Y : rng } ( f : rngfun X Y ) : monoidfun ( rngmultmonoid X ) ( rngmultmonoid Y ) := monoidfunconstr ( pr2 ( pr2 f ) ) . 

Definition rngiso ( X Y : rng ) := rigiso X Y .   
Definition rngisopair { X Y : rng } ( f : weq X Y ) ( is : isrngfun f ) : rngiso X Y := tpair _  f is .
Identity Coercion id_rngiso : rngiso >-> rigiso .

Definition isrngfuninvmap { X Y : rng } ( f : rngiso X Y ) : isrngfun ( invmap f ) := isrigfuninvmap f . 
   






(** **** Computation lemmas for rings *)

Open Scope rng_scope . 

Definition rnginvunel1 ( X : rng ) : paths ( - 0 ) 0 := grinvunel ( rngaddabgr X ) .

Lemma rngismultlcancelableif ( X : rng ) ( x : X ) ( isl: forall y , paths ( x * y ) 0 -> paths y 0 ) : islcancelable op2 x . 
Proof . intros . apply ( @isinclbetweensets X X ) . apply setproperty .  apply setproperty . intros x1 x2 e . assert ( e' := maponpaths ( fun a => a + ( x * ( -x2 ) ) ) e ) .  simpl in e' .  rewrite ( pathsinv0 ( rngldistr X _ _ x ) ) in e' .  rewrite ( pathsinv0 ( rngldistr X _ _ x ) ) in e' . rewrite ( rngrinvax1 X x2 ) in e' . rewrite ( rngmultx0 X _ ) in e' .  assert ( e'' := isl ( x1 - x2 ) e' ) . assert ( e''' := maponpaths ( fun a => a + x2 ) e'' ) .  simpl in e''' .  rewrite ( rngassoc1 X _ _ x2  ) in e''' .  rewrite ( rnglinvax1 X x2 ) in e''' . rewrite ( rnglunax1 X _ ) in e''' .   rewrite ( rngrunax1 X _ ) in e''' . apply e''' . Defined .

Opaque  rngismultlcancelableif .

Lemma rngismultrcancelableif ( X : rng ) ( x : X ) ( isr: forall y , paths ( y * x ) 0 -> paths y 0 ) : isrcancelable op2 x . 
Proof . intros . apply ( @isinclbetweensets X X ) . apply setproperty .  apply setproperty . intros x1 x2 e . assert ( e' := maponpaths ( fun a => a + ( ( -x2 ) * x ) ) e ) .  simpl in e' .  rewrite ( pathsinv0 ( rngrdistr X _ _ x ) ) in e' .  rewrite ( pathsinv0 ( rngrdistr X _ _ x ) ) in e' . rewrite ( rngrinvax1 X x2 ) in e' . rewrite ( rngmult0x X _ ) in e' .  assert ( e'' := isr ( x1 - x2 ) e' ) . assert ( e''' := maponpaths ( fun a => a + x2 ) e'' ) .  simpl in e''' .  rewrite ( rngassoc1 X _ _ x2  ) in e''' .  rewrite ( rnglinvax1 X x2 ) in e''' . rewrite ( rnglunax1 X _ ) in e''' .   rewrite ( rngrunax1 X _ ) in e''' . apply e''' . Defined .

Opaque  rngismultrcancelableif .

Lemma rngismultcancelableif ( X : rng ) ( x : X ) ( isl: forall y , paths ( x * y ) 0 -> paths y 0 )  ( isr: forall y , paths ( y * x ) 0 -> paths y 0 ) : iscancelable op2 x .
Proof . intros . apply ( dirprodpair ( rngismultlcancelableif X x isl ) ( rngismultrcancelableif X x isr ) ) . Defined . 

Lemma rnglmultminus ( X : rng ) ( a b : X ) : paths ( ( - a ) * b ) ( - ( a * b ) ) .
Proof . intros .  apply ( @grrcan ( rngaddabgr X ) _ _ ( a * b ) ) .  change ( paths ( -a * b + a * b ) ( - ( a * b ) + a * b ) ) . rewrite ( rnglinvax1 X _ ) .  rewrite ( pathsinv0 ( rngrdistr X _ _ _ ) ) .  rewrite ( rnglinvax1 X _ ) . rewrite ( rngmult0x X _ ) . apply idpath . Defined . 

Opaque rnglmultminus .

Lemma rngrmultminus ( X : rng ) ( a b : X ) : paths ( a * ( - b ) ) ( - ( a * b ) ) .
Proof . intros .  apply ( @grrcan ( rngaddabgr X ) _ _ ( a * b ) ) .  change ( paths ( a * ( - b ) + a * b ) ( - ( a * b ) + a * b ) ) . rewrite ( rnglinvax1 X _ ) .  rewrite ( pathsinv0 ( rngldistr X _ _ _ ) ) .  rewrite ( rnglinvax1 X _ ) . rewrite ( rngmultx0 X _ ) . apply idpath . Defined . 
 
Opaque rngrmultminus .

Lemma rngmultminusminus ( X : rng ) ( a b : X ) : paths ( -a * - b ) ( a * b ) .
Proof . intros . apply ( @grrcan ( rngaddabgr X ) _ _ ( - a * b ) ) .  simpl .  rewrite ( pathsinv0 ( rngldistr X _ _ ( - a ) ) ) . rewrite ( pathsinv0 ( rngrdistr X _ _ b ) ) .  rewrite ( rnglinvax1 X b ) . rewrite ( rngrinvax1 X a ) .  rewrite ( rngmult0x X _ ) . rewrite ( rngmultx0 X _ ) . apply idpath . Defined .

Opaque rngmultminusminus .  

Lemma rngminusminus ( X : rng ) ( a : X ) : paths ( - - a ) a .
Proof . intros . apply  ( grinvinv ( rngaddabgr X ) a ) . Defined . 

Definition rnginvmaponpathsminus ( X : rng ) { a b : X } ( e : paths ( - a ) ( - b ) ) : paths a b := grinvmaponpathsinv ( rngaddabgr X ) e . 


(** **** Relations compatible with the additive structure on rings *)


Definition rngfromgt0 ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) { x : X } ( is : R x 0 ) : R 0 ( - x ) := grfromgtunel ( rngaddabgr X ) is0 is . 

Definition rngtogt0 ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) { x : X } ( is : R 0 ( - x ) ) : R x 0  := grtogtunel ( rngaddabgr X ) is0 is . 

Definition rngfromlt0 ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) { x : X } ( is : R 0 x ) : R ( - x ) 0 := grfromltunel ( rngaddabgr X ) is0 is . 

Definition rngtolt0 ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) { x : X } ( is : R ( - x ) 0 ) : R 0 x := grtoltunel ( rngaddabgr X ) is0 is .


(** **** Relations compatible with the multiplicative structure on rings *)
 

Definition isrngmultgt ( X : rng ) ( R : hrel X ) := forall a b , R a 0 -> R b 0 -> R ( a * b ) 0 . 

Lemma rngmultgt0lt0 ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is : isrngmultgt X R ) { x y : X } ( isx : R x 0 ) ( isy : R 0 y ) : R 0 ( x * y ) .
Proof . intros . assert ( isy' := grfromltunel ( rngaddabgr X ) is0 isy ) . assert ( r := is _ _ isx isy' ) .  change ( pr1 ( R ( x * ( - y ) ) 0 ) ) in r . rewrite ( rngrmultminus X _ _ ) in r . assert ( r' := grfromgtunel ( rngaddabgr X ) is0 r ) . change ( pr1 ( R 0 ( - - ( x * y ) ) ) ) in r' . rewrite ( rngminusminus X ( x * y ) ) in r' .   apply r' .  Defined . 

Opaque rngmultgt0lt0 . 

Lemma rngmultlt0gt0 ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is : isrngmultgt X R ) { x y : X } ( isx : R 0 x ) ( isy : R y 0 ) : R 0 ( x * y ) .
Proof . intros . assert ( isx' := grfromltunel ( rngaddabgr X ) is0 isx ) . assert ( r := is _ _ isx' isy ) .  change ( pr1 ( R ( ( - x ) * y ) 0 ) ) in r . rewrite ( rnglmultminus X _ _ ) in r . assert ( r' := grfromgtunel ( rngaddabgr X ) is0 r ) . change ( pr1 ( R 0 ( - - ( x * y ) ) ) ) in r' . rewrite ( rngminusminus X ( x * y ) ) in r' .   apply r' .  Defined . 

Opaque rngmultlt0gt0 .

Lemma rngmultlt0lt0 ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is : isrngmultgt X R ) { x y : X } ( isx : R 0 x ) ( isy : R 0 y ) : R ( x * y ) 0 .
Proof . intros . assert ( rx := rngfromlt0 _ is0 isx ) .   assert ( ry := rngfromlt0 _ is0 isy ) . assert ( int := is _ _ rx ry ) . rewrite ( rngmultminusminus X _ _ ) in int .   apply int . Defined . 

Opaque rngmultlt0lt0 .

Lemma isrngmultgttoislrngmultgt ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is : isrngmultgt X R ) : forall a b c : X , R c 0 -> R a b -> R ( c * a ) ( c * b ) . 
Proof . intros X R is0 is a b c rc0 rab . set ( rab':= ( pr2 is0 ) _ _ ( - b ) rab ) .  clearbody rab' . change ( pr1 ( R ( a - b ) ( b - b ) ) ) in rab' .  rewrite ( rngrinvax1 X b ) in rab' . set ( r' := is _ _ rc0 rab' ) . clearbody r' . set ( r'' :=  ( pr2 is0 ) _ _ ( c * b ) r' ) .  clearbody r'' .  change ( pr1 ( R ( c * ( a - b ) + c * b ) ( 0 + c * b ) ) ) in r'' . rewrite ( rnglunax1 X _ ) in r'' .  rewrite ( pathsinv0 ( rngldistr X _ _ c ) ) in r'' .  rewrite ( rngassoc1 X a _ _ ) in r'' .  rewrite ( rnglinvax1 X b ) in r'' .   rewrite ( rngrunax1 X _ ) in r'' .  apply r'' .  Defined . 

Opaque isrngmultgttoislrngmultgt .

Lemma islrngmultgttoisrngmultgt ( X : rng ) { R : hrel X } ( is : forall a b c : X , R c 0 -> R a b -> R ( c * a ) ( c * b ) ) : isrngmultgt X R . 
Proof . intros . intros a b ra rb . set ( int := is b 0 a ra rb ) .  clearbody int .  rewrite ( rngmultx0 X _ ) in int .  apply int . Defined . 

Opaque islrngmultgttoisrngmultgt . 

Lemma isrngmultgttoisrrngmultgt ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is : isrngmultgt X R ) : forall a b c : X , R c 0 -> R a b -> R ( a * c ) ( b * c ) . 
Proof . intros X R is0 is a b c rc0 rab . set ( rab':= ( pr2 is0 ) _ _ ( - b ) rab ) .  clearbody rab' . change ( pr1 ( R ( a - b ) ( b - b ) ) ) in rab' .  rewrite ( rngrinvax1 X b ) in rab' . set ( r' := is _ _ rab' rc0 ) . clearbody r' . set ( r'' :=  ( pr2 is0 ) _ _ ( b * c ) r' ) .  clearbody r'' .  change ( pr1 ( R ( ( a - b ) * c + b * c ) ( 0 + b * c ) ) ) in r'' . rewrite ( rnglunax1 X _ ) in r'' .  rewrite ( pathsinv0 ( rngrdistr X _ _ c ) ) in r'' .  rewrite ( rngassoc1 X a _ _ ) in r'' .  rewrite ( rnglinvax1 X b ) in r'' .   rewrite ( rngrunax1 X _ ) in r'' .  apply r'' .  Defined . 

Opaque isrngmultgttoisrrngmultgt . 

Lemma isrrngmultgttoisrngmultgt ( X : rng ) { R : hrel X } ( is1 : forall a b c : X , R c 0 -> R a b -> R ( a * c ) ( b * c ) ) : isrngmultgt X R . 
Proof . intros . intros a b ra rb . set ( int := is1 _ _ _ rb ra ) .  clearbody int .  rewrite ( rngmult0x X _ ) in int .  apply int . Defined . 

Opaque isrrngmultgttoisrngmultgt .


Lemma isrngmultgtaspartbinophrel ( X : rng ) ( R : hrel X ) ( is0 : @isbinophrel ( rngaddabgr X ) R ) : ( isrngmultgt X R ) <-> ( @ispartbinophrel ( rngmultmonoid X ) ( fun a => R a 0 ) R ) . 
Proof . intros . split .  intro ism . split .  apply ( isrngmultgttoislrngmultgt X is0 ism ) .   apply ( isrngmultgttoisrrngmultgt X is0 ism ) . intro isp . apply ( islrngmultgttoisrngmultgt X ( pr1 isp ) ) . Defined .  


Lemma isrngmultgttoisrigmultgt ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is : isrngmultgt X R ) : isrigmultgt X R .
Proof . intros . set ( rer := abmonoidrer ( rngaddabgr X ) ) . simpl in rer .  intros a b c d rab rcd .  assert ( intab : R ( a - b ) 0 ) . destruct ( rngrinvax1 X b ) . apply ( ( pr2 is0 ) _ _ ( - b ) ) . apply rab .  assert ( intcd : R ( c - d ) 0 ) . destruct ( rngrinvax1 X d ) . apply ( ( pr2 is0 ) _ _ ( - d ) ) . apply rcd .  
set ( int := is _ _ intab intcd ) .  rewrite ( rngrdistr X _ _ _ ) in int .  rewrite ( rngldistr X _ _ _ ) in int .  rewrite ( rngldistr X _ _ _ ) in int . set ( int' := ( pr2 is0 ) _ _ ( a * d + b * c ) int ) . clearbody int' .  simpl in int' .  rewrite ( rnglunax1 _ ) in int' .  rewrite ( rngcomm1 X ( - b * c ) _ ) in int' .  rewrite ( rer _ ( a * - d ) _ _ ) in int' . rewrite ( rngassoc1 X  _ (a * - d + - b * c) _ ) in int' .  rewrite ( rer _ _ ( a * d ) _ ) in int' . rewrite ( pathsinv0 ( rngldistr X _ _ a ) ) in int'.  rewrite ( rnglinvax1 X d ) in int' . rewrite ( rngmultx0 X _ ) in int' .  rewrite ( pathsinv0 ( rngrdistr X _ _ c ) ) in int' .   rewrite ( rnglinvax1 X b ) in int' . rewrite ( rngmult0x X _ ) in int' . rewrite ( rngrunax1 X _ ) in int' . rewrite ( rngrunax1 X _ ) in int' . rewrite ( rngmultminusminus X b d ) in int' .   apply int' .  Defined . 

Opaque isrngmultgttoisrigmultgt . 

Lemma isrigmultgttoisrngmultgt ( X : rng ) { R : hrel X } ( is : isrigmultgt X R ) : isrngmultgt X R .
Proof . intros .  intros a b ra0 rb0 . set ( is' := is _ _ _ _ ra0 rb0 ) .  simpl in is' . fold ( pr1rng ) in is' . rewrite ( rngmult0x X b ) in is' .   rewrite ( rngmultx0 X a ) in is' .  rewrite ( rngmult0x X 0 ) in is' .   rewrite ( rngrunax1 X _ ) in is' .  rewrite ( rngrunax1 X _ ) in is' .  apply is' .  Defined . 

Opaque isrigmultgttoisrngmultgt .


(** **** Relations "inversely compatible" with the multiplicative structure on rings *)



Definition isinvrngmultgt  ( X : rng ) ( R : hrel X ) := dirprod ( forall a b , R ( a * b ) 0 -> R a 0 -> R b 0  ) ( forall a b , R ( a * b ) 0 -> R b 0 -> R a 0  ) .


Lemma isinvrngmultgttoislinvrngmultgt ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is : isinvrngmultgt X R ) : forall a b c : X , R c 0 -> R ( c * a ) ( c * b ) -> R a b . 
Proof . intros X R is0 is a b c rc0 r . set ( rab':= ( pr2 is0 ) _ _ ( c * - b ) r ) .  clearbody rab' . change ( pr1 ( R ( c * a + c * - b ) ( c * b + c * - b ) ) ) in rab' .  rewrite ( pathsinv0 ( rngldistr X _ _ c ) ) in rab' .  rewrite ( pathsinv0 ( rngldistr X _ _ c ) ) in rab' .  rewrite ( rngrinvax1 X b ) in rab' .  rewrite ( rngmultx0 X _ ) in rab' .  set ( r' := ( pr1 is ) _ _ rab' rc0 ) . clearbody r' . set ( r'' :=  ( pr2 is0 ) _ _ b r' ) .  clearbody r'' .  change ( pr1 ( R ( a - b + b ) ( 0 + b ) ) ) in r'' . rewrite ( rnglunax1 X _ ) in r'' .  rewrite ( rngassoc1 X a _ _ ) in r'' .  rewrite ( rnglinvax1 X b ) in r'' .   rewrite ( rngrunax1 X _ ) in r'' .  apply r'' .  Defined . 

Opaque isinvrngmultgttoislinvrngmultgt .

Lemma isinvrngmultgttoisrinvrngmultgt ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is : isinvrngmultgt X R ) : forall a b c : X , R c 0 -> R ( a * c ) ( b * c ) -> R a b . 
Proof . intros X R is0 is a b c rc0 r . set ( rab':= ( pr2 is0 ) _ _ ( - b * c ) r ) .  clearbody rab' . change ( pr1 ( R ( a * c + - b * c ) ( b * c + - b * c ) ) ) in rab' .  rewrite ( pathsinv0 ( rngrdistr X _ _ c ) ) in rab' .  rewrite ( pathsinv0 ( rngrdistr X _ _ c ) ) in rab' .  rewrite ( rngrinvax1 X b ) in rab' .  rewrite ( rngmult0x X _ ) in rab' .  set ( r' := ( pr2 is ) _ _ rab' rc0 ) . clearbody r' . set ( r'' :=  ( pr2 is0 ) _ _ b r' ) .  clearbody r'' .  change ( pr1 ( R ( a - b + b ) ( 0 + b ) ) ) in r'' . rewrite ( rnglunax1 X _ ) in r'' .  rewrite ( rngassoc1 X a _ _ ) in r'' .  rewrite ( rnglinvax1 X b ) in r'' .   rewrite ( rngrunax1 X _ ) in r'' .  apply r'' .  Defined . 

Opaque isinvrngmultgttoisrinvrngmultgt . 


Lemma islrinvrngmultgttoisinvrngmultgt ( X : rng ) { R : hrel X } ( isl : forall a b c : X , R c 0 -> R ( c * a ) ( c * b ) -> R a b ) ( isr : forall a b c : X , R c 0 -> R ( a * c ) ( b * c ) -> R a b ) : isinvrngmultgt X R . 
Proof . intros . split . 

intros a b rab ra . rewrite ( pathsinv0 ( rngmultx0 X a ) ) in rab . apply ( isl _ _ _ ra rab ) .  
intros a b rab rb . rewrite ( pathsinv0 ( rngmult0x X b ) ) in rab . apply ( isr _ _ _ rb rab ) .  Defined . 

Opaque islrinvrngmultgttoisinvrngmultgt .


Lemma isinvrngmultgtaspartinvbinophrel ( X : rng ) ( R : hrel X ) ( is0 : @isbinophrel ( rngaddabgr X ) R ) : ( isinvrngmultgt X R ) <-> ( @ispartinvbinophrel ( rngmultmonoid X ) ( fun a => R a 0 ) R ) . 
Proof . intros . split .  intro ism . split .  apply ( isinvrngmultgttoislinvrngmultgt X is0 ism ) .   apply ( isinvrngmultgttoisrinvrngmultgt X is0 ism ) . intro isp . apply ( islrinvrngmultgttoisinvrngmultgt X ( pr1 isp ) ( pr2 isp ) ) . Defined .   


Lemma isinvrngmultgttoisinvrigmultgt ( X : rng ) { R : hrel X } ( is0 : @isbinophrel ( rngaddabgr X ) R ) ( is : isinvrngmultgt X R ) : isinvrigmultgt X R .
Proof . intros .  set ( rer := abmonoidrer ( rngaddabgr X ) ) . simpl in rer .   split .  

intros a b c d r rab . set ( r' := ( pr2 is0 ) _ _ (a * - d + - b * c) r ) .  clearbody r' .  simpl in r' . rewrite ( rer _ ( b * c ) _ _ ) in r' . rewrite ( pathsinv0 ( rngldistr X _ _ a ) ) in r' . rewrite ( pathsinv0 ( rngrdistr X _ _ c ) ) in r' .  rewrite ( rngrinvax1 X d ) in r' .  rewrite ( rngrinvax1 X b ) in r' . rewrite ( rngmult0x X _ ) in r' .  rewrite ( rngmultx0 X _ ) in r' .  rewrite ( rnglunax1 X ) in r' .  rewrite ( rer _ ( b * d ) _ _ ) in r' . rewrite ( pathsinv0 ( rngldistr X _ _ a ) ) in r' .  simpl in r' .   fold pr1rng in r' . rewrite ( pathsinv0 ( rngmultminusminus X b d ) ) in r' . rewrite ( pathsinv0 ( rngldistr X _ _ ( - b ) ) ) in r' . rewrite ( rngcomm1 X _ c ) in r' . rewrite ( pathsinv0 ( rngrdistr X _ _ _ ) ) in r'. set ( rab' := ( pr2 is0 ) _ _ ( - b ) rab ) . clearbody rab'.  simpl in rab' .  rewrite ( rngrinvax1 X b ) in rab' . set ( rcd' := ( pr1 is ) _ _ r' rab' ) . set ( rcd'' := ( pr2 is0 ) _ _ d rcd' ) .     simpl in rcd'' .  rewrite ( rngassoc1 _ _ _ ) in rcd''. rewrite ( rnglinvax1 X _ ) in rcd'' . rewrite ( rnglunax1 X _ ) in rcd''.  rewrite ( rngrunax1 X _ ) in rcd'' .  apply rcd''. 

intros a b c d r rcd . set ( r' := ( pr2 is0 ) _ _ (a * - d + - b * c) r ) .  clearbody r' .  simpl in r' . rewrite ( rer _ ( b * c ) _ _ ) in r' . rewrite ( pathsinv0 ( rngldistr X _ _ a ) ) in r' . rewrite ( pathsinv0 ( rngrdistr X _ _ c ) ) in r' .  rewrite ( rngrinvax1 X d ) in r' .  rewrite ( rngrinvax1 X b ) in r' . rewrite ( rngmult0x X _ ) in r' .  rewrite ( rngmultx0 X _ ) in r' .  rewrite ( rnglunax1 X ) in r' .  rewrite ( rer _ ( b * d ) _ _ ) in r' . rewrite ( pathsinv0 ( rngldistr X _ _ a ) ) in r' .  simpl in r' .   fold pr1rng in r' . rewrite ( pathsinv0 ( rngmultminusminus X b d ) ) in r' . rewrite ( pathsinv0 ( rngldistr X _ _ ( - b ) ) ) in r' . rewrite ( rngcomm1 X _ c ) in r' . rewrite ( pathsinv0 ( rngrdistr X _ _ _ ) ) in r'. set ( rcd' := ( pr2 is0 ) _ _ ( - d ) rcd ) . clearbody rcd'.  simpl in rcd' .  rewrite ( rngrinvax1 X d ) in rcd' . set ( rab' := ( pr2 is ) _ _ r' rcd' ) . set ( rab'' := ( pr2 is0 ) _ _ b rab' ) .     simpl in rab'' .  rewrite ( rngassoc1 _ _ _ ) in rab''. rewrite ( rnglinvax1 X _ ) in rab'' . rewrite ( rnglunax1 X _ ) in rab''.  rewrite ( rngrunax1 X _ ) in rab'' .  apply rab''. Defined . 

Opaque isinvrngmultgttoisinvrigmultgt .


(** **** Relations on rings and ring homomorphisms *)

Lemma rngaddhrelandfun { X Y : rng } ( f : rngfun X Y ) ( R : hrel Y ) ( isr :  @isbinophrel ( rngaddabgr Y ) R ) :  @isbinophrel ( rngaddabgr X ) ( fun x x' => R ( f x ) ( f x' ) ) .
Proof . intros . apply ( binophrelandfun ( rngaddfun f ) R isr ) .   Defined . 

Lemma rngmultgtandfun { X Y : rng } ( f : rngfun X Y ) ( R : hrel Y ) ( isr : isrngmultgt Y R ) : isrngmultgt X ( fun x x' => R ( f x ) ( f x' ) ) .
Proof . intros . intros a b ra rb . assert ( ax0 := ( pr2 ( pr1 ( pr2 f ) ) ) : paths ( f 0 ) 0 ) .  assert ( ax1 := ( pr1 ( pr2 ( pr2 f ) ) ) : forall a b , paths ( f ( a * b ) ) ( ( f a ) * ( f b ) ) ) . rewrite ax0 in ra . rewrite ax0 in rb . rewrite ax0 . rewrite ( ax1 _ _  ) .  apply ( isr _ _ ra rb ) . Defined .  

Lemma rnginvmultgtandfun { X Y : rng } ( f : rngfun X Y ) ( R : hrel Y ) ( isr : isinvrngmultgt Y R ) : isinvrngmultgt X ( fun x x' => R ( f x ) ( f x' ) ) .
Proof . intros . assert ( ax0 := ( pr2 ( pr1 ( pr2 f ) ) ) : paths ( f 0 ) 0 ) .  assert ( ax1 := ( pr1 ( pr2 ( pr2 f ) ) ) : forall a b , paths ( f ( a * b ) ) ( ( f a ) * ( f b ) ) ) . split . 
intros a b rab ra . rewrite ax0 in ra . rewrite ax0 in rab . rewrite ax0 . rewrite ( ax1 _ _  ) in rab .  apply ( ( pr1 isr ) _ _ rab ra ) . 

intros a b rab rb . rewrite ax0 in rb . rewrite ax0 in rab . rewrite ax0 . rewrite ( ax1 _ _  ) in rab .  apply ( ( pr2 isr ) _ _ rab rb ) . Defined .  



Close Scope rng_scope . 
 

(** **** Subobjects *)

Definition issubrng { X : rng } ( A : hsubtypes X ) := dirprod ( @issubgr ( rngaddabgr X ) A ) ( @issubmonoid ( rngmultmonoid X ) A ) . 

Lemma isapropissubrng { X : rng } ( A : hsubtypes X ) : isaprop ( issubrng A ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropissubgr . apply isapropissubmonoid . Defined . 

Definition subrngs ( X : rng ) := total2 ( fun  A : hsubtypes X => issubrng A ) .
Definition subrngpair { X : rng } := tpair ( fun  A : hsubtypes X => issubrng A ) .
Definition pr1subrng ( X : rng ) : @subrngs X -> hsubtypes X := @pr1 _ (fun  A : hsubtypes X => issubrng A ) .

Definition subrngtosubsetswith2binop ( X : rng ) : subrngs X -> @subsetswith2binop X := fun A : _ => subsetswith2binoppair ( pr1 A ) ( dirprodpair ( pr1 ( pr1 ( pr1 ( pr2 A ) ) ) ) ( pr1 ( pr2 ( pr2 A ) ) ) ) . 
Coercion subrngtosubsetswith2binop : subrngs >-> subsetswith2binop . 

Definition addsubgr { X : rng } : subrngs X -> @subgrs ( rngaddabgr X ) := fun A : _ => @subgrpair ( rngaddabgr X ) ( pr1 A ) ( pr1 ( pr2 A ) ) .
Definition multsubmonoid { X : rng } : subrngs X -> @submonoids ( rngmultmonoid X ) := fun A : _ => @submonoidpair ( rngmultmonoid X ) ( pr1 A ) ( pr2 ( pr2 A ) ) .  

Lemma isrngcarrier { X : rng } ( A : subrngs X ) : isrngops ( @op1 A ) ( @op2 A ) .
Proof . intros . split with ( dirprodpair ( isabgrcarrier ( addsubgr A ) ) ( ismonoidcarrier ( multsubmonoid A ) ) ) . split .    

intros a b c . apply ( invmaponpathsincl _ ( isinclpr1carrier A ) ) .  simpl . apply rngldistr .  
intros a b c . apply ( invmaponpathsincl _ ( isinclpr1carrier A ) ) .  simpl . apply rngrdistr . Defined .   

Definition carrierofasubrng ( X : rng ) ( A : subrngs X ) : rng .
Proof . intros . split with A . apply isrngcarrier .  Defined . 

Coercion carrierofasubrng : subrngs >-> rng .  



(** **** Quotient objects *)

Definition rngeqrel { X : rng } := @twobinopeqrel X .
Identity Coercion id_rngeqrel : rngeqrel >-> twobinopeqrel .

Definition rngaddabgreqrel { X : rng } ( R : @rngeqrel X ) : @binopeqrel ( rngaddabgr X ) := @binopeqrelpair ( rngaddabgr X ) ( pr1 R ) ( pr1 ( pr2 R ) ) .     

Definition rngmultmonoideqrel { X : rng } ( R : @rngeqrel X ) : @binopeqrel ( rngmultmonoid X ) := @binopeqrelpair ( rngmultmonoid X ) ( pr1 R ) ( pr2 ( pr2 R ) ) .

Lemma isrngquot { X : rng } ( R : @rngeqrel X ) : isrngops ( @op1 ( setwith2binopquot R ) ) ( @op2 ( setwith2binopquot R ) ) . 
Proof . intros . split with ( dirprodpair ( isabgrquot ( rngaddabgreqrel R ) ) ( ismonoidquot ( rngmultmonoideqrel R ) ) ) .  simpl . set ( opp1 := @op1 ( setwith2binopquot R ) ) . set ( opp2 := @op2 ( setwith2binopquot R ) ) .  split .   

unfold isldistr . apply  ( setquotuniv3prop R ( fun x x' x''  => hProppair _ ( setproperty ( setwith2binopquot R ) ( opp2  x'' ( opp1 x x' ) ) ( opp1 ( opp2 x'' x ) ( opp2 x'' x' ) ) ) ) ) .  intros x x' x'' .   apply ( maponpaths ( setquotpr R ) ( rngldistr X x x' x'' ) ) .  

unfold isrdistr . apply  ( setquotuniv3prop R ( fun x x' x''  => hProppair _ ( setproperty ( setwith2binopquot R ) ( opp2  ( opp1 x x' ) x''  ) ( opp1 ( opp2 x x'' ) ( opp2 x' x'' ) ) ) ) ) .  intros x x' x'' .   apply ( maponpaths ( setquotpr R ) ( rngrdistr X x x' x'' ) ) .  Defined .

Definition rngquot { X : rng } ( R : @rngeqrel X ) : rng := @rngpair ( setwith2binopquot R ) ( isrngquot R ) .   



(** **** Direct products *)

Lemma isrngdirprod ( X Y : rng ) : isrngops ( @op1 ( setwith2binopdirprod X Y ) ) ( @op2 ( setwith2binopdirprod X Y ) ) .
Proof . intros . split with ( dirprodpair ( isabgrdirprod ( rngaddabgr X ) ( rngaddabgr Y ) ) ( ismonoiddirprod ( rngmultmonoid X ) ( rngmultmonoid Y ) ) ) . simpl .  split . 

intros xy xy' xy'' . unfold setwith2binopdirprod . unfold op1 . unfold op2 .  simpl . apply pathsdirprod .  apply ( rngldistr X ) .  apply ( rngldistr Y ) . 
intros xy xy' xy'' . unfold setwith2binopdirprod . unfold op1 . unfold op2 .  simpl . apply pathsdirprod .  apply ( rngrdistr X ) .  apply ( rngrdistr Y ) .  Defined . 


Definition rngdirprod ( X Y : rng ) := @rngpair ( setwith2binopdirprod X Y ) ( isrngdirprod X Y ) . 




(** **** Ring of differences associated with a rig *)

Open Scope rig_scope . 

Definition rigtorngaddabgr ( X : rig ) : abgr := abgrfrac ( rigaddabmonoid X ) . 

Definition rigtorngcarrier ( X : rig ) : hSet := pr1 ( pr1 ( rigtorngaddabgr X ) ) . 

Definition rigtorngop1int ( X : rig ) : binop ( dirprod X X ) := fun x x' => dirprodpair ( ( pr1 x ) + ( pr1 x' ) ) ( ( pr2 x ) + ( pr2 x' ) ) .

Definition rigtorngop1 ( X : rig ) :  binop ( rigtorngcarrier X ) := @op ( rigtorngaddabgr X ) . 

Definition rigtorngop1axs ( X : rig ) : isabgrop ( rigtorngop1 X ) := pr2 ( rigtorngaddabgr X ) . 

Definition rigtorngunel1 ( X : rig ) : rigtorngcarrier X := unel ( rigtorngaddabgr X ) . 

Definition eqrelrigtorng (  X : rig ) : eqrel ( dirprod X X ) := eqrelabgrfrac ( rigaddabmonoid X ) .

Definition rigtorngop2int (  X : rig ) : binop ( dirprod X X ) := fun xx xx' : dirprod X X => dirprodpair ( pr1 xx * pr1 xx' + pr2 xx * pr2 xx' ) ( pr1 xx * pr2 xx' + pr2 xx * pr1 xx' ) . 

Definition rigtorngunel2int ( X : rig ) : dirprod X X := dirprodpair 1 0 . 

Lemma rigtorngop2comp ( X : rig ) : iscomprelrelfun2 ( eqrelrigtorng X ) ( eqrelrigtorng X ) ( rigtorngop2int X ) .
Proof . intros . apply iscomprelrelfun2if .  intros xx xx' aa .  simpl .  apply @hinhfun .  intro tt1 . destruct tt1 as [ x0 e ] .  split with ( x0 * pr2 aa + x0 * pr1 aa ) . set ( rd := rigrdistr X ) . set ( cm1 := rigcomm1 X ) . set ( as1 := rigassoc1 X ) . set ( rr := abmonoidoprer ( rigop1axs X ) ) .  

rewrite ( cm1 ( pr1 xx * pr1 aa ) ( pr2 xx  * pr2 aa ) ) .  rewrite ( rr _ (  pr1 xx * pr1 aa ) (pr1 xx' * pr2 aa) _ ) . rewrite ( cm1 (pr2 xx * pr2 aa ) ( pr1 xx' * pr2 aa ) ) .  destruct ( rd ( pr1 xx ) ( pr2 xx' ) (pr1 aa ) ) . destruct ( rd ( pr1 xx' ) ( pr2 xx ) ( pr2 aa ) ) . rewrite ( rr ( (pr1 xx' + pr2 xx) * pr2 aa ) ( (pr1 xx + pr2 xx') * pr1 aa ) ( x0 * pr2 aa ) ( x0 * pr1 aa ) ) .  destruct ( rd (pr1 xx' + pr2 xx) x0 ( pr2 aa ) ) . destruct ( rd (pr1 xx + pr2 xx') x0 ( pr1 aa ) ) . 

rewrite ( cm1 ( pr1 xx' * pr1 aa ) ( pr2 xx'  * pr2 aa ) ) .  rewrite ( rr _ (  pr1 xx' * pr1 aa ) (pr1 xx * pr2 aa) _ ) . rewrite ( cm1 (pr2 xx' * pr2 aa ) ( pr1 xx * pr2 aa ) ) .  destruct ( rd ( pr1 xx' ) ( pr2 xx ) (pr1 aa ) ) . destruct ( rd ( pr1 xx ) ( pr2 xx' ) ( pr2 aa ) ) . rewrite ( rr ( (pr1 xx + pr2 xx') * pr2 aa ) ( (pr1 xx' + pr2 xx) * pr1 aa ) ( x0 * pr2 aa ) ( x0 * pr1 aa ) ) . destruct ( rd (pr1 xx + pr2 xx' ) x0 ( pr2 aa ) ) . destruct ( rd (pr1 xx' + pr2 xx) x0 ( pr1 aa ) ) . destruct e .  apply idpath . 

intros aa xx xx' .  simpl .  apply @hinhfun .  intro tt1 . destruct tt1 as [ x0 e ] .  split with ( pr1 aa * x0 + pr2 aa * x0 ) . set ( ld := rigldistr X ) . set ( cm1 := rigcomm1 X ) . set ( as1 := rigassoc1 X ) . set ( rr := abmonoidoprer ( rigop1axs X ) ) .

rewrite ( rr _ ( pr2 aa * pr2 xx ) (pr1 aa * pr2 xx' ) _ ) . destruct ( ld ( pr1 xx ) ( pr2 xx' ) ( pr1 aa ) ) . destruct ( ld ( pr2 xx ) ( pr1 xx' ) ( pr2 aa ) ) . rewrite ( rr _ ( pr2 aa * (pr2 xx + pr1 xx') ) ( pr1 aa * x0 ) _ ) .  destruct ( ld (pr1 xx + pr2 xx') x0 ( pr1 aa ) ) .  destruct ( ld (pr2 xx + pr1 xx') x0 ( pr2 aa ) ) . 

rewrite ( rr _ ( pr2 aa * pr2 xx' ) (pr1 aa * pr2 xx ) _ ) . destruct ( ld ( pr1 xx' ) ( pr2 xx ) ( pr1 aa ) ) . destruct ( ld ( pr2 xx' ) ( pr1 xx ) ( pr2 aa ) ) . rewrite ( rr _ ( pr2 aa * (pr2 xx' + pr1 xx) ) ( pr1 aa * x0 ) _ ) .  destruct ( ld (pr1 xx' + pr2 xx) x0 ( pr1 aa ) ) .  destruct ( ld (pr2 xx' + pr1 xx) x0 ( pr2 aa ) ) .  rewrite ( cm1 ( pr2 xx ) ( pr1 xx' ) ) .  rewrite ( cm1 ( pr2 xx' ) ( pr1 xx ) ) . destruct e . apply idpath . Defined .  


Opaque rigtorngop2comp .

Definition rigtorngop2 ( X : rig ) : binop ( rigtorngcarrier X ) := setquotfun2 ( eqrelrigtorng X ) ( eqrelrigtorng X ) ( rigtorngop2int X ) ( rigtorngop2comp X ) . 

Lemma rigtorngassoc2 ( X : rig ) : isassoc ( rigtorngop2 X ) .
Proof . intro . unfold isassoc .  apply ( setquotuniv3prop ( eqrelrigtorng X ) ( fun x x' x'' : rigtorngcarrier X, eqset (rigtorngop2 X (rigtorngop2 X x x') x'') (rigtorngop2 X x (rigtorngop2 X x' x'')) ) ) . intros x x' x'' . change ( paths ( setquotpr (eqrelrigtorng X)  ( rigtorngop2int X ( rigtorngop2int X x x' ) x'' ) ) ( setquotpr (eqrelrigtorng X)  ( rigtorngop2int X x ( rigtorngop2int X x' x'' ) ) ) ) . 
apply ( maponpaths ( setquotpr ( eqrelrigtorng X ) ) ) . unfold rigtorngop2int . simpl .  set ( rd := rigrdistr X ) . set ( ld := rigldistr X ) . set ( cm1 := rigcomm1 X ) .  set ( as1 := rigassoc1 X ) . set ( as2 := rigassoc2 X ) . set ( rr := abmonoidoprer ( rigop1axs X ) ) .  apply pathsdirprod .  

rewrite ( rd _ _ ( pr1 x'' ) ) . rewrite ( rd _ _ ( pr2 x'' ) ) . rewrite ( ld _ _ ( pr1 x ) ) . rewrite ( ld _ _ ( pr2 x ) ) . destruct ( as2 ( pr1 x ) ( pr1 x' ) ( pr1 x'' ) ) . destruct ( as2 ( pr1 x ) ( pr2 x' ) ( pr2 x'' ) ) .   destruct ( as2 ( pr2 x ) ( pr1 x' ) ( pr2 x'' ) ) . destruct ( as2 ( pr2 x ) ( pr2 x' ) ( pr1 x'' ) ) . destruct ( cm1 ( pr2 x * pr2 x' * pr1 x'' ) ( pr2 x * pr1 x' * pr2 x'' ) ) . rewrite ( rr _ ( pr2 x * pr2 x' * pr1 x'' ) (pr1 x * pr2 x' * pr2 x'' ) _ ) .  apply idpath . 

rewrite ( rd _ _ ( pr1 x'' ) ) . rewrite ( rd _ _ ( pr2 x'' ) ) . rewrite ( ld _ _ ( pr1 x ) ) . rewrite ( ld _ _ ( pr2 x ) ) . destruct ( as2 ( pr1 x ) ( pr1 x' ) ( pr2 x'' ) ) . destruct ( as2 ( pr1 x ) ( pr2 x' ) ( pr1 x'' ) ) .   destruct ( as2 ( pr2 x ) ( pr1 x' ) ( pr1 x'' ) ) . destruct ( as2 ( pr2 x ) ( pr2 x' ) ( pr2 x'' ) ) . destruct ( cm1 ( pr2 x * pr2 x' * pr2 x'' ) ( pr2 x * pr1 x' * pr1 x'' ) ) . rewrite ( rr _ ( pr1 x * pr2 x' * pr1 x'' ) (pr2 x * pr2 x' * pr2 x'' ) _ ) .  apply idpath . Defined . 

Opaque rigtorngassoc2 .

Definition rigtorngunel2 ( X : rig ) : rigtorngcarrier X := setquotpr ( eqrelrigtorng X ) ( rigtorngunel2int X ) .   

Lemma rigtornglunit2 ( X : rig ) : islunit ( rigtorngop2 X ) ( rigtorngunel2 X ) . 
Proof . intro . unfold islunit .  apply ( setquotunivprop ( eqrelrigtorng X ) ( fun x : rigtorngcarrier X, eqset (rigtorngop2 X (rigtorngunel2 X) x) x ) ) .  intro x .  change ( paths ( setquotpr (eqrelrigtorng X ) ( rigtorngop2int X ( rigtorngunel2int X ) x ) ) ( setquotpr (eqrelrigtorng X) x ) ) . apply ( maponpaths ( setquotpr ( eqrelrigtorng X ) ) ) . unfold rigtorngop2int . simpl . destruct x as [ x1 x2 ] .  simpl . set ( lu2 := riglunax2 X ) .  set ( ru1 := rigrunax1 X ) .  set ( m0x := rigmult0x X ) . apply pathsdirprod . 

rewrite ( lu2 x1 ) . rewrite ( m0x x2 ) . apply ( ru1 x1 ) . 
rewrite ( lu2 x2 ) . rewrite ( m0x x1 ) . apply ( ru1 x2 ) .  Defined . 

Opaque rigtornglunit2 .


Lemma rigtorngrunit2 ( X : rig ) : isrunit ( rigtorngop2 X ) ( rigtorngunel2 X ) . 
Proof . intro . unfold isrunit .  apply ( setquotunivprop ( eqrelrigtorng X ) ( fun x : rigtorngcarrier X, eqset (rigtorngop2 X x (rigtorngunel2 X)) x ) ) .  intro x .  change ( paths ( setquotpr (eqrelrigtorng X ) ( rigtorngop2int X x ( rigtorngunel2int X ) ) ) ( setquotpr (eqrelrigtorng X) x ) ) . apply ( maponpaths ( setquotpr ( eqrelrigtorng X ) ) ) . unfold rigtorngop2int . simpl . destruct x as [ x1 x2 ] .  simpl . set ( ru2 := rigrunax2 X ) .  set ( ru1 := rigrunax1 X ) .  set ( lu1 := riglunax1 X ) . set ( mx0 := rigmultx0 X ) . apply pathsdirprod . 

rewrite ( ru2 x1 ) . rewrite ( mx0 x2 ) . apply ( ru1 x1 ) . 
rewrite ( ru2 x2 ) . rewrite ( mx0 x1 ) . apply ( lu1 x2 ) .  Defined . 

Opaque rigtorngrunit2 .

Definition rigtorngisunit ( X : rig ) : isunit  ( rigtorngop2 X ) ( rigtorngunel2 X ) := dirprodpair ( rigtornglunit2 X ) ( rigtorngrunit2 X ) . 

Definition rigtorngisunital ( X : rig ) : isunital ( rigtorngop2 X ) := tpair _ ( rigtorngunel2 X ) ( rigtorngisunit X ) .  

Definition rigtorngismonoidop2 ( X : rig ) : ismonoidop ( rigtorngop2 X ) := dirprodpair ( rigtorngassoc2 X ) ( rigtorngisunital X ) . 

Lemma rigtorngldistr ( X : rig ) : isldistr ( rigtorngop1 X ) ( rigtorngop2 X ) . 
Proof . intro . unfold isldistr .  apply ( setquotuniv3prop ( eqrelrigtorng X ) ( fun x x' x'' : rigtorngcarrier X, eqset (rigtorngop2 X x'' (rigtorngop1 X x x')) (rigtorngop1 X (rigtorngop2 X x'' x) (rigtorngop2 X x'' x')) ) ) . intros x x' x'' . change ( paths ( setquotpr (eqrelrigtorng X ) ( rigtorngop2int X x'' ( rigtorngop1int X x x' ) ) ) ( setquotpr (eqrelrigtorng X ) ( rigtorngop1int X ( rigtorngop2int X x'' x ) ( rigtorngop2int X x'' x' ) ) ) ) . apply ( maponpaths ( setquotpr ( eqrelrigtorng X ) ) ) .  unfold rigtorngop1int . unfold rigtorngop2int . simpl . set ( ld := rigldistr X ) .  set ( cm1 := rigcomm1 X ) . set ( rr := abmonoidoprer ( rigop1axs X ) ) .   apply pathsdirprod .  

rewrite ( ld _ _ ( pr1 x'' ) ) . rewrite ( ld _ _ ( pr2 x'' ) ) . apply ( rr _ ( pr1 x'' * pr1 x' ) (pr2 x'' * pr2 x ) _ ) . 
rewrite ( ld _ _ ( pr1 x'' ) ) . rewrite ( ld _ _ ( pr2 x'' ) ) . apply ( rr _ (pr1 x'' * pr2 x' ) ( pr2 x'' * pr1 x ) _ ) . Defined . 

Opaque rigtorngldistr . 


Lemma rigtorngrdistr ( X : rig ) : isrdistr ( rigtorngop1 X ) ( rigtorngop2 X ) . 
Proof . intro . unfold isrdistr .  apply ( setquotuniv3prop ( eqrelrigtorng X ) ( fun x x' x'' : rigtorngcarrier X, eqset (rigtorngop2 X (rigtorngop1 X x x') x'' ) (rigtorngop1 X (rigtorngop2 X x x'' ) (rigtorngop2 X x' x'' )) ) ) . intros x x' x'' . change ( paths ( setquotpr (eqrelrigtorng X ) ( rigtorngop2int X ( rigtorngop1int X x x' ) x'' ) ) ( setquotpr (eqrelrigtorng X ) ( rigtorngop1int X ( rigtorngop2int X x x'' ) ( rigtorngop2int X x' x'' ) ) ) ) . apply ( maponpaths ( setquotpr ( eqrelrigtorng X ) ) ) .  unfold rigtorngop1int . unfold rigtorngop2int . simpl . set ( rd := rigrdistr X ) .  set ( cm1 := rigcomm1 X ) . set ( rr := abmonoidoprer ( rigop1axs X ) ) .   apply pathsdirprod .  

rewrite ( rd _ _ ( pr1 x'' ) ) . rewrite ( rd _ _ ( pr2 x'' ) ) . apply ( rr _ ( pr1 x' * pr1 x'' ) (pr2 x * pr2 x'' ) _ ) . 
rewrite ( rd _ _ ( pr1 x'' ) ) . rewrite ( rd _ _ ( pr2 x'' ) ) . apply ( rr _ (pr1 x' * pr2 x'' ) ( pr2 x * pr1 x'' ) _ ) . Defined . 

Opaque rigtorngrdistr . 

Definition rigtorngdistr ( X : rig ) : isdistr  ( rigtorngop1 X ) ( rigtorngop2 X )  := dirprodpair ( rigtorngldistr X ) ( rigtorngrdistr X ) .

Definition rigtorng ( X : rig ) : rng .
Proof . intro . split with ( @setwith2binoppair ( rigtorngcarrier X ) ( dirprodpair ( rigtorngop1 X ) ( rigtorngop2 X ) ) ) . split . apply ( dirprodpair ( rigtorngop1axs X ) ( rigtorngismonoidop2 X ) ) . apply ( rigtorngdistr X ) .  Defined . 


(** **** Canonical homomorphism to the ring associated with a rig (ring of differences) *)

Definition torngdiff ( X : rig ) ( x : X ) : rigtorng X := setquotpr _ ( dirprodpair x 0 ) .

Lemma isbinop1funtorngdiff ( X : rig ) : @isbinopfun ( rigaddabmonoid X ) ( rngaddabgr ( rigtorng X ) ) ( torngdiff X ) . 
Proof . intros . unfold isbinopfun . intros x x' .  apply ( isbinopfuntoabgrfrac ( rigaddabmonoid X ) x x' ) . Defined . 

Opaque isbinop1funtorngdiff .

Lemma isunital1funtorngdiff ( X : rig ) : paths ( torngdiff X 0 ) 0%rng .
Proof . intro. apply idpath . Defined .

Opaque isunital1funtorngdiff .  

Definition isaddmonoidfuntorngdiff ( X : rig ) : @ismonoidfun  ( rigaddabmonoid X ) ( rngaddabgr ( rigtorng X ) ) ( torngdiff X ) := dirprodpair ( isbinop1funtorngdiff X ) ( isunital1funtorngdiff X ) . 

Lemma isbinop2funtorngdiff  ( X : rig ) : @isbinopfun ( rigmultmonoid X ) ( rngmultmonoid ( rigtorng X ) ) ( torngdiff X ) . 
Proof . intros . unfold isbinopfun . intros x x' . change ( paths ( setquotpr _  ( dirprodpair ( x * x' ) 0 ) ) ( setquotpr (eqrelrigtorng X ) ( rigtorngop2int X ( dirprodpair x 0 ) ( dirprodpair x' 0 ) ) ) ) . apply ( maponpaths ( setquotpr _ ) ) . unfold rigtorngop2int .  simpl .  apply pathsdirprod . 

rewrite ( rigmultx0 X _ ) .  rewrite  ( rigrunax1 X _ ) . apply idpath .  

rewrite ( rigmult0x X _ ) . rewrite ( rigmultx0 X _ ) .  rewrite ( rigrunax1 X _ ) . apply idpath . Defined . 

Lemma isunital2funtorngdiff  ( X : rig ) : paths ( torngdiff X 1 ) 1%rng .
Proof . intro. apply idpath . Defined .

Opaque isunital2funtorngdiff .   

Definition ismultmonoidfuntorngdiff  ( X : rig ) : @ismonoidfun  ( rigmultmonoid X ) ( rngmultmonoid ( rigtorng X ) ) ( torngdiff X ) := dirprodpair ( isbinop2funtorngdiff X ) ( isunital2funtorngdiff X ) . 

Definition isrigfuntorngdiff ( X : rig ) : @isrigfun X ( rigtorng X ) ( torngdiff X ) := dirprodpair ( isaddmonoidfuntorngdiff X ) ( ismultmonoidfuntorngdiff X ) .

Definition isincltorngdiff ( X : rig ) ( iscanc : forall x : X , @isrcancelable X ( @op1 X ) x ) : isincl ( torngdiff X ) := isincltoabgrfrac ( rigaddabmonoid X ) iscanc .   


(** **** Relations similar to "greater" or "greater or equal"  on the ring associated with a rig *)

Definition rigtorngrel ( X : rig ) { R : hrel X } ( is : @isbinophrel ( rigaddabmonoid X ) R ) : hrel ( rigtorng X ) := abgrfracrel ( rigaddabmonoid X ) is .

Lemma isrngrigtorngmultgt  ( X : rig ) { R : hrel X } ( is0 : @isbinophrel ( rigaddabmonoid X ) R ) ( is : isrigmultgt X R ) : isrngmultgt ( rigtorng X ) ( rigtorngrel X is0 ) .
Proof . intros . set ( assoc := rigassoc1 X ) .  set ( comm := rigcomm1 X ) .   set ( rer := ( abmonoidrer ( rigaddabmonoid X ) ) : forall a b c d : X , paths ( ( a + b ) + ( c + d ) ) ( ( a + c ) + ( b + d ) ) ) . set ( ld := rigldistr X ) . set ( rd := rigrdistr X ) .

assert ( int : forall a b , isaprop ( rigtorngrel X is0 a rngunel1 -> rigtorngrel X is0 b rngunel1 ->  rigtorngrel X is0 (a * b) rngunel1 ) ) . intros a b . apply impred . intro . apply impred .  intro . apply ( pr2 _ ) .   unfold isrngmultgt . apply ( setquotuniv2prop _ ( fun a b => hProppair _ ( int a b ) ) ) .  


intros xa1 xa2 . change ( ( abgrfracrelint ( rigaddabmonoid X ) R ) xa1 ( dirprodpair ( @rigunel1 X ) ( @rigunel1 X ) ) -> ( abgrfracrelint ( rigaddabmonoid X ) R ) xa2 ( dirprodpair ( @rigunel1 X ) ( @rigunel1 X ) ) -> ( abgrfracrelint ( rigaddabmonoid X ) R ( @rigtorngop2int X xa1 xa2 ) ( dirprodpair ( @rigunel1 X ) ( @rigunel1 X ) ) ) ) .  unfold abgrfracrelint . simpl . apply hinhfun2 . intros t22 t21 .   set ( c2 := pr1 t21 ) . set ( c1 := pr1 t22 ) . set ( r1 := pr2 t21 ) . set ( r2 := pr2 t22 ) . set ( x1 := pr1 xa1 ) . set ( a1 := pr2 xa1 ) .  set ( x2 := pr1 xa2 ) . set ( a2 := pr2 xa2 ) . split with ( ( x1 * c2 + a1 * c2 ) + ( ( c1 * x2 + c1 * c2 ) + ( c1 * a2 + c1 * c2 ) ) ) . change ( pr1 ( R ( x1 * x2 + a1 * a2 + 0 + ( ( x1 * c2 + a1 * c2 ) + ( ( c1 * x2 + c1 * c2 ) + ( c1 * a2 + c1 * c2 ) ) ) )  ( 0 + ( x1 * a2 + a1 * x2 ) + ( x1 * c2 + a1 * c2 +  ( ( c1 * x2 + c1 * c2 ) + ( c1 * a2 + c1 * c2 ) ) ) ) ) ) . rewrite ( riglunax1 X _ ) .  rewrite ( rigrunax1 X _ ) .   rewrite ( assoc ( x1 * c2 ) _ _ ) .  rewrite ( rer _ ( a1 * a2 ) _ _ ) .  rewrite ( rer _ ( a1 * x2 ) _ _ ) . rewrite ( pathsinv0 ( assoc ( a1 * a2 ) _ _  ) ) . rewrite ( pathsinv0 ( assoc ( a1 * x2 ) _ _  ) ) . rewrite ( pathsinv0 ( assoc ( x1 * x2 + _ ) _ _ ) ) . rewrite ( pathsinv0 ( assoc ( x1 * a2 + _ ) _ _ ) ) .  rewrite ( rer _ ( a1 * a2 + _ ) _ _ ) .  rewrite ( rer _ ( a1 * x2 + _ ) _ _ ) .  rewrite ( pathsinv0 ( ld _ _ x1 ) ) . rewrite ( pathsinv0 ( ld _ _ x1 ) ) . rewrite ( pathsinv0 ( ld _ _ c1 ) ) . rewrite ( pathsinv0 ( ld _ _ c1 ) ) . rewrite ( pathsinv0 ( ld _ _ a1 ) ) .  rewrite ( pathsinv0 ( ld _ _ a1 ) ) .  rewrite ( pathsinv0 ( rd _ _ ( x2 + c2 ) ) ) .  rewrite ( pathsinv0 ( rd _ _ ( a2 + c2 ) ) ) . rewrite ( comm ( a1 * _ ) _ ) .  rewrite ( rer _ ( c1 * _ ) _ _ ) . rewrite ( pathsinv0 ( rd _ _ ( x2 + c2 ) ) ) .  rewrite ( pathsinv0 ( rd _ _ ( a2 + c2 ) ) ) .  clearbody r1 . clearbody r2 . change ( pr1 ( R ( x2 + 0 + c2 ) ( 0 + a2 + c2 ) ) ) in r1 . change ( pr1 ( R ( x1 + 0 + c1 ) ( 0 + a1 + c1 ) ) ) in r2 .  rewrite ( rigrunax1 X _ ) in r1 .   rewrite ( riglunax1 X _ ) in r1 .   rewrite ( rigrunax1 X _ ) in r2 .   rewrite ( riglunax1 X _ ) in r2 . rewrite ( comm c1 a1 ) . apply ( is _ _ _ _ r2 r1 ) .   Defined . 
 
Opaque isrngrigtorngmultgt . 

Definition isdecrigtorngrel ( X : rig ) { R : hrel X } ( is : @isbinophrel ( rigaddabmonoid X ) R ) ( is' : @isinvbinophrel ( rigaddabmonoid X ) R )  ( isd : isdecrel R ) : isdecrel ( rigtorngrel X is ) .
Proof . intros . apply ( isdecabgrfracrel ( rigaddabmonoid X ) is is' isd ) . Defined . 


Lemma isinvrngrigtorngmultgt ( X : rig ) { R : hrel X } ( is0 : @isbinophrel ( rigaddabmonoid X ) R ) ( is1 : @isinvbinophrel ( rigaddabmonoid X ) R ) ( is : isinvrigmultgt X R ) : isinvrngmultgt ( rigtorng X ) ( rigtorngrel X is0 ) .
Proof . intros .  split .  

assert ( int : forall a b , isaprop ( rigtorngrel X is0 (a * b) rngunel1 -> rigtorngrel X is0 a rngunel1 -> rigtorngrel X is0 b rngunel1 ) ) . intros . apply impred . intro . apply impred . intro . apply ( pr2 _ ) .  apply (  setquotuniv2prop _ ( fun a b => hProppair _ ( int a b ) ) ) . 

intros xa1 xa2 . change ( ( abgrfracrelint ( rigaddabmonoid X ) R ( @rigtorngop2int X xa1 xa2 ) ( dirprodpair ( @rigunel1 X ) ( @rigunel1 X ) ) ) -> ( abgrfracrelint ( rigaddabmonoid X ) R ) xa1 ( dirprodpair ( @rigunel1 X ) ( @rigunel1 X ) ) -> ( abgrfracrelint ( rigaddabmonoid X ) R ) xa2 ( dirprodpair ( @rigunel1 X ) ( @rigunel1 X ) ) ) .   unfold abgrfracrelint . simpl . apply hinhfun2 . intros t22 t21 .   set ( c2 := pr1 t22 ) . set ( c1 := pr1 t21 ) . set ( r1 := pr2 t21 ) . set ( r2 := pr2 t22 ) . set ( x1 := pr1 xa1 ) . set ( a1 := pr2 xa1 ) .  set ( x2 := pr1 xa2 ) . set ( a2 := pr2 xa2 ) . simpl in r2 . clearbody r2 .  change ( pr1 ( R ( x1 * x2 + a1 * a2 + 0 + c2 ) ( 0 + ( x1 * a2 + a1 * x2 ) + c2 ) ) ) in r2 . rewrite ( riglunax1 X _ ) in r2 .  rewrite ( rigrunax1 X _ ) in r2 . rewrite ( rigrunax1 X _ ) . rewrite ( riglunax1 X _ ) . set ( r2' := ( pr2 is1 ) _ _ c2 r2 ) .  clearbody r1 . change ( pr1 ( R ( x1 + 0 + c1 ) ( 0 + a1 + c1 ) ) ) in r1 . rewrite ( riglunax1 X _ ) in r1 .  rewrite ( rigrunax1 X _ ) in r1  .   set ( r1' := ( pr2 is1 ) _ _ c1 r1 ) . split with 0 .  rewrite ( rigrunax1 X _ ) .  rewrite ( rigrunax1 X _ ) .  apply ( ( pr1 is ) _ _ _ _ r2' r1' ) . 

assert ( int : forall a b , isaprop ( rigtorngrel X is0 (a * b) rngunel1 -> rigtorngrel X is0 b rngunel1  -> rigtorngrel X is0 a rngunel1 ) ) . intros . apply impred . intro . apply impred . intro . apply ( pr2 _ ) .  apply (  setquotuniv2prop _ ( fun a b => hProppair _ ( int a b ) ) ) . 

intros xa1 xa2 . change ( ( abgrfracrelint ( rigaddabmonoid X ) R ( @rigtorngop2int X xa1 xa2 ) ( dirprodpair ( @rigunel1 X ) ( @rigunel1 X ) ) ) -> ( abgrfracrelint ( rigaddabmonoid X ) R ) xa2 ( dirprodpair ( @rigunel1 X ) ( @rigunel1 X ) ) -> ( abgrfracrelint ( rigaddabmonoid X ) R ) xa1 ( dirprodpair ( @rigunel1 X ) ( @rigunel1 X ) ) ) .   unfold abgrfracrelint . simpl . apply hinhfun2 . intros t22 t21 .   set ( c2 := pr1 t22 ) . set ( c1 := pr1 t21 ) . set ( r1 := pr2 t21 ) . set ( r2 := pr2 t22 ) . set ( x1 := pr1 xa1 ) . set ( a1 := pr2 xa1 ) .  set ( x2 := pr1 xa2 ) . set ( a2 := pr2 xa2 ) . simpl in r2 . clearbody r2 .  change ( pr1 ( R ( x1 * x2 + a1 * a2 + 0 + c2 ) ( 0 + ( x1 * a2 + a1 * x2 ) + c2 ) ) ) in r2 . rewrite ( riglunax1 X _ ) in r2 .  rewrite ( rigrunax1 X _ ) in r2 . rewrite ( rigrunax1 X _ ) . rewrite ( riglunax1 X _ ) . set ( r2' := ( pr2 is1 ) _ _ c2 r2 ) .  clearbody r1 . change ( pr1 ( R ( x2 + 0 + c1 ) ( 0 + a2 + c1 ) ) ) in r1 . rewrite ( riglunax1 X _ ) in r1 .  rewrite ( rigrunax1 X _ ) in r1  .   set ( r1' := ( pr2 is1 ) _ _ c1 r1 ) . split with 0 .  rewrite ( rigrunax1 X _ ) .  rewrite ( rigrunax1 X _ ) .  apply ( ( pr2 is ) _ _ _ _ r2' r1' ) . Defined .

Opaque isinvrngrigtorngmultgt . 


(** **** Realations and the canonical homomorphism to the ring associated with a rig (ring of differences) *)


Definition iscomptorngdiff ( X : rig ) { L : hrel X } ( is0 : @isbinophrel ( rigaddabmonoid X ) L ) : iscomprelrelfun L ( rigtorngrel X is0 ) ( torngdiff X ) := iscomptoabgrfrac ( rigaddabmonoid X ) is0 . 

Opaque iscomptorngdiff . 

Close Scope rig_scope . 




(** *** Commutative rings *)

(** **** General definitions *)

Definition iscommrng ( X : setwith2binop ) := iscommrngops ( @op1 X ) ( @op2 X ) .

Definition commrng := total2 ( fun X : setwith2binop => iscommrngops ( @op1 X ) ( @op2 X ) ) .
Definition commrngpair ( X : setwith2binop ) ( is : iscommrngops ( @op1 X ) ( @op2 X ) ) := tpair ( fun X : setwith2binop => iscommrngops ( @op1 X ) ( @op2 X ) ) X is .

Definition commrngconstr { X : hSet } ( opp1 opp2 : binop X ) ( ax11 : isgrop opp1 ) ( ax12 : iscomm opp1 ) ( ax21 : ismonoidop opp2 ) ( ax22 : iscomm opp2 ) ( dax : isdistr opp1 opp2 ) : commrng := @commrngpair ( setwith2binoppair X ( dirprodpair opp1 opp2 ) ) ( dirprodpair ( dirprodpair ( dirprodpair ( dirprodpair ax11 ax12 ) ax21 ) dax ) ax22 ) . 

Definition commrngtorng : commrng -> rng := fun X : _ => @rngpair ( pr1 X ) ( pr1 ( pr2 X ) ) . 
Coercion commrngtorng : commrng >-> rng .

Definition rngcomm2 ( X : commrng ) : iscomm ( @op2 X ) := pr2 ( pr2 X ) . 
Definition commrngop2axs ( X : commrng ) : isabmonoidop ( @op2 X ) := tpair _ ( rngop2axs X ) ( rngcomm2 X ) . 


Definition rngmultabmonoid ( X : commrng ) : abmonoid := abmonoidpair ( setwithbinoppair X op2 ) ( dirprodpair ( rngop2axs X ) ( rngcomm2 X ) ) . 

Definition commrngtocommrig ( X : commrng ) : commrig := commrigpair _ ( pr2 X ) .
Coercion commrngtocommrig : commrng >-> commrig . 

(** **** Computational lemmas for commutative rings *)

Open Scope rng_scope.

Lemma commrngismultcancelableif ( X : commrng ) ( x : X ) ( isl : forall y , paths ( x * y ) 0 -> paths y 0 ) : iscancelable op2 x .
Proof . intros . split . apply ( rngismultlcancelableif X x isl ) .  assert ( isr : forall y , paths ( y * x ) 0 -> paths y 0 ) . intros y e . rewrite ( rngcomm2 X _ _ ) in e . apply ( isl y e ) . apply ( rngismultrcancelableif X x isr ) . Defined .  

Opaque commrngismultcancelableif .


Close Scope rng_scope. 


(** **** Subobjects *)

Lemma iscommrngcarrier { X : commrng } ( A : @subrngs X ) : iscommrngops ( @op1 A ) ( @op2 A ) .
Proof . intros . split with ( isrngcarrier A ) . apply ( pr2 ( @isabmonoidcarrier ( rngmultabmonoid X ) ( multsubmonoid A ) ) ) .  Defined . 

Definition carrierofasubcommrng { X : commrng } ( A : @subrngs X ) : commrng := commrngpair A ( iscommrngcarrier A ) . 


(** **** Quotient objects *)

Lemma iscommrngquot { X : commrng } ( R : @rngeqrel X ) : iscommrngops ( @op1 ( setwith2binopquot R ) ) ( @op2 ( setwith2binopquot R ) ) . 
Proof . intros . split with ( isrngquot R ) . apply ( pr2 ( @isabmonoidquot  ( rngmultabmonoid X ) ( rngmultmonoideqrel R ) ) ) .  Defined . 

Definition commrngquot { X : commrng } ( R : @rngeqrel X ) : commrng := commrngpair ( setwith2binopquot R ) ( iscommrngquot R ) . 




(** **** Direct products *)

Lemma iscommrngdirprod ( X Y : commrng ) : iscommrngops ( @op1 ( setwith2binopdirprod X Y ) ) ( @op2 ( setwith2binopdirprod X Y ) ) .
Proof . intros . split with ( isrngdirprod X Y ) . apply ( pr2 ( isabmonoiddirprod ( rngmultabmonoid X ) ( rngmultabmonoid Y ) ) ) . Defined . 

Definition commrngdirprod ( X Y : commrng ) := commrngpair ( setwith2binopdirprod X Y ) ( iscommrngdirprod X Y ) . 


(** **** Commutative rigs to commuttaive rings *)

Open Scope rig_scope . 

Lemma commrigtocommrngcomm2 ( X : commrig ) : iscomm ( rigtorngop2 X ) .
Proof . intro . unfold iscomm .   apply ( setquotuniv2prop ( eqrelrigtorng X ) ( fun x x' : rigtorngcarrier X, eqset (rigtorngop2 X x x' ) (rigtorngop2 X x' x ) ) ) . intros x x' . change ( paths ( setquotpr (eqrelrigtorng X)  ( rigtorngop2int X x x' ) ) ( setquotpr (eqrelrigtorng X)  ( rigtorngop2int X x' x ) ) ) . 
apply ( maponpaths ( setquotpr ( eqrelrigtorng X ) ) ) . unfold rigtorngop2int . set ( cm1 := rigcomm1 X ) . set ( cm2 := rigcomm2 X ) .  apply pathsdirprod .  

rewrite ( cm2 ( pr1 x ) ( pr1 x' ) ) . rewrite ( cm2 ( pr2 x ) ( pr2 x' ) ) .   apply idpath . 
rewrite ( cm2 ( pr1 x ) ( pr2 x' ) ) . rewrite ( cm2 ( pr2 x ) ( pr1 x' ) ) .  apply cm1 . Defined . 

Opaque commrigtocommrngcomm2 . 

Definition commrigtocommrng ( X : commrig ) : commrng .
Proof . intro . split with ( rigtorng X ) . split .   apply ( pr2 ( rigtorng X ) ) . apply ( commrigtocommrngcomm2 X ) .  Defined . 

Close Scope rig_scope . 


   

(** **** Rings of fractions *)

Open Scope rng_scope . 

Definition commrngfracop1int (  X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : binop ( dirprod X S ) := fun x1s1 x2s2 : dirprod X S =>  @dirprodpair X S ( ( ( pr1 ( pr2 x2s2 ) ) * ( pr1 x1s1 ) ) + ( ( pr1 ( pr2 x1s1 ) ) * ( pr1 x2s2 ) ) ) ( @op S ( pr2 x1s1 ) ( pr2 x2s2 ) )  .

Definition commrngfracop2int (  X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : binop ( dirprod X S ) := abmonoidfracopint ( rngmultabmonoid X ) S . 

Definition commrngfracunel1int ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : dirprod X S := dirprodpair 0 ( unel S ) .

Definition commrngfracunel2int ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : dirprod X S := dirprodpair 1 ( unel S ) . 

Definition commrngfracinv1int  ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : dirprod X S -> dirprod X S := fun xs : _ => dirprodpair ( ( -1 ) * ( pr1 xs ) ) ( pr2 xs ) .

Definition eqrelcommrngfrac (  X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : eqrel ( dirprod X S ) := eqrelabmonoidfrac ( rngmultabmonoid X ) S . 

Lemma commrngfracl1 ( X : commrng ) ( x1 x2 x3 x4 a1 a2 s1 s2 s3 s4 : X ) ( eq1 : paths ( ( x1 * s2 ) * a1 ) ( ( x2 * s1 ) * a1 ) ) ( eq2 : paths ( ( x3 * s4 ) * a2 ) ( ( x4 * s3 ) * a2 ) ) : paths ( ( ( ( s3 * x1 ) + ( s1 * x3 ) ) * ( s2 * s4 ) ) * ( a1 * a2 ) ) ( ( ( ( s4 * x2 ) + ( s2 * x4 ) ) * ( s1 * s3 ) ) * ( a1 * a2 ) ) .
Proof . intros . set ( rdistr := rngrdistr X ) . set ( assoc2 := rngassoc2 X ) . set ( op2axs := commrngop2axs X ) . set ( comm2 := rngcomm2 X ) . set ( rer := abmonoidoprer op2axs ) . 

rewrite ( rdistr ( s3 * x1 ) ( s1 * x3 )  ( s2 * s4 ) ) . rewrite ( rdistr ( s4 * x2 ) ( s2 * x4 ) ( s1 * s3 ) ) .  rewrite ( rdistr ( ( s3 * x1 ) * ( s2 * s4 ) ) ( ( s1 * x3 ) * ( s2 * s4 ) )  ( a1 * a2 ) ) . rewrite ( rdistr ( ( s4 * x2 ) * ( s1 * s3 ) ) ( ( s2 * x4 ) * ( s1 * s3 ) ) ( a1 * a2 ) ) .  clear rdistr .  

assert ( e1 : paths ( ( ( s3 * x1 ) * ( s2 * s4 ) ) * ( a1 * a2 ) ) ( ( ( s4 * x2 ) * ( s1 * s3 ) ) * ( a1 * a2 ) ) ) .  destruct ( assoc2 ( s3 * x1 ) s2 s4  ) .  rewrite ( assoc2 s3 x1 s2 ) .  rewrite ( rer ( s3 * ( x1 * s2 ) ) s4 a1 a2 ) .  rewrite ( assoc2 s3 ( x1 * s2 ) a1 ) .  destruct ( assoc2 ( s4 * x2 ) s1 s3  ) .  rewrite ( assoc2 s4 x2 s1 ) .  rewrite ( rer ( s4 * ( x2 * s1 ) ) s3 a1 a2 ) . rewrite ( assoc2 s4 ( x2 * s1 ) a1 ) . destruct eq1 .  rewrite ( comm2 s3 ( ( x1 * s2 ) * a1 ) ) . rewrite ( comm2 s4 ( ( x1 * s2 ) * a1 ) ) .  rewrite ( rer ( ( x1 * s2 ) * a1 ) s3 s4 a2 ) .  apply idpath .  

assert ( e2 : paths ( ( ( s1 * x3 ) * ( s2 * s4 ) ) * ( a1 * a2 ) ) ( ( ( s2 * x4 ) * ( s1 * s3 ) ) * ( a1 * a2 ) ) ) .  destruct ( comm2 s4 s2 ) .  destruct ( comm2 s3 s1 ) .  destruct ( comm2 a2 a1 ) . destruct ( assoc2 ( s1 * x3 ) s4 s2 ) .  destruct ( assoc2 ( s2 * x4 ) s3 s1 ) .  rewrite ( assoc2 s1 x3 s4 ) .  rewrite ( assoc2 s2 x4 s3 ) .  rewrite ( rer ( s1 * ( x3 * s4 ) ) s2 a2 a1 ) .  rewrite ( rer ( s2 * ( x4 * s3 ) ) s1 a2 a1 ) .  rewrite ( assoc2 s1 ( x3 * s4 ) a2 ) .  rewrite ( assoc2 s2 ( x4 * s3 ) a2 ) . destruct eq2 . destruct ( comm2 ( ( x3 * s4 ) * a2 ) s1 ) .  destruct ( comm2 ( ( x3 *s4 ) * a2 ) s2 ) . rewrite ( rer ( ( x3 * s4 ) * a2 ) s1 s2 a1 ) . apply idpath .  

destruct e1 . destruct e2 . apply idpath . Defined .  

Opaque commrngfracl1 .  

Lemma commrngfracop1comp ( X : commrng ) ( S :  @subabmonoids ( rngmultabmonoid X ) ) : iscomprelrelfun2 ( eqrelcommrngfrac X S ) ( eqrelcommrngfrac X S )  ( commrngfracop1int X S ) .
Proof . intros .  intros xs1 xs2 xs3 xs4 .  simpl .  set ( ff := @hinhfun2 ) .  simpl in ff . apply ff . clear ff . intros tt1 tt2 . split with ( @op S ( pr1 tt1 ) ( pr1 tt2 ) ) .  assert ( eq1 := pr2 tt1 ) .  simpl in eq1 .  assert ( eq2 := pr2 tt2 ) . simpl in eq2 . unfold pr1carrier . 
apply ( commrngfracl1 X ( pr1 xs1 ) ( pr1 xs2 ) ( pr1 xs3 ) ( pr1 xs4 ) ( pr1 ( pr1 tt1 ) ) ( pr1 ( pr1 tt2 ) ) ( pr1 ( pr2 xs1 ) )  ( pr1 ( pr2 xs2 ) ) ( pr1 ( pr2 xs3 ) ) ( pr1 ( pr2 xs4 ) ) eq1 eq2 ) . Defined . 

Opaque commrngfracop1comp .

Definition commrngfracop1 ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : binop ( setquotinset ( eqrelcommrngfrac X S ) ) := setquotfun2 ( eqrelcommrngfrac X S ) ( eqrelcommrngfrac X S ) ( commrngfracop1int X S ) ( commrngfracop1comp X S ) .

Lemma commrngfracl2 ( X : commrng ) ( x x' x'' s s' s'' : X ) : paths ( ( s'' * ( ( s' * x ) + ( s * x' ) ) ) + ( ( s * s' ) * x'' ) ) ( ( ( s' * s'' ) * x ) + ( s * ( ( s'' * x' ) + ( s' * x'' ) ) ) ) .
Proof. intros . set ( ldistr := rngldistr X ) . set ( comm2 := rngcomm2 X ) . set ( assoc2 := rngassoc2 X ) . set ( assoc1 := rngassoc1 X ) . rewrite ( ldistr ( s' * x ) ( s * x' ) s'' ) .  rewrite ( ldistr ( s'' * x' ) ( s' * x'' ) s ) .  destruct ( comm2 s'' s' ) .  destruct ( assoc2 s'' s' x ) . destruct ( assoc2 s'' s x' ) .  destruct ( assoc2 s s'' x' ) .  destruct ( comm2 s s'' ) .  destruct ( assoc2 s s' x'' ) . apply ( assoc1 ( ( s'' * s' ) * x ) ( ( s * s'' ) * x' ) ( ( s * s' ) * x'' ) ) .  Defined .

Opaque commrngfracl2 .


Lemma commrngfracassoc1 ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : isassoc ( commrngfracop1 X S ) .
Proof . intros . set ( R := eqrelcommrngfrac X S ) . set ( add1int := commrngfracop1int X S ) . set ( add1 := commrngfracop1 X S ) .  unfold isassoc . 
assert ( int : forall xs xs' xs'' : dirprod X S , paths ( setquotpr R ( add1int ( add1int xs xs' ) xs'' ) ) ( setquotpr R ( add1int xs ( add1int xs' xs'' ) ) ) ) . unfold add1int . unfold commrngfracop1int . intros xs xs' xs'' .  apply ( @maponpaths _ _ ( setquotpr R ) ) .   simpl .  apply pathsdirprod . unfold pr1carrier . apply ( commrngfracl2 X  ( pr1 xs ) ( pr1 xs' ) ( pr1 xs'' ) ( pr1 ( pr2 xs ) )  ( pr1 ( pr2 xs' ) ) ( pr1 ( pr2 xs'' ) ) ) . apply ( invmaponpathsincl _ ( isinclpr1carrier ( pr1 S ) ) ) .  unfold pr1carrier . simpl .  set ( assoc2 := rngassoc2 X ) .  apply ( assoc2 (pr1 (pr2 xs)) (pr1 (pr2 xs')) (pr1 (pr2 xs'')) ) . 

apply ( setquotuniv3prop R ( fun x x' x'' : setquotinset R => @eqset ( setquotinset R ) ( add1 ( add1 x x' ) x'') ( add1 x ( add1 x' x'') ) ) int ) . Defined .   
  
Opaque commrngfracassoc1 .

Lemma commrngfraccomm1 ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : iscomm ( commrngfracop1 X S ) .
Proof . intros .  set ( R := eqrelcommrngfrac X S ) .  set ( add1int := commrngfracop1int X S ) . set ( add1 := commrngfracop1 X S ) . unfold iscomm . apply ( setquotuniv2prop R ( fun x x' : setquotinset R  => @eqset ( setquotinset R ) ( add1 x x') ( add1 x' x ) ) ) . intros xs xs' .   apply ( @maponpaths _ _ ( setquotpr R ) ( add1int xs xs' ) ( add1int xs' xs ) ) .  unfold add1int . unfold commrngfracop1int . destruct xs as [ x s ] . destruct s as [ s iss ] . destruct xs' as [ x' s' ] . destruct s' as [ s' iss' ] . simpl .   apply pathsdirprod .  

change ( paths ( ( s' * x) + ( s * x' ) ) ( ( s * x' ) + ( s' * x ) ) ) . destruct ( rngcomm1 X ( s' * x ) ( s * x' ) ) . apply idpath . 

apply ( invmaponpathsincl _ ( isinclpr1carrier ( pr1 S ) ) ) .  simpl .  change (  paths ( s * s' ) ( s' * s ) ) . apply ( rngcomm2 X ) . Defined . 

Opaque commrngfraccomm1 .


Definition commrngfracunel1 ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) := setquotpr  ( eqrelcommrngfrac X S ) ( commrngfracunel1int X S ) .

Definition commrngfracunel2 ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) := setquotpr  ( eqrelcommrngfrac X S ) ( commrngfracunel2int X S ) . 

Lemma commrngfracinv1comp ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : iscomprelrelfun ( eqrelcommrngfrac X S ) ( eqrelcommrngfrac X S ) ( commrngfracinv1int X S ) .
Proof . intros . set ( assoc2 := rngassoc2 X ) . intros xs xs' .  simpl .  set ( ff := @hinhfun ) .  simpl in ff . apply ff . clear ff .  intro tt0 .  split with ( pr1 tt0 ) . set ( x := pr1 xs ) . set ( s := pr1 ( pr2 xs ) ) . set ( x' := pr1 xs' ) . set ( s' := pr1 ( pr2 xs' ) ) . set ( a0 := pr1 ( pr1 tt0 ) ) .  change ( paths ( -1 * x * s' * a0 ) ( -1 * x' * s * a0 ) ) . rewrite ( assoc2 -1 x s' ) .  rewrite ( assoc2 -1 x' s ) . rewrite ( assoc2 -1 ( x * s' ) a0 ) . rewrite ( assoc2 -1 ( x' * s ) a0 ) . apply ( maponpaths ( fun x0 : X => -1 * x0 ) ( pr2 tt0 ) ) . Defined .   

Definition commrngfracinv1 ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) := setquotfun ( eqrelcommrngfrac X S ) ( eqrelcommrngfrac X S ) ( commrngfracinv1int X S ) ( commrngfracinv1comp X S ) . 

Lemma commrngfracisinv1 ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : isinv ( commrngfracop1 X S ) ( commrngfracunel1 X S ) ( commrngfracinv1 X S ) .
Proof . intros .  

assert ( isl : islinv  ( commrngfracop1 X S ) ( commrngfracunel1 X S ) ( commrngfracinv1 X S ) ) . set ( R := eqrelcommrngfrac X S ) . set ( add1int := commrngfracop1int X S ) . set ( add1 := commrngfracop1 X S ) . set ( inv1 := commrngfracinv1 X S ) . set ( inv1int := commrngfracinv1int X S ) . set ( qunel1int := commrngfracunel1int X S ) .  set ( qunel1 := commrngfracunel1 X S) . set ( assoc2 := rngassoc2 X ) .  unfold islinv . apply ( setquotunivprop R ( fun  x : setquotinset R => @eqset ( setquotinset R ) ( add1 ( inv1 x ) x ) qunel1 ) ) .  intro xs .   apply ( iscompsetquotpr R  ( add1int ( inv1int xs ) xs ) qunel1int ) . simpl . apply hinhpr .  split with ( unel S ) .  set ( x := pr1 xs ) . set ( s := pr1 ( pr2 xs ) ) . change ( paths ( ( s * ( -1 * x ) + s * x ) * 1 * 1 ) ( 0 * ( s * s ) * 1 ) ) .  destruct ( rngldistr X ( -1 * x ) x s ) . rewrite ( rngmultwithminus1 X x ) . rewrite ( rnglinvax1 X x ) .  rewrite ( rngmultx0 X s ) . rewrite ( rngmult0x X 1 ) .  rewrite ( rngmult0x X 1 ) . rewrite ( rngmult0x X ( s * s ) ) . apply ( pathsinv0 ( rngmult0x X 1 ) ) .

apply ( dirprodpair isl ( weqlinvrinv ( commrngfracop1 X S ) ( commrngfraccomm1 X S ) ( commrngfracunel1 X S ) ( commrngfracinv1 X S ) isl ) ) .  Defined .  

Opaque commrngfracisinv1 . 


Lemma commrngfraclunit1 ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : islunit ( commrngfracop1 X S ) ( commrngfracunel1 X S ) .
Proof . intros .  set ( R := eqrelcommrngfrac X S ) . set ( add1int := commrngfracop1int X S ) . set ( add1 := commrngfracop1 X S ) . set ( un1 := commrngfracunel1 X S ). 
unfold islunit .  apply ( setquotunivprop R ( fun x : _ => @eqset ( setquotinset R ) (add1 un1 x) x ) ) .  intro xs . 
assert ( e0 : paths ( add1int ( commrngfracunel1int X S ) xs ) xs ) .  unfold add1int . unfold commrngfracop1int .  destruct xs as [ x s ] . destruct s as [ s iss ] .  apply pathsdirprod . simpl .    change ( paths ( ( s * 0 ) + ( 1 * x ) ) x ) . rewrite (  @rngmultx0 X s  ) . rewrite ( rnglunax2 X x ) . rewrite ( rnglunax1 X x ) . apply idpath . apply ( invmaponpathsincl _ ( isinclpr1carrier ( pr1 S ) ) ) . change ( paths ( 1 * s ) s ) .  apply ( rnglunax2 X s ) .  apply ( maponpaths ( setquotpr R ) e0 ) . Defined .

Opaque commrngfraclunit1 .

Lemma commrngfracrunit1 ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : isrunit ( commrngfracop1 X S ) ( commrngfracunel1 X S ) .
Proof . intros . apply ( weqlunitrunit (commrngfracop1 X S) ( commrngfraccomm1 X S ) (commrngfracunel1 X S) ( commrngfraclunit1 X S ) ) .  Defined .  

Opaque commrngfracrunit1 .

Definition commrngfracunit1 ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : ismonoidop ( commrngfracop1 X S ) := tpair _ ( commrngfracassoc1 X S ) ( tpair _ ( commrngfracunel1 X S ) ( dirprodpair ( commrngfraclunit1 X S ) ( commrngfracrunit1 X S ) ) ) . 


Definition commrngfracop2 ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : binop ( setquotinset ( eqrelcommrngfrac X S ) ) := abmonoidfracop ( rngmultabmonoid X ) S .

Lemma commrngfraccomm2 ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : iscomm ( commrngfracop2 X S ) .
Proof . intros . apply ( commax ( abmonoidfrac ( rngmultabmonoid X ) S ) ) . Defined .   

Opaque commrngfraccomm2 .


Lemma commrngfracldistr  ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : isldistr ( commrngfracop1 X S ) ( commrngfracop2 X S ) .
Proof . intros . set ( R := eqrelcommrngfrac X S ) . set ( mult1int := commrngfracop2int X S ) . set ( mult1 := commrngfracop2 X S ) . set ( add1int := commrngfracop1int X S ) . set ( add1 := commrngfracop1 X S ) .  unfold isldistr .  apply ( setquotuniv3prop R ( fun x x' x'' : setquotinset R  => @eqset ( setquotinset R ) ( mult1 x'' ( add1 x x')) ( add1 ( mult1 x'' x) ( mult1  x'' x')) ) ) . intros xs xs' xs'' .  apply ( iscompsetquotpr R ( mult1int xs'' ( add1int xs xs' ) ) ( add1int ( mult1int xs'' xs ) ( mult1int xs'' xs' ) ) ) . 

destruct xs as [ x s ] .  destruct xs' as [ x' s' ] . destruct xs'' as [ x'' s'' ] . destruct s'' as [ s'' iss'' ] . simpl . apply hinhpr . split with ( unel S ) . 
destruct s as [ s iss ] .  destruct s' as [ s' iss' ] . simpl . 

change ( paths ( ( ( x'' * ( ( s' * x ) + ( s * x' ) ) ) * ( ( s'' * s ) * ( s'' * s' ) ) ) * 1 ) ( ( ( ( ( s'' * s') * ( x'' * x ) ) + ( ( s'' * s ) * ( x'' * x' ) ) ) * ( s'' * ( s * s' ) ) ) * 1 ) ) . 

rewrite ( rngldistr X ( s' * x ) ( s * x' ) x'' ) .  rewrite ( rngrdistr X _ _ ( ( s'' * s) * ( s'' * s') ) ) .  rewrite ( rngrdistr X _ _ ( s'' * ( s * s') ) ) .  set ( assoc := rngassoc2 X ) . set ( comm := rngcomm2 X ) . set ( rer := @abmonoidoprer X ( @op2 X ) ( commrngop2axs X ) ) . 

assert ( e1 : paths ( ( x'' * ( s' * x ) ) * ( ( s'' * s ) * ( s'' * s' ) ) ) ( ( ( s'' * s') * ( x'' * x ) ) * ( s'' * ( s * s' ) ) ) ) . destruct ( assoc x'' s' x ) .  destruct ( comm s' x'' ) .  rewrite ( assoc s' x'' x ) .  destruct ( comm (  x'' * x ) s' ) .  destruct ( comm (  x'' * x ) (  s'' * s' ) ) .  destruct ( assoc s'' s s' ) . destruct ( comm (  s'' * s' ) (  s'' * s ) ) .  destruct ( comm s' (  s'' * s ) ) . destruct ( rer (  x'' * x ) s' (  s'' * s' ) (  s'' * s ) ) .  apply idpath . 

assert ( e2 : paths ( ( x'' * ( s * x' ) ) * ( ( s'' * s ) * ( s'' * s' ) ) )  ( ( ( s'' * s ) * ( x'' * x' ) ) * ( s'' * ( s * s' ) ) ) ) . destruct ( assoc x'' s x' ) .  destruct ( comm s x'' ) .  rewrite ( assoc s x'' x' ) .  destruct ( comm (  x'' * x' ) s ) .  destruct ( comm (  x'' * x' ) (  s'' * s ) ) . destruct ( rer (  x'' * x' ) (  s'' * s ) s (  s'' * s' ) ) .  destruct ( assoc s s'' s' ) . destruct ( assoc s'' s s' ) . destruct ( comm s s'' ) . apply idpath .

rewrite e1 .  rewrite e2 . apply idpath . Defined .  

Opaque commrngfracldistr .


Lemma commrngfracrdistr  ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : isrdistr ( commrngfracop1 X S ) ( commrngfracop2 X S ) .
Proof . intros . apply ( weqldistrrdistr (commrngfracop1 X S) ( commrngfracop2 X S ) ( commrngfraccomm2 X S ) ( commrngfracldistr X S ) ) .  Defined .  


  

(** Notes : 

1. Construction of the addition on the multiplicative monoid of fractions requires only commutativity and associativity of multiplication and ( right ) distributivity . No properties of the addition are used . 

2. The proof of associtivity for the addition on the multiplicative monoid of fractions requires in the associativity of the original addition but no other properties . 

*) 

Definition commrngfrac ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : commrng .   
Proof .  intros .  set ( R := eqrelcommrngfrac  X S ) . set ( mult1 := commrngfracop2 X S ) . set ( add1 := commrngfracop1 X S ) . set ( uset := setquotinset R ) . apply ( commrngconstr add1 mult1 ) . 
split with ( commrngfracunit1 X S ) .  split with ( commrngfracinv1 X S ) .  apply ( commrngfracisinv1 X S ) .  apply ( commrngfraccomm1 X S ) .  apply ( pr2 ( abmonoidfrac ( rngmultabmonoid X ) S ) ) . apply ( commrngfraccomm2 X S ) .  apply ( dirprodpair ( commrngfracldistr X S ) ( commrngfracrdistr X S ) ) .  Defined . 

Definition prcommrngfrac ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : X -> S -> commrngfrac X S := fun x s => setquotpr _ ( dirprodpair x s ) .

Lemma invertibilityincommrngfrac  ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : forall a a' : S , isinvertible ( @op2 ( commrngfrac X S ) ) ( prcommrngfrac X S ( pr1 a ) a' ) .  
Proof . intros . apply ( invertibilityinabmonoidfrac ( rngmultabmonoid X ) S ) . Defined . 



(** **** Canonical homomorphism to the ring of fractions *)

Definition tocommrngfrac ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) ( x : X ) : commrngfrac X S := setquotpr _ ( dirprodpair x ( unel S ) ) .

Lemma isbinop1funtocommrngfrac ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : @isbinopfun ( rngaddabgr X ) ( rngaddabgr ( commrngfrac X S ) ) ( tocommrngfrac X S ) .
Proof . intros . unfold isbinopfun . intros x x' . change ( paths ( setquotpr _ ( dirprodpair ( x + x' ) ( unel S ) ) ) ( setquotpr ( eqrelcommrngfrac X S )  ( commrngfracop1int X S ( dirprodpair x ( unel S ) ) ( dirprodpair x' ( unel S ) ) ) ) ) .  apply ( maponpaths ( setquotpr _ ) ) . unfold commrngfracop1int .   simpl . apply pathsdirprod .  

rewrite ( rnglunax2 X _ ) . rewrite ( rnglunax2 X _ ) .  apply idpath . 

change ( paths ( unel S ) ( op ( unel S ) ( unel S ) ) ) . apply ( pathsinv0 ( runax S _ ) ) . Defined . 

Opaque isbinop1funtocommrngfrac .

Lemma isunital1funtocommrngfrac ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : paths ( tocommrngfrac X S 0 ) 0 .
Proof . intros. apply idpath . Defined .

Opaque isunital1funtocommrngfrac .  

Definition isaddmonoidfuntocommrngfrac ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : @ismonoidfun  ( rngaddabgr X ) ( rngaddabgr ( commrngfrac X S ) ) ( tocommrngfrac X S ) := dirprodpair ( isbinop1funtocommrngfrac X S ) ( isunital1funtocommrngfrac X S ) . 

Definition tocommrngfracandminus0 ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) ( x : X ) : paths ( tocommrngfrac X S ( - x ) ) ( - tocommrngfrac X S x ) := grinvandmonoidfun _ _ ( isaddmonoidfuntocommrngfrac X S ) x .

Definition tocommrngfracandminus ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) ( x y : X ) : paths ( tocommrngfrac X S ( x - y ) ) ( tocommrngfrac X S x - tocommrngfrac X S y ) .
Proof . intros .  rewrite ( ( isbinop1funtocommrngfrac X S x ( - y ) ) : paths (tocommrngfrac X S (x - y)) ( (tocommrngfrac X S x + tocommrngfrac X S ( - y ) ) ) ) . rewrite ( tocommrngfracandminus0 X S y ) .  apply idpath . Defined .   

Opaque tocommrngfracandminus .

Definition isbinop2funtocommrngfrac  ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : @isbinopfun ( rngmultmonoid X ) ( rngmultmonoid ( commrngfrac X S ) ) ( tocommrngfrac X S ) := isbinopfuntoabmonoidfrac ( rngmultabmonoid X ) S . 

Opaque isbinop2funtocommrngfrac .

Lemma isunital2funtocommrngfrac  ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : paths ( tocommrngfrac X S 1 ) 1 .
Proof . intros. apply idpath . Defined .

Opaque isunital2funtocommrngfrac .   

Definition ismultmonoidfuntocommrngfrac  ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : @ismonoidfun  ( rngmultmonoid X ) ( rngmultmonoid ( commrngfrac X S ) ) ( tocommrngfrac X S ) := dirprodpair ( isbinop2funtocommrngfrac X S ) ( isunital2funtocommrngfrac X S ) . 
 
Definition isrngfuntocommrngfrac ( X : commrng ) ( S : @subabmonoids ( rngmultabmonoid X ) ) : @isrngfun X ( commrngfrac X S ) ( tocommrngfrac X S ) := dirprodpair ( isaddmonoidfuntocommrngfrac X S ) ( ismultmonoidfuntocommrngfrac X S ) .




(** **** Ring of fractions in the case when all elements which are being inverted are cancelable *) 

Definition  hrelcommrngfrac0 ( X : commrng ) ( S : @submonoids ( rngmultabmonoid X ) ) : hrel ( dirprod X S ) :=  fun xa yb : setdirprod X S => eqset ( ( pr1 xa ) * ( pr1 ( pr2 yb ) ) )  ( ( pr1 yb ) * ( pr1 ( pr2 xa ) ) ) .

Lemma weqhrelhrel0commrngfrac ( X : commrng ) ( S : @submonoids ( rngmultabmonoid X ) ) ( iscanc : forall a : S , isrcancelable ( @op2 X ) ( pr1carrier _ a ) ) ( xa xa' : dirprod X S ) : weq ( eqrelcommrngfrac X S xa xa' ) ( hrelcommrngfrac0 X S xa xa' ) .
Proof . intros .  unfold eqrelabmonoidfrac .  unfold hrelabmonoidfrac . simpl .  apply weqimplimpl .  

apply ( @hinhuniv _ ( eqset (pr1 xa * pr1 (pr2 xa')) (pr1 xa' * pr1 (pr2 xa)) ) ) .  intro ae .  destruct ae as [ a eq ] .  apply ( invmaponpathsincl _ ( iscanc a ) _ _ eq ) . 
intro eq . apply hinhpr . split with ( unel S ) . rewrite ( rngrunax2 X )  .  rewrite ( rngrunax2 X ) .  apply eq . apply ( isapropishinh _ ) .  apply ( setproperty X ) .   Defined .

Opaque weqhrelhrel0abmonoidfrac .


Lemma isinclprcommrngfrac ( X : commrng ) ( S : @submonoids ( rngmultabmonoid X ) ) ( iscanc : forall a : S , isrcancelable ( @op2 X ) ( pr1carrier _ a ) ) : forall a' : S , isincl ( fun x => prcommrngfrac X S x a' ) .
Proof . intros . apply isinclbetweensets . apply ( setproperty X ) .  apply ( setproperty ( commrngfrac X S ) ) .  intros x x' .   intro e .  set ( e' := invweq ( weqpathsinsetquot ( eqrelcommrngfrac X S ) ( dirprodpair x a' ) ( dirprodpair x' a' ) )  e ) . set ( e'' := weqhrelhrel0commrngfrac X S iscanc ( dirprodpair _ _ ) ( dirprodpair _ _ ) e' )  . simpl in e'' . apply ( invmaponpathsincl _ ( iscanc a' ) ) . apply e'' .  Defined . 

Definition isincltocommrngfrac ( X : commrng ) ( S : @submonoids ( rngmultabmonoid X ) ) ( iscanc : forall a : S , isrcancelable ( @op2 X ) ( pr1carrier _ a ) ) : isincl ( tocommrngfrac X S ) := isinclprcommrngfrac X S iscanc ( unel S ) . 

Lemma isdeceqcommrngfrac ( X : commrng ) ( S : @submonoids ( rngmultabmonoid  X ) ) ( iscanc : forall a : S , isrcancelable ( @op2 X ) ( pr1carrier _ a ) ) ( is : isdeceq X ) : isdeceq ( commrngfrac X S ) .
Proof . intros . apply ( isdeceqsetquot ( eqrelcommrngfrac X S ) ) .   intros xa xa' .   apply ( isdecpropweqb ( weqhrelhrel0commrngfrac X S iscanc xa xa' ) ) . apply isdecpropif  . unfold isaprop . simpl . set ( int := setproperty X (pr1 xa * pr1 (pr2 xa')) (pr1 xa' * pr1 (pr2 xa))) . simpl in int . apply int . unfold hrelcommrngfrac0 . unfold eqset .   simpl . apply ( is _ _ ) . Defined . 



(** **** Relations similar to "greater" or "greater or equal"  on the rings of fractions *)



Lemma ispartbinopcommrngfracgt ( X : commrng ) ( S : @submonoids ( rngmultabmonoid X ) ) { R : hrel X } ( is0 : @isbinophrel ( rigaddabmonoid X ) R ) ( is1 : isrngmultgt X R ) ( is2 : forall c : X , S c -> R c 0 ) : @ispartbinophrel ( rngmultabmonoid X ) S R .  
Proof . intros . split . 

intros a b c s rab . apply ( isrngmultgttoislrngmultgt X is0 is1 _ _ _ ( is2 c s ) rab ) . 
intros a b c s rab . apply ( isrngmultgttoisrrngmultgt X is0 is1 _ _ _ ( is2 c s ) rab ) .  Defined .    

Definition commrngfracgt ( X : commrng ) ( S : @submonoids ( rngmultabmonoid X ) ) { R : hrel X } ( is0 : @isbinophrel ( rigaddabmonoid X ) R ) ( is1 : isrngmultgt X R ) ( is2 : forall c : X , S c -> R c 0 )  : hrel ( commrngfrac X S ) := abmonoidfracrel ( rngmultabmonoid X ) S ( ispartbinopcommrngfracgt X S is0 is1 is2 ) .

Lemma isrngmultcommrngfracgt ( X : commrng ) ( S : @submonoids ( rngmultabmonoid X ) ) { R : hrel X } ( is0 : @isbinophrel ( rigaddabmonoid X ) R ) ( is1 : isrngmultgt X R ) ( is2 : forall c : X , S c -> R c 0 ) : isrngmultgt ( commrngfrac X S ) ( commrngfracgt X S is0 is1 is2 ) . 
Proof . intros . set ( rer2 := ( abmonoidrer ( rngmultabmonoid X )) : forall a b c d : X , paths ( ( a * b ) * ( c * d ) ) ( ( a * c ) * ( b * d ) ) ) . apply islrngmultgttoisrngmultgt . 

assert ( int : forall a b c : rngaddabgr (commrngfrac X S) , isaprop ( commrngfracgt X S is0 is1 is2 c 0 -> commrngfracgt X S is0 is1 is2 a b -> commrngfracgt X S is0 is1 is2 (c * a) (c * b) ) ) . intros a b c . apply impred . intro . apply impred . intro . apply ( pr2 _ ) . apply ( setquotuniv3prop _ ( fun a b c => hProppair _ ( int a b c ) ) ) . intros xa1 xa2 xa3 . change ( abmonoidfracrelint ( rngmultabmonoid X ) S R xa3 ( dirprodpair 0 ( unel S ) )  -> abmonoidfracrelint ( rngmultabmonoid X ) S R xa1 xa2 -> abmonoidfracrelint ( rngmultabmonoid X ) S R ( commrngfracop2int X S xa3 xa1 ) ( commrngfracop2int X S xa3 xa2 ) ) .  simpl . apply hinhfun2 . intros t21 t22 .  set ( c1s := pr1 t21 ) . set ( c1 := pr1 c1s ) . set ( r1 := pr2 t21 ) .   set ( c2s := pr1 t22 ) . set ( c2 := pr1 c2s ) . set ( r2 := pr2 t22 ) . set ( x1 := pr1 xa1 ) . set ( a1 := pr1 ( pr2 xa1 ) ) .  set ( x2 := pr1 xa2 ) . set ( a2 := pr1 ( pr2 xa2 ) ) .  set ( x3 := pr1 xa3 ) . set ( a3 := pr1 ( pr2 xa3 ) ) . split with ( @op S c1s c2s ) . change ( pr1 ( R ( x3 * x1 * ( a3 * a2 ) * ( c1 * c2 ) ) ( x3 * x2 * ( a3 * a1 ) * ( c1 * c2 ) ) ) ) . rewrite ( rngcomm2 X a3 a2 ) .  rewrite ( rngcomm2 X a3 a1 ) . rewrite ( rngassoc2 X _ _ ( c1 * c2 ) ) .  rewrite ( rngassoc2 X ( x3 * x2 ) _ ( c1 * c2 ) ) . rewrite ( rer2 _ a3 c1 _ ) . rewrite ( rer2 _ a3 c1 _ ) . rewrite ( rngcomm2 X a2 c1 ) . rewrite ( rngcomm2 X a1 c1 ) . rewrite ( pathsinv0 ( rngassoc2 X ( x3 * x1 ) _ _ ) ) . rewrite ( pathsinv0 ( rngassoc2 X ( x3 * x2 ) _ _ ) ) . rewrite ( rer2 _ x1 c1 _ ) .  rewrite ( rer2 _ x2 c1 _ ) . rewrite ( rngcomm2 X a3 c2 ) . rewrite ( pathsinv0 ( rngassoc2 X _ c2 a3 ) ) .  rewrite ( pathsinv0 ( rngassoc2 X _ c2 _ ) ) . apply ( ( isrngmultgttoisrrngmultgt X is0 is1 ) _ _ _ ( is2 _ ( pr2 ( pr2 xa3 ) ) ) ) .  rewrite ( rngassoc2 X _ _ c2 ) . rewrite ( rngassoc2 X _ ( x2 * a1 ) c2 ) . 

simpl in r1 . clearbody r1 . simpl in r2 . clearbody r2 . change ( pr1 ( R ( x3 * 1 * c1 ) ( 0 * a3 * c1 ) ) ) in r1 .  rewrite ( rngrunax2 _ _ ) in r1 . rewrite ( rngmult0x X _ ) in r1 . rewrite ( rngmult0x X _ ) in r1 . apply ( ( isrngmultgttoislrngmultgt X is0 is1 ) _ _ _ r1 r2 ) . Defined . 

Opaque isrngmultcommrngfracgt .

Lemma isrngaddcommrngfracgt ( X : commrng ) ( S : @submonoids ( rngmultabmonoid X ) ) { R : hrel X } ( is0 : @isbinophrel ( rigaddabmonoid X ) R ) ( is1 : isrngmultgt X R ) ( is2 : forall c : X , S c -> R c 0 ) : @isbinophrel ( rngaddabgr ( commrngfrac X S ) ) ( commrngfracgt X S is0 is1 is2 ) . 
Proof .  intros . set ( rer2 := ( abmonoidrer ( rngmultabmonoid X )) : forall a b c d : X , paths ( ( a * b ) * ( c * d ) ) ( ( a * c ) * ( b * d ) ) ) .  apply isbinophrelif . intros a b . apply ( rngcomm1 ( commrngfrac X S )  a b ) . 

assert ( int : forall a b c : rngaddabgr (commrngfrac X S) , isaprop ( commrngfracgt X S is0 is1 is2 a b -> commrngfracgt X S is0 is1 is2 (op c a) (op c b) ) ) . intros a b c . apply impred . intro . apply ( pr2 _ ) . apply ( setquotuniv3prop _ ( fun a b c => hProppair _ ( int a b c ) ) ) . intros xa1 xa2 xa3 . change ( abmonoidfracrelint ( rngmultabmonoid X ) S R xa1 xa2 -> abmonoidfracrelint ( rngmultabmonoid X ) S R ( commrngfracop1int X S xa3 xa1 ) ( commrngfracop1int X S xa3 xa2 ) ) . simpl . apply hinhfun .  intro t2 . set ( c0s := pr1 t2 ) . set ( c0 := pr1 c0s ) . set ( r := pr2 t2 ) . split with c0s .   set ( x1 := pr1 xa1 ) . set ( a1 := pr1 ( pr2 xa1 ) ) .  set ( x2 := pr1 xa2 ) . set ( a2 := pr1 ( pr2 xa2 ) ) .  set ( x3 := pr1 xa3 ) . set ( a3 := pr1 ( pr2 xa3 ) ) . change ( pr1 ( R ( ( a1 * x3 + a3 * x1 ) * ( a3 * a2 ) * c0 ) ( ( a2 * x3 + a3 * x2 ) * ( a3 * a1 ) * c0 ) ) ) . rewrite ( rngassoc2 X _ _ c0 ) .  rewrite ( rngassoc2 X _ ( a3 * _ ) c0 ) . rewrite ( rngrdistr X _ _ _ ) .   rewrite ( rngrdistr X _ _ _ ) . rewrite ( rer2 _ x3 _ _ ) .  rewrite ( rer2 _ x3 _ _ ) . rewrite ( rngcomm2 X a3 a2 ) . rewrite ( rngcomm2 X a3 a1 ) .  rewrite ( pathsinv0 ( rngassoc2 X a1 a2 a3 ) ) .   rewrite ( pathsinv0 ( rngassoc2 X a2 a1 a3 ) ) . rewrite ( rngcomm2 X a1 a2 ) .  apply ( ( pr1 is0 ) _ _ _ ) .  rewrite ( rngcomm2 X  a2 a3 ) .  rewrite ( rngcomm2 X  a1 a3 ) . rewrite ( rngassoc2 X a3 a2 c0 ) . rewrite ( rngassoc2 X a3 a1 c0 ) . rewrite ( rer2 _ x1 a3 _ ) . rewrite ( rer2 _ x2 a3 _ ) . rewrite ( pathsinv0 ( rngassoc2 X x1 _ _ ) ) . rewrite ( pathsinv0 ( rngassoc2 X x2 _ _ ) ) . apply ( ( isrngmultgttoislrngmultgt X is0 is1 ) _ _ _ ( is2 _ ( pr2 ( @op S ( pr2 xa3 ) ( pr2 xa3 ) ) ) ) r )  . Defined . 

Opaque isrngaddcommrngfracgt .


Definition isdeccommrngfracgt ( X : commrng ) ( S : @submonoids ( rngmultabmonoid X ) ) { R : hrel X } ( is0 : @isbinophrel ( rigaddabmonoid X ) R ) ( is1 : isrngmultgt  X R ) ( is2 : forall c : X , S c -> R c 0 ) ( is' : @ispartinvbinophrel ( rngmultabmonoid X ) S R )  ( isd : isdecrel R ) : isdecrel ( commrngfracgt X S is0 is1 is2 ) .
Proof . intros . apply ( isdecabmonoidfracrel ( rngmultabmonoid X ) S ( ispartbinopcommrngfracgt X S is0 is1 is2 ) is' isd ) . Defined .   



(** **** Realations and the canonical homomorphism to the ring of fractions *)


Definition iscomptocommrngfrac ( X : commrng ) ( S : @submonoids ( rngmultabmonoid X ) ) { L : hrel X } ( is0 : @isbinophrel ( rigaddabmonoid X ) L ) ( is1 : isrngmultgt X L ) ( is2 : forall c : X , S c -> L c 0 ) : iscomprelrelfun L ( commrngfracgt X S is0 is1 is2 ) ( tocommrngfrac X S ) := iscomptoabmonoidfrac ( rngmultabmonoid X ) S ( ispartbinopcommrngfracgt X S is0 is1 is2 ) . 

Opaque iscomptocommrngfrac . 
 



Close Scope rng_scope . 













(* End of the file algebra1c.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)