(** * Algebra I. Part B.  Monoids, abelian monoids groups, abelian groups. Vladimir Voevodsky. Aug. 2011 - . 

*)



(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)


(** Imports *)

Require Export algebra1a .


(** To upstream files *)


(** ** Standard Algebraic Structures *)


(** *** Monoids *)


(** ****  Basic definitions *)



Definition monoid := total2 ( fun X : setwithbinop => ismonoidop ( @op X ) ) .
Definition monoidpair := tpair ( fun X : setwithbinop => ismonoidop ( @op X ) ) .
Definition monoidconstr := monoidpair .
Definition pr1monoid : monoid -> setwithbinop := @pr1 _ _ . 
Coercion pr1monoid : monoid >-> setwithbinop .

Definition assocax ( X : monoid ) : isassoc ( @op X ) := pr1 ( pr2 X ) .
Definition unel ( X : monoid) : X := pr1 ( pr2 ( pr2 X ) ) .
Definition lunax ( X : monoid ) : islunit ( @op X ) ( unel X ) := pr1 ( pr2 ( pr2 ( pr2 X ) ) ) .  
Definition runax ( X : monoid ) : isrunit ( @op X ) ( unel X ) := pr2 ( pr2 ( pr2 ( pr2 X ) ) ) . 

Notation "x + y" := ( op x y ) : addmonoid_scope . 
Notation "0" := ( unel _ ) : addmonoid_scope .   

Delimit Scope addmonoid_scope with addmonoid. 

Notation "x * y" := ( op x y ) : multmonoid_scope . 
Notation "1" := ( unel _ ) : multmonoid_scope .   

Delimit Scope multmonoid_scope with multmonoid. 



(** **** Functions betweens monoids compatible with structure ( homomorphisms ) and their properties *)


Definition ismonoidfun { X Y : monoid } ( f : X -> Y ) := dirprod ( isbinopfun f ) ( paths ( f ( unel X ) ) ( unel Y ) ) . 

Lemma isapropismonoidfun { X Y : monoid } ( f : X -> Y ) : isaprop ( ismonoidfun f ) .
Proof . intros . apply isofhleveldirprod . apply isapropisbinopfun .  apply ( setproperty Y ) . Defined .

Definition monoidfun ( X Y : monoid ) : UU0 := total2 ( fun f : X -> Y => ismonoidfun f ) .
Definition monoidfunconstr { X Y : monoid } { f : X -> Y } ( is : ismonoidfun f ) : monoidfun X Y := tpair _ f is . 
Definition pr1monoidfun ( X Y : monoid ) : monoidfun X Y -> ( X -> Y ) := @pr1 _ _ . 

Definition monoidfuntobinopfun ( X Y : monoid ) : monoidfun X Y -> binopfun X Y := fun f => binopfunpair ( pr1 f ) ( pr1 ( pr2 f ) ) .
Coercion monoidfuntobinopfun : monoidfun >-> binopfun .  


Lemma isasetmonoidfun  ( X Y : monoid ) : isaset ( monoidfun X Y ) .
Proof . intros . apply ( isasetsubset ( pr1monoidfun X Y  ) ) . change ( isofhlevel 2 ( X -> Y ) ) . apply impred .  intro . apply ( setproperty Y ) . apply isinclpr1 .  intro .  apply isapropismonoidfun . Defined .  


Lemma ismonoidfuncomp { X Y Z : monoid } ( f : monoidfun X Y ) ( g : monoidfun Y Z ) : ismonoidfun ( funcomp ( pr1 f ) ( pr1 g ) ) .
Proof . intros . split with ( isbinopfuncomp f g ) . unfold funcomp .  rewrite ( pr2 ( pr2 f ) ) .  apply ( pr2 ( pr2 g ) ) . Defined .  

Opaque ismonoidfuncomp . 

Definition monoidfuncomp { X Y Z : monoid } ( f : monoidfun X Y ) ( g : monoidfun Y Z ) : monoidfun X Z := monoidfunconstr ( ismonoidfuncomp f g ) . 


Definition monoidmono ( X Y : monoid ) : UU0 := total2 ( fun f : incl X Y => ismonoidfun f ) .
Definition monoidmonopair { X Y : monoid } ( f : incl X Y ) ( is : ismonoidfun f ) : monoidmono X Y := tpair _  f is .
Definition pr1monoidmono ( X Y : monoid ) : monoidmono X Y -> incl X Y := @pr1 _ _ .
Coercion pr1monoidmono : monoidmono >-> incl .

Definition monoidincltomonoidfun ( X Y : monoid ) : monoidmono X Y -> monoidfun X Y := fun f => monoidfunconstr ( pr2 f ) .
Coercion monoidincltomonoidfun : monoidmono >-> monoidfun . 

Definition monoidmonotobinopmono ( X Y : monoid ) : monoidmono X Y -> binopmono X Y := fun f => binopmonopair ( pr1 f ) ( pr1 ( pr2 f ) ) .
Coercion monoidmonotobinopmono : monoidmono >-> binopmono .  

Definition monoidmonocomp { X Y Z : monoid } ( f : monoidmono X Y ) ( g : monoidmono Y Z ) : monoidmono X Z := monoidmonopair ( inclcomp ( pr1 f ) ( pr1 g ) ) ( ismonoidfuncomp f g ) . 


Definition monoidiso ( X Y : monoid ) : UU0 := total2 ( fun f : weq X Y => ismonoidfun f ) .   
Definition monoidisopair { X Y : monoid } ( f : weq X Y ) ( is : ismonoidfun f ) : monoidiso X Y := tpair _  f is .
Definition pr1monoidiso ( X Y : monoid ) : monoidiso X Y -> weq X Y := @pr1 _ _ .
Coercion pr1monoidiso : monoidiso >-> weq .

Definition monoidisotomonoidmono ( X Y : monoid ) : monoidiso X Y -> monoidmono X Y := fun f => monoidmonopair ( pr1 f ) ( pr2 f ) .
Coercion monoidisotomonoidmono : monoidiso >-> monoidmono . 

Definition monoidisotobinopiso ( X Y : monoid ) : monoidiso X Y -> binopiso X Y := fun f => binopisopair ( pr1 f ) ( pr1 ( pr2 f ) ) .
Coercion monoidisotobinopiso : monoidiso >-> binopiso .  


Lemma ismonoidfuninvmap { X Y : monoid } ( f : monoidiso X Y ) : ismonoidfun ( invmap ( pr1 f ) ) . 
Proof . intros . split with ( isbinopfuninvmap f ) .  apply ( invmaponpathsweq ( pr1 f ) ) .  rewrite ( homotweqinvweq ( pr1 f ) ) . apply ( pathsinv0 ( pr2 ( pr2 f ) ) ) . Defined .

Opaque ismonoidfuninvmap .  

Definition invmonoidiso { X Y : monoid } ( f : monoidiso X Y ) : monoidiso Y X := monoidisopair ( invweq ( pr1 f ) ) ( ismonoidfuninvmap f ) .




(** **** Subobjects *)

Definition issubmonoid { X : monoid } ( A : hsubtypes X ) := dirprod ( issubsetwithbinop ( @op X ) A ) ( A ( unel X ) ) . 

Lemma isapropissubmonoid { X : monoid } ( A : hsubtypes X ) : isaprop ( issubmonoid A ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropissubsetwithbinop . apply ( pr2 ( A ( unel X ) ) ) . Defined .  

Definition submonoids { X : monoid } := total2 ( fun A : hsubtypes X => issubmonoid A )  . 
Definition submonoidpair { X : monoid } := tpair ( fun A : hsubtypes X => issubmonoid A ) . 
Definition submonoidconstr { X : monoid } := @submonoidpair X . 
Definition pr1submonoids ( X : monoid ) : @submonoids X -> hsubtypes X := @pr1 _ _ . 

Definition totalsubmonoid  ( X : monoid ) : @submonoids X .
Proof . intro . split with ( fun x : _ => htrue ) . split . intros x x' . apply tt . apply tt . Defined .   

Definition submonoidstosubsetswithbinop ( X : monoid ) : @submonoids X -> @subsetswithbinop X := fun A : _ => subsetswithbinoppair ( pr1 A ) ( pr1 ( pr2 A ) ) . 
Coercion  submonoidstosubsetswithbinop : submonoids >-> subsetswithbinop .

Lemma ismonoidcarrier { X : monoid } ( A : @submonoids X ) : ismonoidop ( @op A ) . 
Proof . intros . split .  intros a a' a'' .  apply ( invmaponpathsincl _ ( isinclpr1carrier A ) ) . simpl .  apply ( assocax X ) . split with ( carrierpair _ ( unel X ) ( pr2 ( pr2 A ) ) ) .   split . simpl . intro a . apply ( invmaponpathsincl _ ( isinclpr1carrier A ) ) .  simpl . apply ( lunax X ) .  intro a . apply ( invmaponpathsincl _ ( isinclpr1carrier A ) ) .  simpl . apply ( runax X ) . Defined . 

Definition carrierofsubmonoid { X : monoid } ( A : @submonoids X ) : monoid .
Proof . intros . split with A . apply ismonoidcarrier . Defined . 

Coercion carrierofsubmonoid : submonoids >-> monoid . 




(** **** Quotient objects *)

Lemma isassocquot { X : monoid } ( R : @binopeqrel X ) : isassoc ( @op ( setwithbinopquot R ) ) . 
Proof . intros . intros a b c .  apply  ( setquotuniv3prop R ( fun x x' x'' : setwithbinopquot R  => hProppair _ ( setproperty ( setwithbinopquot R ) ( op ( op x x' ) x'' ) ( op x ( op x' x'' )) ) ) ) .  intros x x' x'' . apply ( maponpaths ( setquotpr R ) ( assocax X x x' x'' ) ) .  Defined . 

Opaque isassocquot .
    

Lemma isunitquot { X : monoid } ( R : @binopeqrel X ) : isunit ( @op ( setwithbinopquot R ) ) ( setquotpr R ( pr1 ( pr2 ( pr2 X ) ) ) ) .
Proof . intros .  set ( qun := setquotpr R ( pr1 ( pr2 ( pr2 X ) ) ) ) . set ( qsetwithop := setwithbinopquot R ) .  split .  

intro x . apply ( setquotunivprop R ( fun x => @eqset qsetwithop ( ( @op qsetwithop ) qun x ) x ) ) .  simpl . intro x0 .   apply ( maponpaths ( setquotpr R ) ( lunax X x0 ) ) . 

intro x . apply ( setquotunivprop R ( fun x => @eqset qsetwithop ( ( @op qsetwithop ) x qun ) x ) ) .  simpl . intro x0 . apply ( maponpaths ( setquotpr R ) ( runax X x0 ) ) . Defined .

Opaque isunitquot . 


Definition ismonoidquot { X : monoid } ( R : @binopeqrel X ) : ismonoidop ( @op ( setwithbinopquot R ) ) := tpair _ ( isassocquot R ) ( tpair _ ( setquotpr R ( pr1 ( pr2 ( pr2 X ) ) ) ) ( isunitquot R ) ) .  

Definition monoidquot { X : monoid } ( R : @binopeqrel X ) : monoid .
Proof . intros . split with ( setwithbinopquot R ) . apply ismonoidquot . Defined . 


(** **** Direct products *)

Lemma isassocdirprod ( X Y : monoid ) : isassoc ( @op ( setwithbinopdirprod X Y ) ) .
Proof . intros .  simpl . intros xy xy' xy'' .  simpl . apply pathsdirprod .  apply ( assocax X ) .  apply ( assocax Y ) .  Defined . 

Opaque isassocdirprod .

Lemma isunitindirprod ( X Y : monoid ) : isunit ( @op ( setwithbinopdirprod X Y ) ) ( dirprodpair ( unel X ) ( unel Y ) ) .
Proof . split . 

intro xy . destruct xy as [ x y ] . simpl . apply pathsdirprod .  apply ( lunax X ) .  apply ( lunax Y ) . 
intro xy .  destruct xy as [ x y ] . simpl . apply pathsdirprod .  apply ( runax X ) .  apply ( runax Y ) . Defined . 

Opaque isunitindirprod . 

Definition ismonoiddirprod ( X Y : monoid ) : ismonoidop ( @op ( setwithbinopdirprod X Y ) ) := tpair _ ( isassocdirprod X Y ) ( tpair _ ( dirprodpair ( unel X ) ( unel Y ) ) ( isunitindirprod X Y ) ) .  

Definition monoiddirprod ( X Y : monoid ) : monoid .
Proof . intros . split with ( setwithbinopdirprod X Y ) . apply ismonoiddirprod . Defined .  






(** *** Abelian ( commutative ) monoids *)


(** **** Basic definitions *)


Definition abmonoid := total2 ( fun X : setwithbinop =>  isabmonoidop ( @op X ) ) .
Definition abmonoidpair := tpair ( fun X : setwithbinop =>  isabmonoidop ( @op X ) ) .
Definition abmonoidconstr := abmonoidpair .

Definition abmonoidtomonoid : abmonoid -> monoid := fun X : _ => monoidpair ( pr1 X ) ( pr1 ( pr2 X ) ) .
Coercion abmonoidtomonoid : abmonoid >-> monoid .

Definition commax ( X : abmonoid ) : iscomm ( @op X ) := pr2 ( pr2 X ) .

Definition abmonoidrer ( X : abmonoid ) ( a b c d : X ) : paths ( op ( op a b ) ( op c d ) ) ( op ( op a c ) ( op b d ) ) := abmonoidoprer ( pr2 X ) a b c d .  


(** **** Subobjects *)

Definition subabmonoids { X : abmonoid } := @submonoids X .
Identity Coercion id_subabmonoids : subabmonoids >-> submonoids . 

Lemma iscommcarrier { X : abmonoid } ( A : @submonoids X ) : iscomm ( @op A ) . 
Proof . intros .   intros a a' .  apply ( invmaponpathsincl _ ( isinclpr1carrier A ) ) .  simpl . apply ( pr2 ( pr2 X ) ) . Defined .

Opaque iscommcarrier . 

Definition  isabmonoidcarrier  { X : abmonoid } ( A : @submonoids X ) : isabmonoidop ( @op A ) := dirprodpair ( ismonoidcarrier A ) ( iscommcarrier A ) . 

Definition carrierofsubabmonoid { X : abmonoid } ( A : @subabmonoids X ) : abmonoid .
Proof . intros . unfold subabmonoids in A . split with A . apply isabmonoidcarrier . Defined . 

Coercion carrierofsubabmonoid : subabmonoids >-> abmonoid . 




(** **** Quotient objects *)

Lemma iscommquot { X : abmonoid } ( R : @binopeqrel X ) : iscomm ( @op ( setwithbinopquot R ) ) .
Proof . intros .  set ( X0 := setwithbinopquot R ) . intros x x' .  apply ( setquotuniv2prop R ( fun x x' : X0 => hProppair _ ( setproperty X0 ( op x x') ( op x' x) ) ) ) . intros x0 x0' .  apply ( maponpaths ( setquotpr R ) ( ( commax X ) x0 x0' ) ) . Defined .

Opaque iscommquot . 

Definition isabmonoidquot { X : abmonoid } ( R : @binopeqrel X ) : isabmonoidop ( @op ( setwithbinopquot R ) ) := dirprodpair ( ismonoidquot R ) ( iscommquot R ) . 

Definition abmonoidquot { X : abmonoid } ( R : @binopeqrel X ) : abmonoid .
Proof . intros . split with  ( setwithbinopquot R )  . apply isabmonoidquot . Defined .  


(** **** Direct products *)

Lemma iscommdirprod ( X Y : abmonoid ) : iscomm ( @op ( setwithbinopdirprod X Y ) ) .
Proof . intros . intros xy xy' . destruct xy as [ x y ] . destruct xy' as [ x' y' ] .  simpl .  apply pathsdirprod .  apply ( commax X ) .  apply ( commax Y ) .  Defined .

Opaque iscommdirprod . 

Definition isabmonoiddirprod ( X Y : abmonoid ) : isabmonoidop ( @op ( setwithbinopdirprod X Y ) ) := dirprodpair ( ismonoiddirprod X Y ) ( iscommdirprod X Y ) .

Definition abmonoiddirprod ( X Y : abmonoid ) : abmonoid .
Proof . intros . split with ( setwithbinopdirprod X Y ) . apply isabmonoiddirprod .  Defined . 




(** **** Monoid of fractions of an abelian monoid 

Note : the following construction uses onbly associativity and commutativity of the [ abmonoid ] operations but does not use the unit element . *)

Open Scope addmonoid_scope .

Definition abmonoidfracopint ( X : abmonoid ) ( A : @submonoids X ) : binop ( dirprod X A ) := @op ( setwithbinopdirprod X A ) .

Definition  hrelabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : hrel ( setwithbinopdirprod X A ) :=  fun xa yb : dirprod X A => hexists ( fun a0 : A =>  paths ( ( ( pr1 xa ) + ( pr1 ( pr2 yb ) ) ) + ( pr1 a0 ) )  ( ( ( pr1 yb ) + ( pr1 ( pr2 xa ) ) + ( pr1 a0 ) ) ) ) . 

Lemma iseqrelabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : iseqrel ( hrelabmonoidfrac X A ) .
Proof . intros . set ( assoc := assocax X ) . set ( comm := commax X ) . set ( R := hrelabmonoidfrac X A ) .

assert ( symm : issymm R ) . intros xa yb .  unfold R . simpl . apply hinhfun .  intro eq1 . destruct eq1 as [ x1 eq1 ] . split with x1 . destruct x1 as [ x1 isx1 ] .  simpl . apply ( pathsinv0 eq1 ) . 

assert ( trans : istrans R ) .  unfold istrans . intros ab cd ef .  simpl . apply hinhfun2 .   destruct ab as [ a b ] . destruct cd as [ c d ] . destruct ef as [ e f ] .   destruct b as [ b isb ] . destruct d as [ d isd ] .  destruct f as [ f isf ] .   intros eq1 eq2 .  destruct eq1 as [ x1 eq1 ] . destruct eq2 as [ x2 eq2 ] . simpl in * . split with ( @op A ( tpair _ d isd ) ( @op A x1 x2 ) ) .  destruct x1 as [ x1 isx1 ] . destruct x2 as [ x2 isx2 ] . destruct A as [ A ax ] . simpl in * .  rewrite ( assoc a f ( d + ( x1 + x2 ) ) ) .  rewrite ( comm f ( d + ( x1 + x2 ) ) ) .  destruct ( assoc a ( d + ( x1 + x2 ) ) f ) .  destruct ( assoc a d ( x1 + x2 ) )  .  destruct ( assoc ( a + d ) x1 x2 )  . rewrite eq1 . rewrite ( comm x1 x2 ) .   rewrite ( assoc e b ( d + ( x2 + x1 ) ) ) .  rewrite ( comm b ( d + ( x2 + x1 ) ) ) .  destruct ( assoc e ( d + ( x2 + x1 ) ) b ) . destruct ( assoc e d ( x2 + x1 ) )  . destruct ( assoc ( e + d ) x2 x1 ) .  destruct eq2 . rewrite ( assoc ( c + b ) x1 x2 ) .  rewrite ( assoc ( c + f ) x2 x1 )  . rewrite ( comm x1 x2 ) .  rewrite ( assoc ( c + b ) ( x2 + x1 ) f ) .  rewrite ( assoc ( c + f ) ( x2 + x1 ) b ) .   rewrite ( comm ( x2 + x1 ) f ) .  rewrite ( comm ( x2 + x1 ) b ) . destruct ( assoc ( c + b ) f ( x2 + x1 ) ) .  destruct ( assoc ( c + f ) b ( x2 + x1 ) ) . rewrite ( assoc c b f ) .  rewrite ( assoc c f b ) . rewrite ( comm b f ) .  apply idpath . 

assert ( refl : isrefl R ) . intro xa .  simpl .  apply hinhpr . split with ( pr2 xa ) . apply idpath .  

apply ( iseqrelconstr trans refl symm ) . Defined .

Opaque iseqrelabmonoidfrac .  

Definition eqrelabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : eqrel ( setwithbinopdirprod X A ) := eqrelpair ( hrelabmonoidfrac X A ) ( iseqrelabmonoidfrac X A ) .

Lemma isbinophrelabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : @isbinophrel ( setwithbinopdirprod X A ) ( eqrelabmonoidfrac X A ) . 
Proof . intros . apply ( isbinopreflrel ( eqrelabmonoidfrac X A ) ( eqrelrefl ( eqrelabmonoidfrac X A ) ) ) .  set ( rer := abmonoidoprer ( pr2 X ) ) .  intros a b c d .  simpl . apply hinhfun2 .  destruct a as [ a a' ] . destruct a' as [ a' isa' ] . destruct b as [ b b' ] . destruct b' as [ b' isb' ] . destruct c as [ c c' ] . destruct c' as [ c' isc' ] . destruct d as [ d d' ] . destruct d' as [ d' isd' ] . intros ax ay .  destruct ax as [ a1 eq1 ] . destruct ay as [ a2 eq2 ] . split with ( @op A  a1 a2 ) .  destruct a1 as [ a1 aa1 ] . destruct a2 as [ a2 aa2 ] . simpl in *.  rewrite ( rer a c b' d' ) . rewrite ( rer b d a' c' ) . rewrite ( rer ( a + b' ) ( c + d' ) a1 a2 ) .  rewrite ( rer ( b + a' ) ( d + c' ) a1 a2 ) . destruct eq1 . destruct eq2 . apply idpath . Defined .

Opaque isbinophrelabmonoidfrac .
 
Definition abmonoidfracop ( X : abmonoid ) ( A : @submonoids X ) : binop ( setquot ( hrelabmonoidfrac X A ) ) := setquotfun2 ( hrelabmonoidfrac X A ) ( eqrelabmonoidfrac X A ) ( abmonoidfracopint X A ) ( ( iscompbinoptransrel _ ( eqreltrans _ ) ( isbinophrelabmonoidfrac X A ) ) ) . 

Definition binopeqrelabmonoidfrac ( X : abmonoid ) ( A : @subabmonoids X ) : @binopeqrel ( abmonoiddirprod X A ) := @binopeqrelpair ( setwithbinopdirprod X A ) ( eqrelabmonoidfrac X A ) ( isbinophrelabmonoidfrac X A ) .   

Definition abmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : abmonoid := abmonoidquot ( binopeqrelabmonoidfrac X A ) . 

Definition prabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : X -> A -> abmonoidfrac X A := fun ( x : X ) ( a : A ) => setquotpr ( eqrelabmonoidfrac X A ) ( dirprodpair x a ) . 

(* ??? could the use of [ issubabmonoid ] in [ binopeqrelabmonoidfrac ] and [ submonoid ] in [ abmonoidfrac ] lead to complications for the unification machinery? See also [ abmonoidfracisbinoprelint ] below . *)

Lemma invertibilityinabmonoidfrac  ( X : abmonoid ) ( A : @submonoids X ) : forall a a' : A , isinvertible ( @op ( abmonoidfrac X A ) ) ( prabmonoidfrac X A ( pr1 a ) a' ) .  
Proof . intros . set ( R := eqrelabmonoidfrac X A ) .   unfold isinvertible .  

assert ( isl : islinvertible ( @op ( abmonoidfrac X A ) ) ( prabmonoidfrac X A ( pr1 a ) a' ) ) . unfold islinvertible .  set ( f := fun x0 : abmonoidfrac X A => prabmonoidfrac X A (pr1 a) a' + x0 ) . set ( g := fun x0 : abmonoidfrac X A => prabmonoidfrac X A (pr1 a' ) a + x0 ) .
assert ( egf : forall x0 : _ , paths ( g ( f x0 ) ) x0 ) . apply ( setquotunivprop R ( fun x0 : abmonoidfrac X A => eqset (g (f x0)) x0 ) ) .  intro xb . simpl . apply ( iscompsetquotpr R ( @dirprodpair X A ( ( pr1 a' ) + ( ( pr1 a ) + ( pr1 xb ) ) ) ( ( @op A ) a ( ( @op A ) a' ( pr2 xb ) ) ) ) ) .   simpl .  apply hinhpr .  split with ( unel A ) .  unfold pr1carrier . simpl . set  ( e := assocax X ( pr1 a ) ( pr1 a' ) ( pr1 ( pr2 xb ) ) ) . simpl in e . destruct e .  set ( e := assocax X ( pr1 xb ) ( pr1 a + pr1 a' ) ( pr1 ( pr2 xb ) ) ) . simpl in e .  destruct e . set ( e := assocax X ( pr1 a' ) ( pr1 a ) ( pr1 xb ) ) . simpl in e .  destruct e . set ( e := commax X ( pr1 a ) ( pr1 a' ) ) . simpl in e . destruct e .  set ( e := commax X ( pr1 a + pr1 a' ) ( pr1 xb ) ) . simpl in e . destruct e . apply idpath . 
assert ( efg : forall x0 : _ , paths ( f ( g x0 ) ) x0 ) .  apply ( setquotunivprop R ( fun x0 : abmonoidfrac X A => eqset (f (g x0)) x0 ) ) .  intro xb . simpl . apply ( iscompsetquotpr R ( @dirprodpair X A ( ( pr1 a ) + ( ( pr1 a' ) + ( pr1 xb ) ) ) ( ( @op A ) a' ( ( @op A ) a ( pr2 xb ) ) ) ) ) .   simpl .  apply hinhpr .  split with ( unel A ) .  unfold pr1carrier . simpl . set  ( e := assocax X ( pr1 a' ) ( pr1 a ) ( pr1 ( pr2 xb ) ) ) . simpl in e . destruct e .  set ( e := assocax X ( pr1 xb ) ( pr1 a' + pr1 a ) ( pr1 ( pr2 xb ) ) ) . simpl in e .  destruct e . set ( e := assocax X ( pr1 a ) ( pr1 a' ) ( pr1 xb ) ) . simpl in e .  destruct e . set ( e := commax X ( pr1 a' ) ( pr1 a ) ) . simpl in e . destruct e .  set ( e := commax X ( pr1 a' + pr1 a ) ( pr1 xb ) ) . simpl in e . destruct e . apply idpath .
apply ( gradth _ _ egf efg ) . 

apply ( dirprodpair isl ( weqlinvertiblerinvertible ( @op ( abmonoidfrac X A ) ) ( commax ( abmonoidfrac X A ) ) ( prabmonoidfrac X A ( pr1 a ) a' ) isl ) ) . 
Defined .  


(** **** Canonical homomorphism to the monoid of fractions *)

Definition toabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) ( x : X ) : abmonoidfrac X A := setquotpr _ ( dirprodpair x ( unel A ) ) . 

Lemma isbinopfuntoabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : isbinopfun ( toabmonoidfrac X A ) .
Proof . intros . unfold isbinopfun . intros x1 x2 .  change ( paths ( setquotpr _ ( dirprodpair ( x1 + x2 ) ( @unel A ) ) ) ( setquotpr ( eqrelabmonoidfrac X A ) ( dirprodpair ( x1 + x2 ) ( ( unel A ) + ( unel A ) ) ) ) ) .  apply ( maponpaths ( setquotpr _  ) ) .  apply ( @pathsdirprod X A ) . apply idpath .  apply ( pathsinv0 ( lunax A 0 ) ) . Defined . 

Lemma isunitalfuntoabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : paths ( toabmonoidfrac X A ( unel X ) ) ( unel ( abmonoidfrac X A ) ) .
Proof . intros . apply idpath . Defined .  

Definition ismonoidfuntoabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : ismonoidfun ( toabmonoidfrac X A ) := dirprodpair ( isbinopfuntoabmonoidfrac X A ) ( isunitalfuntoabmonoidfrac X A ) .


(** **** Abelian monoid of fractions in the case when elements of the localziation submonoid are cancelable *)

Definition  hrel0abmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) : hrel ( dirprod X A ) :=  fun xa yb : setdirprod X A => eqset ( ( pr1 xa ) + ( pr1 ( pr2 yb ) ) )  ( ( pr1 yb ) + ( pr1 ( pr2 xa ) ) ) .

Lemma weqhrelhrel0abmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) ( iscanc : forall a : A , isrcancelable ( @op X ) ( pr1carrier _ a ) ) ( xa xa' : dirprod X A ) : weq ( eqrelabmonoidfrac X A xa xa' ) ( hrel0abmonoidfrac X A xa xa' ) .
Proof . intros .  unfold eqrelabmonoidfrac .  unfold hrelabmonoidfrac . simpl .  apply weqimplimpl .  

apply ( @hinhuniv _ ( eqset (pr1 xa + pr1 (pr2 xa')) (pr1 xa' + pr1 (pr2 xa)) ) ) .  intro ae .  destruct ae as [ a eq ] .  apply ( invmaponpathsincl _ ( iscanc a ) _ _ eq ) . 
intro eq . apply hinhpr . split with ( unel A ) . rewrite ( runax X )  .  rewrite ( runax X ) .  apply eq . apply ( isapropishinh _ ) .  apply ( setproperty X ) .   Defined .


Lemma isinclprabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) ( iscanc : forall a : A , isrcancelable ( @op X ) ( pr1carrier _ a ) ) : forall a' : A , isincl ( fun x => prabmonoidfrac X A x a' ) .
Proof . intros . apply isinclbetweensets . apply ( setproperty X ) .  apply ( setproperty ( abmonoidfrac X A ) ) .  intros x x' .   intro e .  set ( e' := invweq ( weqpathsinsetquot ( eqrelabmonoidfrac X A ) ( dirprodpair x a' ) ( dirprodpair x' a' ) )  e ) . set ( e'':= weqhrelhrel0abmonoidfrac X A iscanc ( dirprodpair _ _ ) ( dirprodpair _ _ ) e' ) . simpl in e'' . apply ( invmaponpathsincl _ ( iscanc a' ) ) . apply e'' .  Defined .

Definition isincltoabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) ( iscanc : forall a : A , isrcancelable ( @op X ) ( pr1carrier _ a ) ) : isincl ( toabmonoidfrac X A ) := isinclprabmonoidfrac X A iscanc ( unel A ) .   


Lemma isdeceqabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) ( iscanc : forall a : A , isrcancelable ( @op X ) ( pr1carrier _ a ) ) ( is : isdeceq X ) : isdeceq ( abmonoidfrac X A ) .
Proof . intros . apply ( isdeceqsetquot ( eqrelabmonoidfrac X A ) ) .   intros xa xa' .  apply ( isdecpropweqb ( weqhrelhrel0abmonoidfrac X A iscanc xa xa' ) ) . apply isdecpropif  . unfold isaprop . simpl . set ( int := setproperty X (pr1 xa + pr1 (pr2 xa')) (pr1 xa' + pr1 (pr2 xa))) . simpl in int . apply int . unfold hrel0abmonoidfrac . unfold eqset .   simpl . apply ( is _ _ ) . Defined . 



(** **** Relations on the abelian monoid of fractions *) 

Definition abmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) ( L : hrel X ) : hrel ( setwithbinopdirprod X A ) := fun xa yb => hexists ( fun c0 : A => L ( ( ( pr1 xa ) + ( pr1 ( pr2 yb ) ) ) + ( pr1 c0 ) ) ( ( ( pr1 yb ) + ( pr1 ( pr2 xa ) ) ) + ( pr1 c0 ) ) ) .    

Lemma iscomprelabmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) : iscomprelrel ( eqrelabmonoidfrac X A ) ( abmonoidfracrelint X A L ) . 
Proof . intros . set ( assoc := ( assocax X ) : isassoc ( @op X ) ) . unfold isassoc in assoc .  set ( comm := commax X ) .  unfold iscomm in comm . set ( rer := abmonoidrer X ) . apply iscomprelrelif .   apply ( eqrelsymm ( eqrelabmonoidfrac X A ) ) . 

intros xa xa' yb . unfold hrelabmonoidfrac . simpl . apply ( @hinhfun2 ) . intros t2e t2l .  destruct t2e as [ c1a e ] . destruct t2l as [ c0a l ] . set ( x := pr1 xa ) . set ( a := pr1 ( pr2 xa ) ) . set ( x' := pr1 xa' ) . set ( a' := pr1 ( pr2 xa' ) ) . set ( y := pr1 yb ) . set ( b := pr1 ( pr2 yb ) ) . set ( c0 := pr1 c0a ) . set ( c1 := pr1 c1a ) . split with ( ( pr2 xa ) + c1a + c0a ) . change ( L ( ( x' + b ) + ( ( a + c1 ) + c0 ) ) ( ( y + a' ) + ( ( a + c1 ) + c0 ) ) ) . change ( paths ( x + a' + c1 ) ( x' + a + c1 ) ) in e .   rewrite ( rer x' _ _ c0 ) .  destruct ( assoc x' a c1 )  . destruct e .  rewrite ( assoc x a' c1 ) .  rewrite ( rer x _ _ c0 ) . rewrite ( assoc a c1 c0 ) . rewrite ( rer _ a' a _ ) . rewrite ( assoc a' c1 c0 ) . rewrite ( comm a' _ ) .  rewrite ( comm c1 _ ) . rewrite ( assoc  c0 c1 a' ) . destruct ( assoc ( x + b ) c0 ( @op X c1 a' ) ) .  destruct ( assoc ( y + a ) c0 ( @op X c1 a' ) ) . apply ( ( pr2 is ) _ _ _ ( pr2 ( @op A c1a ( pr2 xa' ) ) ) l )  . 

intros xa yb yb' . unfold hrelabmonoidfrac . simpl . apply ( @hinhfun2 ) . intros t2e t2l .  destruct t2e as [ c1a e ] . destruct t2l as [ c0a l ] . set ( x := pr1 xa ) . set ( a := pr1 ( pr2 xa ) ) . set ( y' := pr1 yb' ) . set ( b' := pr1 ( pr2 yb' ) ) . set ( y := pr1 yb ) . set ( b := pr1 ( pr2 yb ) ) . set ( c0 := pr1 c0a ) . set ( c1 := pr1 c1a ) . split with ( ( pr2 yb ) + c1a + c0a ) . change ( L ( ( x + b' ) + ( ( b + c1 ) + c0 ) ) ( ( y' + a ) + ( ( b + c1 ) + c0 ) ) ) . change ( paths ( y + b' + c1 ) ( y' + b + c1 ) ) in e .   rewrite ( rer y' _ _ c0 ) .  destruct ( assoc y' b c1 )  . destruct e .  rewrite ( assoc y b' c1 ) .  rewrite ( rer y _ _ c0 ) . rewrite ( assoc b c1 c0 ) . rewrite ( rer _ b' b _ ) . rewrite ( assoc b' c1 c0 ) . rewrite ( comm b' _ ) .  rewrite ( comm c1 _ ) . rewrite ( assoc  c0 c1 b' ) . destruct ( assoc ( x + b ) c0 ( @op X c1 b' ) ) .  destruct ( assoc ( y + a ) c0 ( @op X c1 b' ) ) . apply ( ( pr2 is ) _ _ _ ( pr2 ( @op A c1a ( pr2 yb' ) ) ) l )  . Defined . 

Opaque iscomprelabmonoidfracrelint . 

Definition abmonoidfracrel ( X : abmonoid ) ( A : @submonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) := quotrel ( iscomprelabmonoidfracrelint X A is ) . 

Lemma istransabmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : istrans L ) : istrans ( abmonoidfracrelint X A L ) .
Proof . intros .  set ( assoc := ( assocax X ) : isassoc ( @op X ) ) . unfold isassoc in assoc .  set ( comm := commax X ) .  unfold iscomm in comm . set ( rer := abmonoidrer X ) . intros xa1 xa2 xa3 .  unfold abmonoidfracrelint .  simpl .   apply hinhfun2 . intros t2l1 t2l2 .  set ( c1a := pr1 t2l1 ) . set ( l1 := pr2 t2l1 ) . set ( c2a := pr1 t2l2 ) . set ( l2 := pr2 t2l2 ) .   set ( x1 := pr1 xa1 ) . set ( a1 := pr1 ( pr2 xa1 ) ) .  set ( x2 := pr1 xa2 ) . set ( a2 := pr1 ( pr2 xa2 ) ) .  set ( x3 := pr1 xa3 ) . set ( a3 := pr1 ( pr2 xa3 ) ) . set ( c1 := pr1 c1a ) . set ( c2 := pr1 c2a ) . split with ( ( pr2 xa2 ) + ( @op A c1a c2a ) ) . change ( L ( ( x1 + a3 ) + ( a2 + ( c1 + c2 ) ) ) ( ( x3 + a1 ) + ( a2 + ( c1 + c2 ) ) ) ) . 

assert ( ll1 : L ( ( x1 + a3 ) + ( a2 + ( @op X c1 c2 ) ) ) ( ( ( x2 + a1 ) + c1 ) + ( c2 + a3 ) ) ) .  rewrite ( rer _ a3 a2 _ ) .  rewrite ( comm a3 ( @op X c1 c2 ) ) . rewrite ( assoc c1 c2 a3 ) . destruct ( assoc ( x1 + a2 ) c1 ( @op X c2 a3 ) ) . apply ( ( pr2 is ) _ _ _ ( pr2 ( @op A c2a ( pr2 xa3 ) ) ) l1 ) . 

assert ( ll2 : L ( ( ( x2 + a3 ) + c2 ) + ( @op X a1 c1 ) )  ( ( x3 + a1 ) + ( a2 + ( @op X c1 c2 ) ) ) ) .  rewrite ( rer _ a1 a2 _ ) .  destruct ( assoc a1 c1 c2 ) . rewrite ( comm ( a1 + c1 ) c2 )  . destruct ( assoc ( x3 + a2 ) c2 ( @op X a1 c1 )) .  apply ( ( pr2 is ) _ _ _ ( pr2 ( @op A ( pr2 xa1 ) c1a ) ) l2 ) .  

assert ( e : paths (x2 + a1 + c1 + (c2 + a3)) (x2 + a3 + c2 + (a1 + c1)) ) . rewrite ( assoc ( x2 + a1 ) c1 _ ) .  rewrite ( assoc ( x2 + a3 ) c2 _ ) . rewrite ( assoc x2 a1 _ ) .  rewrite ( assoc x2 a3 _ ) . destruct ( assoc a1 c1 ( c2 + a3 ) ) . destruct ( assoc a3 c2 ( a1 + c1 ) ) .  destruct ( comm ( c2 + a3 ) ( a1 + c1 ) ) .  rewrite ( comm a3 c2 ) . apply idpath . 

destruct e . apply ( isl _ _ _ ll1 ll2 ) . Defined . 

Opaque istransabmonoidfracrelint . 

Lemma istransabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : istrans L ) : istrans ( abmonoidfracrel X A is ) .
Proof . intros .  apply istransquotrel . apply istransabmonoidfracrelint .  apply is . apply isl . Defined . 

Lemma issymmabmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : issymm L ) : issymm ( abmonoidfracrelint X A L ) .
Proof . intros . intros xa1 xa2 .  unfold abmonoidfracrelint .  simpl .   apply hinhfun . intros t2l1 .  set ( c1a := pr1 t2l1 ) . set ( l1 := pr2 t2l1 ) .  split with ( c1a ) . apply ( isl _ _ l1 ) . Defined . 

Opaque issymmabmonoidfracrelint .

Lemma issymmabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : issymm L ) : issymm ( abmonoidfracrel X A is ) .
Proof . intros .  apply issymmquotrel . apply issymmabmonoidfracrelint .  apply is . apply isl . Defined . 

Lemma isreflabmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : isrefl L ) : isrefl ( abmonoidfracrelint X A L ) .
Proof . intros . intro xa . unfold abmonoidfracrelint .  simpl . apply hinhpr . split with ( unel A ) .  apply ( isl _ ) . Defined .

Lemma isreflabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : isrefl L ) : isrefl ( abmonoidfracrel X A is ) .
Proof . intros .  apply isreflquotrel . apply isreflabmonoidfracrelint .  apply is . apply isl . Defined . 

Lemma ispoabmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : ispo L ) : ispo ( abmonoidfracrelint X A L ) .
Proof . intros . split with ( istransabmonoidfracrelint X A is ( pr1 isl ) ) .  apply ( isreflabmonoidfracrelint X A is ( pr2 isl ) ) .  Defined . 

Lemma ispoabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : ispo L ) : ispo ( abmonoidfracrel X A is ) .
Proof . intros .  apply ispoquotrel . apply ispoabmonoidfracrelint .  apply is . apply isl . Defined . 

Lemma iseqrelabmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : iseqrel L ) : iseqrel ( abmonoidfracrelint X A L ) .
Proof . intros . split with ( ispoabmonoidfracrelint X A is ( pr1 isl ) ) .  apply ( issymmabmonoidfracrelint X A is ( pr2 isl ) ) .  Defined . 

Lemma iseqrelabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : iseqrel L ) : iseqrel ( abmonoidfracrel X A is ) .
Proof . intros .  apply iseqrelquotrel . apply iseqrelabmonoidfracrelint .  apply is . apply isl . Defined .

Lemma isirreflabmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : isirrefl L ) : isirrefl ( abmonoidfracrelint X A L ) .
Proof . intros . unfold isirrefl.  intro xa .  unfold abmonoidfracrelint . simpl .  unfold neg . apply ( @hinhuniv _ ( hProppair _ isapropempty ) ) .  intro t2 . apply ( isl _ ( pr2 t2 ) ) .  Defined . 

Lemma isirreflabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : isirrefl L ) : isirrefl ( abmonoidfracrel X A is ) .
Proof . intros . apply isirreflquotrel . apply isirreflabmonoidfracrelint .  apply is . apply isl .  Defined . 

Lemma isasymmabmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : isasymm L ) : isasymm ( abmonoidfracrelint X A L ) .
Proof . intros . set ( assoc := ( assocax X ) : isassoc ( @op X ) ) . unfold isassoc in assoc .  set ( comm := commax X ) .  unfold iscomm in comm . unfold isasymm.  intros xa1 xa2 . unfold abmonoidfracrelint . simpl .  apply ( @hinhuniv2 _ _ ( hProppair _ isapropempty ) ) .  intros t2l1 t2l2 .   set ( c1a := pr1 t2l1 ) . set ( l1 := pr2 t2l1 ) . set ( c2a := pr1 t2l2 ) . set ( l2 := pr2 t2l2 ) .  set ( c1 := pr1 c1a ) . set ( c2 := pr1 c2a ) .  set ( x1 := pr1 xa1 ) . set ( a1 := pr1 ( pr2 xa1 ) ) .  set ( x2 := pr1 xa2 ) . set ( a2 := pr1 ( pr2 xa2 ) ) . 

assert ( ll1 : L ( ( x1 + a2 ) + ( @op X c1 c2 ) ) ( ( x2 + a1 ) + ( @op X c1 c2 ) ) ) . destruct ( assoc ( x1 + a2 ) c1 c2 ) . destruct ( assoc ( x2 + a1 ) c1 c2 ) . apply ( ( pr2 is ) _ _ _ ( pr2 c2a ) ) . apply l1 .  

assert ( ll2 : L ( ( x2 + a1 ) + ( @op X c1 c2 ) ) ( ( x1 + a2 ) + ( @op X c1 c2 ) ) ) .  destruct ( comm c2 c1 ) .  destruct ( assoc ( x1 + a2 ) c2 c1 ) . destruct ( assoc ( x2 + a1 ) c2 c1 ) . apply ( ( pr2 is ) _ _ _ ( pr2 c1a ) ) . apply l2 .

apply ( isl _ _ ll1 ll2 ) . Defined .

Opaque  isasymmabmonoidfracrelint .


Lemma isasymmabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : isasymm L ) : isasymm ( abmonoidfracrel X A is ) .
Proof . intros . apply isasymmquotrel . apply isasymmabmonoidfracrelint . apply is . apply isl .    Defined .


Lemma iscoasymmabmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : iscoasymm L ) : iscoasymm ( abmonoidfracrelint X A L ) .
Proof . intros . set ( assoc := ( assocax X ) : isassoc ( @op X ) ) . unfold isassoc in assoc .  set ( comm := commax X ) .  unfold iscomm in comm . unfold iscoasymm.  intros xa1 xa2 .  intro nl0 . set ( nl := neghexisttoforallneg _ nl0 ( unel A ) ) . simpl in nl .  set ( l := isl _ _ nl ) . apply hinhpr . split with ( unel A ) . apply l . Defined . 

Opaque  isasymmabmonoidfracrelint .

Lemma iscoasymmabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : iscoasymm L ) : iscoasymm ( abmonoidfracrel X A is ) .
Proof . intros . apply iscoasymmquotrel . apply iscoasymmabmonoidfracrelint . apply is . apply isl .   Defined .


Lemma istotalabmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : istotal L ) : istotal ( abmonoidfracrelint X A L ) .
Proof . intros . unfold istotal .  intros x1 x2 . unfold abmonoidfracrelint . set  ( int := isl ( pr1 x1 + pr1 (pr2 x2) ) (pr1 x2 + pr1 (pr2 x1) ) ) .  generalize int . clear int . simpl .    apply hinhfun . apply coprodf .  intro l .  apply hinhpr .  split with ( unel A ) .  rewrite ( runax X _ ) .  rewrite ( runax X _ ) . apply l .  intro l .  apply hinhpr .  split with ( unel A ) .  rewrite ( runax X _ ) .  rewrite ( runax X _ ) . apply l . Defined .  

Lemma istotalabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : istotal L ) : istotal ( abmonoidfracrel X A is ) .
Proof . intros .  apply istotalquotrel . apply istotalabmonoidfracrelint .  apply is . apply isl . Defined .


Lemma iscotransabmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : iscotrans L ) : iscotrans ( abmonoidfracrelint X A L ) .
Proof . intros . set ( assoc := ( assocax X ) : isassoc ( @op X ) ) . unfold isassoc in assoc .  set ( comm := ( commax X ) : iscomm ( @op X ) ) .  unfold iscomm in comm . set ( rer := abmonoidrer X ) .  unfold iscotrans .  intros xa1 xa2 xa3 . unfold abmonoidfracrelint .  simpl . apply ( @hinhuniv _ ( ishinh _ ) )  .  intro t2 .  set ( c0a := pr1 t2 ) . set ( l0 := pr2 t2 ) .  set ( x1 := pr1 xa1 ) . set ( a1 := pr1 ( pr2 xa1 ) ) .  set ( x2 := pr1 xa2 ) . set ( a2 := pr1 ( pr2 xa2 ) ) .  set ( x3 := pr1 xa3 ) . set ( a3 := pr1 ( pr2 xa3 ) ) . set ( c0 := pr1 c0a ) .  set ( z1 := ( x1 + a3 + ( a2 + c0 ) ) ) . set ( z2 := x2 + a1 + ( a3 + c0 ) ) .  set ( z3 := x3 + a1 + ( a2 + c0 ) ) .     

assert ( int : L z1 z3 ) . unfold z1 . unfold z3 . rewrite ( comm a2 c0 ) .  rewrite ( pathsinv0 ( assoc _ _ a2 ) ) . rewrite ( pathsinv0 ( assoc _ _ a2 ) ) .  apply ( ( pr2 is ) _ _ _ ( pr2 ( pr2 xa2 ) ) l0 ) . set ( int' := isl z1 z2 z3 int ) . generalize int' . clear int' . simpl .  apply hinhfun .  intro cc .  destruct cc as [ l12 | l23 ] .

apply ii1 .  apply hinhpr .  split with ( ( pr2 xa3 ) + c0a ) . change ( L ( x1 + a2 + ( a3 + c0 ) ) ( x2 + a1 + ( a3 + c0 ) ) ) . rewrite ( rer _ a2 a3 _ ) . apply l12 . 

apply ii2 . apply hinhpr . split with ( ( pr2 xa1 ) + c0a ) . change ( L ( x2 + a3 + ( a1 + c0 ) ) ( x3 + a2 + ( a1 + c0 ) ) ) .  rewrite ( rer _ a3 a1 _ ) . rewrite ( rer _ a2 a1 _ ) . apply l23 . Defined .    

Opaque iscotransabmonoidfracrelint . 

Lemma iscotransabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : iscotrans L ) : iscotrans ( abmonoidfracrel X A is ) .
Proof . intros .  apply iscotransquotrel . apply iscotransabmonoidfracrelint .  apply is . apply isl . Defined .




Lemma isantisymmnegabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : isantisymmneg L ) : isantisymmneg ( abmonoidfracrel X A is ) .
Proof . intros . assert ( int : forall x1 x2  , isaprop ( neg ( abmonoidfracrel X A is x1 x2 )-> neg ( abmonoidfracrel X A is x2 x1 ) -> paths x1 x2 ) ) .  intros x1 x2 . apply impred . intro . apply impred . intro . apply ( isasetsetquot _ x1 x2 ) . unfold isantisymmneg .   apply ( setquotuniv2prop _ ( fun x1 x2 => hProppair _ ( int x1 x2 ) ) ) .  intros xa1 xa2 . intros r r' . apply ( weqpathsinsetquot _  ) . generalize r r' . clear r r' . change ( neg ( abmonoidfracrelint X A L xa1 xa2 ) -> neg ( abmonoidfracrelint X A L xa2 xa1 ) -> ( eqrelabmonoidfrac X A xa1 xa2 ) )  .    intros nr12 nr21 . set ( nr12' := neghexisttoforallneg _ nr12 ( unel A ) ) .  set ( nr21' := neghexisttoforallneg _ nr21 ( unel A ) ) .  set ( int' := isl _ _ nr12' nr21' ) .  simpl .   apply hinhpr . split with ( unel A ) . apply int' . Defined .  

Opaque  isantisymmnegabmonoidfracrel .


Lemma isantisymmabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isl : isantisymm L ) : isantisymm ( abmonoidfracrel X A is ) .
Proof . intros . set ( assoc := ( assocax X ) : isassoc ( @op X ) ) . unfold isassoc in assoc .  set ( comm := commax X ) .  unfold iscomm in comm . unfold isantisymm.  assert ( int : forall x1 x2  , isaprop ( ( abmonoidfracrel X A is x1 x2 )-> ( abmonoidfracrel X A is x2 x1 )-> paths x1 x2 ) ) .  intros x1 x2 . apply impred . intro . apply impred . intro . apply ( isasetsetquot _ x1 x2 ) .  apply ( setquotuniv2prop _ ( fun x1 x2 => hProppair _ ( int x1 x2 ) ) ) .  intros xa1 xa2 . intros r r' . apply ( weqpathsinsetquot _  ) . generalize r r' . clear r r' . change ( ( abmonoidfracrelint X A L xa1 xa2 ) -> ( abmonoidfracrelint X A L xa2 xa1 ) -> ( eqrelabmonoidfrac X A xa1 xa2 ) )  .  unfold abmonoidfracrelint . unfold eqrelabmonoidfrac . simpl .  apply hinhfun2 .  intros t2l1 t2l2 .   set ( c1a := pr1 t2l1 ) . set ( l1 := pr2 t2l1 ) . set ( c2a := pr1 t2l2 ) . set ( l2 := pr2 t2l2 ) .  set ( c1 := pr1 c1a ) . set ( c2 := pr1 c2a ) . split with ( @op A c1a c2a ) .  set ( x1 := pr1 xa1 ) . set ( a1 := pr1 ( pr2 xa1 ) ) .  set ( x2 := pr1 xa2 ) . set ( a2 := pr1 ( pr2 xa2 ) ) . change ( paths ( x1 + a2 + ( @op X c1 c2 ) ) ( x2 + a1 + ( @op X c1 c2 ) ) ) .  

assert ( ll1 : L ( ( x1 + a2 ) + ( @op X c1 c2 ) ) ( ( x2 + a1 ) + ( @op X c1 c2 ) ) ) . destruct ( assoc ( x1 + a2 ) c1 c2 ) . destruct ( assoc ( x2 + a1 ) c1 c2 ) . apply ( ( pr2 is ) _ _ _ ( pr2 c2a ) ) . apply l1 .  

assert ( ll2 : L ( ( x2 + a1 ) + ( @op X c1 c2 ) ) ( ( x1 + a2 ) + ( @op X c1 c2 ) ) ) .  destruct ( comm c2 c1 ) .  destruct ( assoc ( x1 + a2 ) c2 c1 ) . destruct ( assoc ( x2 + a1 ) c2 c1 ) . apply ( ( pr2 is ) _ _ _ ( pr2 c1a ) ) . apply l2 .

apply ( isl _ _ ll1 ll2 ) . Defined .

Opaque  isantisymmabmonoidfracrel .




 
Lemma ispartbinopabmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) : @ispartbinophrel ( setwithbinopdirprod X A ) ( fun xa => A ( pr1 xa ) ) ( abmonoidfracrelint X A L ) . 
Proof . intros . set ( assoc := ( assocax X ) : isassoc ( @op X ) ) . unfold isassoc in assoc .  set ( comm := commax X ) .  unfold iscomm in comm . set ( rer := abmonoidrer X ) . apply ispartbinophrelif . apply ( commax ( abmonoiddirprod X A ) ) . intros xa yb zc s . unfold abmonoidfracrelint . simpl . apply ( @hinhfun ) .  intro t2l .  destruct t2l as [ c0a l ] . set ( x := pr1 xa ) . set ( a := pr1 ( pr2 xa ) ) . set ( y := pr1 yb ) . set ( b := pr1 ( pr2 yb ) ) . set ( z := pr1 zc ) .  set ( c := pr1 ( pr2 zc ) ) . set ( c0 := pr1 c0a ) . split with c0a .  change ( L ( ( ( z + x ) + ( c + b ) ) + c0 ) ( ( ( z + y ) + ( c + a ) ) + c0 ) ) .  change ( pr1 ( L ( ( x + b ) + c0 ) ( ( y + a ) + c0 ) ) ) in l . rewrite ( rer z _ _ b ) . rewrite ( assoc ( z + c ) _ _ ) . rewrite ( rer z _ _ a ) . rewrite ( assoc ( z + c ) _ _ ) .  apply ( ( pr1 is ) _ _ _ ( pr2 ( @op A ( carrierpair A z s ) ( pr2 zc ) ) ) ) . apply l . Defined . 

Opaque ispartbinopabmonoidfracrelint . 

Lemma ispartlbinopabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( aa aa' : A ) ( z z' : abmonoidfrac X A ) ( l : abmonoidfracrel X A is z z' ) : abmonoidfracrel X A is ( ( prabmonoidfrac X A ( pr1 aa ) aa' ) + z ) ( ( prabmonoidfrac X A ( pr1 aa ) aa' ) + z' ) .
Proof . intros X A L is aa aa' . set ( assoc := ( assocax X ) : isassoc ( @op X ) ) . unfold isassoc in assoc .  set ( comm := commax X ) .  unfold iscomm in comm . set ( rer := abmonoidrer X ) . assert ( int : forall z z' , isaprop ( abmonoidfracrel X A is z z' -> abmonoidfracrel X A is (prabmonoidfrac X A (pr1 aa) aa' + z) (prabmonoidfrac X A (pr1 aa) aa' + z') ) ) . intros z z' . apply impred . intro . apply ( pr2 ( abmonoidfracrel _ _ _ _ _ ) ) .  apply ( setquotuniv2prop _ ( fun z z' => hProppair _ ( int z z' ) ) ) . intros xa1 xa2 .  change ( abmonoidfracrelint X A L xa1 xa2 -> abmonoidfracrelint X A L ( @op ( abmonoiddirprod X A ) ( dirprodpair ( pr1 aa ) aa' ) xa1 ) (  @op ( abmonoiddirprod X A ) ( dirprodpair ( pr1 aa ) aa' ) xa2 ) ) . unfold abmonoidfracrelint .  simpl . apply hinhfun . intro t2l .  set ( a := pr1 aa ) . set ( a' := pr1 aa' ) . set ( c0a := pr1 t2l ) . set ( l := pr2 t2l ) .  set ( c0 := pr1 c0a ) .  set ( x1 := pr1 xa1 ) . set ( a1 := pr1 ( pr2 xa1 ) ) .  set ( x2 := pr1 xa2 ) . set ( a2 := pr1 ( pr2 xa2 ) ) . split with c0a .  

change ( L ( a + x1 + ( a' + a2 ) + c0 ) ( a + x2 + ( a' + a1 ) + c0 ) ) . rewrite ( rer _ x1 a' _ ) . rewrite ( rer _ x2 a' _ ) .  rewrite ( assoc _ ( x1 + a2 ) c0 ) .  rewrite ( assoc _ ( x2 + a1 ) c0 ) . apply ( ( pr1 is ) _ _ _ ( pr2 ( @op A aa aa' ) ) ) . apply l . Defined . 

Opaque ispartlbinopabmonoidfracrel . 


Lemma ispartrbinopabmonoidfracrel ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( aa aa' : A ) ( z z' : abmonoidfrac X A ) ( l : abmonoidfracrel X A is z z' ) : abmonoidfracrel X A is ( z + ( prabmonoidfrac X A ( pr1 aa ) aa' ) ) ( z' + ( prabmonoidfrac X A ( pr1 aa ) aa' ) ) .
Proof . intros X A L is aa aa' . set ( assoc := ( assocax X ) : isassoc ( @op X ) ) . unfold isassoc in assoc .  set ( comm := commax X ) .  unfold iscomm in comm . set ( rer := abmonoidrer X ) . assert ( int : forall z z' : abmonoidfrac X A , isaprop ( abmonoidfracrel X A is z z' -> abmonoidfracrel X A is ( z + ( prabmonoidfrac X A (pr1 aa) aa') )  ( z' + prabmonoidfrac X A (pr1 aa) aa' ) ) )  . intros z z' . apply impred . intro . apply ( pr2 ( abmonoidfracrel _ _ _ _ _ ) ) .  apply ( setquotuniv2prop _ ( fun z z' => hProppair _ ( int z z' ) ) ) . intros xa1 xa2 .  change ( abmonoidfracrelint X A L xa1 xa2 -> abmonoidfracrelint X A L ( @op ( abmonoiddirprod X A ) xa1 ( dirprodpair ( pr1 aa ) aa' ) ) (  @op ( abmonoiddirprod X A ) xa2 ( dirprodpair ( pr1 aa ) aa' ) ) ) . unfold abmonoidfracrelint .  simpl . apply hinhfun . intro t2l .  set ( a := pr1 aa ) . set ( a' := pr1 aa' ) . set ( c0a := pr1 t2l ) . set ( l := pr2 t2l ) .  set ( c0 := pr1 c0a ) .  set ( x1 := pr1 xa1 ) . set ( a1 := pr1 ( pr2 xa1 ) ) .  set ( x2 := pr1 xa2 ) . set ( a2 := pr1 ( pr2 xa2 ) ) . split with c0a .  

change ( L ( x1 + a + ( a2 + a' ) + c0 ) ( x2 + a + ( a1 + a' ) + c0 ) ) . rewrite ( rer _ a a2 _ ) . rewrite ( rer _ a a1 _ ) .  rewrite ( assoc ( x1 + a2 ) _ c0 ) .  rewrite ( assoc ( x2 + a1 ) _ c0 ) .  rewrite ( comm _ c0 ) . destruct ( assoc ( x1 + a2 ) c0 ( a + a' ) ) . destruct ( assoc ( x2 + a1 ) c0 ( a + a' ) ) . apply ( ( pr2 is ) _ _ _ ( pr2 ( @op A aa aa' ) ) ) . apply l . Defined . 

Opaque ispartrbinopabmonoidfracrel .


Lemma abmonoidfracrelimpl ( X : abmonoid ) ( A : @subabmonoids X ) { L L' : hrel X } ( is : ispartbinophrel A L ) ( is' : ispartbinophrel A L' )  ( impl : forall x x' , L x x' -> L' x x' ) ( x x' : abmonoidfrac X A ) ( ql : abmonoidfracrel X A is x x' ) : abmonoidfracrel X A is' x x'  .
Proof . intros .  generalize ql .  apply quotrelimpl .  intros x0 x0' .  unfold abmonoidfracrelint .  simpl .  apply hinhfun .  intro t2 . split with ( pr1 t2 ) .   apply ( impl _ _ ( pr2 t2 ) ) . Defined . 


Opaque abmonoidfracrelimpl . 


Lemma abmonoidfracrellogeq ( X : abmonoid ) ( A : @subabmonoids X ) { L L' : hrel X } ( is : ispartbinophrel A L ) ( is' : ispartbinophrel A L' )  ( lg : forall x x' , L x x' <-> L' x x' ) ( x x' : abmonoidfrac X A ) :  ( abmonoidfracrel X A is x x' ) <-> ( abmonoidfracrel X A is' x x' ) .
Proof . intros .   apply quotrellogeq .  intros x0 x0' .  split . 

unfold abmonoidfracrelint .  simpl .  apply hinhfun .  intro t2 . split with ( pr1 t2 ) .   apply ( pr1 ( lg _ _ ) ( pr2 t2 ) ) .
unfold abmonoidfracrelint .  simpl .  apply hinhfun .  intro t2 . split with ( pr1 t2 ) .   apply ( pr2 ( lg _ _ ) ( pr2 t2 ) ) . Defined . 

Opaque abmonoidfracrellogeq . 



Definition isdecabmonoidfracrelint ( X : abmonoid ) ( A : @subabmonoids X ) { L : hrel X } ( is : ispartinvbinophrel A L ) ( isl : isdecrel L ) : isdecrel ( abmonoidfracrelint X A L ) . 
Proof . intros . intros xa1 xa2 .  set ( x1 := pr1 xa1 ) . set ( a1 := pr1 ( pr2 xa1 ) ) .  set ( x2 := pr1 xa2 ) . set ( a2 := pr1 ( pr2 xa2 ) ) .  assert ( int : coprod ( L ( x1 + a2 ) ( x2 + a1 ) ) ( neg ( L ( x1 + a2 ) ( x2 + a1 ) ) ) )  . apply ( isl _ _ ) . destruct int as [ l | nl ] .  apply ii1 . unfold abmonoidfracrelint .  apply hinhpr .  split with ( unel A ) .  rewrite ( runax X _ ) .   rewrite ( runax X _ ) . apply l . apply ii2 . generalize nl . clear nl . apply negf . unfold abmonoidfracrelint .   simpl .  apply ( @hinhuniv _ ( hProppair _ ( pr2 ( L _ _ ) ) ) ) .   intro t2l . destruct t2l as [ c0a l ] . simpl . apply ( ( pr2 is ) _ _ _ ( pr2 c0a ) l ) .  Defined . 

Definition isdecabmonoidfracrel ( X : abmonoid ) ( A : @submonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) ( isi : ispartinvbinophrel A L ) ( isl : isdecrel L ) : isdecrel ( abmonoidfracrel X A is ) .  
Proof . intros . apply isdecquotrel . apply isdecabmonoidfracrelint .   apply isi . apply isl . Defined . 



(** **** Relations and the canonical homomorphism to [ abmonoidfrac ] *)

Lemma iscomptoabmonoidfrac ( X : abmonoid ) ( A : @submonoids X ) { L : hrel X } ( is : ispartbinophrel A L ) : iscomprelrelfun L ( abmonoidfracrel X A is ) ( toabmonoidfrac X A ) .
Proof . intros . unfold iscomprelrelfun .  intros x x' l . change ( abmonoidfracrelint X A L ( dirprodpair x ( unel A ) ) ( dirprodpair x' ( unel A ) ) ) .    simpl . apply ( hinhpr ) .  split with ( unel A ) .  apply ( ( pr2 is ) _ _ 0 ) . apply ( pr2 ( unel A ) ) .   apply ( ( pr2 is ) _ _ 0 ) . apply ( pr2 ( unel A ) ) . apply l . Defined .

Opaque iscomptoabmonoidfrac .   



Close Scope addmonoid_scope . 



(** *** Groups *)

(** **** Basic definitions *)

Definition gr := total2 ( fun X : setwithbinop =>  isgrop ( @op X ) ) .
Definition grpair := tpair ( fun X : setwithbinop => isgrop ( @op X ) ) .
Definition grconstr := grpair .
Definition grtomonoid : gr -> monoid := fun X : _ => monoidpair ( pr1 X ) ( pr1 ( pr2 X ) ) . 
Coercion grtomonoid : gr >-> monoid .

Definition grinv ( X : gr ) : X -> X := pr1 ( pr2 ( pr2 X ) ) .
Definition grlinvax ( X : gr ) : islinv ( @op X ) ( unel X ) ( grinv X ) := pr1 ( pr2 ( pr2 ( pr2 X ) ) ) .
Definition grrinvax ( X : gr ) : isrinv ( @op X ) ( unel X ) ( grinv X ) := pr2 ( pr2 ( pr2 ( pr2 X ) ) ) .

Lemma monoidfuninvtoinv { X Y : gr } ( f : monoidfun X Y ) ( x : X ) : paths ( f ( grinv X x ) ) ( grinv Y ( f x ) ) .
Proof . intros . apply ( invmaponpathsweq ( weqpair _ ( isweqrmultingr_is ( pr2 Y ) ( f x ) ) ) ) . simpl . change ( paths (op (pr1 f (grinv X x)) (pr1 f x))
     (op (grinv Y (pr1 f x)) (pr1 f x)) ) . rewrite ( grlinvax Y ( pr1 f x) ) .  destruct ( pr1 ( pr2 f ) (grinv X x) x ) .  rewrite ( grlinvax X x ) .   apply ( pr2 ( pr2 f ) ) . Defined .  


(** **** Computation lemmas for groups *)

Definition weqlmultingr ( X : gr ) ( x0 : X ) := weqpair _ ( isweqlmultingr_is ( pr2 X ) x0 ) .

Definition weqrmultingr ( X : gr ) ( x0 : X ) := weqpair _ ( isweqrmultingr_is ( pr2 X ) x0 ) .

Lemma grlcan ( X : gr ) { a b : X } ( c : X ) ( e : paths ( op c a ) ( op c b ) ) : paths a b .
Proof . intros . apply ( invmaponpathsweq ( weqlmultingr X c ) _ _ e ) .  Defined .  

Lemma grrcan ( X : gr ) { a b : X } ( c : X ) ( e : paths ( op a c ) ( op b c ) ) : paths a b .
Proof . intros . apply ( invmaponpathsweq ( weqrmultingr X c ) _ _ e ) .  Defined .  

Lemma grinvunel ( X : gr ) : paths ( grinv X ( unel X ) ) ( unel X ) .
Proof . intro . apply ( grrcan X ( unel X ) ) . rewrite ( grlinvax X ) . rewrite ( runax X ) . apply idpath .  Defined .   

Lemma grinvinv ( X : gr ) ( a : X ) : paths ( grinv X ( grinv X a ) ) a . 
Proof . intros . apply ( grlcan X ( grinv X a ) ) .  rewrite ( grlinvax X a ) . rewrite ( grrinvax X _ ) . apply idpath . Defined . 

Lemma grinvmaponpathsinv ( X : gr ) { a b : X } ( e : paths ( grinv X a ) ( grinv X b ) ) : paths a b . 
Proof . intros . assert ( e' := maponpaths ( fun x => grinv X x ) e ) .   simpl in e' .  rewrite ( grinvinv X _ ) in e' .   rewrite ( grinvinv X _ ) in e' .  apply e'. Defined .

Lemma grinvandmonoidfun ( X Y : gr ) { f : X -> Y } ( is : ismonoidfun f ) ( x : X ) : paths ( f ( grinv X x ) ) ( grinv Y ( f x ) ) .
Proof . intros . apply ( grrcan Y ( f x ) ) .  rewrite ( pathsinv0 ( pr1 is _ _ ) ) . rewrite ( grlinvax X ) .  rewrite ( grlinvax Y ) .  apply ( pr2 is ) .  Defined . 


 

(** **** Relations on groups *)

Lemma isinvbinophrelgr ( X : gr ) { R : hrel X } ( is : isbinophrel R ) : isinvbinophrel R .
Proof . intros . set ( is1 := pr1 is ) . set ( is2 := pr2 is ) .   split . 

intros a b c r .  set ( r' := is1 _ _ ( grinv X c ) r ) . clearbody r' .  rewrite ( pathsinv0 ( assocax X _ _ a ) ) in r' .  rewrite ( pathsinv0 ( assocax X _ _ b ) ) in r' .  rewrite ( grlinvax X c ) in r' .  rewrite ( lunax X a ) in r' .   rewrite ( lunax X b ) in r' . apply r' .   

intros a b c r .  set ( r' := is2 _ _ ( grinv X c ) r ) . clearbody r' .  rewrite ( ( assocax X a _ _ ) ) in r' .  rewrite ( ( assocax X b _ _ ) ) in r' .  rewrite ( grrinvax X c ) in r' .  rewrite ( runax X a ) in r' . rewrite ( runax X b ) in r' . apply r' . Defined .

Opaque isinvbinophrelgr .

Lemma isbinophrelgr ( X : gr ) { R : hrel X } ( is : isinvbinophrel R ) : isbinophrel R .
Proof . intros . set ( is1 := pr1 is ) . set ( is2 := pr2 is ) .   split . 

intros a b c r .  rewrite ( pathsinv0 ( lunax X a ) ) in r .  rewrite ( pathsinv0 ( lunax X b ) ) in r .  rewrite ( pathsinv0 ( grlinvax X c ) ) in r .  rewrite ( assocax X _ _ a ) in r .  rewrite ( assocax X _ _ b ) in r .  apply ( is1 _ _ ( grinv X c ) r ) . 

intros a b c r . rewrite ( pathsinv0 ( runax X a ) ) in r .  rewrite ( pathsinv0 ( runax X b ) ) in r .  rewrite ( pathsinv0 ( grrinvax X c ) ) in r .  rewrite ( pathsinv0 ( assocax X a _ _ ) ) in r .  rewrite ( pathsinv0 ( assocax X b _ _ ) ) in r .  apply ( is2 _ _ ( grinv X c ) r ) .  Defined .

Opaque isbinophrelgr . 

Lemma grfromgtunel ( X : gr ) { R : hrel X } ( is : isbinophrel R ) { x : X } ( isg : R x ( unel X ) ) : R ( unel X ) ( grinv X x ) .
Proof . intros . assert ( r := ( pr2 is ) _ _ ( grinv X x ) isg ) . rewrite ( grrinvax X x ) in r .  rewrite ( lunax X _ ) in r . apply r . Defined .    

Lemma grtogtunel ( X : gr ) { R : hrel X } ( is : isbinophrel R ) { x : X } ( isg : R ( unel X ) ( grinv X x )  ) : R x ( unel X )  .
Proof . intros . assert ( r := ( pr2 is ) _ _ x isg ) . rewrite ( grlinvax X x ) in r .  rewrite ( lunax X _ ) in r . apply r . Defined .    
    
Lemma grfromltunel ( X : gr ) { R : hrel X } ( is : isbinophrel R ) { x : X } ( isg : R ( unel X ) x ) : R ( grinv X x ) ( unel X ) .
Proof . intros . assert ( r := ( pr1 is ) _ _ ( grinv X x ) isg ) . rewrite ( grlinvax X x ) in r .  rewrite ( runax X _ ) in r . apply r . Defined . 

Lemma grtoltunel ( X : gr ) { R : hrel X } ( is : isbinophrel R ) { x : X } ( isg :  R ( grinv X x ) ( unel X ) ) : R ( unel X ) x .
Proof . intros . assert ( r := ( pr1 is ) _ _ x isg ) . rewrite ( grrinvax X x ) in r .  rewrite ( runax X _ ) in r . apply r . Defined .


(** **** Subobjects *)

Definition issubgr { X : gr } ( A : hsubtypes X ) := dirprod ( issubmonoid A ) ( forall x : X , A x -> A ( grinv X x ) ) . 

Lemma isapropissubgr { X : gr } ( A : hsubtypes X ) : isaprop ( issubgr A ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropissubmonoid . apply impred . intro x .   apply impred . intro a . apply ( pr2 (A ( grinv X x)) ) . Defined . 


 

Definition subgrs { X : gr } := total2 ( fun A : hsubtypes X => issubgr A ) .
Definition subgrpair { X : gr } := tpair ( fun A : hsubtypes X => issubgr A ) . 
Definition subgrconstr { X : gr } := @subgrpair X .  
Definition subgrstosubmonoids ( X : gr ) : @subgrs X -> @submonoids X := fun A : _ => submonoidpair ( pr1 A ) ( pr1 ( pr2 A ) ) . 
Coercion subgrstosubmonoids : subgrs >-> submonoids .

Lemma isinvoncarrier { X : gr } ( A : @subgrs X ) : isinv ( @op A ) ( unel A ) ( fun a : A => carrierpair _ ( grinv X ( pr1 a ) ) ( pr2 ( pr2 A ) ( pr1 a ) ( pr2 a ) ) ) .
Proof . intros . split .

intro a .  apply ( invmaponpathsincl _ ( isinclpr1carrier A ) ) .  simpl . apply ( grlinvax X ( pr1 a ) ) .  
intro a .  apply ( invmaponpathsincl _ ( isinclpr1carrier A ) ) .  simpl . apply ( grrinvax X ( pr1 a ) ) . Defined .  

Definition isgrcarrier { X : gr } ( A : @subgrs X ) : isgrop ( @op A ) := tpair _ ( ismonoidcarrier A ) ( tpair _ ( fun a : A => carrierpair _ ( grinv X ( pr1 a ) ) ( pr2 ( pr2 A ) ( pr1 a ) ( pr2 a ) ) ) ( isinvoncarrier A ) ) . 

Definition carrierofasubgr { X : gr } ( A : @subgrs X ) : gr .
Proof . intros . split with A . apply ( isgrcarrier A ) . Defined .   


Coercion carrierofasubgr : subgrs >-> gr . 



(** **** Quotient objects *)

Lemma grquotinvcomp { X : gr } ( R : @binopeqrel X ) : iscomprelrelfun R R (grinv X) .
Proof . intros .  destruct R as [ R isb ] . set ( isc := iscompbinoptransrel _ ( eqreltrans _ ) isb  ) . unfold iscomprelrelfun .   intros x x' r .  destruct R as [ R iseq ] .  destruct iseq as [ ispo0 symm0 ] . destruct ispo0 as [ trans0 refl0 ] . unfold isbinophrel in isb .   set ( r0 := isc _ _ _ _ ( isc _ _ _ _ ( refl0 ( grinv X x' ) ) r ) ( refl0 ( grinv X x ) ) ) .   rewrite ( grlinvax X x' ) in r0 .  rewrite ( assocax X ( grinv X x' ) x ( grinv X x ) ) in r0 .  rewrite ( grrinvax X x ) in r0 . rewrite ( lunax X _ ) in r0 . rewrite ( runax X _ ) in r0 .   apply ( symm0 _ _ r0 ) .  Defined . 

Opaque grquotinvcomp . 

Definition invongrquot { X : gr } ( R : @binopeqrel X ) : setquot R -> setquot R := setquotfun R R ( grinv X ) ( grquotinvcomp R ) .
  
Lemma isinvongrquot { X : gr } ( R : @binopeqrel X ) : isinv ( @op ( setwithbinopquot R ) ) ( setquotpr R ( unel X ) ) ( invongrquot R ) . 
Proof . intros . split .

unfold islinv .  apply ( setquotunivprop R ( fun x : setwithbinopquot R, eqset (@op ( setwithbinopquot R ) (invongrquot R x) x) (setquotpr R (unel X)) ) ) .  intro x . apply ( @maponpaths _ _ ( setquotpr R ) ( @op X ( grinv X x ) x ) ( unel X ) ) .  apply ( grlinvax X ) . 

unfold isrinv .  apply ( setquotunivprop R ( fun x : setwithbinopquot R, eqset (@op ( setwithbinopquot R ) x (invongrquot R x) ) (setquotpr R (unel X)) ) ) .  intro x . apply ( @maponpaths _ _ ( setquotpr R ) ( @op X x ( grinv X x ) ) ( unel X ) ) .  apply ( grrinvax X ) . Defined .

Opaque isinvongrquot . 

Definition isgrquot { X : gr } ( R : @binopeqrel X ) : isgrop ( @op ( setwithbinopquot R ) ) := tpair _ ( ismonoidquot R ) ( tpair _ ( invongrquot R ) ( isinvongrquot R ) ) . 

Definition grquot { X : gr } ( R : @binopeqrel X ) : gr .
Proof . intros . split with ( setwithbinopquot R ) . apply isgrquot . Defined .  


(** **** Direct products *)


Lemma isgrdirprod ( X Y : gr ) : isgrop ( @op ( setwithbinopdirprod X Y ) ) .
Proof . intros . split with ( ismonoiddirprod X Y ) .  split with ( fun xy : _ => dirprodpair ( grinv X ( pr1 xy ) ) ( grinv Y ( pr2 xy ) ) ) .  split .

intro xy . destruct xy as [ x y ] .  unfold unel_is . simpl . apply pathsdirprod . apply ( grlinvax X x ) .  apply ( grlinvax Y y ) . 
intro xy . destruct xy as [ x y ] .  unfold unel_is . simpl .  apply pathsdirprod . apply ( grrinvax X x ) .  apply ( grrinvax Y y ) . Defined .

Definition grdirprod ( X Y : gr ) : gr .
Proof . intros . split with ( setwithbinopdirprod X Y ) . apply isgrdirprod . Defined .   




(** *** Abelian groups *)


(** **** Basic definitions *)


Definition abgr := total2 ( fun X : setwithbinop =>  isabgrop ( @op X ) ) .
Definition abgrpair ( X : setwithbinop ) ( is : isabgrop ( @op X ) ) : abgr  := tpair ( fun X : setwithbinop =>  isabgrop ( @op X ) ) X is .
Definition abgrconstr ( X : abmonoid ) ( inv0 : X -> X ) ( is : isinv ( @op X ) ( unel X ) inv0 ) : abgr := abgrpair X ( dirprodpair ( isgroppair ( pr2 X ) ( tpair _ inv0 is ) ) ( commax X ) ) .
Definition abgrtogr : abgr -> gr := fun X : _ => grpair ( pr1 X ) ( pr1 ( pr2 X ) ) . 
Coercion abgrtogr : abgr >-> gr .

Definition abgrtoabmonoid : abgr -> abmonoid := fun X : _ => abmonoidpair ( pr1 X ) ( dirprodpair ( pr1 ( pr1 ( pr2 X ) ) ) ( pr2 ( pr2 X ) ) )  .  
Coercion abgrtoabmonoid : abgr >-> abmonoid .


(** **** Subobjects *)


Definition subabgrs { X : abgr } := @subgrs X .
Identity Coercion id_subabgrs : subabgrs >-> subgrs .

Lemma isabgrcarrier { X : abgr } ( A : @subgrs X ) : isabgrop ( @op A ) .
Proof . intros . split with ( isgrcarrier A ) . apply ( pr2 ( @isabmonoidcarrier X A ) ) .  Defined . 

Definition carrierofasubabgr { X : abgr } ( A : @subabgrs X ) : abgr .
Proof . intros . split with A . apply isabgrcarrier .  Defined . 

Coercion carrierofasubabgr : subabgrs >-> abgr . 



(** **** Quotient objects *)

Lemma isabgrquot { X : abgr } ( R : @binopeqrel X ) : isabgrop ( @op ( setwithbinopquot R ) ) .
Proof . intros . split with ( isgrquot R ) . apply ( pr2 ( @isabmonoidquot X R ) ) .  Defined . 


Definition abgrquot { X : abgr } ( R : @binopeqrel X ) : abgr .
Proof . intros . split with ( setwithbinopquot R ) . apply isabgrquot . Defined . 


(** **** Direct products *)

Lemma isabgrdirprod ( X Y : abgr ) : isabgrop ( @op ( setwithbinopdirprod X Y ) ) .
Proof . intros . split with ( isgrdirprod X Y ) .  apply ( pr2 ( isabmonoiddirprod X Y ) ) .  Defined . 

Definition abgrdirprod ( X Y : abgr ) : abgr .
Proof . intros . split with ( setwithbinopdirprod X Y ) . apply isabgrdirprod . Defined . 


(** **** Abelian group of fractions of an abelian unitary monoid *)

Open Scope addmonoid_scope . 

Definition hrelabgrfrac ( X : abmonoid ) : hrel ( dirprod X X ) := fun xa1 xa2 => hexists ( fun x0 : X =>  paths ( ( ( pr1 xa1 ) + ( pr2 xa2 ) ) + x0 )  ( ( ( pr1 xa2 ) + ( pr2 xa1 ) ) + x0 ) ) . 

Definition abgrfracphi ( X : abmonoid ) ( xa : dirprod X X ) : dirprod X ( totalsubtype X ) := dirprodpair ( pr1 xa ) ( carrierpair ( fun x : X => htrue ) ( pr2 xa ) tt ) .  

Definition hrelabgrfrac' ( X : abmonoid ) : hrel ( dirprod X X ) :=  fun xa1 xa2 =>  eqrelabmonoidfrac X ( totalsubmonoid X ) ( abgrfracphi X xa1 ) ( abgrfracphi X xa2 )  .

Lemma logeqhrelsabgrfrac ( X : abmonoid ) : hrellogeq ( hrelabgrfrac' X ) ( hrelabgrfrac X ) . 
Proof . intros . split . simpl . apply hinhfun . intro t2 .  set ( a0 := pr1 ( pr1 t2 ) ) . split with a0 . apply ( pr2 t2 ) .  simpl . apply hinhfun . intro t2 . set ( x0 := pr1 t2 ) . split with ( tpair _ x0 tt ) .  apply ( pr2 t2 ) .  Defined . 


Lemma iseqrelabgrfrac ( X : abmonoid ) : iseqrel ( hrelabgrfrac X ) .
Proof . intro . apply ( iseqrellogeqf ( logeqhrelsabgrfrac X ) ) .   apply ( iseqrelconstr ) . intros xx' xx'' xx''' . intros r1 r2 . apply ( eqreltrans ( eqrelabmonoidfrac X ( totalsubmonoid X ) ) _ _ _ r1 r2 ) . intro xx. apply ( eqrelrefl ( eqrelabmonoidfrac X ( totalsubmonoid X ) ) _ ) . intros xx xx' .  intro r . apply ( eqrelsymm ( eqrelabmonoidfrac X ( totalsubmonoid X ) ) _ _ r ) . Defined .

Opaque iseqrelabgrfrac . 

Definition eqrelabgrfrac ( X : abmonoid ) : @eqrel ( abmonoiddirprod X X ) := eqrelpair _ ( iseqrelabgrfrac X ) .

Lemma isbinophrelabgrfrac ( X : abmonoid ) : @isbinophrel ( abmonoiddirprod X X ) ( hrelabgrfrac X ) .
Proof . intro .  apply ( @isbinophrellogeqf ( abmonoiddirprod X X ) _ _ ( logeqhrelsabgrfrac X ) ) . split . intros a b c r . apply ( pr1 ( isbinophrelabmonoidfrac X ( totalsubmonoid X ) ) _ _ ( dirprodpair ( pr1 c ) ( carrierpair ( fun x : X => htrue ) ( pr2 c ) tt ) ) r ) .  intros a b c r . apply ( pr2 ( isbinophrelabmonoidfrac X ( totalsubmonoid X ) ) _ _ ( dirprodpair ( pr1 c ) ( carrierpair ( fun x : X => htrue ) ( pr2 c ) tt ) ) r ) .   Defined .  

Opaque isbinophrelabgrfrac .

Definition binopeqrelabgrfrac ( X : abmonoid ) : @binopeqrel ( abmonoiddirprod X X ) := binopeqrelpair ( eqrelabgrfrac X ) ( isbinophrelabgrfrac X ) .

Definition abgrfraccarrier ( X : abmonoid ) : abmonoid := @abmonoidquot ( abmonoiddirprod X X ) ( binopeqrelabgrfrac X ) .

Definition abgrfracinvint ( X : abmonoid ) :  dirprod X X -> dirprod X X := fun xs : _ => dirprodpair ( pr2 xs ) ( pr1 xs ) . 

Lemma  abgrfracinvcomp ( X : abmonoid ) : iscomprelrelfun ( hrelabgrfrac X ) ( eqrelabgrfrac X ) ( abgrfracinvint X ) .   
Proof . intros .  unfold iscomprelrelfun . unfold eqrelabgrfrac . unfold hrelabgrfrac .   unfold eqrelabmonoidfrac .  unfold hrelabmonoidfrac . simpl . intros xs xs' .  apply ( hinhfun ) .   intro tt0 . set ( x := pr1 xs ) .  set ( s := pr2 xs ) . set ( x' := pr1 xs' ) . set ( s' := pr2 xs' ) . split with ( pr1 tt0 ) . destruct tt0 as [ a eq ] .  change ( paths ( s + x' + a ) ( s' + x + a ) ) .  apply pathsinv0 . simpl . set  ( e := commax X s' x ) . simpl in e . rewrite e . clear e . set  ( e := commax X s x' ) . simpl in e . rewrite e .    clear e.  apply eq . Defined . 

Opaque abgrfracinvcomp . 

Definition abgrfracinv ( X : abmonoid ) : abgrfraccarrier X -> abgrfraccarrier X := setquotfun ( hrelabgrfrac X ) ( eqrelabgrfrac X ) ( abgrfracinvint X ) ( abgrfracinvcomp X ) .   

Lemma abgrfracisinv ( X : abmonoid ) : isinv ( @op ( abgrfraccarrier X ) ) ( unel ( abgrfraccarrier X ) ) ( abgrfracinv X ) . 
Proof . intros . set ( R := eqrelabgrfrac X ) . 

assert ( isl : islinv ( @op ( abgrfraccarrier X ) ) ( unel ( abgrfraccarrier X ) ) ( abgrfracinv X ) ) .  unfold islinv . apply ( setquotunivprop R  ( fun x : abgrfraccarrier X => eqset (abgrfracinv X x + x) (unel (abgrfraccarrier X)) ) ) . intro xs . set ( x := pr1 xs ) .  set ( s := pr2 xs ) . apply ( iscompsetquotpr R ( @op ( abmonoiddirprod X X  ) ( abgrfracinvint X xs ) xs ) ( unel _ ) ) .  simpl . apply hinhpr . split with ( unel X ) . change ( paths ( s + x + ( unel X ) + ( unel X ) ) ( ( unel X ) + ( x + s ) + ( unel X ) ) ) .   destruct ( commax X x s ) .  destruct ( commax X ( unel X ) ( x + s ) ) . apply idpath .

apply ( dirprodpair isl ( weqlinvrinv ( @op ( abgrfraccarrier X ) ) ( commax ( abgrfraccarrier X ) ) ( unel ( abgrfraccarrier X ) ) ( abgrfracinv X ) isl ) ) .   Defined . 


Opaque abgrfracisinv . 

Definition abgrfrac ( X : abmonoid ) : abgr := abgrconstr ( abgrfraccarrier X ) ( abgrfracinv X ) ( abgrfracisinv X ) .  

Definition prabgrfrac ( X : abmonoid ) : X -> X -> abgrfrac X := fun x x' : X => setquotpr ( eqrelabgrfrac X ) ( dirprodpair x x' ) .



(** **** Abelian group of fractions and abelian monoid of fractions *)

Definition weqabgrfracint ( X : abmonoid ) : weq ( dirprod X X ) ( dirprod X ( totalsubtype X ) ) := weqdirprodf ( idweq X ) ( invweq ( weqtotalsubtype X ) ) . 

Definition weqabgrfrac ( X : abmonoid ) : weq ( abgrfrac X ) ( abmonoidfrac X ( totalsubmonoid X ) ) .
Proof . intros . apply ( weqsetquotweq ( eqrelabgrfrac X ) ( eqrelabmonoidfrac  X ( totalsubmonoid X ) ) ( weqabgrfracint X ) ) .   

simpl .  intros x x' .  destruct x as [ x1 x2 ] . destruct x' as [ x1' x2' ] . simpl in * . apply hinhfun . intro tt0 . destruct tt0 as [ xx0 is0 ] .   split with ( carrierpair ( fun x : X => htrue ) xx0 tt  ) .  apply is0 .

simpl .  intros x x' .  destruct x as [ x1 x2 ] . destruct x' as [ x1' x2' ] . simpl in * . apply hinhfun . intro tt0 . destruct tt0 as [ xx0 is0 ] .   split with ( pr1 xx0 ) .  apply is0 . 
Defined . 




(** **** Canonical homomorphism to the abelian group of fractions *)

Definition toabgrfrac ( X : abmonoid ) ( x : X ) : abgrfrac X := setquotpr _ ( dirprodpair x ( unel X ) ) . 

Lemma isbinopfuntoabgrfrac ( X : abmonoid ) : isbinopfun ( toabgrfrac X ) .
Proof . intros . unfold isbinopfun . intros x1 x2 .  change ( paths ( setquotpr _ ( dirprodpair ( x1 + x2 ) ( unel X ) ) ) ( setquotpr ( eqrelabgrfrac X ) ( dirprodpair ( x1 + x2 ) ( ( unel X ) + ( unel X ) ) ) ) ) .  apply ( maponpaths ( setquotpr _  ) ) .  apply ( @pathsdirprod X X ) . apply idpath .  apply ( pathsinv0 ( lunax X 0 ) ) . Defined . 

Lemma isunitalfuntoabgrfrac ( X : abmonoid )  : paths ( toabgrfrac X ( unel X ) ) ( unel ( abgrfrac X ) ) .
Proof . intros . apply idpath . Defined .  

Definition ismonoidfuntoabgrfrac ( X : abmonoid ) : ismonoidfun ( toabgrfrac X ) := dirprodpair ( isbinopfuntoabgrfrac X ) ( isunitalfuntoabgrfrac X ) .





(** **** Abelian group of fractions in the case when all elements are cancelable *) 


Lemma isinclprabgrfrac ( X : abmonoid ) ( iscanc : forall x : X , isrcancelable ( @op X ) x ) : forall x' : X , isincl ( fun x => prabgrfrac X x x' ) .
Proof . intros . set ( int := isinclprabmonoidfrac X ( totalsubmonoid X ) ( fun a : totalsubmonoid X => iscanc ( pr1 a ) ) ( carrierpair ( fun x : X => htrue ) x' tt ) ) . 
set ( int1 := isinclcomp ( inclpair _ int ) ( invweq ( weqabgrfrac X ) ) ) . apply int1 .  Defined . 

Definition isincltoabgrfrac ( X : abmonoid ) ( iscanc : forall x : X , isrcancelable ( @op X ) x ) : isincl ( toabgrfrac X ) := isinclprabgrfrac X iscanc ( unel X ) . 

Lemma isdeceqabgrfrac ( X : abmonoid ) ( iscanc : forall x : X , isrcancelable ( @op X ) x ) ( is : isdeceq X ) : isdeceq ( abgrfrac X ) .
Proof . intros . apply ( isdeceqweqf ( invweq ( weqabgrfrac X ) ) ) .   apply ( isdeceqabmonoidfrac X ( totalsubmonoid X ) ( fun a : totalsubmonoid X => iscanc ( pr1 a ) ) is ) . Defined .  







(** **** Relations on the abelian group of fractions *) 

Definition abgrfracrelint ( X : abmonoid ) ( L : hrel X ) : hrel ( setwithbinopdirprod X X ) := fun xa yb => hexists ( fun c0 : X => L ( ( ( pr1 xa ) + ( pr2 yb ) ) + c0 ) ( ( ( pr1 yb ) + ( pr2 xa ) ) + c0 ) ) .

Definition abgrfracrelint' ( X : abmonoid ) ( L : hrel X ) : hrel ( setwithbinopdirprod X X ) := fun xa1 xa2 => abmonoidfracrelint _ ( totalsubmonoid X ) L ( abgrfracphi X xa1 )  ( abgrfracphi X xa2 ) . 

Lemma logeqabgrfracrelints ( X : abmonoid ) ( L : hrel X ) : hrellogeq ( abgrfracrelint' X L ) ( abgrfracrelint X L ) .
Proof . intros . split . unfold abgrfracrelint . unfold abgrfracrelint' . simpl .  apply hinhfun .  intro t2 .  set ( a0 := pr1 ( pr1 t2 ) ) . split with a0 . apply ( pr2 t2 ) .  simpl . apply hinhfun . intro t2 . set ( x0 := pr1 t2 ) . split with ( tpair _ x0 tt ) .  apply ( pr2 t2 ) .  Defined .

Lemma iscomprelabgrfracrelint ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) : iscomprelrel ( eqrelabgrfrac X ) ( abgrfracrelint X L ) . 
Proof . intros . apply ( iscomprelrellogeqf1 _ ( logeqhrelsabgrfrac X ) ) . apply ( iscomprelrellogeqf2 _ ( logeqabgrfracrelints X L ) ) .  intros x x' x0 x0' r r0 .  apply ( iscomprelabmonoidfracrelint _ ( totalsubmonoid X ) ( isbinoptoispartbinop _ _ is )  _ _ _ _ r r0 ) .  Defined . 

Opaque iscomprelabgrfracrelint . 

Definition abgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) := quotrel ( iscomprelabgrfracrelint X is ) .

Definition abgrfracrel' ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) : hrel ( abgrfrac X ) := fun x x' => abmonoidfracrel X ( totalsubmonoid X ) ( isbinoptoispartbinop _ _ is ) ( weqabgrfrac X x ) ( weqabgrfrac X x' )  .
 
Definition logeqabgrfracrels ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) : hrellogeq ( abgrfracrel' X is ) ( abgrfracrel X is ) .
Proof . intros X L is x1 x2 . split . 

assert ( int : forall x x' , isaprop ( abgrfracrel' X is x x' -> abgrfracrel X is x x' ) ) . intros x x' . apply impred . intro . apply ( pr2 _ ) . generalize x1 x2 . clear x1 x2 . apply ( setquotuniv2prop _ ( fun x x' => hProppair _ ( int x x' ) ) ) . intros x x' .  change ( ( abgrfracrelint' X L x x' )  -> ( abgrfracrelint _ L x x' ) ) . apply ( pr1 ( logeqabgrfracrelints X L x x' ) ) . 


assert ( int : forall x x' , isaprop ( abgrfracrel X is x x' -> abgrfracrel' X is x x' ) ) . intros x x' . apply impred . intro . apply ( pr2 _ ) .   generalize x1 x2 . clear x1 x2 . apply ( setquotuniv2prop _ ( fun x x' => hProppair _ ( int x x' ) ) ) . intros x x' .  change ( ( abgrfracrelint X L x x' )  -> ( abgrfracrelint' _ L x x' ) ) . apply ( pr2 ( logeqabgrfracrelints X L x x' ) ) . Defined . 


Lemma istransabgrfracrelint ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : istrans L ) : istrans ( abgrfracrelint X L ) .
Proof . intros .  apply ( istranslogeqf ( logeqabgrfracrelints X L ) ) .  intros a b c rab rbc . apply ( istransabmonoidfracrelint _ ( totalsubmonoid X ) ( isbinoptoispartbinop _ _ is ) isl _ _ _ rab rbc ) .  Defined . 

Opaque istransabgrfracrelint . 

Lemma istransabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : istrans L ) : istrans ( abgrfracrel X is ) .
Proof . intros . apply istransquotrel .  apply istransabgrfracrelint . apply is . apply isl . Defined . 


Lemma issymmabgrfracrelint ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : issymm L ) : issymm ( abgrfracrelint X L ) .
Proof . intros . apply ( issymmlogeqf ( logeqabgrfracrelints X L ) ) .  intros a b rab . apply ( issymmabmonoidfracrelint _ ( totalsubmonoid X ) ( isbinoptoispartbinop _ _ is ) isl _ _ rab ) .  Defined . 

Opaque issymmabgrfracrelint .

Lemma issymmabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : issymm L ) : issymm ( abgrfracrel X is ) .
Proof . intros .  apply issymmquotrel . apply issymmabgrfracrelint .  apply is . apply isl . Defined . 

Lemma isreflabgrfracrelint ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : isrefl L ) : isrefl ( abgrfracrelint X L ) .
Proof . intros . intro xa . unfold abgrfracrelint .  simpl . apply hinhpr . split with ( unel X ) .  apply ( isl _ ) . Defined .

Lemma isreflabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : isrefl L ) : isrefl ( abgrfracrel X is ) .
Proof . intros .  apply isreflquotrel . apply isreflabgrfracrelint .  apply is . apply isl . Defined . 

Lemma ispoabgrfracrelint ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : ispo L ) : ispo ( abgrfracrelint X L ) .
Proof . intros . split with ( istransabgrfracrelint X is ( pr1 isl ) ) .  apply ( isreflabgrfracrelint X is ( pr2 isl ) ) .  Defined . 

Lemma ispoabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : ispo L ) : ispo ( abgrfracrel X is ) .
Proof . intros .  apply ispoquotrel . apply ispoabgrfracrelint .  apply is . apply isl . Defined . 

Lemma iseqrelabgrfracrelint ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : iseqrel L ) : iseqrel ( abgrfracrelint X L ) .
Proof . intros . split with ( ispoabgrfracrelint X is ( pr1 isl ) ) .  apply ( issymmabgrfracrelint X is ( pr2 isl ) ) .  Defined . 

Lemma iseqrelabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : iseqrel L ) : iseqrel ( abgrfracrel X is ) .
Proof . intros .  apply iseqrelquotrel . apply iseqrelabgrfracrelint .  apply is . apply isl . Defined .


Lemma isantisymmnegabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : isantisymmneg L ) : isantisymmneg ( abgrfracrel X is ) .
Proof . intros . apply ( isantisymmneglogeqf ( logeqabgrfracrels X is ) ) .  intros a b rab rba . set ( int := isantisymmnegabmonoidfracrel _ ( totalsubmonoid X ) ( isbinoptoispartbinop _ _ is ) isl ( weqabgrfrac X a ) ( weqabgrfrac X b ) rab rba ) . apply ( invmaponpathsweq _ _ _ int ) .  Defined . 

Lemma isantisymmabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : isantisymm L ) : isantisymm ( abgrfracrel X is ) .
Proof . intros . apply ( isantisymmlogeqf ( logeqabgrfracrels X is ) ) .  intros a b rab rba . set ( int := isantisymmabmonoidfracrel _ ( totalsubmonoid X ) ( isbinoptoispartbinop _ _ is ) isl ( weqabgrfrac X a ) ( weqabgrfrac X b ) rab rba ) . apply ( invmaponpathsweq _ _ _ int ) .  Defined .

Opaque  isantisymmabgrfracrel .


Lemma isirreflabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : isirrefl L ) : isirrefl ( abgrfracrel X is ) .
Proof . intros .  apply ( isirrefllogeqf ( logeqabgrfracrels X is ) ) .  intros a raa . apply ( isirreflabmonoidfracrel _ ( totalsubmonoid X ) ( isbinoptoispartbinop _ _ is ) isl ( weqabgrfrac X a ) raa ) . Defined .

Opaque isirreflabgrfracrel .


Lemma isasymmabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : isasymm L ) : isasymm ( abgrfracrel X is ) .
Proof . intros . apply ( isasymmlogeqf ( logeqabgrfracrels X is ) ) .  intros a b rab rba . apply ( isasymmabmonoidfracrel _ ( totalsubmonoid X ) ( isbinoptoispartbinop _ _ is ) isl ( weqabgrfrac X a ) ( weqabgrfrac X b ) rab rba ) . Defined .

Opaque  isasymmabgrfracrel .

Lemma iscoasymmabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : iscoasymm L ) : iscoasymm ( abgrfracrel X is ) .
Proof . intros . apply ( iscoasymmlogeqf ( logeqabgrfracrels X is ) ) .  intros a b rab . apply ( iscoasymmabmonoidfracrel _ ( totalsubmonoid X ) ( isbinoptoispartbinop _ _ is ) isl ( weqabgrfrac X a ) ( weqabgrfrac X b ) rab ) .  Defined .

Opaque  iscoasymmabgrfracrel .

Lemma istotalabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : istotal L ) : istotal ( abgrfracrel X is ) .
Proof . intros . apply ( istotallogeqf ( logeqabgrfracrels X is ) ) .  intros a b . apply ( istotalabmonoidfracrel _ ( totalsubmonoid X ) ( isbinoptoispartbinop _ _ is ) isl ( weqabgrfrac X a ) ( weqabgrfrac X b ) ) . Defined .

Opaque istotalabgrfracrel . 

Lemma iscotransabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isl : iscotrans L ) : iscotrans ( abgrfracrel X is ) .
Proof . intros . apply ( iscotranslogeqf ( logeqabgrfracrels X is ) ) .  intros a b c . apply ( iscotransabmonoidfracrel _ ( totalsubmonoid X ) ( isbinoptoispartbinop _ _ is ) isl ( weqabgrfrac X a ) ( weqabgrfrac X b ) ( weqabgrfrac X c ) ) . Defined .

Opaque iscotransabgrfracrel . 




Lemma abgrfracrelimpl ( X : abmonoid ) { L L' : hrel X } ( is : isbinophrel L ) ( is' : isbinophrel L' )  ( impl : forall x x' , L x x' -> L' x x' ) ( x x' : abgrfrac X ) ( ql : abgrfracrel X is x x' ) : abgrfracrel X is' x x'  .
Proof . intros .   generalize ql .  apply quotrelimpl .  intros x0 x0' .  simpl .  apply hinhfun .  intro t2 . split with ( pr1 t2 ) .   apply ( impl _ _ ( pr2 t2 ) ) . Defined . 


Opaque abgrfracrelimpl . 


Lemma abgrfracrellogeq ( X : abmonoid ) { L L' : hrel X } ( is : isbinophrel L ) ( is' : isbinophrel L' )  ( lg : forall x x' , L x x' <-> L' x x' ) ( x x' : abgrfrac X ) :  ( abgrfracrel X is x x' ) <-> ( abgrfracrel X is' x x' ) .
Proof . intros .   apply quotrellogeq .  intros x0 x0' .  split . 

simpl .  apply hinhfun .  intro t2 . split with ( pr1 t2 ) .   apply ( pr1 ( lg _ _ ) ( pr2 t2 ) ) .
simpl .  apply hinhfun .  intro t2 . split with ( pr1 t2 ) .   apply ( pr2 ( lg _ _ ) ( pr2 t2 ) ) . Defined . 

Opaque abgrfracrellogeq . 
  

Lemma isbinopabgrfracrelint ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) : @isbinophrel ( setwithbinopdirprod X X ) ( abgrfracrelint X L ) . 
Proof . intros . apply ( isbinophrellogeqf ( logeqabgrfracrelints X L ) ) . split .  

intros a b c lab . apply ( pr1 ( ispartbinopabmonoidfracrelint _ ( totalsubmonoid X ) ( isbinoptoispartbinop _ _ is ) ) ( abgrfracphi X a ) ( abgrfracphi X b ) ( abgrfracphi X c ) tt lab ) . 

intros a b c lab . apply ( pr2 ( ispartbinopabmonoidfracrelint _ ( totalsubmonoid X ) ( isbinoptoispartbinop _ _ is ) ) ( abgrfracphi X a ) ( abgrfracphi X b ) ( abgrfracphi X c ) tt lab ) . Defined . 

Opaque isbinopabgrfracrelint . 

Lemma isbinopabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) : @isbinophrel ( abgrfrac X ) ( abgrfracrel X is ) . 
Proof . intros . apply ( isbinopquotrel ( binopeqrelabgrfrac X ) ( iscomprelabgrfracrelint X is ) ) . apply ( isbinopabgrfracrelint X is ) .  Defined . 


Definition isdecabgrfracrelint ( X : abmonoid ) { L : hrel X } ( is : isinvbinophrel L ) ( isl : isdecrel L ) : isdecrel ( abgrfracrelint X L ) . 
Proof . intros . intros xa1 xa2 .  set ( x1 := pr1 xa1 ) . set ( a1 := pr2 xa1 ) .  set ( x2 := pr1 xa2 ) . set ( a2 := pr2 xa2 ) .  assert ( int : coprod ( L ( x1 + a2 ) ( x2 + a1 ) ) ( neg ( L ( x1 + a2 ) ( x2 + a1 ) ) ) )  . apply ( isl _ _ ) . destruct int as [ l | nl ] .  apply ii1 . unfold abgrfracrelint .  apply hinhpr .  split with ( unel X ) .  rewrite ( runax X _ ) .   rewrite ( runax X _ ) . apply l . apply ii2 . generalize nl . clear nl . apply negf . unfold abgrfracrelint .   simpl .  apply ( @hinhuniv _ ( hProppair _ ( pr2 ( L _ _ ) ) ) ) .   intro t2l . destruct t2l as [ c0a l ] . simpl . apply ( ( pr2 is ) _ _ c0a l ) .  Defined . 

Definition isdecabgrfracrel ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) ( isi : isinvbinophrel L ) ( isl : isdecrel L ) : isdecrel ( abgrfracrel X is ) .  
Proof . intros . apply isdecquotrel . apply isdecabgrfracrelint .   apply isi . apply isl . Defined .  


(** **** Relations and the canonical homomorphism to [ abgrfrac ] *)

Lemma iscomptoabgrfrac ( X : abmonoid ) { L : hrel X } ( is : isbinophrel L ) : iscomprelrelfun L ( abgrfracrel X is ) ( toabgrfrac X ) .
Proof . intros . unfold iscomprelrelfun .  intros x x' l . change ( abgrfracrelint X L ( dirprodpair x ( unel X ) ) ( dirprodpair x' ( unel X ) ) ) .    simpl . apply ( hinhpr ) .  split with ( unel X ) .  apply ( ( pr2 is ) _ _ 0 ) .   apply ( ( pr2 is ) _ _ 0 ) .  apply l . Defined .

Opaque iscomptoabgrfrac .   




Close Scope addmonoid_scope . 











(* End of the file algebra1b.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)