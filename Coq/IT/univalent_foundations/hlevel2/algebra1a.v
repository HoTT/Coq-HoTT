(** * Algebra 1 . Part A .  Generalities. Vladimir Voevodsky. Aug. 2011 - . 

*)



(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)


(** Imports *)

Require Export hSet .


(** To upstream files *)



(** ** Sets with one and two binary operations *)

(** *** Binary operations *)

(** **** General definitions *)

Definition binop ( X : UU0 ) := X -> X -> X .

Definition islcancelable { X : UU0 } ( opp : binop X ) ( x : X ) := isincl ( fun x0 : X => opp x x0 ) .

Definition isrcancelable { X : UU0 } ( opp : binop X ) ( x : X ) := isincl ( fun x0 : X => opp x0 x ) .

Definition iscancelable { X : UU0 } ( opp : binop X ) ( x : X )  := dirprod ( islcancelable opp x ) ( isrcancelable opp x ) . 

Definition islinvertible { X : UU0 } ( opp : binop X ) ( x : X ) := isweq ( fun x0 : X => opp x x0 ) .

Definition isrinvertible { X : UU0 } ( opp : binop X ) ( x : X ) := isweq ( fun x0 : X => opp x0 x ) .

Definition isinvertible { X : UU0 } ( opp : binop X ) ( x : X ) := dirprod ( islinvertible opp x ) ( isrinvertible opp x ) . 



(** **** Standard conditions on one binary operation on a set *)

(** *)

Definition isassoc { X : hSet} ( opp : binop X ) := forall x x' x'' , paths ( opp ( opp x x' ) x'' ) ( opp x ( opp x' x'' ) ) .

Lemma isapropisassoc { X : hSet } ( opp : binop X ) : isaprop ( isassoc opp ) .
Proof . intros . apply impred . intro x . apply impred . intro x' . apply impred . intro x'' . simpl . apply ( setproperty X ) . Defined .

(** *)

Definition islunit { X : hSet} ( opp : binop X ) ( un0 : X ) := forall x : X , paths ( opp un0 x ) x .

Lemma isapropislunit { X : hSet} ( opp : binop X ) ( un0 : X ) : isaprop ( islunit opp un0 ) . 
Proof . intros . apply impred . intro x . simpl . apply ( setproperty X ) .  Defined .  

Definition isrunit { X : hSet} ( opp : binop X ) ( un0 : X ) := forall x : X , paths ( opp x un0 ) x  .

Lemma isapropisrunit { X : hSet} ( opp : binop X ) ( un0 : X ) : isaprop ( isrunit opp un0 ) .
Proof . intros . apply impred . intro x . simpl . apply ( setproperty X ) .  Defined .  

Definition isunit { X : hSet} ( opp : binop X ) ( un0 : X ) := dirprod ( islunit opp un0 ) ( isrunit opp un0 ) .

Definition isunital { X : hSet} ( opp : binop X ) := total2 ( fun un0 : X => isunit opp un0 ) .
Definition isunitalpair { X : hSet } { opp : binop X } ( un0 : X ) ( is : isunit opp un0 ) : isunital opp := tpair _ un0 is .  

Lemma isapropisunital { X : hSet} ( opp : binop X )  : isaprop ( isunital opp ) .
Proof . intros .  apply ( @isapropsubtype X ( fun un0 : _ => hconj ( hProppair _ ( isapropislunit opp un0 ) ) ( hProppair _ ( isapropisrunit opp un0 ) ) ) )  .  intros u1 u2 .  intros ua1 ua2 .  apply ( pathscomp0 ( pathsinv0 ( pr2 ua2 u1 ) ) ( pr1 ua1 u2 ) ) .  Defined . 


(** *)

Definition ismonoidop { X : hSet } ( opp : binop X ) := dirprod ( isassoc opp ) ( isunital opp ) .
Definition assocax_is { X : hSet } { opp : binop X } : ismonoidop opp -> isassoc opp := @pr1 _ _ .  
Definition unel_is { X : hSet } { opp : binop X } ( is : ismonoidop opp ) : X := pr1 ( pr2 is ) .
Definition lunax_is { X : hSet } { opp : binop X } ( is : ismonoidop opp ) := pr1 ( pr2 ( pr2 is ) ) . 
Definition runax_is { X : hSet } { opp : binop X } ( is : ismonoidop opp ) := pr2 ( pr2 ( pr2 is ) ) . 


Lemma isapropismonoidop { X : hSet } ( opp : binop X ) : isaprop ( ismonoidop opp ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply ( isapropisassoc ) .  apply ( isapropisunital ) .  Defined .  



(** *)

Definition islinv { X : hSet } ( opp : binop X ) ( un0 : X ) ( inv0 : X -> X ) := forall x : X , paths ( opp ( inv0 x ) x ) un0 .

Lemma isapropislinv { X : hSet } ( opp : binop X ) ( un0 : X ) ( inv0 : X -> X ) : isaprop ( islinv opp un0 inv0 ) .
Proof . intros . apply impred . intro x .  apply ( setproperty X (opp (inv0 x) x) un0 ) . Defined .

Definition isrinv { X : hSet } ( opp : binop X ) ( un0 : X ) ( inv0 : X -> X ) := forall x : X , paths ( opp x ( inv0 x ) ) un0 .

Lemma isapropisrinv { X : hSet } ( opp : binop X ) ( un0 : X ) ( inv0 : X -> X ) : isaprop ( isrinv opp un0 inv0 ) .
Proof . intros . apply impred . intro x .  apply ( setproperty X ) . Defined .

Definition isinv { X : hSet } ( opp : binop X ) ( un0 : X ) ( inv0 : X -> X ) := dirprod ( islinv opp un0 inv0 ) ( isrinv opp un0 inv0 ) . 

Lemma isapropisinv { X : hSet } ( opp : binop X ) ( un0 : X ) ( inv0 : X -> X ) : isaprop ( isinv opp un0 inv0 ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropislinv .  apply isapropisrinv . Defined .  

Definition invstruct { X : hSet } ( opp : binop X ) ( is : ismonoidop opp  ) := total2 ( fun inv0 : X -> X =>  isinv opp ( unel_is is ) inv0 ) .

Definition isgrop { X : hSet } ( opp : binop X ) := total2 ( fun is : ismonoidop opp => invstruct opp is ) .
Definition isgroppair { X : hSet } { opp : binop X } ( is1 : ismonoidop opp ) ( is2 : invstruct opp is1 ) : isgrop opp := tpair ( fun is : ismonoidop opp => invstruct opp is ) is1 is2 . 
Definition pr1isgrop ( X : hSet ) ( opp : binop X ) : isgrop opp -> ismonoidop opp := @pr1 _ _ .
Coercion pr1isgrop : isgrop >-> ismonoidop . 

Definition grinv_is { X : hSet } { opp : binop X } ( is : isgrop opp ) : X -> X := pr1 ( pr2 is ) . 

Definition grlinvax_is { X : hSet } { opp : binop X } ( is : isgrop opp ) := pr1 ( pr2 ( pr2 is ) ) . 

Definition grrinvax_is { X : hSet } { opp : binop X } ( is : isgrop opp ) := pr2 ( pr2 ( pr2 is ) ) . 


Lemma isweqrmultingr_is { X : hSet } { opp : binop X } ( is : isgrop opp ) ( x0 : X ) : isrinvertible opp x0 .
Proof . intros .  destruct is as [ is istr ] . set ( f := fun x : X => opp x x0 ) . set ( g := fun x : X , opp x ( ( pr1 istr ) x0 ) ) .  destruct is as [ assoc isun0 ] . destruct istr as [ inv0 axs ] .   destruct isun0 as [ un0 unaxs ] .  simpl in * |-  . 
assert ( egf : forall x : _ , paths ( g ( f x ) ) x ) . intro x . unfold f . unfold g . destruct ( pathsinv0 ( assoc x x0 ( inv0 x0 ) ) ) .  assert ( e := pr2 axs x0 ) .   simpl in e . rewrite e . apply ( pr2 unaxs x ) .  
assert ( efg : forall x : _ , paths ( f ( g x ) ) x ) . intro x .  unfold f . unfold g . destruct ( pathsinv0 ( assoc x ( inv0 x0 ) x0 ) ) . assert ( e := pr1 axs x0 ) . simpl in e . rewrite e . apply ( pr2 unaxs x ) .  
apply ( gradth _ _ egf efg ) . Defined .  

Lemma isweqlmultingr_is { X : hSet } { opp : binop X } ( is : isgrop opp )  ( x0 : X ) : islinvertible opp x0 .
Proof . intros .   destruct is as [ is istr ] .  set ( f := fun x : X => opp x0 x ) . set ( g := fun x : X , opp ( ( pr1 istr ) x0 ) x ) .  destruct is as [ assoc isun0 ] . destruct istr as [ inv0 axs ] .  destruct isun0 as [ un0 unaxs ] .  simpl in * |-  . 
assert ( egf : forall x : _ , paths ( g ( f x ) ) x ) . intro x . unfold f . unfold g . destruct ( assoc ( inv0 x0 ) x0 x  ) . assert ( e := pr1 axs x0 ) . simpl in e . rewrite e . apply ( pr1 unaxs x ) .  
assert ( efg : forall x : _ , paths ( f ( g x ) ) x ) . intro x . unfold f . unfold g . destruct ( assoc x0 ( inv0 x0 ) x  ) . assert ( e := pr2 axs x0 ) . simpl in e . rewrite e . apply ( pr1 unaxs x ) .  
apply ( gradth _ _ egf efg ) . Defined .  


Lemma isapropinvstruct { X : hSet } { opp : binop X } ( is : ismonoidop opp ) : isaprop ( invstruct opp is ) . 
Proof . intros . apply isofhlevelsn . intro is0 . set ( un0 := pr1 ( pr2 is ) ) . assert ( int : forall i : X -> X , isaprop ( dirprod ( forall x : X , paths ( opp ( i x ) x ) un0 ) ( forall x : X , paths ( opp x ( i x ) ) un0 ) ) ) . intro i . apply ( isofhleveldirprod 1 ) .  apply impred . intro x .  simpl . apply ( setproperty X  ) . apply impred . intro x .   simpl .  apply ( setproperty X ) . apply ( isapropsubtype ( fun i : _ => hProppair _ ( int i ) ) ) .  intros inv1 inv2 .  simpl . intro ax1 .  intro ax2 .  apply funextfun . intro x0 . apply ( invmaponpathsweq ( weqpair _ ( isweqrmultingr_is ( tpair _ is is0 ) x0 ) ) ) .    simpl . rewrite ( pr1 ax1 x0 ) .   rewrite ( pr1 ax2 x0 ) .  apply idpath .  Defined . 

Lemma isapropisgrop { X : hSet } ( opp : binop X ) : isaprop ( isgrop opp ) .
Proof . intros . apply ( isofhleveltotal2 1 ) . apply isapropismonoidop . apply isapropinvstruct . Defined .  

(* (** Unitary monoid where all elements are invertible is a group *)

Definition allinvvertibleinv { X : hSet } { opp : binop X } ( is : ismonoidop opp ) ( allinv : forall x : X , islinvertible opp x ) : X -> X := fun x : X => invmap ( weqpair _ ( allinv x ) ) ( unel_is is ) .   

*)


(** The following lemma is an analog of [ Bourbaki , Alg. 1 , ex. 2 , p. 132 ] *)

Lemma isgropif { X : hSet } { opp : binop X } ( is0 : ismonoidop opp ) ( is : forall x : X, hexists ( fun x0 : X => eqset ( opp x x0 ) ( unel_is is0 ) ) ) : isgrop opp . 
Proof . intros . split with is0 .  destruct is0 as [ assoc isun0 ] . destruct isun0 as [ un0 unaxs0 ] . simpl in is .  simpl in unaxs0 . simpl in un0 . simpl in assoc . simpl in unaxs0 .  

assert ( l1 : forall x' : X , isincl ( fun x0 : X => opp x0 x' ) ) . intro x' . apply ( @hinhuniv ( total2 ( fun x0 : X => paths ( opp x' x0 ) un0 ) ) ( hProppair _ ( isapropisincl ( fun x0 : X => opp x0 x' ) ) ) ) .  intro int1 . simpl . apply isinclbetweensets .  apply ( pr2 X ) .  apply ( pr2 X ) .   intros a b .  intro e .  rewrite ( pathsinv0 ( pr2 unaxs0 a ) ) . rewrite ( pathsinv0 ( pr2 unaxs0 b ) ) .  destruct int1 as [ invx' eq ] .  rewrite ( pathsinv0 eq ) . destruct ( assoc a x' invx' ) .  destruct ( assoc b x' invx' ) .  rewrite e . apply idpath .  apply ( is x' ) .  

assert ( is' :  forall x : X, hexists ( fun x0 : X => eqset ( opp x0 x ) un0 ) ) . intro x . apply ( fun f : _  => hinhuniv f ( is x ) ) .  intro s1 .  destruct s1 as [ x' eq ] .  apply hinhpr . split with x' . simpl . apply ( invmaponpathsincl _ ( l1 x' ) ) .   rewrite ( assoc x' x x' ) . rewrite eq .  rewrite ( pr1 unaxs0 x' ) . unfold unel_is.   simpl . rewrite ( pr2 unaxs0 x' ) .  apply idpath . 

assert ( l1' :  forall x' : X , isincl ( fun x0 : X => opp x' x0 ) ) . intro x' . apply ( @hinhuniv ( total2 ( fun x0 : X => paths ( opp x0 x' ) un0 ) ) ( hProppair _ ( isapropisincl ( fun x0 : X => opp x' x0 ) ) ) ) .  intro int1 . simpl . apply isinclbetweensets .  apply ( pr2 X ) .  apply ( pr2 X ) .   intros a b .  intro e .  rewrite ( pathsinv0 ( pr1 unaxs0 a ) ) . rewrite ( pathsinv0 ( pr1 unaxs0 b ) ) .  destruct int1 as [ invx' eq ] .  rewrite ( pathsinv0 eq ) . destruct ( pathsinv0 ( assoc invx' x' a )  ) .  destruct ( pathsinv0 ( assoc invx' x' b ) ) .  rewrite e . apply idpath .  apply ( is' x' ) .  

assert ( int : forall x : X , isaprop ( total2 ( fun x0 : X => eqset ( opp x0 x ) un0 ) ) ) . intro x .   apply isapropsubtype .  intros x1 x2 .  intros eq1 eq2 .  apply ( invmaponpathsincl _ ( l1 x ) ) . rewrite eq1 .   rewrite eq2 .  apply idpath . 

simpl . set ( linv0 := fun x : X => hinhunivcor1 ( hProppair _ ( int x ) ) ( is' x ) ) .  simpl in linv0 .  set ( inv0 := fun x : X => pr1 ( linv0 x ) ) .  split with inv0 . simpl . split with ( fun x : _ => pr2 ( linv0 x ) ) .  intro x .  apply ( invmaponpathsincl _ ( l1 x ) ) . rewrite ( assoc x ( inv0 x ) x ) . change ( inv0 x ) with ( pr1 ( linv0 x ) ) . rewrite ( pr2 ( linv0 x ) ) . unfold unel_is . simpl . rewrite ( pr1 unaxs0 x ) . rewrite ( pr2 unaxs0 x ) . apply idpath .  Defined . 



(** *)

Definition iscomm { X : hSet} ( opp : binop X ) := forall x x' : X , paths ( opp x x' ) ( opp x' x ) . 

Lemma isapropiscomm { X : hSet } ( opp : binop X ) : isaprop ( iscomm opp ) .
Proof . intros . apply impred . intros x . apply impred . intro x' . simpl . apply ( setproperty X ) . Defined . 

Definition isabmonoidop { X : hSet } ( opp : binop X ) := dirprod ( ismonoidop opp ) ( iscomm opp ) . 
Definition pr1isabmonoidop ( X : hSet ) ( opp : binop X ) : isabmonoidop opp -> ismonoidop opp := @pr1 _ _ .
Coercion pr1isabmonoidop : isabmonoidop >-> ismonoidop .

Definition commax_is { X : hSet} { opp : binop X } ( is : isabmonoidop opp ) : iscomm opp := pr2 is . 

Lemma isapropisabmonoidop { X : hSet } ( opp : binop X ) : isaprop ( isabmonoidop opp ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropismonoidop . apply isapropiscomm . Defined . 

Lemma abmonoidoprer { X : hSet } { opp : binop X } ( is : isabmonoidop opp ) ( a b c d : X ) : paths ( opp ( opp a b ) ( opp c d ) ) ( opp ( opp a c ) ( opp b d ) ) .
Proof . intros . destruct is as [ is comm ] . destruct is as [ assoc unital0 ] .  simpl in * .  destruct ( assoc ( opp a b ) c d ) .  destruct ( assoc ( opp a c ) b d ) . destruct ( pathsinv0 ( assoc a b c ) ) . destruct ( pathsinv0 ( assoc a c b ) ) .   destruct ( comm b c ) . apply idpath .  Defined . 




(** *)


Lemma weqlcancelablercancelable { X : hSet } ( opp : binop X ) ( is : iscomm opp ) ( x : X ) : weq ( islcancelable opp x ) ( isrcancelable opp x ) .
Proof . intros . 

assert ( f : ( islcancelable opp x ) -> ( isrcancelable opp x ) ) . unfold islcancelable . unfold isrcancelable .  intro isl . apply ( fun h : _ => isinclhomot _ _ h isl ) .  intro x0 . apply is .  
assert ( g : ( isrcancelable opp x ) -> ( islcancelable opp x ) ) . unfold islcancelable . unfold isrcancelable .  intro isr . apply ( fun h : _ => isinclhomot _ _ h isr ) .  intro x0 . apply is . 

split with f . apply ( isweqimplimpl f g ( isapropisincl ( fun x0 : X => opp x x0 ) )  ( isapropisincl ( fun x0 : X => opp x0 x ) ) ) .  Defined .  



Lemma weqlinvertiblerinvertible { X : hSet } ( opp : binop X ) ( is : iscomm opp ) ( x : X ) : weq ( islinvertible opp x ) ( isrinvertible opp x ) .
Proof . intros . 

assert ( f : ( islinvertible opp x ) -> ( isrinvertible opp x ) ) . unfold islinvertible . unfold isrinvertible .  intro isl . apply ( fun h : _ => isweqhomot _ _ h isl ) .  apply is .  
assert ( g : ( isrinvertible opp x ) -> ( islinvertible opp x ) ) . unfold islinvertible . unfold isrinvertible .  intro isr . apply ( fun h : _ => isweqhomot _ _ h isr ) .  intro x0 . apply is . 

split with f . apply ( isweqimplimpl f g ( isapropisweq ( fun x0 : X => opp x x0 ) )  ( isapropisweq ( fun x0 : X => opp x0 x ) ) ) .  Defined .  


Lemma weqlunitrunit { X : hSet } ( opp : binop X ) ( is : iscomm opp ) ( un0 : X ) : weq ( islunit opp un0 ) ( isrunit opp un0 ) .
Proof . intros . 

assert ( f : ( islunit opp un0 ) -> ( isrunit opp un0 ) ) . unfold islunit . unfold isrunit .  intro isl .  intro x .  destruct ( is un0 x ) .  apply ( isl x ) .  
assert ( g : ( isrunit opp un0 ) -> ( islunit opp un0 ) ) . unfold islunit . unfold isrunit .  intro isr . intro x .  destruct ( is x un0 ) .  apply ( isr x ) .  

split with f . apply ( isweqimplimpl f g ( isapropislunit opp un0 )  ( isapropisrunit opp un0 ) ) .  Defined .  


Lemma weqlinvrinv { X : hSet } ( opp : binop X ) ( is : iscomm opp ) ( un0 : X ) ( inv0 : X -> X ) : weq ( islinv opp un0 inv0 ) ( isrinv opp un0 inv0 ) .
Proof . intros . 

assert ( f : ( islinv opp un0 inv0 ) -> ( isrinv opp un0 inv0 ) ) . unfold islinv . unfold isrinv .  intro isl .  intro x .  destruct ( is ( inv0 x ) x ) .  apply ( isl x ) .  
assert ( g : ( isrinv opp un0 inv0 ) -> ( islinv opp un0 inv0 ) ) . unfold islinv . unfold isrinv .  intro isr . intro x .  destruct ( is x ( inv0 x ) ) .  apply ( isr x ) .  

split with f . apply ( isweqimplimpl f g ( isapropislinv opp un0 inv0 )  ( isapropisrinv opp un0 inv0 ) ) .  Defined .  


Opaque abmonoidoprer .


(** *)

Definition isabgrop { X : hSet } ( opp : binop X ) := dirprod ( isgrop opp ) ( iscomm opp ) .
Definition pr1isabgrop ( X : hSet ) ( opp : binop X ) : isabgrop opp -> isgrop opp := @pr1 _ _ .
Coercion pr1isabgrop : isabgrop >-> isgrop .

Definition isabgroptoisabmonoidop ( X : hSet ) ( opp : binop X ) : isabgrop opp -> isabmonoidop opp := fun is : _ => dirprodpair ( pr1 ( pr1 is ) ) ( pr2 is ) .
Coercion isabgroptoisabmonoidop : isabgrop >-> isabmonoidop .

Lemma isapropisabgrop { X : hSet } ( opp : binop X ) : isaprop ( isabgrop opp ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropisgrop . apply isapropiscomm . Defined .  








(** **** Standard conditions on a pair of binary operations on a set *)

(** *)

Definition isldistr { X : hSet} ( opp1 opp2 : binop X ) := forall x x' x'' : X , paths ( opp2 x'' ( opp1 x x' ) ) ( opp1 ( opp2 x'' x ) ( opp2 x'' x' ) ) .

Lemma isapropisldistr { X : hSet} ( opp1 opp2 : binop X ) : isaprop ( isldistr opp1 opp2 ) .
Proof . intros . apply impred . intro x . apply impred . intro x' . apply impred . intro x'' . simpl . apply ( setproperty X ) . Defined .   

Definition isrdistr { X : hSet} ( opp1 opp2 : binop X ) := forall x x' x'' : X , paths ( opp2 ( opp1 x x' ) x'' ) ( opp1 ( opp2 x x'' ) ( opp2 x' x'' ) ) .

Lemma isapropisrdistr { X : hSet} ( opp1 opp2 : binop X ) : isaprop ( isrdistr opp1 opp2 ) .
Proof . intros . apply impred . intro x . apply impred . intro x' . apply impred . intro x'' . simpl . apply ( setproperty X ) . Defined .   

Definition isdistr { X : hSet } ( opp1 opp2 : binop X ) := dirprod ( isldistr opp1 opp2 ) ( isrdistr opp1 opp2 ) .

Lemma isapropisdistr { X : hSet } ( opp1 opp2 : binop X ) : isaprop ( isdistr opp1 opp2  ) .
Proof . intros . apply ( isofhleveldirprod 1 _ _ ( isapropisldistr _ _ ) ( isapropisrdistr _ _ ) ) . Defined .  

(** *)

Lemma weqldistrrdistr { X : hSet} ( opp1 opp2 : binop X ) ( is : iscomm opp2 ) : weq ( isldistr opp1 opp2 ) ( isrdistr opp1 opp2 ) .
Proof .  intros . 

assert ( f : ( isldistr opp1 opp2 ) -> ( isrdistr opp1 opp2 ) ) . unfold isldistr . unfold isrdistr .  intro isl .  intros x x' x'' .  destruct ( is x'' ( opp1 x x' ) ) . destruct ( is x'' x ) . destruct ( is x'' x' ) .  apply ( isl x x' x'' ) .  
assert ( g : ( isrdistr opp1 opp2 ) -> ( isldistr opp1 opp2 ) ) . unfold isldistr . unfold isrdistr .  intro isr .  intros x x' x'' .  destruct ( is ( opp1 x x' ) x'' ) . destruct ( is x x'' ) . destruct ( is x' x'' ) .  apply ( isr x x' x'' ) .   

split with f . apply ( isweqimplimpl f g ( isapropisldistr opp1 opp2 )  ( isapropisrdistr opp1 opp2 ) ) .  Defined . 


(** *)


Definition isrigops { X : hSet } ( opp1 opp2 : binop X ) :=  dirprod ( total2 ( fun axs : dirprod ( isabmonoidop opp1 ) ( ismonoidop opp2 ) => ( dirprod ( forall x : X , paths ( opp2 ( unel_is ( pr1 axs ) ) x ) ( unel_is ( pr1 axs ) ) ) ) ( forall x : X , paths ( opp2 x ( unel_is ( pr1 axs ) ) ) ( unel_is ( pr1 axs ) ) ) ) ) ( isdistr opp1 opp2 ) .
    
Definition rigop1axs_is { X : hSet } { opp1 opp2 : binop X } : isrigops opp1 opp2 -> isabmonoidop opp1 := fun is : _ => pr1 ( pr1 ( pr1 is ) ) .
Definition rigop2axs_is { X : hSet } { opp1 opp2 : binop X } : isrigops opp1 opp2 -> ismonoidop opp2 := fun is : _ => pr2 ( pr1 ( pr1 is ) ) .
Definition rigdistraxs_is { X : hSet } { opp1 opp2 : binop X } : isrigops opp1 opp2 -> isdistr opp1 opp2 := fun is : _ =>  pr2 is .
Definition rigldistrax_is { X : hSet } { opp1 opp2 : binop X } : isrigops opp1 opp2 -> isldistr opp1 opp2 := fun is : _ => pr1 ( pr2 is ) .
Definition rigrdistrax_is { X : hSet } { opp1 opp2 : binop X } : isrigops opp1 opp2 -> isrdistr opp1 opp2 := fun is : _ => pr2 ( pr2 is ) .
Definition rigunel1_is { X : hSet } { opp1 opp2 : binop X } ( is : isrigops opp1 opp2 ) : X := pr1 (pr2 (pr1 (rigop1axs_is is))) .
Definition rigunel2_is { X : hSet } { opp1 opp2 : binop X } ( is : isrigops opp1 opp2 ) : X := (pr1 (pr2 (rigop2axs_is is))) .
Definition rigmult0x_is { X : hSet } { opp1 opp2 : binop X } ( is : isrigops opp1 opp2 ) ( x : X ) : paths ( opp2 ( rigunel1_is is ) x ) ( rigunel1_is is )  := pr1 ( pr2 ( pr1 is ) ) x .
Definition rigmultx0_is { X : hSet } { opp1 opp2 : binop X } ( is : isrigops opp1 opp2 ) ( x : X ) : paths ( opp2 x ( rigunel1_is is ) ) ( rigunel1_is is ) := pr2 ( pr2 ( pr1 is ) ) x .


Lemma isapropisrigops { X : hSet } ( opp1 opp2 : binop X ) : isaprop ( isrigops opp1 opp2 ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply ( isofhleveltotal2 1 ) . apply ( isofhleveldirprod 1 ) . apply isapropisabmonoidop . apply isapropismonoidop. intro x . apply ( isofhleveldirprod 1 ) . apply impred. intro x' . apply ( setproperty X ) . apply impred . intro x' . apply ( setproperty X ) . apply isapropisdistr . Defined . 




(** *)


Definition isrngops { X : hSet } ( opp1 opp2 : binop X ) := dirprod ( dirprod ( isabgrop opp1 ) ( ismonoidop opp2 ) ) ( isdistr opp1 opp2 ) . 

Definition rngop1axs_is { X : hSet } { opp1 opp2 : binop X } : isrngops opp1 opp2 -> isabgrop opp1 := fun is : _ => pr1 ( pr1 is ) .
Definition rngop2axs_is { X : hSet } { opp1 opp2 : binop X } : isrngops opp1 opp2 -> ismonoidop opp2 := fun is : _ => pr2 ( pr1 is ) .
Definition rngdistraxs_is { X : hSet } { opp1 opp2 : binop X } : isrngops opp1 opp2 -> isdistr opp1 opp2 := fun is : _ =>  pr2 is .
Definition rngldistrax_is { X : hSet } { opp1 opp2 : binop X } : isrngops opp1 opp2 -> isldistr opp1 opp2 := fun is : _ => pr1 ( pr2 is ) .
Definition rngrdistrax_is { X : hSet } { opp1 opp2 : binop X } : isrngops opp1 opp2 -> isrdistr opp1 opp2 := fun is : _ => pr2 ( pr2 is ) .
Definition rngunel1_is { X : hSet } { opp1 opp2 : binop X } ( is : isrngops opp1 opp2 ) : X := unel_is ( pr1 ( pr1 is ) ) .
Definition rngunel2_is { X : hSet } { opp1 opp2 : binop X } ( is : isrngops opp1 opp2 ) : X := unel_is ( pr2 ( pr1 is ) ) .


Lemma isapropisrngops { X : hSet } ( opp1 opp2 : binop X ) : isaprop ( isrngops opp1 opp2 ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply ( isofhleveldirprod 1 ) . apply isapropisabgrop . apply isapropismonoidop. apply isapropisdistr . Defined . 

Lemma multx0_is_l { X : hSet } { opp1 opp2 : binop X } ( is1 : isgrop opp1 ) ( is2 : ismonoidop opp2 ) ( is12 : isdistr opp1 opp2 ) : forall x : X , paths ( opp2 x ( unel_is ( pr1 is1 ) ) ) ( unel_is ( pr1 is1 ) )  .
Proof . intros .  destruct is12 as [ ldistr0 rdistr0 ] . destruct is2 as [ assoc2 [ un2 [ lun2 run2 ] ] ] . simpl in * . apply ( invmaponpathsweq ( weqpair _ ( isweqrmultingr_is is1 ( opp2 x un2 ) ) ) ) .  simpl .  destruct is1 as [ [ assoc1 [ un1 [ lun1 run1 ] ] ] [ inv0 [ linv0 rinv0 ] ] ] .  unfold unel_is .  simpl in * . rewrite ( lun1 ( opp2 x un2 ) ) . destruct ( ldistr0 un1 un2 x ) .    rewrite ( run2 x ) .  rewrite ( lun1 un2 ) .  rewrite ( run2 x ) . apply idpath .  Defined .

Opaque multx0_is_l .

Lemma mult0x_is_l { X : hSet } { opp1 opp2 : binop X } ( is1 : isgrop opp1 ) ( is2 : ismonoidop opp2 ) ( is12 : isdistr opp1 opp2 ) : forall x : X , paths ( opp2 ( unel_is ( pr1 is1 ) ) x ) ( unel_is ( pr1 is1 ) ) .
Proof . intros .  destruct is12 as [ ldistr0 rdistr0 ] . destruct is2 as [ assoc2 [ un2 [ lun2 run2 ] ] ] . simpl in * . apply ( invmaponpathsweq ( weqpair _ ( isweqrmultingr_is is1 ( opp2 un2 x ) ) ) ) .  simpl .  destruct is1 as [ [ assoc1 [ un1 [ lun1 run1 ] ] ] [ inv0 [ linv0 rinv0 ] ] ] .  unfold unel_is .  simpl in * . rewrite ( lun1 ( opp2 un2 x ) ) . destruct ( rdistr0 un1 un2 x ) .  rewrite ( lun2 x ) .  rewrite ( lun1 un2 ) .  rewrite ( lun2 x ) . apply idpath .  Defined .

Opaque mult0x_is_l .



Definition minus1_is_l { X : hSet } { opp1 opp2 : binop X } ( is1 : isgrop opp1 ) ( is2 : ismonoidop opp2 ) := ( grinv_is is1 ) ( unel_is is2 ) . 

Lemma islinvmultwithminus1_is_l { X : hSet } { opp1 opp2 : binop X } ( is1 : isgrop opp1 ) ( is2 : ismonoidop opp2 ) ( is12 : isdistr opp1 opp2 ) ( x : X ) : paths ( opp1 ( opp2 ( minus1_is_l is1 is2 ) x ) x ) ( unel_is ( pr1 is1 ) ) .
Proof . intros . set ( xinv := opp2 (minus1_is_l is1 is2) x ) . rewrite ( pathsinv0 ( lunax_is is2 x ) ) . unfold xinv .  rewrite ( pathsinv0 ( pr2 is12 _ _ x ) ) . unfold minus1_is_l . unfold grinv_is . rewrite ( grlinvax_is is1 _ ) .  apply mult0x_is_l .   apply is2 . apply is12 .  Defined . 

Opaque islinvmultwithminus1_is_l .

Lemma isrinvmultwithminus1_is_l { X : hSet } { opp1 opp2 : binop X } ( is1 : isgrop opp1 ) ( is2 : ismonoidop opp2 ) ( is12 : isdistr opp1 opp2 ) ( x : X ) : paths ( opp1 x ( opp2 ( minus1_is_l is1 is2 ) x ) ) ( unel_is ( pr1 is1 ) ) .
Proof . intros . set ( xinv := opp2 (minus1_is_l is1 is2) x ) . rewrite ( pathsinv0 ( lunax_is is2 x ) ) . unfold xinv .  rewrite ( pathsinv0 ( pr2 is12 _ _ x ) ) . unfold minus1_is_l . unfold grinv_is . rewrite ( grrinvax_is is1 _ ) .  apply mult0x_is_l .   apply is2 . apply is12 .  Defined . 

Opaque isrinvmultwithminus1_is_l . 


Lemma isminusmultwithminus1_is_l { X : hSet } { opp1 opp2 : binop X } ( is1 : isgrop opp1 ) ( is2 : ismonoidop opp2 ) ( is12 : isdistr opp1 opp2 ) ( x : X ) : paths ( opp2 ( minus1_is_l is1 is2 ) x ) ( grinv_is is1 x ) .
Proof . intros . apply ( invmaponpathsweq ( weqpair _ ( isweqrmultingr_is is1 x ) ) ) .    simpl . rewrite ( islinvmultwithminus1_is_l is1 is2 is12 x ) . unfold grinv_is . rewrite ( grlinvax_is is1 x ) .  apply idpath . Defined . 

Opaque isminusmultwithminus1_is_l . 

Lemma isrngopsif { X : hSet } { opp1 opp2 : binop X } ( is1 : isgrop opp1 ) ( is2 : ismonoidop opp2 ) ( is12 : isdistr opp1 opp2 ) : isrngops opp1 opp2 .
Proof . intros .  set ( assoc1 := pr1 ( pr1 is1 ) ) . split . split .  split with is1 . 
intros x y .    apply ( invmaponpathsweq ( weqpair _ ( isweqrmultingr_is is1 ( opp2 ( minus1_is_l is1 is2 ) ( opp1 x y ) ) ) ) ) . simpl . rewrite ( isrinvmultwithminus1_is_l is1 is2 is12 ( opp1 x y ) ) . rewrite ( pr1 is12 x y _ ) .  destruct ( assoc1 ( opp1 y x ) (opp2 (minus1_is_l is1 is2) x) (opp2 (minus1_is_l is1 is2) y)) . rewrite ( assoc1 y x _ ) . destruct ( pathsinv0 ( isrinvmultwithminus1_is_l is1 is2 is12 x ) ) . unfold unel_is .  rewrite ( runax_is ( pr1 is1 ) y ) . rewrite ( isrinvmultwithminus1_is_l is1 is2 is12 y ) .  apply idpath . apply is2 . apply is12 .  Defined .

Definition rngmultx0_is { X : hSet } { opp1 opp2 : binop X } ( is : isrngops opp1 opp2 ) := multx0_is_l ( rngop1axs_is is ) ( rngop2axs_is is ) ( rngdistraxs_is is )  .

Definition rngmult0x_is { X : hSet } { opp1 opp2 : binop X } ( is : isrngops opp1 opp2 ) := mult0x_is_l ( rngop1axs_is is ) ( rngop2axs_is is ) ( rngdistraxs_is is )  .

Definition rngminus1_is { X : hSet } { opp1 opp2 : binop X } ( is : isrngops opp1 opp2 ) := minus1_is_l ( rngop1axs_is is ) ( rngop2axs_is is ) .

Definition rngmultwithminus1_is { X : hSet } { opp1 opp2 : binop X } ( is : isrngops opp1 opp2 ) := isminusmultwithminus1_is_l ( rngop1axs_is is ) ( rngop2axs_is is ) ( rngdistraxs_is is ) .
 
Definition isrngopstoisrigops ( X : hSet ) ( opp1 opp2 : binop X ) ( is : isrngops opp1 opp2 ) : isrigops opp1 opp2 .
Proof. intros . split . split with ( dirprodpair ( isabgroptoisabmonoidop _ _ ( rngop1axs_is is ) ) ( rngop2axs_is is ) ) . split . simpl .  apply ( rngmult0x_is )  . simpl . apply ( rngmultx0_is ) .  apply ( rngdistraxs_is is ) . Defined . 

Coercion isrngopstoisrigops : isrngops >-> isrigops . 



(** *)

Definition iscommrigops { X : hSet } ( opp1 opp2 : binop X )  :=  dirprod ( isrigops opp1 opp2 ) ( iscomm opp2 ) .
Definition pr1iscommrigops ( X : hSet ) ( opp1 opp2 : binop X ) : iscommrigops opp1 opp2 -> isrigops opp1 opp2 := @pr1 _ _ .
Coercion pr1iscommrigops : iscommrigops >-> isrigops .  

Definition rigiscommop2_is { X : hSet } { opp1 opp2 : binop X } ( is : iscommrigops opp1 opp2 ) : iscomm opp2 := pr2 is . 

Lemma isapropiscommrig  { X : hSet } ( opp1 opp2 : binop X ) : isaprop ( iscommrigops opp1 opp2 ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropisrigops . apply isapropiscomm . Defined .






(** *) 

Definition iscommrngops { X : hSet } ( opp1 opp2 : binop X )  :=  dirprod ( isrngops opp1 opp2 ) ( iscomm opp2 ) . 
Definition pr1iscommrngops ( X : hSet ) ( opp1 opp2 : binop X ) : iscommrngops opp1 opp2 -> isrngops opp1 opp2 := @pr1 _ _ .
Coercion pr1iscommrngops : iscommrngops >-> isrngops .  

Definition rngiscommop2_is { X : hSet } { opp1 opp2 : binop X } ( is : iscommrngops opp1 opp2 ) : iscomm opp2 := pr2 is . 

Lemma isapropiscommrng  { X : hSet } ( opp1 opp2 : binop X ) : isaprop ( iscommrngops opp1 opp2 ) .
Proof . intros . apply ( isofhleveldirprod 1 ) . apply isapropisrngops . apply isapropiscomm . Defined . 

Definition iscommrngopstoiscommrigops ( X : hSet ) ( opp1 opp2 : binop X ) ( is : iscommrngops opp1 opp2 ) : iscommrigops opp1 opp2 := dirprodpair ( isrngopstoisrigops _ _ _ ( pr1 is ) ) ( pr2 is ) .
Coercion iscommrngopstoiscommrigops : iscommrngops >-> iscommrigops . 




(** *** Sets with one binary operation *)

(** **** General definitions *)


Definition setwithbinop := total2 ( fun X : hSet => binop X ) . 
Definition setwithbinoppair ( X : hSet ) ( opp : binop X ) : setwithbinop := tpair ( fun X : hSet => binop X ) X opp .
Definition pr1setwithbinop : setwithbinop -> hSet := @pr1 _ ( fun X : hSet => binop X ) .
Coercion pr1setwithbinop : setwithbinop >-> hSet .


Definition op { X : setwithbinop } : binop X := pr2 X . 

Notation "x + y" := ( op x y ) : addoperation_scope .
Notation "x * y" := ( op x y ) : multoperation_scope .  



(** **** Functions compatible with a binary operation ( homomorphisms ) and their properties *)

Definition isbinopfun { X Y : setwithbinop } ( f : X -> Y ) := forall x x' : X , paths ( f ( op x x' ) ) ( op ( f x ) ( f x' ) ) . 

Lemma isapropisbinopfun { X Y : setwithbinop } ( f : X -> Y ) : isaprop ( isbinopfun f ) .
Proof . intros . apply impred . intro x . apply impred . intro x' . apply ( setproperty Y ) . Defined .

Definition binopfun ( X Y : setwithbinop ) : UU0 := total2 ( fun f : X -> Y => isbinopfun f ) .
Definition binopfunpair { X Y : setwithbinop } ( f : X -> Y ) ( is : isbinopfun f ) : binopfun X Y := tpair _ f is . 
Definition pr1binopfun ( X Y : setwithbinop ) : binopfun X Y -> ( X -> Y ) := @pr1 _ _ . 
Coercion pr1binopfun : binopfun >-> Funclass . 

Lemma isasetbinopfun  ( X Y : setwithbinop ) : isaset ( binopfun X Y ) .
Proof . intros . apply ( isasetsubset ( pr1binopfun X Y  ) ) . change ( isofhlevel 2 ( X -> Y ) ) . apply impred .  intro . apply ( setproperty Y ) . apply isinclpr1 .  intro .  apply isapropisbinopfun . Defined .  

Lemma isbinopfuncomp { X Y Z : setwithbinop } ( f : binopfun X Y ) ( g : binopfun Y Z ) : isbinopfun ( funcomp ( pr1 f ) ( pr1 g ) ) .
Proof . intros . set ( axf := pr2 f ) . set ( axg := pr2 g ) .  intros a b . unfold funcomp .  rewrite ( axf a b ) . rewrite ( axg ( pr1 f a ) ( pr1 f b ) ) .  apply idpath . Defined .  

Opaque isbinopfuncomp . 

Definition binopfuncomp { X Y Z : setwithbinop } ( f : binopfun X Y ) ( g : binopfun Y Z ) : binopfun X Z := binopfunpair ( funcomp ( pr1 f ) ( pr1 g ) ) ( isbinopfuncomp f g ) . 


Definition binopmono ( X Y : setwithbinop ) : UU0 := total2 ( fun f : incl X Y => isbinopfun ( pr1 f ) ) .
Definition binopmonopair { X Y : setwithbinop } ( f : incl X Y ) ( is : isbinopfun f ) : binopmono X Y := tpair _  f is .
Definition pr1binopmono ( X Y : setwithbinop ) : binopmono X Y -> incl X Y := @pr1 _ _ .
Coercion pr1binopmono : binopmono >-> incl .

Definition binopincltobinopfun ( X Y : setwithbinop ) : binopmono X Y -> binopfun X Y := fun f => binopfunpair ( pr1 ( pr1 f ) ) ( pr2 f ) .
Coercion binopincltobinopfun : binopmono >-> binopfun . 


Definition binopmonocomp { X Y Z : setwithbinop } ( f : binopmono X Y ) ( g : binopmono Y Z ) : binopmono X Z := binopmonopair ( inclcomp ( pr1 f ) ( pr1 g ) ) ( isbinopfuncomp f g ) . 

Definition binopiso ( X Y : setwithbinop ) : UU0 := total2 ( fun f : weq X Y => isbinopfun f ) .   
Definition binopisopair { X Y : setwithbinop } ( f : weq X Y ) ( is : isbinopfun f ) : binopiso X Y := tpair _  f is .
Definition pr1binopiso ( X Y : setwithbinop ) : binopiso X Y -> weq X Y := @pr1 _ _ .
Coercion pr1binopiso : binopiso >-> weq .

Definition binopisotobinopmono ( X Y : setwithbinop ) : binopiso X Y -> binopmono X Y := fun f => binopmonopair ( pr1 f ) ( pr2 f ) .
Coercion binopisotobinopmono : binopiso >-> binopmono . 

Definition binopisocomp { X Y Z : setwithbinop } ( f : binopiso X Y ) ( g : binopiso Y Z ) : binopiso X Z := binopisopair ( weqcomp ( pr1 f ) ( pr1 g ) ) ( isbinopfuncomp f g ) .

Lemma isbinopfuninvmap { X Y : setwithbinop } ( f : binopiso X Y ) : isbinopfun ( invmap ( pr1 f ) ) . 
Proof . intros . set ( axf := pr2 f ) . intros a b .  apply ( invmaponpathsweq ( pr1 f ) ) .  rewrite ( homotweqinvweq ( pr1 f ) ( op a b ) ) . rewrite ( axf (invmap (pr1 f) a) (invmap (pr1 f) b) ) .  rewrite ( homotweqinvweq ( pr1 f ) a ) .   rewrite ( homotweqinvweq ( pr1 f ) b ) .   apply idpath . Defined .

Opaque isbinopfuninvmap .  

Definition invbinopiso { X Y : setwithbinop } ( f : binopiso X Y ) : binopiso Y X := binopisopair ( invweq ( pr1 f ) ) ( isbinopfuninvmap f ) .



(** **** Transport of properties of a binary operation  *)


Lemma isincltwooutof3a { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( isg : isincl g ) ( isgf : isincl ( funcomp f g ) ) : isincl f .
Proof . intros . apply ( isofhlevelff 1 f g isgf ) .  apply ( isofhlevelfsnincl 1 g isg ) . Defined .


Lemma islcancelablemonob { X Y : setwithbinop } ( f : binopmono X Y ) ( x : X ) ( is : islcancelable ( @op Y ) ( f x ) ) : islcancelable ( @op X ) x .
Proof . intros .  unfold islcancelable . apply ( isincltwooutof3a (fun x0 : X => op x x0) f ( pr2 ( pr1 f ) ) ) .    

assert ( h : homot ( funcomp f ( fun y0 : Y => op ( f x ) y0 ) ) (funcomp (fun x0 : X => op x x0) f) ) .  intro x0 .  unfold funcomp .  apply ( pathsinv0 ( ( pr2 f ) x x0 ) ) . 

apply ( isinclhomot _ _ h ) . apply ( isinclcomp f ( inclpair _ is ) ) .  Defined .


Lemma isrcancelablemonob { X Y : setwithbinop } ( f : binopmono X Y ) ( x : X ) ( is : isrcancelable ( @op Y ) ( f x ) ) : isrcancelable ( @op X ) x .
Proof . intros .  unfold islcancelable . apply ( isincltwooutof3a (fun x0 : X => op x0 x) f ( pr2 ( pr1 f ) ) ) .    

assert ( h : homot ( funcomp f ( fun y0 : Y => op y0 ( f x ) ) ) (funcomp (fun x0 : X => op x0 x ) f) ) .  intro x0 .  unfold funcomp .  apply ( pathsinv0 ( ( pr2 f ) x0 x ) ) . 

apply ( isinclhomot _ _ h ) . apply ( isinclcomp f ( inclpair _ is ) ) .  Defined .


Lemma iscancelablemonob { X Y : setwithbinop } ( f : binopmono X Y ) ( x : X ) ( is : iscancelable ( @op Y ) ( f x ) ) : iscancelable ( @op X ) x . 
Proof . intros . apply ( dirprodpair ( islcancelablemonob f x ( pr1 is ) ) ( isrcancelablemonob f x ( pr2 is ) ) ) . Defined .

Notation islcancelableisob := islcancelablemonob . 
Notation isrcancelableisob := isrcancelablemonob . 
Notation iscancelableisob := iscancelablemonob .


Lemma islinvertibleisob  { X Y : setwithbinop } ( f : binopiso X Y ) ( x : X ) ( is : islinvertible ( @op Y ) ( f x ) ) : islinvertible ( @op X ) x .
Proof . intros .  unfold islinvertible . apply ( twooutof3a (fun x0 : X => op x x0) f ) .     

assert ( h : homot ( funcomp f ( fun y0 : Y => op ( f x ) y0 ) ) (funcomp (fun x0 : X => op x x0) f) ) .  intro x0 .  unfold funcomp .  apply ( pathsinv0 ( ( pr2 f ) x x0 ) ) . 

apply ( isweqhomot _ _ h ) . apply ( pr2 ( weqcomp f ( weqpair _ is ) ) ) . apply ( pr2 ( pr1 f ) ) . Defined .  

Lemma isrinvertibleisob { X Y : setwithbinop } ( f : binopiso X Y ) ( x : X ) ( is : isrinvertible ( @op Y ) ( f x ) ) : isrinvertible ( @op X ) x .
Proof . intros .  unfold islinvertible . apply ( twooutof3a (fun x0 : X => op x0 x) f ) .    

assert ( h : homot ( funcomp f ( fun y0 : Y => op y0 ( f x ) ) ) (funcomp (fun x0 : X => op x0 x ) f) ) .  intro x0 .  unfold funcomp .  apply ( pathsinv0 ( ( pr2 f ) x0 x ) ) . 

apply ( isweqhomot _ _ h ) . apply ( pr2 ( weqcomp f ( weqpair _ is ) ) ) . apply ( pr2 ( pr1 f ) ) . Defined .


Lemma isinvertiblemonob { X Y : setwithbinop } ( f : binopiso X Y ) ( x : X ) ( is : isinvertible ( @op Y ) ( f x ) ) : isinvertible ( @op X ) x . 
Proof . intros . apply ( dirprodpair ( islinvertibleisob f x ( pr1 is ) ) ( isrinvertibleisob f x ( pr2 is ) ) ) . Defined .


Definition islinvertibleisof  { X Y : setwithbinop } ( f : binopiso X Y ) ( x : X ) ( is : islinvertible ( @op X ) x ) : islinvertible ( @op Y ) ( f x ) .
Proof . intros . unfold islinvertible . apply ( twooutof3b f ) .  apply ( pr2 ( pr1 f ) ) .    

assert ( h : homot ( funcomp ( fun x0 : X => op x x0 ) f ) (fun x0 : X => op (f x) (f x0))  ) .  intro x0 .  unfold funcomp .   apply ( pr2 f x x0 ) .

apply ( isweqhomot _ _ h ) . apply ( pr2 ( weqcomp ( weqpair _ is ) f ) ) . Defined .  

Definition isrinvertibleisof  { X Y : setwithbinop } ( f : binopiso X Y ) ( x : X ) ( is : isrinvertible ( @op X ) x ) : isrinvertible ( @op Y ) ( f x ) .
Proof . intros . unfold isrinvertible . apply ( twooutof3b f ) .  apply ( pr2 ( pr1 f ) ) .    

assert ( h : homot ( funcomp ( fun x0 : X => op x0 x ) f ) (fun x0 : X => op (f x0) (f x) )  ) .  intro x0 .  unfold funcomp .   apply ( pr2 f x0 x ) .

apply ( isweqhomot _ _ h ) . apply ( pr2 ( weqcomp ( weqpair _ is ) f ) ) . Defined . 

Lemma isinvertiblemonof { X Y : setwithbinop } ( f : binopiso X Y ) ( x : X ) ( is : isinvertible ( @op X ) x ) : isinvertible ( @op Y ) ( f x ) . 
Proof . intros . apply ( dirprodpair ( islinvertibleisof f x ( pr1 is ) ) ( isrinvertibleisof f x ( pr2 is ) ) ) . Defined .


Lemma isassocmonob { X Y : setwithbinop } ( f : binopmono X Y ) ( is : isassoc ( @op Y ) ) : isassoc ( @op X ) .
Proof . intros . set ( axf := pr2 f ) .  simpl in axf .  intros a b c . apply ( invmaponpathsincl _ ( pr2 ( pr1 f ) ) ) . rewrite ( axf ( op a b ) c ) .  rewrite ( axf a b ) . rewrite ( axf a ( op b c ) ) . rewrite ( axf b c ) . apply is . Defined .   

Opaque isassocmonob .

Lemma iscommmonob { X Y : setwithbinop } ( f : binopmono X Y ) ( is : iscomm ( @op Y ) ) : iscomm ( @op X ) .
Proof . intros . set ( axf := pr2 f ) .  simpl in axf .  intros a b . apply ( invmaponpathsincl _ ( pr2 ( pr1 f ) ) ) . rewrite ( axf a b ) .  rewrite ( axf b a  ) . apply is . Defined .  

Opaque iscommmonob .

Notation isassocisob := isassocmonob .
Notation iscommisob := iscommmonob . 

Lemma isassocisof  { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isassoc ( @op X ) ) : isassoc ( @op Y ) .
Proof . intros . apply ( isassocmonob ( invbinopiso f ) is ) . Defined .  

Opaque isassocisof .

Lemma iscommisof { X Y : setwithbinop } ( f : binopiso X Y ) ( is : iscomm ( @op X ) ) : iscomm ( @op Y ) .
Proof . intros .  apply ( iscommmonob ( invbinopiso f ) is ) . Defined . 

Opaque iscommisof . 

Lemma isunitisof { X Y : setwithbinop } ( f : binopiso X Y ) ( unx : X ) ( is : isunit ( @op X ) unx ) : isunit ( @op Y ) ( f unx ) .
Proof . intros . set ( axf := pr2 f ) .  split . 

intro a . change ( f unx ) with ( pr1 f unx ) . apply ( invmaponpathsweq ( pr1 ( invbinopiso f ) ) ) .  rewrite ( pr2 ( invbinopiso f ) ( pr1 f unx ) a ) . simpl . rewrite ( homotinvweqweq ( pr1 f ) unx ) .  apply ( pr1 is ) .  

intro a . change ( f unx ) with ( pr1 f unx ) . apply ( invmaponpathsweq ( pr1 ( invbinopiso f ) ) ) .  rewrite ( pr2 ( invbinopiso f ) a ( pr1 f unx ) ) . simpl . rewrite ( homotinvweqweq ( pr1 f ) unx ) .  apply ( pr2 is ) . Defined .   

Opaque isunitisof . 

Definition isunitalisof { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isunital ( @op X ) ) : isunital ( @op Y ) := isunitalpair ( f ( pr1 is ) ) ( isunitisof f ( pr1 is ) ( pr2 is ) ) .

Lemma isunitisob { X Y : setwithbinop } ( f : binopiso X Y ) ( uny : Y ) ( is : isunit ( @op Y ) uny ) : isunit ( @op X ) ( ( invmap f ) uny ) .
Proof . intros . set ( int := isunitisof ( invbinopiso f ) ) .  simpl . simpl in int . apply int .  apply is .  Defined .

Opaque isunitisob .

Definition isunitalisob  { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isunital ( @op Y ) ) : isunital ( @op X ) := isunitalpair ( ( invmap f ) ( pr1 is ) ) ( isunitisob f ( pr1 is ) ( pr2 is ) ) .


Definition ismonoidopisof { X Y : setwithbinop } ( f : binopiso X Y ) ( is : ismonoidop ( @op X ) ) : ismonoidop ( @op Y ) := dirprodpair ( isassocisof f ( pr1 is ) ) ( isunitalisof f ( pr2 is ) ) . 

Definition ismonoidopisob { X Y : setwithbinop } ( f : binopiso X Y ) ( is : ismonoidop ( @op Y ) ) : ismonoidop ( @op X ) := dirprodpair ( isassocisob f ( pr1 is ) ) ( isunitalisob f ( pr2 is ) ) . 

Lemma isinvisof { X Y : setwithbinop } ( f : binopiso X Y ) ( unx : X ) ( invx : X -> X ) ( is : isinv ( @op X ) unx invx ) : isinv ( @op Y ) ( pr1 f unx ) ( funcomp ( invmap ( pr1 f ) ) ( funcomp invx ( pr1 f ) ) ) .
Proof . intros . set ( axf := pr2 f ) . set ( axinvf := pr2 ( invbinopiso f ) ) .  simpl in axf . simpl in axinvf . unfold funcomp . split .

intro a .  apply ( invmaponpathsweq ( pr1 ( invbinopiso f ) ) ) .  simpl . rewrite ( axinvf ( ( pr1 f ) (invx (invmap ( pr1 f ) a))) a ) . rewrite ( homotinvweqweq ( pr1 f ) unx ) .  rewrite ( homotinvweqweq ( pr1 f ) (invx (invmap ( pr1 f ) a)) ) . apply ( pr1 is ) .   

intro a .  apply ( invmaponpathsweq ( pr1 ( invbinopiso f ) ) ) .  simpl . rewrite ( axinvf a ( ( pr1 f ) (invx (invmap ( pr1 f ) a))) ) . rewrite ( homotinvweqweq ( pr1 f ) unx ) .  rewrite ( homotinvweqweq ( pr1 f ) (invx (invmap ( pr1 f ) a)) ) . apply ( pr2 is ) . Defined .      

Opaque isinvisof .

Definition isgropisof  { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isgrop ( @op X ) ) : isgrop ( @op Y ) :=  tpair _ ( ismonoidopisof f is ) ( tpair _ ( funcomp ( invmap ( pr1 f ) ) ( funcomp ( grinv_is is ) ( pr1 f ) ) ) ( isinvisof f ( unel_is is ) ( grinv_is is ) ( pr2 ( pr2 is ) ) ) ) .  

Lemma isinvisob { X Y : setwithbinop } ( f : binopiso X Y ) ( uny : Y ) ( invy : Y -> Y ) ( is : isinv ( @op Y ) uny invy ) : isinv ( @op X ) ( invmap (  pr1 f ) uny ) ( funcomp ( pr1 f ) ( funcomp invy ( invmap ( pr1 f ) ) ) ) .
Proof . intros . apply ( isinvisof ( invbinopiso f ) uny invy is ) . Defined .  

Opaque isinvisob .

Definition isgropisob  { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isgrop ( @op Y ) ) : isgrop ( @op X ) :=  tpair _ ( ismonoidopisob f is ) ( tpair _  ( funcomp ( pr1 f ) ( funcomp ( grinv_is is ) ( invmap ( pr1 f ) ) ) ) ( isinvisob f ( unel_is is ) ( grinv_is is ) ( pr2 ( pr2 is ) ) ) ) .

Definition isabmonoidopisof { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isabmonoidop ( @op X ) ) : isabmonoidop ( @op Y ) := tpair _ ( ismonoidopisof f is ) ( iscommisof f ( commax_is is ) )  . 

Definition isabmonoidopisob { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isabmonoidop ( @op Y ) ) : isabmonoidop ( @op X ) := tpair _ ( ismonoidopisob f is ) ( iscommisob f ( commax_is is ) )  .


Definition isabgropisof { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isabgrop ( @op X ) ) : isabgrop ( @op Y ) := tpair _ ( isgropisof f is ) ( iscommisof f ( commax_is is ) )  . 

Definition isabgropisob { X Y : setwithbinop } ( f : binopiso X Y ) ( is : isabgrop ( @op Y ) ) : isabgrop ( @op X ) := tpair _ ( isgropisob f is ) ( iscommisob f ( commax_is is ) )  .

 


   


(** **** Subobjects *)

Definition issubsetwithbinop { X : hSet } ( opp : binop X ) ( A : hsubtypes X ) := forall a a' : A , A ( opp ( pr1 a ) ( pr1 a' ) ) .

Lemma isapropissubsetwithbinop { X : hSet } ( opp : binop X ) ( A : hsubtypes X ) : isaprop ( issubsetwithbinop opp A ) .
Proof .  intros .  apply impred .  intro a . apply impred . intros a' . apply ( pr2 ( A ( opp (pr1 a) (pr1 a')) ) ) . Defined .

Definition subsetswithbinop { X : setwithbinop } := total2 ( fun A : hsubtypes X => issubsetwithbinop ( @op X ) A ) .
Definition subsetswithbinoppair { X : setwithbinop } := tpair ( fun A : hsubtypes X => issubsetwithbinop ( @op X ) A ) . 
Definition subsetswithbinopconstr { X : setwithbinop } := @subsetswithbinoppair X .  
Definition pr1subsetswithbinop ( X : setwithbinop ) : @subsetswithbinop X -> hsubtypes X := @pr1 _ ( fun A : hsubtypes X => issubsetwithbinop ( @op X ) A ) . 
Coercion pr1subsetswithbinop : subsetswithbinop >-> hsubtypes .

Definition totalsubsetwithbinop ( X : setwithbinop ) : @subsetswithbinop X .
Proof . intros .  split with ( fun x : X => htrue ) . intros x x' .  apply tt . Defined .  


Definition carrierofasubsetwithbinop { X : setwithbinop } ( A : @subsetswithbinop X ) : setwithbinop .
Proof . intros . set ( aset := ( hSetpair ( carrier A ) ( isasetsubset ( pr1carrier A ) ( setproperty X ) ( isinclpr1carrier A ) ) ) : hSet ) . split with aset . 
set ( subopp := ( fun a a' : A => carrierpair A ( op ( pr1carrier _ a ) ( pr1carrier _ a' ) ) ( pr2 A a a' ) ) : ( A -> A -> A ) ) .  simpl . unfold binop . apply subopp .  Defined . 

Coercion carrierofasubsetwithbinop : subsetswithbinop >-> setwithbinop . 






(** **** Relations compatible with a binary operation and quotient objects *)

Definition isbinophrel { X : setwithbinop } ( R : hrel X ) := dirprod ( forall a b c : X , R a b -> R ( op c a ) ( op c b ) ) ( forall a b c : X , R a b -> R ( op a c ) ( op b c ) ) .

Definition isbinophrellogeqf { X : setwithbinop } { L R : hrel X } ( lg : hrellogeq L R ) ( isl : isbinophrel L ) : isbinophrel R .
Proof . intros . split . intros a b c rab . apply ( ( pr1 ( lg _ _ ) ( ( pr1 isl ) _ _ _ ( pr2 ( lg  _ _ ) rab ) ) ) ) . intros a b c rab .  apply ( ( pr1 ( lg _ _ ) ( ( pr2 isl ) _ _ _ ( pr2 ( lg  _ _ ) rab ) ) ) ) . Defined .     

Lemma isapropisbinophrel { X : setwithbinop } ( R : hrel X ) : isaprop ( isbinophrel R ) . 
Proof . intros . apply isapropdirprod . apply impred . intro a . apply impred . intro b . apply impred . intro c . apply impred . intro r . apply ( pr2 ( R _ _ ) ) .  apply impred . intro a . apply impred . intro b . apply impred . intro c . apply impred . intro r . apply ( pr2 ( R _ _ ) ) .  Defined .
  
Lemma isbinophrelif { X : setwithbinop } ( R : hrel X ) ( is : iscomm ( @op X ) ) ( isl : forall a b c : X , R a b -> R ( op c a ) ( op c b ) ) : isbinophrel R . 
Proof . intros . split with isl .  intros a b c rab .  destruct ( is c a ) . destruct ( is c b ) . apply ( isl _ _ _ rab ) . Defined .  
 
Lemma iscompbinoptransrel { X : setwithbinop } ( R : hrel X ) ( ist : istrans R )  ( isb : isbinophrel R ) : iscomprelrelfun2 R R ( @op X ) . 
Proof . intros . intros a b c d .  intros rab rcd . set ( racbc := pr2 isb a b c rab ) .  set ( rbcbd := pr1 isb c d b rcd ) .  apply ( ist _ _ _ racbc rbcbd ) .  Defined .  

Lemma isbinopreflrel { X : setwithbinop } ( R : hrel X ) ( isr : isrefl R )  ( isb : iscomprelrelfun2 R R ( @op X ) ) : isbinophrel R .
Proof . intros . split .   intros a b c rab .  apply ( isb c c a b ( isr c ) rab ) .  intros a b c rab . apply ( isb a b c c rab ( isr c ) ) .  Defined . 


Definition binophrel { X : setwithbinop } := total2 ( fun R : hrel X => isbinophrel R ) .
Definition binophrelpair { X : setwithbinop } := tpair ( fun R : hrel X => isbinophrel R ) .
Definition pr1binophrel ( X : setwithbinop ) : @binophrel X -> hrel X := @pr1 _ ( fun R : hrel X => isbinophrel R ) .
Coercion pr1binophrel : binophrel >-> hrel . 

Definition binoppo { X : setwithbinop } := total2 ( fun R : po X => isbinophrel R ) .
Definition binoppopair { X : setwithbinop } := tpair ( fun R : po X => isbinophrel R ) .
Definition pr1binoppo ( X : setwithbinop ) : @binoppo X -> po X := @pr1 _ ( fun R : po X => isbinophrel R ) .
Coercion pr1binoppo : binoppo >-> po . 

Definition binopeqrel { X : setwithbinop } := total2 ( fun R : eqrel X => isbinophrel R ) .
Definition binopeqrelpair { X : setwithbinop } := tpair ( fun R : eqrel X => isbinophrel R ) .
Definition pr1binopeqrel ( X : setwithbinop ) : @binopeqrel X -> eqrel X := @pr1 _ ( fun R : eqrel X => isbinophrel R ) .
Coercion pr1binopeqrel : binopeqrel >-> eqrel . 

Definition setwithbinopquot { X : setwithbinop } ( R : @binopeqrel X ) : setwithbinop .
Proof . intros . split with ( setquotinset R )  .  set ( qt  := setquot R ) . set ( qtset := setquotinset R ) .  
assert ( iscomp : iscomprelrelfun2 R R op ) . apply ( iscompbinoptransrel R ( eqreltrans R ) ( pr2 R ) ) .
set ( qtmlt := setquotfun2 R R op iscomp ) .   simpl . unfold binop . apply qtmlt . Defined . 


Definition ispartbinophrel { X : setwithbinop } ( S : hsubtypes X ) ( R : hrel X ) := dirprod ( forall a b c : X , S c -> R a b -> R ( op c a ) ( op c b ) ) ( forall a b c : X , S c -> R a b -> R ( op a c ) ( op b c ) ) .

Definition isbinoptoispartbinop { X : setwithbinop } ( S : hsubtypes X ) ( L : hrel X ) ( is : isbinophrel L ) : ispartbinophrel S L .
Proof . intros X S L .  unfold isbinophrel . unfold ispartbinophrel . intro d2 .  split .  intros a b c is .  apply ( pr1 d2 a b c ) . intros a b c is . apply ( pr2 d2 a b c ) . Defined .  

Definition ispartbinophrellogeqf { X : setwithbinop } ( S : hsubtypes X ) { L R : hrel X } ( lg : hrellogeq L R ) ( isl : ispartbinophrel S L ) : ispartbinophrel S R .
Proof . intros . split . intros a b c is rab .  apply ( ( pr1 ( lg _ _ ) ( ( pr1 isl ) _ _ _ is ( pr2 ( lg _ _ ) rab ) ) ) ) . intros a b c is rab .  apply ( ( pr1 ( lg _ _ ) ( ( pr2 isl ) _ _ _ is ( pr2 ( lg  _ _ ) rab ) ) ) ) . Defined .    

Lemma ispartbinophrelif { X : setwithbinop } ( S : hsubtypes X ) ( R : hrel X ) ( is : iscomm ( @op X ) ) ( isl : forall a b c : X , S c -> R a b -> R ( op c a ) ( op c b ) ) : ispartbinophrel S R .
Proof . intros .  split with isl .  intros a b c s rab .  destruct ( is c a ) . destruct ( is c b ) . apply ( isl _ _ _ s rab ) . Defined .  
  


(** **** Relations inversely compatible with a binary operation *)

Definition isinvbinophrel { X : setwithbinop } ( R : hrel X ) := dirprod ( forall a b c : X , R ( op c a ) ( op c b ) ->  R a b ) ( forall a b c : X , R ( op a c ) ( op b c ) -> R a b ) .

Definition isinvbinophrellogeqf { X : setwithbinop } { L R : hrel X } ( lg : hrellogeq L R ) ( isl : isinvbinophrel L ) : isinvbinophrel R .
Proof . intros . split . intros a b c rab . apply ( ( pr1 ( lg _ _ ) ( ( pr1 isl ) _ _ _ ( pr2 ( lg  _ _ ) rab ) ) ) ) . intros a b c rab .  apply ( ( pr1 ( lg _ _ ) ( ( pr2 isl ) _ _ _ ( pr2 ( lg  _ _ ) rab ) ) ) ) . Defined .  

Lemma isapropisinvbinophrel { X : setwithbinop } ( R : hrel X ) : isaprop ( isinvbinophrel R ) . 
Proof . intros . apply isapropdirprod . apply impred . intro a . apply impred . intro b . apply impred . intro c . apply impred . intro r . apply ( pr2 ( R _ _ ) ) .  apply impred . intro a . apply impred . intro b . apply impred . intro c . apply impred . intro r . apply ( pr2 ( R _ _ ) ) .  Defined .     

Lemma isinvbinophrelif { X : setwithbinop } ( R : hrel X ) ( is : iscomm ( @op X ) ) ( isl : forall a b c : X ,  R ( op c a ) ( op c b ) -> R a b ) : isinvbinophrel R . 
Proof . intros . split with isl .  intros a b c rab .  destruct ( is c a ) . destruct ( is c b ) . apply ( isl _ _ _ rab ) . Defined . 



 
 
Definition ispartinvbinophrel { X : setwithbinop } ( S : hsubtypes X ) ( R : hrel X ) := dirprod ( forall a b c : X , S c -> R ( op c a ) ( op c b ) -> R a b ) ( forall  a b c : X  , S c -> R ( op a c ) ( op b c ) -> R a b ) .

Definition isinvbinoptoispartinvbinop { X : setwithbinop } ( S : hsubtypes X ) ( L : hrel X ) ( is : isinvbinophrel L ) : ispartinvbinophrel S L .
Proof . intros X S L .  unfold isinvbinophrel . unfold ispartinvbinophrel . intro d2 .  split .  intros a b c s .  apply ( pr1 d2 a b c ) . intros a b c s . apply ( pr2 d2 a b c ) . Defined .  

Definition ispartinvbinophrellogeqf { X : setwithbinop } ( S : hsubtypes X ) { L R : hrel X } ( lg : hrellogeq L R ) ( isl : ispartinvbinophrel S L ) : ispartinvbinophrel S R .
Proof . intros . split . intros a b c s rab . apply ( ( pr1 ( lg _ _ ) ( ( pr1 isl ) _ _ _ s ( pr2 ( lg  _ _ ) rab ) ) ) ) . intros a b c s rab .  apply ( ( pr1 ( lg _ _ ) ( ( pr2 isl ) _ _ _ s ( pr2 ( lg  _ _ ) rab ) ) ) ) . Defined .  

Lemma ispartinvbinophrelif { X : setwithbinop } ( S : hsubtypes X ) ( R : hrel X ) ( is : iscomm ( @op X ) ) ( isl : forall a b c : X , S c -> R ( op c a ) ( op c b ) -> R a b ) : ispartinvbinophrel S R .
Proof . intros .  split with isl .  intros a b c s rab .  destruct ( is c a ) . destruct ( is c b ) . apply ( isl _ _ _ s rab ) . Defined .   


(** **** Homomorphisms and relations *)

Lemma binophrelandfun { X Y : setwithbinop } ( f : binopfun X Y ) ( R : hrel Y ) ( is : @isbinophrel Y R ) : @isbinophrel X ( fun x x' => R ( f x ) ( f x' ) ) . 
Proof . intros . set ( ish := ( pr2 f ) : forall a0 b0 , paths ( f ( op a0 b0 ) ) ( op ( f a0 ) ( f b0 ) ) ) . split . 

intros a b c r . rewrite ( ish _ _ ) .   rewrite ( ish _ _ ) .  apply ( pr1 is ) . apply r . 

intros a b c r . rewrite ( ish _ _ ) .   rewrite ( ish _ _ ) .  apply ( pr2 is ) . apply r . Defined . 


Lemma ispartbinophrelandfun { X Y : setwithbinop } ( f : binopfun X Y ) ( SX : hsubtypes X ) ( SY : hsubtypes Y ) ( iss : forall x : X , ( SX x ) -> ( SY ( f x ) ) ) ( R : hrel Y ) ( is : @ispartbinophrel Y SY R ) : @ispartbinophrel X SX ( fun x x' => R ( f x ) ( f x' ) ) . 
Proof . intros . set ( ish := ( pr2 f ) : forall a0 b0 , paths ( f ( op a0 b0 ) ) ( op ( f a0 ) ( f b0 ) ) ) . split . 

intros a b c s r . rewrite ( ish _ _ ) .   rewrite ( ish _ _ ) .  apply ( ( pr1 is ) _ _ _ ( iss _ s ) r ) .  

intros a b c s r . rewrite ( ish _ _ ) .   rewrite ( ish _ _ ) .  apply ( ( pr2 is ) _ _ _ ( iss _ s ) r ) . Defined .  

Lemma invbinophrelandfun { X Y : setwithbinop } ( f : binopfun X Y ) ( R : hrel Y ) ( is : @isinvbinophrel Y R ) : @isinvbinophrel X ( fun x x' => R ( f x ) ( f x' ) ) .
Proof . intros .  set ( ish := ( pr2 f ) : forall a0 b0 , paths ( f ( op a0 b0 ) ) ( op ( f a0 ) ( f b0 ) ) ) . split . 

intros a b c r . rewrite ( ish _ _ ) in r .   rewrite ( ish _ _ ) in r .  apply ( ( pr1 is ) _ _ _ r ) .  

intros a b c r . rewrite ( ish _ _ ) in r .   rewrite ( ish _ _ ) in r .  apply ( ( pr2 is ) _ _ _ r ) . Defined . 
 

Lemma ispartinvbinophrelandfun { X Y : setwithbinop } ( f : binopfun X Y ) ( SX : hsubtypes X ) ( SY : hsubtypes Y ) ( iss : forall x : X , ( SX x ) -> ( SY ( f x ) ) ) ( R : hrel Y ) ( is : @ispartinvbinophrel Y SY R ) : @ispartinvbinophrel X SX ( fun x x' => R ( f x ) ( f x' ) ) . 
Proof . intros .  set ( ish := ( pr2 f ) : forall a0 b0 , paths ( f ( op a0 b0 ) ) ( op ( f a0 ) ( f b0 ) ) ) . split . 

intros a b c s r . rewrite ( ish _ _ ) in r .   rewrite ( ish _ _ ) in r .  apply ( ( pr1 is ) _ _ _ ( iss _ s ) r ) .  

intros a b c s r . rewrite ( ish _ _ ) in r .   rewrite ( ish _ _ ) in r .  apply ( ( pr2 is ) _ _ _ ( iss _ s ) r ) . Defined . 


(** **** Quotient relations *)

Lemma isbinopquotrel { X : setwithbinop } ( R : @binopeqrel X ) { L : hrel X } ( is : iscomprelrel R L ) ( isl : isbinophrel L ) : @isbinophrel ( setwithbinopquot R ) ( quotrel is ) . 
Proof .  intros .  unfold isbinophrel .   split . assert ( int : forall a b c :  setwithbinopquot R , isaprop ( quotrel is a b -> quotrel is (op c a ) (op c b ) ) ) . intros a b c .  apply impred . intro .  apply ( pr2 ( quotrel is _ _ ) ) .  apply ( setquotuniv3prop R ( fun a b c => hProppair _ ( int a b c ) ) ) . exact ( pr1 isl )  . 
 assert ( int : forall a b c :  setwithbinopquot R , isaprop ( quotrel is a b -> quotrel is (op a c ) (op b c ) ) ) . intros a b c .  apply impred . intro .  apply ( pr2 ( quotrel is _ _ ) ) .  apply ( setquotuniv3prop R ( fun a b c => hProppair _ ( int a b c ) ) ) . exact ( pr2 isl )  . Defined .  



(** **** Direct products *)

Definition setwithbinopdirprod ( X Y : setwithbinop ) : setwithbinop .
Proof . intros . split with ( setdirprod X Y ) . unfold binop .  simpl . apply ( fun xy xy' : _ => dirprodpair ( op ( pr1 xy ) ( pr1 xy' ) ) ( op ( pr2 xy ) ( pr2 xy' ) ) ) . Defined .  






(** *** Sets with two binary operations *)

(** **** General definitions *)


Definition setwith2binop := total2 ( fun X : hSet => dirprod ( binop X ) ( binop X ) ) . 
Definition setwith2binoppair ( X : hSet ) ( opps : dirprod ( binop X ) ( binop X ) ) : setwith2binop := tpair ( fun X : hSet => dirprod ( binop X ) ( binop X ) ) X opps .
Definition pr1setwith2binop : setwith2binop -> hSet := @pr1 _ ( fun X : hSet => dirprod ( binop X ) ( binop X ) ) .
Coercion pr1setwith2binop : setwith2binop >-> hSet . 

Definition op1 { X : setwith2binop } : binop X := pr1 ( pr2 X ) .
Definition op2 { X : setwith2binop } : binop X := pr2 ( pr2 X ) .

Definition setwithbinop1 ( X : setwith2binop ) : setwithbinop := setwithbinoppair ( pr1 X ) ( @op1 X ) . 
Definition setwithbinop2 ( X : setwith2binop ) : setwithbinop := setwithbinoppair ( pr1 X ) ( @op2 X ) . 

Notation "x + y" := ( op1 x y ) : twobinops_scope .
Notation "x * y" := ( op2 x y ) : twobinops_scope .   


(** **** Functions compatible with a pair of binary operation ( homomorphisms ) and their properties *)

Definition istwobinopfun { X Y : setwith2binop } ( f : X -> Y ) := dirprod ( forall x x' : X , paths ( f ( op1 x x' ) ) ( op1 ( f x ) ( f x' ) ) ) ( forall x x' : X , paths ( f ( op2 x x' ) ) ( op2 ( f x ) ( f x' ) ) )  . 

Lemma isapropistwobinopfun { X Y : setwith2binop } ( f : X -> Y ) : isaprop ( istwobinopfun f ) .
Proof . intros . apply isofhleveldirprod . apply impred . intro x . apply impred . intro x' . apply ( setproperty Y ) . apply impred . intro x . apply impred . intro x' . apply ( setproperty Y ) . Defined .

Definition twobinopfun ( X Y : setwith2binop ) : UU0 := total2 ( fun f : X -> Y => istwobinopfun f ) .
Definition twobinopfunpair { X Y : setwith2binop } ( f : X -> Y ) ( is : istwobinopfun f ) : twobinopfun X Y := tpair _ f is . 
Definition pr1twobinopfun ( X Y : setwith2binop ) : twobinopfun X Y -> ( X -> Y ) := @pr1 _ _ . 
Coercion pr1twobinopfun : twobinopfun >-> Funclass .

Definition binop1fun { X Y : setwith2binop } ( f : twobinopfun X Y ) : binopfun ( setwithbinop1 X ) ( setwithbinop1 Y ) := @binopfunpair ( setwithbinop1 X ) ( setwithbinop1 Y ) ( pr1 f ) ( pr1 ( pr2 f ) ) .

Definition binop2fun { X Y : setwith2binop } ( f : twobinopfun X Y ) : binopfun ( setwithbinop2 X ) ( setwithbinop2 Y ) := @binopfunpair ( setwithbinop2 X ) ( setwithbinop2 Y ) ( pr1 f ) ( pr2 ( pr2 f ) ) .  
Lemma isasettwobinopfun  ( X Y : setwith2binop ) : isaset ( twobinopfun X Y ) .
Proof . intros . apply ( isasetsubset ( pr1twobinopfun X Y  ) ) . change ( isofhlevel 2 ( X -> Y ) ) . apply impred .  intro . apply ( setproperty Y ) . apply isinclpr1 .  intro .  apply isapropistwobinopfun . Defined . 
 

Lemma istwobinopfuncomp { X Y Z : setwith2binop } ( f : twobinopfun X Y ) ( g : twobinopfun Y Z ) : istwobinopfun ( funcomp ( pr1 f ) ( pr1 g ) ) .
Proof . intros . set ( ax1f := pr1 ( pr2 f ) ) . set ( ax2f := pr2 ( pr2 f ) ) . set ( ax1g := pr1 ( pr2 g ) ) . set ( ax2g := pr2 ( pr2 g ) ) .  split.

intros a b . unfold funcomp .  rewrite ( ax1f a b ) . rewrite ( ax1g ( pr1 f a ) ( pr1 f b ) ) .  apply idpath .
intros a b . unfold funcomp .  rewrite ( ax2f a b ) . rewrite ( ax2g ( pr1 f a ) ( pr1 f b ) ) .  apply idpath . Defined . 
 
Opaque istwobinopfuncomp . 

Definition twobinopfuncomp { X Y Z : setwith2binop } ( f : twobinopfun X Y ) ( g : twobinopfun Y Z ) : twobinopfun X Z := twobinopfunpair ( funcomp ( pr1 f ) ( pr1 g ) ) ( istwobinopfuncomp f g ) . 


Definition twobinopmono ( X Y : setwith2binop ) : UU0 := total2 ( fun f : incl X Y => istwobinopfun f ) .
Definition twobinopmonopair { X Y : setwith2binop } ( f : incl X Y ) ( is : istwobinopfun f ) : twobinopmono X Y := tpair _  f is .
Definition pr1twobinopmono ( X Y : setwith2binop ) : twobinopmono X Y -> incl X Y := @pr1 _ _ .
Coercion pr1twobinopmono : twobinopmono >-> incl .

Definition twobinopincltotwobinopfun ( X Y : setwith2binop ) : twobinopmono X Y -> twobinopfun X Y := fun f => twobinopfunpair ( pr1 ( pr1 f ) ) ( pr2 f ) .
Coercion twobinopincltotwobinopfun : twobinopmono >-> twobinopfun . 

Definition binop1mono { X Y : setwith2binop } ( f : twobinopmono X Y ) : binopmono ( setwithbinop1 X ) ( setwithbinop1 Y ) := @binopmonopair ( setwithbinop1 X ) ( setwithbinop1 Y ) ( pr1 f ) ( pr1 ( pr2 f ) ) .

Definition binop2mono { X Y : setwith2binop } ( f : twobinopmono X Y ) : binopmono ( setwithbinop2 X ) ( setwithbinop2 Y ) := @binopmonopair ( setwithbinop2 X ) ( setwithbinop2 Y ) ( pr1 f ) ( pr2 ( pr2 f ) ) .  

Definition twobinopmonocomp { X Y Z : setwith2binop } ( f : twobinopmono X Y ) ( g : twobinopmono Y Z ) : twobinopmono X Z := twobinopmonopair ( inclcomp ( pr1 f ) ( pr1 g ) ) ( istwobinopfuncomp f g ) . 

Definition twobinopiso ( X Y : setwith2binop ) : UU0 := total2 ( fun f : weq X Y => istwobinopfun f ) .   
Definition twobinopisopair { X Y : setwith2binop } ( f : weq X Y ) ( is : istwobinopfun f ) : twobinopiso X Y := tpair _  f is .
Definition pr1twobinopiso ( X Y : setwith2binop ) : twobinopiso X Y -> weq X Y := @pr1 _ _ .
Coercion pr1twobinopiso : twobinopiso >-> weq .

Definition twobinopisototwobinopmono ( X Y : setwith2binop ) : twobinopiso X Y -> twobinopmono X Y := fun f => twobinopmonopair ( pr1 f ) ( pr2 f ) .
Coercion twobinopisototwobinopmono : twobinopiso >-> twobinopmono . 

Definition binop1iso { X Y : setwith2binop } ( f : twobinopiso X Y ) : binopiso ( setwithbinop1 X ) ( setwithbinop1 Y ) := @binopisopair ( setwithbinop1 X ) ( setwithbinop1 Y ) ( pr1 f ) ( pr1 ( pr2 f ) ) .

Definition binop2iso { X Y : setwith2binop } ( f : twobinopiso X Y ) : binopiso ( setwithbinop2 X ) ( setwithbinop2 Y ) := @binopisopair ( setwithbinop2 X ) ( setwithbinop2 Y ) ( pr1 f ) ( pr2 ( pr2 f ) ) .  
Definition twobinopisocomp { X Y Z : setwith2binop } ( f : twobinopiso X Y ) ( g : twobinopiso Y Z ) : twobinopiso X Z := twobinopisopair ( weqcomp ( pr1 f ) ( pr1 g ) ) ( istwobinopfuncomp f g ) .

Lemma istwobinopfuninvmap { X Y : setwith2binop } ( f : twobinopiso X Y ) : istwobinopfun ( invmap ( pr1 f ) ) . 
Proof . intros . set ( ax1f := pr1 ( pr2 f ) ) . set ( ax2f := pr2 ( pr2 f ) ) . split .


intros a b .  apply ( invmaponpathsweq ( pr1 f ) ) .  rewrite ( homotweqinvweq ( pr1 f ) ( op1 a b ) ) .   rewrite ( ax1f (invmap (pr1 f) a) (invmap (pr1 f) b) ) .  rewrite ( homotweqinvweq ( pr1 f ) a ) .   rewrite ( homotweqinvweq ( pr1 f ) b ) .   apply idpath .
intros a b .  apply ( invmaponpathsweq ( pr1 f ) ) .  rewrite ( homotweqinvweq ( pr1 f ) ( op2 a b ) ) . rewrite ( ax2f (invmap (pr1 f) a) (invmap (pr1 f) b) ) .  rewrite ( homotweqinvweq ( pr1 f ) a ) .   rewrite ( homotweqinvweq ( pr1 f ) b ) .   apply idpath . Defined .

Opaque istwobinopfuninvmap .  

Definition invtwobinopiso { X Y : setwith2binop } ( f : twobinopiso X Y ) : twobinopiso Y X := twobinopisopair ( invweq ( pr1 f ) ) ( istwobinopfuninvmap f ) .





(** **** Transport of properties of a pair binary operations *)

Lemma isldistrmonob { X Y : setwith2binop } ( f : twobinopmono X Y ) ( is : isldistr ( @op1 Y ) ( @op2 Y ) ) : isldistr ( @op1 X ) ( @op2 X ) .
Proof . intros .   set ( ax1f := pr1 ( pr2 f ) ) .   set ( ax2f := pr2 ( pr2 f )  ) .   intros a b c . apply ( invmaponpathsincl _ ( pr2 ( pr1 f ) ) ) .  change ( paths ( (pr1 f) (op2 c (op1 a b)))
     ( (pr1 f) (op1 (op2 c a) (op2 c b))) ) . rewrite ( ax2f c ( op1 a b ) ) . rewrite ( ax1f a b ) .   rewrite ( ax1f ( op2 c a ) ( op2 c b ) ) . rewrite ( ax2f c a ) . rewrite ( ax2f c b ) .  apply is .  Defined . 

Opaque isldistrmonob .


Lemma isrdistrmonob { X Y : setwith2binop } ( f : twobinopmono X Y ) ( is : isrdistr ( @op1 Y ) ( @op2 Y ) ) : isrdistr ( @op1 X ) ( @op2 X ) .
Proof . intros .  set ( ax1f := pr1 ( pr2 f ) ) .   set ( ax2f := pr2 ( pr2 f ) ) .  intros a b c . apply ( invmaponpathsincl _ ( pr2 ( pr1 f ) ) ) . change ( paths ( (pr1 f) (op2 (op1 a b) c))
     ( (pr1 f) (op1 (op2 a c) (op2 b c))) ) .  rewrite ( ax2f ( op1 a b ) c ) . rewrite ( ax1f a b ) .   rewrite ( ax1f ( op2 a c ) ( op2 b c ) ) . rewrite ( ax2f a c ) . rewrite ( ax2f b c ) .  apply is .  Defined . 

Opaque isrdistrmonob .

Definition isdistrmonob { X Y : setwith2binop } ( f : twobinopmono X Y ) ( is : isdistr ( @op1 Y ) ( @op2 Y ) ) : isdistr ( @op1 X ) ( @op2 X ) := dirprodpair ( isldistrmonob f ( pr1 is ) ) ( isrdistrmonob f ( pr2 is ) ) .

Notation isldistrisob := isldistrmonob .
Notation isrdistrisob := isrdistrmonob .
Notation isdistrisob := isdistrmonob .

Lemma isldistrisof  { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : isldistr ( @op1 X ) ( @op2 X ) ) : isldistr ( @op1 Y ) ( @op2 Y ) .
Proof . intros . apply ( isldistrisob ( invtwobinopiso f ) is ) . Defined .   

Lemma isrdistrisof  { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : isrdistr ( @op1 X ) ( @op2 X ) ) : isrdistr ( @op1 Y ) ( @op2 Y ) .
Proof . intros . apply ( isrdistrisob ( invtwobinopiso f ) is ) . Defined . 

Lemma isdistrisof  { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : isdistr ( @op1 X ) ( @op2 X ) ) : isdistr ( @op1 Y ) ( @op2 Y ) .
Proof . intros . apply ( isdistrisob ( invtwobinopiso f ) is ) . Defined . 


Definition isrigopsisof { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : isrigops ( @op1 X ) ( @op2 X ) ) : isrigops ( @op1 Y ) ( @op2 Y ) .
Proof . intros. split . split with ( dirprodpair ( isabmonoidopisof ( binop1iso f ) ( rigop1axs_is is ) ) ( ismonoidopisof ( binop2iso f ) ( rigop2axs_is is ) ) ) . simpl .   change (unel_is (ismonoidopisof (binop1iso f) (rigop1axs_is is))) with ( (pr1 f ) ( rigunel1_is is ) ) .  split .  intro y . rewrite ( pathsinv0 ( homotweqinvweq f y ) ) . rewrite ( pathsinv0 ( ( pr2 ( pr2 f ) ) _ _ ) ) . apply ( maponpaths ( pr1 f ) ) .  apply ( rigmult0x_is is ) .    intro y . rewrite ( pathsinv0 ( homotweqinvweq f y ) ) . rewrite ( pathsinv0 ( ( pr2 ( pr2 f ) ) _ _ ) ) . apply ( maponpaths ( pr1 f ) ) .  apply ( rigmultx0_is is ) . apply ( isdistrisof f ) .  apply ( rigdistraxs_is is ) .  Defined . 

Definition isrigopsisob { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : isrigops ( @op1 Y ) ( @op2 Y ) ) : isrigops ( @op1 X ) ( @op2 X ) .
Proof. intros . apply ( isrigopsisof ( invtwobinopiso f ) is ) . Defined . 


Definition isrngopsisof { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : isrngops ( @op1 X ) ( @op2 X ) ) : isrngops ( @op1 Y ) ( @op2 Y ) := dirprodpair ( dirprodpair ( isabgropisof ( binop1iso f ) ( rngop1axs_is is ) ) ( ismonoidopisof ( binop2iso f ) ( rngop2axs_is is ) ) ) ( isdistrisof f ( pr2 is ) ) .

Definition isrngopsisob { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : isrngops ( @op1 Y ) ( @op2 Y ) ) : isrngops ( @op1 X ) ( @op2 X ) := dirprodpair ( dirprodpair ( isabgropisob ( binop1iso f ) ( rngop1axs_is is ) ) ( ismonoidopisob ( binop2iso f ) ( rngop2axs_is is ) ) ) ( isdistrisob f ( pr2 is ) ) .


Definition iscommrngopsisof { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : iscommrngops ( @op1 X ) ( @op2 X ) ) : iscommrngops ( @op1 Y ) ( @op2 Y ) := dirprodpair ( isrngopsisof f is ) ( iscommisof ( binop2iso f ) ( pr2 is ) ) .

Definition iscommrngopsisob { X Y : setwith2binop } ( f : twobinopiso X Y ) ( is : iscommrngops ( @op1 Y ) ( @op2 Y ) ) : iscommrngops ( @op1 X ) ( @op2 X ) := dirprodpair ( isrngopsisob f is ) ( iscommisob ( binop2iso f ) ( pr2 is ) ) .




(** **** Subobjects *)

Definition issubsetwith2binop { X : setwith2binop } ( A : hsubtypes X ) := dirprod ( forall a a' : A , A ( op1 ( pr1 a ) ( pr1 a' ) ) ) ( forall a a' : A , A ( op2 ( pr1 a ) ( pr1 a' ) ) ) .

Lemma isapropissubsetwith2binop { X : setwith2binop } ( A : hsubtypes X ) : isaprop ( issubsetwith2binop A ) .
Proof . intros . apply ( isofhleveldirprod 1 ) .
 apply impred .  intro a . apply impred . intros a' . apply ( pr2 ( A ( op1 (pr1 a) (pr1 a')) ) ) .  apply impred .  intro a . apply impred . intros a' . apply ( pr2 ( A ( op2 (pr1 a) (pr1 a')) ) ) .  Defined .

Definition subsetswith2binop { X : setwith2binop } := total2 ( fun A : hsubtypes X => issubsetwith2binop A ) .
Definition subsetswith2binoppair { X : setwith2binop } := tpair ( fun A : hsubtypes X => issubsetwith2binop A ) . 
Definition subsetswith2binopconstr { X : setwith2binop } := @subsetswith2binoppair X .  
Definition pr1subsetswith2binop ( X : setwith2binop ) : @subsetswith2binop X -> hsubtypes X := @pr1 _ ( fun A : hsubtypes X => issubsetwith2binop A ) . 
Coercion pr1subsetswith2binop : subsetswith2binop >-> hsubtypes .

Definition totalsubsetwith2binop ( X : setwith2binop ) : @subsetswith2binop X .
Proof . intros .  split with ( fun x : X => htrue ) . split . intros x x' .  apply tt .  intros . apply tt . Defined .  


Definition carrierofsubsetwith2binop { X : setwith2binop } ( A : @subsetswith2binop X ) : setwith2binop .
Proof . intros . set ( aset := ( hSetpair ( carrier A ) ( isasetsubset ( pr1carrier A ) ( setproperty X ) ( isinclpr1carrier A ) ) ) : hSet ) . split with aset . 
set ( subopp1 := ( fun a a' : A => carrierpair A ( op1 ( pr1carrier _ a ) ( pr1carrier _ a' ) ) ( pr1 ( pr2 A ) a a' ) ) : ( A -> A -> A ) ) . 
set ( subopp2 := ( fun a a' : A => carrierpair A ( op2 ( pr1carrier _ a ) ( pr1carrier _ a' ) ) ( pr2 ( pr2 A ) a a' ) ) : ( A -> A -> A ) ) .
simpl .  apply ( dirprodpair subopp1 subopp2 ) .  Defined . 

Coercion carrierofsubsetwith2binop : subsetswith2binop >-> setwith2binop . 


(** **** Quotient objects *)

Definition is2binophrel { X : setwith2binop } ( R : hrel X ) := dirprod ( @isbinophrel ( setwithbinop1 X ) R ) ( @isbinophrel ( setwithbinop2 X ) R ) . 

Lemma isapropis2binophrel { X : setwith2binop } ( R : hrel X ) : isaprop ( is2binophrel R ) . 
Proof . intros . apply ( isofhleveldirprod 1 ) .  apply isapropisbinophrel . apply isapropisbinophrel .  
Defined .    

Lemma iscomp2binoptransrel { X : setwith2binop } ( R : hrel X ) ( is : istrans R ) ( isb : is2binophrel R ) : dirprod ( iscomprelrelfun2 R R ( @op1 X ) ) ( iscomprelrelfun2 R R ( @op2 X ) ) .
Proof . intros . split . apply ( @iscompbinoptransrel ( setwithbinop1 X ) R is ( pr1 isb ) ) . apply ( @iscompbinoptransrel ( setwithbinop2 X ) R is ( pr2 isb ) ) .  Defined .


Definition twobinophrel { X : setwith2binop } := total2 ( fun R : hrel X => is2binophrel R ) .
Definition twobinophrelpair { X : setwith2binop } := tpair ( fun R : hrel X => is2binophrel R ) .
Definition pr1twobinophrel ( X : setwith2binop ) : @twobinophrel X -> hrel X := @pr1 _ ( fun R : hrel X => is2binophrel R ) .
Coercion pr1twobinophrel : twobinophrel >-> hrel . 

Definition twobinoppo { X : setwith2binop } := total2 ( fun R : po X => is2binophrel R ) .
Definition twobinoppopair { X : setwith2binop } := tpair ( fun R : po X => is2binophrel R ) .
Definition pr1twobinoppo ( X : setwith2binop ) : @twobinoppo X -> po X := @pr1 _ ( fun R : po X => is2binophrel R ) .
Coercion pr1twobinoppo : twobinoppo >-> po . 

Definition twobinopeqrel { X : setwith2binop } := total2 ( fun R : eqrel X => is2binophrel R ) .
Definition twobinopeqrelpair { X : setwith2binop } := tpair ( fun R : eqrel X => is2binophrel R ) .
Definition pr1twobinopeqrel ( X : setwith2binop ) : @twobinopeqrel X -> eqrel X := @pr1 _ ( fun R : eqrel X => is2binophrel R ) .
Coercion pr1twobinopeqrel : twobinopeqrel >-> eqrel . 

Definition setwith2binopquot { X : setwith2binop } ( R : @twobinopeqrel X ) : setwith2binop .
Proof . intros . split with ( setquotinset R )  .  set ( qt  := setquot R ) . set ( qtset := setquotinset R ) .  
assert ( iscomp1 : iscomprelrelfun2 R R ( @op1 X ) ) . apply ( pr1 ( iscomp2binoptransrel ( pr1 R ) ( eqreltrans _ ) ( pr2 R ) ) ) .  set ( qtop1 := setquotfun2 R R ( @op1 X ) iscomp1 ) .   
assert ( iscomp2 : iscomprelrelfun2 R R ( @op2 X ) ) . apply ( pr2 ( iscomp2binoptransrel ( pr1 R ) ( eqreltrans _ ) ( pr2 R ) ) ) .  set ( qtop2 := setquotfun2 R R ( @op2 X ) iscomp2 ) .  
simpl . apply ( dirprodpair qtop1 qtop2 )  . Defined . 


(** **** Direct products *)

Definition setwith2binopdirprod ( X Y : setwith2binop ) : setwith2binop .
Proof . intros . split with ( setdirprod X Y ) . simpl . apply ( dirprodpair ( fun xy xy' : _ => dirprodpair ( op1 ( pr1 xy ) ( pr1 xy' ) ) ( op1 ( pr2 xy ) ( pr2 xy' ) ) ) ( fun xy xy' : _ => dirprodpair ( op2 ( pr1 xy ) ( pr1 xy' ) ) ( op2 ( pr2 xy ) ( pr2 xy' ) ) ) ) . Defined .  







(* End of the file algebra1a.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)