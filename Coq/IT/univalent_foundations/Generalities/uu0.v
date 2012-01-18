(** * Univalent Basics. Vladimir Voevodsky. Feb. 2010 - Sep. 2011 

This file contains results which form a basis of the univalent approach and which do not require the use of universes as types. Fixpoints with values in a universe are used only once in the definition [ isofhlevel ]. Many results in this file do not require any axioms. The first axiom we use is [ funextempty ] which is the functional extensionality axiom for functions with values in the empty type. Closer to the end of the file we use general functional extensionality [ funextfunax ] asserting that two homotopic functions are equal. Since [ funextfunax ] itself is not an "axiom"  in our sense i.e. its type is not of h-level 1 we show that it is logically equivalent to a real axiom [ funcontr ] which asserts that the space of sections of a family with contractible fibers is contractible.  


 *) 



(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)

(** Imports *)

Require Export uuu.

(** Universe structure *)

Definition UU := Type .

(* end of "Preambule". *)





(** ** Some standard constructions not using identity types (paths) *)

(** *** Canonical functions from [ empty ] and to [ unit ] *)

Definition fromempty { X : UU } : empty -> X.
Proof. intros X H.  destruct H. Defined. 

Definition tounit { X : UU } : X -> unit := fun x : X => tt .

(** *** Functions from [ unit ] corresponding to terms *)

Definition termfun { X : UU } ( x : X ) : unit -> X := fun t : unit => x .


(** *** Identity functions and function composition *)

Definition idfun ( T : UU ) := fun t : T => t .

Definition funcomp { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) := fun x : X => g ( f x ) . 

(** *** Iteration of an endomorphism *)

Fixpoint iteration { T : UU } ( f : T -> T ) ( n : nat ) : T -> T := match n with 
O => idfun T |
S m => funcomp ( iteration f m ) f 
end .


(** ***  Basic constructions related to the adjoint evaluation function [ X -> ( ( X -> Y ) -> Y ) ] *)

Definition adjev { X Y : UU } ( x : X ) ( f : X -> Y ) : Y := f x.

Definition adjev2 { X Y : UU } ( phi : ( ( X -> Y ) -> Y ) -> Y ) : X -> Y  :=  (fun  x : X => phi ( fun f : X -> Y => f x ) ) .


(** *** Pairwise direct products *)

Definition dirprod ( X Y : UU ) := total2 ( fun x : X => Y ) .
Definition dirprodpair { X Y : UU } := tpair ( fun x : X => Y ) .

Definition dirprodadj { X Y Z : UU } ( f : dirprod X Y -> Z ) : X -> Y -> Z :=  fun x : X => fun y : Y => f ( dirprodpair x y ) .

Definition dirprodf { X Y X' Y' : UU } ( f : X -> Y ) ( f' : X' -> Y' ) ( xx' : dirprod X X' )  : dirprod Y Y' :=  dirprodpair ( f ( pr1 xx') ) ( f' ( pr2 xx' ) ) .  

Definition ddualand { X Y P : UU } (xp : ( X -> P ) -> P ) ( yp : ( Y -> P ) -> P ) : ( dirprod X Y -> P ) -> P.
Proof. intros X Y P xp yp X0 . set ( int1 := fun ypp : ( ( Y -> P ) -> P ) => fun x : X => yp ( fun y : Y => X0 ( dirprodpair x y) ) ) . apply ( xp ( int1 yp ) ) . Defined . 

(** *** Negation and double negation *)


Definition neg ( X : UU ) : UU := X -> empty.

Definition negf { X Y : UU } ( f : X -> Y ) : neg Y -> neg X := fun phi : Y -> empty => fun x : X => phi ( f x ) .

Definition dneg ( X : UU ) : UU := ( X -> empty ) -> empty .

Definition dnegf { X Y : UU } ( f : X -> Y ) : dneg X -> dneg Y := negf ( negf f ) .

Definition todneg ( X : UU ) : X -> dneg X := adjev .

Definition dnegnegtoneg { X : UU } : dneg ( neg X ) ->  neg X := adjev2  .

Lemma dneganddnegl1 { X Y : UU } ( dnx : dneg X ) ( dny : dneg Y ) : neg ( X -> neg Y ) .
Proof. intros. intro X2. assert ( X3 : dneg X -> neg Y ) . apply ( fun xx : dneg X => dnegnegtoneg ( dnegf X2 xx ) ) .  apply ( dny ( X3 dnx ) ) . Defined.

Definition dneganddnegimpldneg { X Y : UU } ( dnx : dneg X ) ( dny : dneg Y ) : dneg ( dirprod X Y ) := ddualand dnx dny. 


(** *** Logical equivalence *)


Definition logeq ( X Y : UU ) := dirprod ( X -> Y ) ( Y -> X ) .
Notation " X <-> Y " := ( logeq X Y ) : type_scope .  


Definition logeqnegs { X Y : UU } ( l : X <-> Y ) : ( neg X ) <-> ( neg Y ) := dirprodpair ( negf ( pr2 l ) ) ( negf ( pr1 l ) ) . 




(* end of "Some standard constructions not using idenity types (paths)". *)






(** ** Operations on [ paths ] *)



(** *** Composition of paths and inverse paths *)

 
Definition pathscomp0 { X : UU } { a b c : X } ( e1 : paths a b ) ( e2 : paths b c ) : paths a c .
Proof. intros. destruct e1. apply e2 . Defined.
Hint Resolve @pathscomp0 : pathshints .

Definition pathscomp0rid { X : UU } { a b : X } ( e1 : paths a b ) : paths ( pathscomp0 e1 ( idpath b ) ) e1 . 
Proof. intros. destruct e1. simpl. apply idpath.  Defined. 

(** Note that we do no need [ pathscomp0lid ] since the corresponding two terms are convertible to each other due to our definition of [ pathscomp0 ] . If we defined it by destructing [ e2 ] and applying [ e1 ] then [ pathsinv0rid ] would be trivial but [ pathsinv0lid ] would require a proof. Similarly we do not need a lemma to connect [ pathsinv0 ( idpath _ ) ] to [ idpath ] *)

Definition pathsinv0 { X : UU } { a b : X } ( e : paths a b ) : paths b a .
Proof. intros. destruct e.  apply idpath. Defined. 
Hint Resolve @pathsinv0 : pathshints .

Definition pathsinv0l { X : UU } { a b : X } ( e : paths a b ) : paths ( pathscomp0 ( pathsinv0 e ) e ) ( idpath _ ) .
Proof. intros. destruct e.  apply idpath. Defined. 

Definition pathsinv0r { X : UU } { a b : X } ( e : paths a b ) : paths ( pathscomp0 e ( pathsinv0 e ) ) ( idpath _ ) .
Proof. intros. destruct e.  apply idpath. Defined. 

Definition pathsinv0inv0 { X : UU } { x x' : X } ( e : paths x x' ) : paths ( pathsinv0 ( pathsinv0 e ) ) e .
Proof. intros. destruct e. apply idpath. Defined.  



(** *** Direct product of paths  *)

Definition pathsdirprod { X Y : UU } { x1 x2 : X } { y1 y2 : Y } ( ex : paths x1 x2 ) ( ey : paths y1 y2 ) : paths ( dirprodpair x1 y1 ) ( dirprodpair x2 y2 ) .
Proof . intros . destruct ex . destruct ey . apply idpath . Defined . 


(** *** The function [ maponpaths ] between paths types defined by a function between abmbient paths and its behavior relative to [ pathscomp0 ] and [ pathsinv0 ] *)

Definition maponpaths { T1 T2 : UU } ( f : T1 -> T2 ) { t1 t2 : T1 } ( e: paths t1 t2 ) : paths ( f t1 ) ( f t2 ) .
Proof. intros .  destruct e . apply idpath. Defined. 

Definition maponpathscomp0 { X Y : UU } { x1 x2 x3 : X } ( f : X -> Y ) ( e1 : paths x1 x2 ) ( e2 : paths x2 x3 ) : paths ( maponpaths f ( pathscomp0  e1 e2 ) ) ( pathscomp0 ( maponpaths f e1 ) ( maponpaths f e2 ) ) .
Proof. intros.  destruct e1. destruct e2.  simpl. apply idpath. Defined. 

Definition maponpathsinv0 { X Y : UU } ( f : X -> Y ) { x1 x2 : X } ( e : paths x1 x2 ) : paths ( maponpaths f ( pathsinv0 e ) ) ( pathsinv0 ( maponpaths f e ) ) .
Proof. intros . destruct e . apply idpath . Defined .  



(** *** [ maponpaths ] for the identity functions and compositions of functions *)

Lemma maponpathsidfun { X : UU } { x x' : X } ( e : paths x x' ) : paths ( maponpaths ( idfun X ) e ) e . 
Proof. intros. destruct e. apply idpath . Defined. 

Lemma maponpathscomp { X Y Z : UU } { x x' : X } ( f : X -> Y ) ( g : Y -> Z ) ( e : paths x x' ) : paths ( maponpaths g ( maponpaths f e ) ) ( maponpaths ( funcomp f g ) e) .
Proof. intros. destruct e.  apply idpath. Defined. 





(** The following four statements show that [ maponpaths ] defined by a function f which is homotopic to the identity is "surjective". It is later used to show that the maponpaths defined by a function which is a weak equivalence is itself a weak equivalence. *) 


Definition maponpathshomidinv { X : UU } (f:X -> X) ( h: forall x:X, paths (f x) x) ( x x' : X ) : paths (f x) (f x') -> paths x x' := (fun e: paths (f x) (f x') => pathscomp0   (pathsinv0  (h x)) (pathscomp0 e (h x'))).


Lemma maponpathshomid1 { X : UU } (f:X -> X) (h: forall x:X, paths (f x) x) { x x' : X } (e:paths x x'): paths (maponpaths f e) (pathscomp0 (h x) (pathscomp0 e (pathsinv0 (h x')))).
Proof. intros. destruct e. change (pathscomp0 (idpath x) (pathsinv0 (h x))) with (pathsinv0 (h x)). assert (ee: paths  (maponpaths f (idpath x)) (idpath (f x))). apply idpath .  
assert (eee: paths (idpath (f x)) (pathscomp0  (h x)  (pathsinv0 (h x)))). apply (pathsinv0  (pathsinv0r  (h x))). apply (pathscomp0   ee eee). Defined. 


Lemma maponpathshomid12 { X : UU } { x x' fx fx' : X } (e:paths fx fx') (hx:paths fx x) (hx':paths fx' x') : paths   (pathscomp0 hx (pathscomp0 (pathscomp0 (pathsinv0 hx) (pathscomp0 e hx')) (pathsinv0 hx'))) e.
Proof. intros. destruct hx. destruct hx'. destruct e.  simpl. apply idpath. Defined. 


Lemma maponpathshomid2 { X : UU } (f:X->X) (h: forall x:X, paths (f x) x) ( x x' : X ) (e:paths (f x) (f x')) : paths (maponpaths f (maponpathshomidinv f h _ _ e)) e.
Proof.  intros. assert (ee: paths (pathscomp0   (h x) (pathscomp0   (pathscomp0   (pathsinv0  (h x)) (pathscomp0   e (h x'))) (pathsinv0  (h x')))) e). apply (maponpathshomid12 e (h x) (h x')). assert (eee: paths (maponpaths f (pathscomp0   (pathsinv0  (h x)) (pathscomp0   e (h x')))) (pathscomp0   (h x) (pathscomp0   (pathscomp0   (pathsinv0  (h x)) (pathscomp0   e (h x'))) (pathsinv0  (h x'))))). apply maponpathshomid1. apply (pathscomp0   eee ee). Defined. 


(** Here we consider the behavior of maponpaths in the case of a projection [ p ] with a section [ s ]. *)



Definition pathssec1 { X Y : UU } ( s : X -> Y ) ( p : Y -> X ) ( eps : forall x:X , paths ( p ( s x ) ) x ) ( x : X ) ( y : Y ) ( e : paths (s x) y ) : paths x (p y) := pathscomp0 ( pathsinv0 ( eps x ) ) ( maponpaths p e ) .  

Definition pathssec2 { X Y : UU } ( s : X -> Y ) ( p : Y -> X ) ( eps : forall x : X , paths ( p ( s x ) ) x ) ( x x' : X ) ( e : paths ( s x ) ( s x' ) ) : paths x x'.
Proof. intros . set ( e' := pathssec1 s p eps _ _ e ) . apply ( pathscomp0 e' ( eps x' ) ) . Defined .

Definition pathssec2id { X Y : UU } ( s : X -> Y ) ( p : Y -> X ) ( eps : forall x : X , paths ( p ( s x ) ) x ) ( x : X ) : paths ( pathssec2 s p eps _ _  ( idpath ( s x ) ) ) ( idpath x ) .
Proof. intros.  unfold pathssec2. unfold pathssec1. simpl.   assert (e: paths (pathscomp0 (pathsinv0 (eps x)) (idpath (p (s x)))) (pathsinv0 (eps x))). apply pathscomp0rid. assert (ee: paths 
(pathscomp0  (pathscomp0 (pathsinv0 (eps x)) (idpath (p (s x)))) (eps x)) 
(pathscomp0 (pathsinv0 (eps x)) (eps x))). 
apply (maponpaths (fun e0: _ => pathscomp0 e0 (eps x)) e). assert (eee: paths (pathscomp0 (pathsinv0 (eps x)) (eps x)) (idpath x)).  apply (pathsinv0l (eps x)). apply (pathscomp0 ee eee). Defined. 


Definition pathssec3 { X Y : UU } (s:X-> Y) (p:Y->X) (eps: forall x:X, paths (p (s x)) x) { x x' : X } ( e : paths x x' ) : paths  (pathssec2  s p eps  _ _ (maponpaths s  e)) e.
Proof. intros. destruct e.  simpl. unfold pathssec2. unfold pathssec1.  simpl. apply pathssec2id.  Defined. 


(* end of "Operations on [ paths ]". *) 









(** ** Fibrations and paths *)


Definition tppr { T : UU } { P : T -> UU } ( x : total2 P ) : paths x ( tpair _ (pr1 x) (pr2 x) ) .
Proof. intros. destruct x. apply idpath. Defined. 

Definition constr1 { X : UU } ( P : X -> UU ) { x x' : X } ( e : paths x x' ) : total2 (fun f: P x -> P x' => ( total2 ( fun ee : forall p : P x, paths (tpair _ x p) (tpair _ x' ( f p ) ) => forall pp : P x, paths (maponpaths ( @pr1 _ _ ) ( ee pp ) ) e ) ) ) . 
Proof. intros. destruct e. split with ( idfun ( P x ) ). simpl. split with (fun p : P x => idpath _ ) . unfold maponpaths. simpl. apply (fun pp : P x => idpath _ ) . Defined. 

Definition transportf { X : UU } ( P : X -> UU ) { x x' : X } ( e : paths x x' ) : P x -> P x' := pr1 ( constr1 P e ) .

Definition transportb { X : UU } ( P : X -> UU ) { x x' : X } ( e : paths x x' ) : P x' -> P x := transportf P ( pathsinv0 e ) .


Lemma functtransportf { X Y : UU } ( f : X -> Y ) ( P : Y -> UU ) { x x' : X } ( e : paths x x' ) ( p : P ( f x ) ) : paths ( transportf ( fun x => P ( f x ) ) e p ) ( transportf P ( maponpaths f e ) p ) .
Proof.  intros.  destruct e. apply idpath. Defined.   



(** ** First homotopy notions *)

(** *** Homotopy between functions *)


Definition homot { X Y : UU } ( f g : X -> Y ) := forall x : X , paths ( f x ) ( g x ) .


(** *** Contractibility, homotopy fibers etc. *)


(** Contractible types. *)

Definition iscontr (T:UU) : UU := total2 (fun cntr:T => forall t:T, paths t cntr).
Definition iscontrpair { T : UU }  := tpair (fun cntr:T => forall t:T, paths t cntr).
Definition iscontrpr1 { T : UU } := @pr1 T ( fun cntr:T => forall t:T, paths t cntr ) .

Lemma iscontrretract { X Y : UU } ( p : X -> Y ) ( s : Y -> X ) ( eps : forall y : Y, paths ( p ( s y ) ) y  ) ( is : iscontr X ) : iscontr Y.
Proof . intros . destruct is as [ x fe ] . set ( y := p x ) . split with y . intro y' . apply ( pathscomp0 ( pathsinv0 ( eps y' ) ) ( maponpaths p ( fe ( s y' ) ) ) ) .  Defined .    

Lemma proofirrelevancecontr { X : UU }(is: iscontr X) ( x x' : X ): paths x x'.
Proof. intros. unfold iscontr in is.  destruct is as [ t x0 ]. set (e:= x0 x). set (e':= pathsinv0 (x0 x')). apply (pathscomp0 e e'). Defined. 


(** Coconuses - spaces of paths which begin or end at a given point. *)  


Definition coconustot ( T : UU ) ( t : T ) := total2 (fun t':T => paths t' t).
Definition coconustotpair ( T : UU ) { t t' : T } (e: paths t' t) : coconustot T t := tpair (fun t':T => paths t' t) t' e.
Definition coconustotpr1 ( T : UU ) ( t : T ) := @pr1 _ (fun t':T => paths t' t) . 

Lemma connectedcoconustot { T : UU }  { t : T } ( c1 c2 : coconustot T t ) : paths c1 c2.
Proof. intros. destruct c1 as [ x0 x ]. destruct x. destruct c2 as [ x1 x ]. destruct x. apply idpath. Defined. 

Lemma iscontrcoconustot ( T : UU ) (t:T) : iscontr (coconustot T t).
Proof. intros. unfold iscontr.  set (t0:= tpair (fun t':T => paths t' t) t (idpath t)).  split with t0. intros. apply  connectedcoconustot. Defined.



Definition coconusfromt ( T : UU ) (t:T) :=  total2 (fun t':T => paths t t').
Definition coconusfromtpair ( T : UU ) { t t' : T } (e: paths t t') : coconusfromt T t := tpair (fun t':T => paths t t') t' e.
Definition coconusfromtpr1 ( T : UU ) ( t : T ) := @pr1 _ (fun t':T => paths t t') .

Lemma connectedcoconusfromt { T : UU } { t : T } ( e1 e2 : coconusfromt T t ) : paths e1 e2.
Proof. intros. destruct e1 as [x0 x]. destruct x. destruct e2 as [ x1 x ]. destruct x. apply idpath. Defined.

Lemma iscontrcoconusfromt ( T : UU ) (t:T) : iscontr (coconusfromt T t).
Proof. intros. unfold iscontr.  set (t0:= tpair (fun t':T => paths t t') t (idpath t)).  split with t0. intros. apply  connectedcoconusfromt. Defined.

(** Pathsspace of a type. *)

Definition pathsspace (T:UU) := total2 (fun t:T => coconusfromt T t).
Definition pathsspacetriple ( T : UU ) { t1 t2 : T } (e: paths t1 t2): pathsspace T := tpair _ t1 (coconusfromtpair T e). 

Definition deltap ( T : UU ) : T -> pathsspace T := (fun t:T => pathsspacetriple T (idpath t)). 

Definition pathsspace' ( T : UU ) := total2 (fun xy : dirprod T T => (match xy with tpair x y => paths x y end)).


(** Homotopy fibers. *)

Definition hfiber { X Y : UU } (f:X -> Y) (y:Y) : UU := total2 (fun pointover:X => paths (f pointover) y). 
Definition hfiberpair  { X Y : UU } (f:X -> Y) { y : Y } ( x : X ) ( e : paths ( f x ) y ) := tpair (fun pointover:X => paths (f pointover) y) x e .
Definition hfiberpr1 { X Y : UU } ( f : X -> Y ) ( y : Y ) := @pr1 _ (fun pointover:X => paths (f pointover) y) . 



(** Paths in homotopy fibers. *)

Lemma hfibertriangle1 { X Y : UU } (f:X -> Y) { y : Y } { xe1 xe2: hfiber  f y } (e: paths xe1 xe2): paths (pr2 xe1) (pathscomp0   (maponpaths f (maponpaths ( @pr1 _ _ ) e)) (pr2 xe2)).
Proof. intros. destruct e.  simpl. apply idpath. Defined. 

Lemma hfibertriangle1inv0 { X Y : UU } (f:X -> Y) { y : Y } { xe1 xe2: hfiber  f y } (e: paths xe1 xe2) :  paths ( pathscomp0 ( maponpaths f ( pathsinv0 ( maponpaths ( @pr1 _ _ ) e ) ) ) ( pr2 xe1 ) ) ( pr2 xe2 ) .
Proof . intros . destruct e .   apply idpath . Defined .


Lemma hfibertriangle2 { X Y : UU } (f:X -> Y) { y : Y } (xe1 xe2: hfiber  f y) (ee: paths (pr1  xe1) (pr1  xe2))(eee: paths (pr2 xe1) (pathscomp0   (maponpaths f ee) (pr2 xe2))): paths xe1 xe2.
Proof. intros. destruct xe1 as [ t e1 ]. destruct xe2.   simpl in eee. simpl in ee. destruct ee. simpl in eee. apply (maponpaths (fun e: paths (f t) y => hfiberpair f t e)  eee). Defined. 


(** Coconus of a function - the total space of the family of h-fibers. *)

Definition coconusf { X Y : UU } (f: X -> Y):= total2 (fun y:_ => hfiber f y).
Definition fromcoconusf { X Y : UU } (f: X -> Y) : coconusf  f -> X := fun yxe:_ => pr1  (pr2 yxe).
Definition tococonusf { X Y:UU } (f: X -> Y) : X -> coconusf  f := fun x:_ => tpair  _  (f x) (hfiberpair f x (idpath _ ) ).   












(** ** Weak equivalences *)

(** *** Basics *)


Definition isweq { X Y : UU } ( f : X -> Y) : UU := forall y:Y, iscontr (hfiber f y) .

Lemma idisweq (T:UU) : isweq (fun t:T => t).
Proof. intros. 
unfold isweq.
intro y .
assert (y0: hfiber (fun t : T => t) y). apply (tpair (fun pointover:T => paths ((fun t:T => t) pointover) y) y (idpath y)). 
split with y0. intro t.  
destruct y0 as [x0 e0].    destruct t as [x1 e1].  destruct  e0.  destruct e1.  apply idpath. Defined. 



Definition weq ( X Y : UU )  : UU := total2 (fun f:X->Y => isweq f) .
Definition pr1weq ( X Y : UU):= @pr1 _ _ : weq X Y -> (X -> Y).
Coercion pr1weq : weq >-> Funclass. 
Definition weqpair { X Y : UU } (f:X-> Y) (is: isweq f) : weq X Y := tpair (fun f:X->Y => isweq f) f is. 
Definition idweq (X:UU) : weq X X :=  tpair (fun f:X->X => isweq f) (fun x:X => x) ( idisweq X ) .


Definition isweqtoempty { X : UU } (f : X -> empty ) : isweq f.
Proof. intros. intro y.  apply (fromempty y). Defined. 

Definition weqtoempty { X : UU } ( f : X -> empty )  := weqpair _ ( isweqtoempty f ) .

Lemma isweqtoempty2 { X Y : UU } ( f : X -> Y ) ( is : neg Y ) : isweq f .
Proof. intros . intro y . destruct ( is y ) . Defined . 

Definition weqtoempty2 { X Y : UU } ( f : X -> Y ) ( is : neg Y ) := weqpair _ ( isweqtoempty2 f is ) .

Definition invmap { X Y : UU } ( w : weq X Y ) : Y -> X .
Proof. intros X Y w y . apply (pr1  (pr1  ( pr2 w y ))). Defined.


(** We now define different homotopies and maps between the paths spaces corresponding to a weak equivalence. What may look like unnecessary complexity in the  definition of [ weqgf ] is due to the fact that the "naive" definition, that of [ weqgf00 ], needs to be corrected in order for lemma [ weqfgf ] to hold. *)



Definition homotweqinvweq { T1 T2 : UU } ( w : weq T1 T2 ) : forall t2:T2, paths ( w ( invmap w t2 ) ) t2.
Proof. intros. unfold invmap. simpl. apply (pr2  (pr1 ( pr2 w t2 ) ) ) . Defined.


Definition homotinvweqweq0  { X Y : UU } ( w : weq X Y ) ( x : X ) : paths x ( invmap w ( w x ) ) .
Proof. intros. set (isfx:= ( pr2 w ( w x ) ) ). set (pr1fx:= @pr1 X (fun x':X => paths ( w x' ) ( w x ))).
set (xe1:= (hfiberpair  w x (idpath ( w x)))). apply  (maponpaths pr1fx  (pr2 isfx xe1)). Defined.

Definition homotinvweqweq { X Y : UU } ( w : weq X Y )  ( x : X ) : paths (invmap w ( w x ) ) x := pathsinv0  (homotinvweqweq0 w x).

Lemma diaglemma2 { X Y : UU } (f:X -> Y) { x x':X } (e1: paths x x')(e2: paths (f x') (f x)) (ee: paths (idpath (f x)) (pathscomp0 (maponpaths f e1) e2)): paths (maponpaths f  (pathsinv0 e1)) e2.
Proof. intros.  destruct e1. simpl. simpl in ee. assumption. Defined. 

Definition homotweqinvweqweq { X Y : UU } ( w : weq X Y ) ( x : X ) : paths  (maponpaths w (homotinvweqweq w x)) (homotweqinvweq w ( w x)).
Proof. intros.    set (xe1:= hfiberpair w x (idpath (w x))). set (isfx:= ( pr2 w ) (w x)).   set (xe2:= pr1  isfx). set (e:= pr2  isfx xe1). set (ee:=hfibertriangle1 w e). simpl in ee.
apply (diaglemma2 w (homotinvweqweq0 w x) ( homotweqinvweq w ( w x ) ) ee ). Defined.


Definition invmaponpathsweq { X Y : UU } ( w : weq X Y ) ( x x' : X ) : paths (w x) (w x') -> paths x x':= pathssec2  w (invmap w ) (homotinvweqweq w ) _ _ .

Definition invmaponpathsweqid { X Y : UU } ( w : weq X Y ) ( x : X ) :  paths (invmaponpathsweq w _ _ (idpath (w x))) (idpath x):= pathssec2id w  (invmap w ) (homotinvweqweq w ) x.


Definition pathsweq1 { X Y : UU } ( w : weq X Y ) ( x : X ) ( y : Y ) : paths (w x) y -> paths x (invmap w y) := pathssec1  w (invmap w ) (homotinvweqweq w ) _ _ .

Definition pathsweq1' { X Y : UU } ( w : weq X Y )  ( x : X ) ( y : Y ) : paths x (invmap w y) -> paths ( w x ) y := fun e:_ => pathscomp0   (maponpaths w e) (homotweqinvweq w y).


Definition pathsweq3 { X Y : UU } ( w : weq X Y ) { x x' : X } ( e : paths x x' ) : paths  (invmaponpathsweq w x x' (maponpaths w e)) e:= pathssec3 w (invmap w ) (homotinvweqweq w ) _ .

Definition pathsweq4  { X Y : UU } ( w : weq X Y ) ( x x' : X ) ( e : paths ( w x ) ( w x' )) : paths (maponpaths w (invmaponpathsweq w x x' e)) e.  
Proof. intros. destruct w as [ f is1 ] . set ( w := weqpair f is1 ) . set (g:=invmap w ). set (gf:= fun x:X => (g (f x))).  set (ee:= maponpaths g  e). set (eee:= maponpathshomidinv  gf (homotinvweqweq  w ) x x' ee ). 
assert (e1: paths (maponpaths f  eee) e). 
assert (e2: paths (maponpaths g  (maponpaths f  eee)) (maponpaths g  e)). 
assert (e3: paths (maponpaths g  (maponpaths f  eee)) (maponpaths gf  eee)). apply maponpathscomp. 
assert (e4: paths (maponpaths gf eee) ee). apply maponpathshomid2. apply (pathscomp0   e3 e4). 
set (s:= @maponpaths _ _ g (f x) (f x')). set (p:= @pathssec2  _ _ g f (homotweqinvweq w ) (f x) (f x')). set (eps:= @pathssec3  _ _ g f (homotweqinvweq w ) (f x) (f x')).  apply (pathssec2  s p eps _ _  e2 ). 
assert (e5: paths (maponpaths f  (invmaponpathsweq w x x' e)) (maponpaths f (invmaponpathsweq w x x' (maponpaths f eee)))). apply (pathsinv0 (maponpaths (fun e0: paths (f x) (f x') => (maponpaths f  (invmaponpathsweq w x x' e0))) e1)). 
assert (X0: paths  (invmaponpathsweq w x x' (maponpaths f eee)) eee). apply (pathsweq3 w ). 
assert (e6: paths (maponpaths f (invmaponpathsweq w x x' (maponpaths f eee))) (maponpaths f eee)). apply (maponpaths (fun eee0: paths x x' => maponpaths f eee0) X0). set (e7:= pathscomp0   e5 e6). set (pathscomp0   e7 e1). 
assumption. Defined. 










(** *** Weak equivalences between contractible types (other implications are proved below) *)



Lemma iscontrweqb { X Y : UU } ( w : weq X Y ) ( is : iscontr Y ) : iscontr X.
Proof. intros . apply ( iscontrretract (invmap w ) w (homotinvweqweq w ) is ).  Defined. 




(** *** Functions between fibers defined by a path on the base are weak equivalences *)






Lemma isweqtransportf { X : UU } (P:X -> UU) { x x' : X } (e:paths x x'): isweq (transportf P e).
Proof. intros. destruct e. apply idisweq. Defined. 


Lemma isweqtransportb { X : UU } (P:X -> UU) { x x' : X } (e:paths x x'): isweq (transportb P e).
Proof. intros. apply (isweqtransportf  _ (pathsinv0  e)). Defined. 





(** *** [ unit ] and contractibility *)

(** [ unit ] is contractible (recall that [ tt ] is the name of the canonical term of the type [ unit ]). *)

Lemma unitl0: paths tt tt -> coconustot _ tt.
Proof. intros X. apply (coconustotpair _ X). Defined.

Lemma unitl1: coconustot _ tt -> paths tt tt.
Proof. intro X. destruct X as [ x t ]. destruct x.  assumption.  Defined.

Lemma unitl2: forall e: paths tt tt, paths  (unitl1 (unitl0 e)) e.
Proof. intros. unfold unitl0. simpl.  apply idpath.  Defined.

Lemma unitl3: forall e:paths tt tt, paths  e (idpath tt).
Proof. intros.
assert (e0: paths (unitl0 (idpath tt)) (unitl0 e)). eapply connectedcoconustot.
assert (e1:paths  (unitl1 (unitl0 (idpath tt))) (unitl1 (unitl0 e))).   apply (maponpaths  unitl1  e0).    
assert (e2:  paths  (unitl1 (unitl0 e)) e). eapply unitl2.
assert (e3: paths   (unitl1 (unitl0 (idpath tt))) (idpath tt)). eapply unitl2.
 destruct e1. clear e0. destruct e2. assumption.  Defined. 


Theorem iscontrunit: iscontr (unit).
Proof. assert (pp:forall x:unit, paths x tt). intros. destruct x. apply (idpath _).
apply (tpair (fun cntr:unit => forall t:unit, paths  t cntr) tt pp). Defined. 


(** [ paths ] in [ unit ] are contractible. *)

Theorem iscontrpathsinunit ( x x' : unit ) : iscontr ( paths x x' ) .
Proof. intros . assert (c:paths x x'). destruct x. destruct x'. apply idpath.
assert (X: forall g:paths x x', paths g c). intro. assert (e:paths c c).   apply idpath. destruct c. destruct x. apply unitl3. apply (iscontrpair c X). Defined.  



(**  A type [ T : UU ] is contractible if and only if [ T -> unit ] is a weak equivalence. *)


Lemma ifcontrthenunitl0 ( e1 e2 : paths tt tt ) : paths e1 e2.
Proof. intros. assert (e3: paths e1 (idpath tt) ). apply unitl3.
assert (e4: paths e2 (idpath tt)). apply unitl3. destruct e3.  destruct e4. apply idpath. Defined. 


Lemma isweqcontrtounit { T : UU } (is : iscontr T) : (isweq (fun t:T => tt)).
Proof. intros T X. unfold isweq. intro y. destruct y.
assert (c: hfiber  (fun x:T => tt) tt). destruct X as [ t x0 ]. eapply (hfiberpair _ t (idpath tt)).
assert (e: forall d: (hfiber (fun x:T => tt) tt), paths d c). intros. destruct c as [ t x] . destruct d as [ t0 x0 ]. 
assert (e': paths  x x0). apply ifcontrthenunitl0 .
assert (e'': paths  t t0). destruct X as [t1 x1 ].
assert (e''': paths t t1). apply x1.
assert (e'''': paths t0 t1). apply x1. 
destruct e''''. assumption.
destruct e''. destruct e'. apply idpath. apply (iscontrpair c e). Defined. 

Definition weqcontrtounit { T : UU } ( is : iscontr T ) := weqpair _ ( isweqcontrtounit is ) . 

Theorem iscontrifweqtounit { X : UU } ( w : weq X unit ) : iscontr X.
Proof. intros X X0.  apply (iscontrweqb X0 ). apply iscontrunit. Defined. 





(** *** A homotopy equivalence is a weak equivalence *)


Definition hfibersgftog { X Y Z : UU } (f:X -> Y) (g: Y -> Z) (z:Z) ( xe : hfiber  (fun x:X => g(f x)) z ) : hfiber  g z := hfiberpair g ( f ( pr1 xe ) ) ( pr2 xe ) .


Lemma constr2 { X Y : UU } (f:X -> Y)(g: Y-> X) (efg: forall y:Y, paths (f(g y)) y) ( x0 : X) ( z0 : hfiber  g x0 ) : total2  (fun z': hfiber  (fun x:X => g (f x)) x0  => paths z0 (hfibersgftog  f g x0 z')). 
Proof. intros.  destruct z0 as [ y e ]. 

assert (eint: paths y (f x0 )).  assert (e0: paths (f(g y)) y). apply efg. assert (e1: paths (f(g y)) (f x0 )). apply (maponpaths  f  e). destruct e1.  apply pathsinv0. assumption. 

set (int1:=constr1 (fun y:Y => paths (g y) x0 ) eint). destruct int1 as [ t x ].
set (int2:=hfiberpair  (fun x0 : X => g (f x0)) x0 (t e)).   split with int2.  apply x.  Defined. 


Lemma iscontrhfiberl1  { X Y : UU } (f:X -> Y) (g: Y-> X) (efg: forall y:Y, paths (f(g y)) y) (x0 : X): iscontr (hfiber  (fun x:X => g (f x)) x0 ) ->iscontr (hfiber  g x0).
Proof. intros X Y f g efg x0 X0. set (X1:= hfiber  (fun x:X => g(f x)) x0 ). set (Y1:= hfiber  g x0 ). set (f1:= hfibersgftog  f g x0 ). set (g1:= fun z0:_ => pr1  (constr2  f g efg x0 z0)). 
set (efg1:= (fun y1:Y1 => pathsinv0 ( pr2  (constr2 f g efg x0 y1 ) ) ) ) .  simpl in efg1. apply ( iscontrretract  f1 g1 efg1). assumption.   Defined. 


Lemma iscontrhfiberl2 { X Y : UU } ( f1 f2 : X-> Y)  (h: forall x:X, paths (f2 x) (f1 x)) (y:Y): iscontr (hfiber  f2 y) -> iscontr (hfiber  f1 y).
Proof. intros X Y f1 f2 h y X0. 

set (f:= (fun z:(hfiber  f1 y) =>
match z with 
(tpair x e) => hfiberpair  f2 x (pathscomp0   (h x) e)
end)). 

set (g:= (fun z:(hfiber  f2 y) =>
match z with
(tpair x e) => hfiberpair  f1 x (pathscomp0   (pathsinv0 (h x)) e)
end)). 

assert (egf: forall z:(hfiber  f1 y), paths (g (f z)) z). intros. destruct z as [ x e ]. simpl .  apply ( hfibertriangle2 _ (hfiberpair f1 x (pathscomp0 (pathsinv0 (h x)) (pathscomp0 (h x) e))) ( hfiberpair f1 x e )  ( idpath x ) ) .   simpl . destruct e .   destruct ( h x ) . apply idpath .

apply ( iscontrretract  g f egf X0). Defined.

Corollary isweqhomot { X Y : UU } ( f1 f2 : X-> Y ) (h: forall x:X, paths (f1 x) (f2 x)): isweq f1 -> isweq f2.
Proof. intros X Y f1 f2 h X0. unfold isweq. intro y. set (Y0:= X0 y).  apply (iscontrhfiberl2  f2 f1 h). assumption. Defined. 



Theorem gradth { X Y : UU } (f:X->Y) (g:Y->X) (egf: forall x:X, paths (g (f x)) x) (efg: forall y:Y, paths (f (g y)) y ): isweq f.
Proof. intros.  unfold isweq.  intro z. 
assert (iscontr (hfiber  (fun y:Y => (f (g y))) z)). 
assert (efg': forall y:Y, paths y (f (g y))). intros. set (e1:= efg y). apply pathsinv0. assumption. 
apply (iscontrhfiberl2  (fun y:Y => (f (g y)))  (fun  y:Y => y)  efg' z (idisweq Y z)). 
apply (iscontrhfiberl1  g f egf z). assumption. 
Defined.

Definition weqgradth { X Y : UU } (f:X->Y) (g:Y->X) (egf: forall x:X, paths (g (f x)) x) (efg: forall y:Y, paths (f (g y)) y ) : weq X Y := weqpair _ ( gradth _ _ egf efg ) . 
 


(** *** Some basic weak equivalences *)



Corollary isweqinvmap { X Y : UU } ( w : weq X Y ) : isweq (invmap w ).
Proof. intros. set (invf:= invmap w ). assert (efinvf: forall y:Y, paths ( w (invf y)) y). apply homotweqinvweq. 
assert (einvff: forall x:X, paths (invf ( w x)) x). apply homotinvweqweq. apply ( weqgradth _ _ efinvf einvff ) . Defined. 

Definition invweq { X Y : UU } ( w : weq X Y ) : weq Y X := weqpair  (invmap w ) (isweqinvmap w ).

Corollary invinv { X Y :UU } ( w : weq X Y ) ( x : X ) : paths  ( invweq ( invweq w ) x) (w x).
Proof. intros. unfold invweq . unfold invmap . simpl . apply idpath . Defined .  


Corollary iscontrweqf { X Y : UU } ( w : weq X Y ) : iscontr X -> iscontr Y.
Proof. intros X Y w X0 . apply (iscontrweqb ( invweq w ) ). assumption. Defined.

(** The standard weak equivalence from [ unit ] to a contractible type *)

Definition wequnittocontr { X : UU } ( is : iscontr X ) : weq unit X .
Proof . intros . set ( f := fun t : unit => pr1 is ) . set ( g := fun x : X => tt ) . split with f .
assert ( egf : forall a : _ , paths ( g ( f a )) a ) . intro .  destruct a . apply idpath . 
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro . simpl .  apply ( pathsinv0 ( pr2 is a ) ) .  
apply ( gradth _ _ egf efg ) . Defined . 


(** A weak equivalence bwteen types defines weak equivalences on the corresponding [ paths ] types. *)


Corollary isweqmaponpaths { X Y : UU } ( w : weq X Y ) ( x x' : X ) : isweq (@maponpaths _ _ w x x').
Proof. intros. apply (gradth  (@maponpaths _ _ w x x') (@invmaponpathsweq _ _ w x x') (@pathsweq3 _ _ w x x')  (@pathsweq4 _ _ w x x')). Defined.  

Definition weqonpaths { X Y : UU } ( w : weq X Y ) ( x x' : X ) := weqpair _ ( isweqmaponpaths w x x' ) .


Corollary isweqpathsinv0 { X : UU } (x x':X): isweq (@pathsinv0 _ x x').
Proof. intros.  apply (gradth  (@pathsinv0 _ x x') (@pathsinv0 _ x' x) (@pathsinv0inv0 _ _ _  ) (@pathsinv0inv0  _ _ _ )). Defined.

Definition weqpathsinv0 { X : UU } ( x x' : X ) := weqpair _ ( isweqpathsinv0 x x' ) .

Corollary isweqpathscomp0r { X : UU } (x : X ) { x' x'' : X } (e': paths x' x''): isweq (fun e:paths x x' => pathscomp0   e e').
Proof. intros. set (f:= fun e:paths x x' => pathscomp0   e e'). set (g:= fun e'': paths x x'' => pathscomp0   e'' (pathsinv0 e')). 
assert (egf: forall e:_ , paths (g (f e)) e).   intro. destruct e.  simpl. destruct e'.  simpl.  apply idpath.
assert (efg: forall e'':_, paths (f (g e'')) e''). intro. destruct e''. simpl. destruct e'. simpl.   apply idpath. 
apply (gradth  f g egf efg). Defined. 


Corollary isweqtococonusf { X Y : UU } (f:X-> Y): isweq ( tococonusf  f) .
Proof . intros. set (ff:= fromcoconusf  f). set (gg:= tococonusf  f).
assert (egf: forall yxe:_, paths (gg (ff yxe)) yxe). intro. destruct yxe as [t x].   destruct x as [ x e ]. unfold gg. unfold tococonusf. unfold ff. unfold fromcoconusf.  simpl. destruct e. apply idpath.  
assert (efg: forall x:_, paths (ff (gg x)) x). intro. apply idpath.
apply (gradth _ _ efg egf ). Defined.

Definition weqtococonusf { X Y : UU } ( f : X -> Y ) : weq X ( coconusf f ) := weqpair _ ( isweqtococonusf f ) .


Corollary  isweqfromcoconusf { X Y : UU } (f:X-> Y): isweq (fromcoconusf  f).
Proof. intros. set (ff:= fromcoconusf  f). set (gg:= tococonusf  f).
assert (egf: forall yxe:_, paths (gg (ff yxe)) yxe). intro. destruct yxe as [t x].   destruct x as [ x e ]. unfold gg. unfold tococonusf. unfold ff. unfold fromcoconusf.  simpl. destruct e. apply idpath.  
assert (efg: forall x:_, paths (ff (gg x)) x). intro. apply idpath.
apply (gradth _ _ egf efg). Defined.

Definition weqfromcoconusf { X Y : UU } ( f : X -> Y ) : weq ( coconusf f ) X := weqpair _ ( isweqfromcoconusf f ) .

Corollary isweqdeltap (T:UU) : isweq (deltap T).
Proof. intros. set (ff:=deltap T). set (gg:= fun z:pathsspace T => pr1  z). 
assert (egf: forall t:T, paths (gg (ff t)) t). intro. apply idpath.
assert (efg: forall tte: pathsspace T, paths (ff (gg tte)) tte). intro. destruct tte as [ t x ].  destruct x as [ x0 e ]. destruct e. apply idpath. 
apply (gradth _ _ egf efg). Defined. 


Corollary isweqpr1pr1 (T:UU) : isweq (fun a: pathsspace' T => (pr1  (pr1  a))).
Proof. intros. set (f:=  (fun a:_ => (pr1  (pr1  a))): pathsspace' T -> T). set (g:= (fun t:T => tpair _ (dirprodpair  t t) (idpath t)): T -> pathsspace' T). 
assert (efg: forall t:T, paths (f (g t)) t). intro. apply idpath. 
assert (egf: forall a: pathsspace' T, paths (g (f a)) a). intro. destruct a as [ t x ].  destruct t. destruct x.   simpl. apply idpath. 
apply (gradth _ _  egf efg). Defined. 


Lemma hfibershomotftog { X Y : UU } ( f g : X -> Y ) ( h : forall x : X , paths ( f x ) ( g x ) ) ( y : Y ) : hfiber f y -> hfiber g y .
Proof. intros X Y f g h y xe .  destruct xe as [ x e ] .  split with x .  apply ( pathscomp0 ( pathsinv0 ( h x ) ) e  ) . Defined .


Lemma hfibershomotgtof { X Y : UU } ( f g : X -> Y ) ( h : forall x : X , paths ( f x ) ( g x ) ) ( y : Y ) : hfiber g y -> hfiber f y .
Proof. intros X Y f g h y xe .  destruct xe as [ x e ] .  split with x .  apply ( pathscomp0  ( h x ) e  ) . Defined .


Theorem weqhfibershomot { X Y : UU } ( f g : X -> Y ) ( h : forall x : X , paths ( f x ) ( g x ) ) ( y : Y ) : weq ( hfiber f y ) ( hfiber g y ) .
Proof . intros . set ( ff := hfibershomotftog f g h y ) . set ( gg :=  hfibershomotgtof f g h y ) .  split with ff .
assert ( effgg : forall xe : _ , paths ( ff ( gg xe ) ) xe ) . intro . destruct xe as [ x e ] . simpl . 
assert ( eee: paths ( pathscomp0 (pathsinv0 (h x)) (pathscomp0 (h x) e) )  (pathscomp0   (maponpaths g ( idpath x ) ) e ) ) .  simpl .  destruct e . destruct ( h x ) .  simpl .  apply idpath . 
set ( xe1 := hfiberpair g x ( pathscomp0 (pathsinv0 (h x)) (pathscomp0 (h x) e) ) ) . set ( xe2 := hfiberpair g x e ) . apply ( hfibertriangle2 g xe1 xe2 ( idpath x ) eee ) .  
assert ( eggff : forall xe : _ , paths ( gg ( ff xe ) ) xe ) . intro . destruct xe as [ x e ] . simpl .
assert ( eee: paths ( pathscomp0 (h x) (pathscomp0 (pathsinv0 (h x)) e) )  (pathscomp0   (maponpaths f ( idpath x ) ) e ) ) .  simpl .  destruct e . destruct ( h x ) .  simpl .  apply idpath . 
set ( xe1 := hfiberpair f x ( pathscomp0 (h x) (pathscomp0 (pathsinv0 (h x)) e) ) ) . set ( xe2 := hfiberpair f x e ) . apply ( hfibertriangle2 f xe1 xe2 ( idpath x ) eee ) .  
apply ( gradth _ _ eggff effgg ) . Defined .





(** *** The 2-out-of-3 property of weak equivalences.

Theorems showing that if any two of three functions f, g, gf are weak equivalences then so is the third - the 2-out-of-3 property. *)





Theorem twooutof3a { X Y Z : UU } (f:X->Y) (g:Y->Z) (isgf: isweq (fun x:X => g (f x))) (isg: isweq g) : isweq f.
Proof. intros. set ( gw := weqpair g isg ) . set ( gfw := weqpair _ isgf ) . set (invg:= invmap gw ). set (invgf:= invmap gfw ). set (invf := (fun y:Y => invgf (g y))). 

assert (efinvf: forall y:Y, paths (f (invf y)) y). intro.   assert (int1: paths (g (f (invf y))) (g y)). unfold invf.  apply (homotweqinvweq gfw ( g y ) ). apply (invmaponpathsweq gw _ _  int1). 

assert (einvff: forall x: X, paths (invf (f x)) x). intro. unfold invf. apply (homotinvweqweq gfw x).

apply (gradth  f invf einvff efinvf).  Defined.


Corollary isweqcontrcontr { X Y : UU } (f:X -> Y) (isx: iscontr X) (isy: iscontr Y): isweq f.
Proof. intros. set (py:= (fun y:Y => tt)). apply (twooutof3a f py (isweqcontrtounit isx) (isweqcontrtounit isy)). Defined. 

Definition weqcontrcontr { X Y : UU } ( isx : iscontr X) (isy: iscontr Y) := weqpair _ ( isweqcontrcontr ( fun x : X => pr1 isy ) isx isy ) . 

Theorem twooutof3b { X Y Z : UU } (f:X->Y) (g:Y->Z) (isf: isweq f) (isgf: isweq (fun x:X => g(f x))) : isweq g.
Proof. intros. set ( wf := weqpair f isf ) . set ( wgf := weqpair _ isgf ) . set (invf:= invmap wf ). set (invgf:= invmap wgf ). set (invg := (fun z:Z => f ( invgf z))). set (gf:= fun x:X => (g (f x))). 

assert (eginvg: forall z:Z, paths (g (invg z)) z). intro. apply (homotweqinvweq wgf z).  

assert (einvgg: forall y:Y, paths (invg (g y)) y). intro.  assert (isinvf: isweq invf). apply isweqinvmap.  assert (isinvgf: isweq invgf).  apply isweqinvmap. assert (int1: paths (g y) (gf (invf y))).  apply (maponpaths g  (pathsinv0  (homotweqinvweq wf y))). assert (int2: paths (gf (invgf (g y))) (gf (invf y))). assert (int3: paths (gf (invgf (g y))) (g y)). apply (homotweqinvweq wgf ). destruct int1. assumption. assert (int4: paths (invgf (g y)) (invf y)). apply (invmaponpathsweq wgf ). assumption. assert (int5:paths (invf (f (invgf (g y)))) (invgf (g y))). apply (homotinvweqweq wf ). assert (int6: paths (invf (f (invgf (g (y))))) (invf y)).  destruct int4. assumption. apply (invmaponpathsweq ( weqpair invf isinvf ) ). assumption. apply (gradth  g invg  einvgg eginvg). Defined.



Lemma isweql3 { X Y : UU } (f:X-> Y) (g:Y->X) (egf: forall x:X, paths (g (f x)) x): isweq f -> isweq g.
Proof. intros X Y f g egf X0. set (gf:= fun x:X => g (f x)). assert (int1: isweq gf). apply (isweqhomot  (fun x:X => x) gf  (fun x:X => (pathsinv0 (egf x)))). apply idisweq.  apply (twooutof3b  f g X0 int1). Defined. 

Theorem twooutof3c { X Y Z : UU } (f:X->Y) (g:Y->Z) (isf: isweq f) (isg: isweq g) : isweq  (fun x:X => g(f x)).
Proof. intros. set ( wf := weqpair f isf ) . set ( wg := weqpair _ isg ) .  set (gf:= fun x:X => g (f x)). set (invf:= invmap wf ). set (invg:= invmap wg ). set (invgf:= fun z:Z => invf (invg z)). assert (egfinvgf: forall x:X, paths (invgf (gf x)) x). unfold gf. unfold invgf.  intro x.  assert (int1: paths (invf (invg (g (f x))))  (invf (f x))). apply (maponpaths invf (homotinvweqweq wg (f x))). assert (int2: paths (invf (f x)) x). apply homotinvweqweq.  destruct int1. assumption. 
assert (einvgfgf: forall z:Z, paths (gf (invgf z)) z).  unfold gf. unfold invgf. intro z. assert (int1: paths (g (f (invf (invg z)))) (g (invg z))). apply (maponpaths g (homotweqinvweq wf (invg z))).   assert (int2: paths (g (invg z)) z). apply (homotweqinvweq wg z). destruct int1. assumption. apply (gradth  gf invgf egfinvgf einvgfgf). Defined. 


Definition weqcomp { X Y Z : UU } (w1 : weq X Y) (w2 : weq Y Z) : (weq X Z) :=  weqpair  (fun x:X => (pr1  w2 (pr1  w1 x))) (twooutof3c _ _ (pr2  w1) (pr2  w2)). 



(** *** Associativity of [ total2 ]  *)

Lemma total2asstor { X : UU } ( P : X -> UU ) ( Q : total2 P -> UU ) : total2 Q ->  total2 ( fun x : X => total2 ( fun p : P x => Q ( tpair P x p ) ) ) .
Proof. intros X P Q xpq .  destruct xpq as [ xp q ] . destruct xp as [ x p ] . split with x . split with p . assumption . Defined .

Lemma total2asstol { X : UU } ( P : X -> UU ) ( Q : total2 P -> UU ) : total2 ( fun x : X => total2 ( fun p : P x => Q ( tpair P x p ) ) ) -> total2 Q .
Proof. intros X P Q xpq .  destruct xpq as [ x pq ] . destruct pq as [ p q ] . split with ( tpair P x p ) . assumption . Defined .


Theorem weqtotal2asstor { X : UU } ( P : X -> UU ) ( Q : total2 P -> UU ) : weq ( total2 Q ) ( total2 ( fun x : X => total2 ( fun p : P x => Q ( tpair P x p ) ) ) ).
Proof. intros . set ( f := total2asstor P Q ) . set ( g:= total2asstol P Q ) .  split with f .
assert ( egf : forall xpq : _ , paths ( g ( f xpq ) ) xpq ) . intro . destruct xpq as [ xp q ] . destruct xp as [ x p ] . apply idpath . 
assert ( efg : forall xpq : _ , paths ( f ( g xpq ) ) xpq ) . intro . destruct xpq as [ x pq ] . destruct pq as [ p q ] . apply idpath .
apply ( gradth _ _ egf efg ) . Defined.

Definition weqtotal2asstol { X : UU } ( P : X -> UU ) ( Q : total2 P -> UU ) : weq ( total2 ( fun x : X => total2 ( fun p : P x => Q ( tpair P x p ) ) ) ) ( total2 Q ) := invweq ( weqtotal2asstor P Q ) .



(** *** Associativity and commutativity of [ dirprod ] *) 

Definition weqdirprodasstor ( X Y Z : UU ) : weq ( dirprod ( dirprod X Y ) Z ) ( dirprod X ( dirprod Y Z ) ) .
Proof . intros . apply weqtotal2asstor . Defined . 

Definition weqdirprodasstol ( X Y Z : UU ) : weq  ( dirprod X ( dirprod Y Z ) ) ( dirprod ( dirprod X Y ) Z ) := invweq ( weqdirprodasstor X Y Z ) .

Definition weqdirprodcomm ( X Y : UU ) : weq ( dirprod X Y ) ( dirprod Y X ) .
Proof. intros . set ( f := fun xy : dirprod X Y => dirprodpair ( pr2 xy ) ( pr1 xy ) ) . set ( g := fun yx : dirprod Y X => dirprodpair ( pr2 yx ) ( pr1 yx ) ) .
assert ( egf : forall xy : _ , paths ( g ( f xy ) ) xy ) . intro . destruct xy . apply idpath .
assert ( efg : forall yx : _ , paths ( f ( g yx ) ) yx ) . intro . destruct yx . apply idpath .
split with f . apply ( gradth _ _ egf  efg ) . Defined . 
 





(** *** Coproducts and direct products *)


Definition rdistrtocoprod ( X Y Z : UU ): dirprod X (coprod Y Z) -> coprod (dirprod X Y) (dirprod X Z).
Proof. intros X Y Z X0. destruct X0 as [ t x ].  destruct x as [ y | z ] .   apply (ii1  (dirprodpair  t y)). apply (ii2  (dirprodpair  t z)). Defined.


Definition rdistrtoprod (X Y Z:UU): coprod (dirprod X Y) (dirprod X Z) ->  dirprod X (coprod Y Z).
Proof. intros X Y Z X0. destruct X0 as [ d | d ].  destruct d as [ t x ]. apply (dirprodpair  t (ii1  x)). destruct d as [ t x ]. apply (dirprodpair  t (ii2  x)). Defined. 


Theorem isweqrdistrtoprod (X Y Z:UU): isweq (rdistrtoprod X Y Z).
Proof. intros. set (f:= rdistrtoprod X Y Z). set (g:= rdistrtocoprod X Y Z). 
assert (egf: forall a:_, paths (g (f a)) a).  intro. destruct a as [ d | d ] . destruct d. apply idpath. destruct d. apply idpath. 
assert (efg: forall a:_, paths (f (g a)) a). intro. destruct a as [ t x ]. destruct x.  apply idpath. apply idpath.
apply (gradth  f g egf efg). Defined.

Definition weqrdistrtoprod (X Y Z: UU):= weqpair  _ (isweqrdistrtoprod X Y Z).

Corollary isweqrdistrtocoprod (X Y Z:UU): isweq (rdistrtocoprod X Y Z).
Proof. intros. apply (isweqinvmap ( weqrdistrtoprod X Y Z  ) ) . Defined.

Definition weqrdistrtocoprod (X Y Z: UU):= weqpair  _ (isweqrdistrtocoprod X Y Z).
 


(** *** Total space of a family over a coproduct *)


Definition fromtotal2overcoprod { X Y : UU } ( P : coprod X Y -> UU ) ( xyp : total2 P ) : coprod ( total2 ( fun x : X => P ( ii1 x ) ) ) ( total2 ( fun y : Y => P ( ii2 y ) ) ) .
Proof. intros . set ( PX :=  fun x : X => P ( ii1 x ) ) . set ( PY :=  fun y : Y => P ( ii2 y ) ) . destruct xyp as [ xy p ] . destruct xy as [ x | y ] . apply (  ii1 ( tpair PX x p ) ) .   apply ( ii2 ( tpair PY y p ) ) . Defined .

Definition tototal2overcoprod { X Y : UU } ( P : coprod X Y -> UU ) ( xpyp :  coprod ( total2 ( fun x : X => P ( ii1 x ) ) ) ( total2 ( fun y : Y => P ( ii2 y ) ) ) ) : total2 P .
Proof . intros . destruct xpyp as [ xp | yp ] . destruct xp as [ x p ] . apply ( tpair P ( ii1 x ) p ) .   destruct yp as [ y p ] . apply ( tpair P ( ii2 y ) p ) . Defined . 
 
Theorem weqtotal2overcoprod { X Y : UU } ( P : coprod X Y -> UU ) : weq ( total2 P ) ( coprod ( total2 ( fun x : X => P ( ii1 x ) ) ) ( total2 ( fun y : Y => P ( ii2 y ) ) ) ) .
Proof. intros .  set ( f := fromtotal2overcoprod P ) . set ( g := tototal2overcoprod P ) . split with f . 
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro a . destruct a as [ xy p ] . destruct xy as [ x | y ] . simpl . apply idpath . simpl .  apply idpath .     
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro a . destruct a as [ xp | yp ] . destruct xp as [ x p ] . simpl . apply idpath .  destruct yp as [ y p ] . apply idpath .
apply ( gradth _ _ egf efg ) . Defined . 



(** *** Weak equivalences and pairwise direct products *)


Theorem isweqdirprodf { X Y X' Y' : UU } ( w : weq X Y )( w' : weq X' Y' ) : isweq (dirprodf w w' ).
Proof. intros. set ( f := dirprodf w w' ) . set ( g := dirprodf ( invweq w ) ( invweq w' ) ) . 
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro a . destruct a as [ x x' ] .  simpl .   apply pathsdirprod . apply ( homotinvweqweq w x ) .  apply ( homotinvweqweq w' x' ) . 
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro a . destruct a as [ x x' ] .  simpl .   apply pathsdirprod . apply ( homotweqinvweq w x ) .  apply ( homotweqinvweq w' x' ) .
apply ( gradth _ _ egf efg ) . Defined .   

Definition weqdirprodf { X Y X' Y' : UU } ( w : weq X Y ) ( w' : weq X' Y' ) := weqpair _ ( isweqdirprodf w w' ) .

Definition weqtodirprodwithunit (X:UU): weq X (dirprod X unit).
Proof. intros. set (f:=fun x:X => dirprodpair x tt). split with f.  set (g:= fun xu:dirprod X unit => pr1  xu). 
assert (egf: forall x:X, paths (g (f x)) x). intro. apply idpath.
assert (efg: forall xu:_, paths (f (g xu)) xu). intro. destruct xu as  [ t x ]. destruct x. apply idpath.    
apply (gradth  f g egf efg). Defined.




(** *** Basics on pairwise coproducts (disjoint unions)  *)



(** In the current version [ coprod ] is a notation, introduced in uuu.v for [ sum ] of types which is defined in Coq.Init *)



Definition sumofmaps {X Y Z:UU}(fx: X -> Z)(fy: Y -> Z): (coprod X Y) -> Z := fun xy:_ => match xy with ii1 x => fx x | ii2 y => fy y end.


Definition boolascoprod: weq (coprod unit unit) bool.
Proof. set (f:= fun xx: coprod unit unit => match xx with ii1 t => true | ii2 t => false end). split with f. 
set (g:= fun t:bool => match t with true => ii1  tt | false => ii2  tt end). 
assert (egf: forall xx:_, paths (g (f xx)) xx). intro xx .  destruct xx as [ u | u ] . destruct u. apply idpath. destruct u. apply idpath. 
assert (efg: forall t:_, paths (f (g t)) t). destruct t. apply idpath. apply idpath. 
apply (gradth  f g egf efg). Defined.  


Definition coprodasstor (X Y Z:UU): coprod (coprod X Y) Z -> coprod X (coprod Y Z).
Proof. intros X Y Z X0. destruct X0 as [ c | z ] .  destruct c as [ x | y ] .  apply (ii1  x). apply (ii2  (ii1  y)). apply (ii2  (ii2  z)). Defined.

Definition coprodasstol (X Y Z: UU): coprod X (coprod Y Z) -> coprod (coprod X Y) Z.
Proof. intros X Y Z X0. destruct X0 as [ x | c ] .  apply (ii1  (ii1  x)). destruct c as [ y | z ] .   apply (ii1  (ii2  y)). apply (ii2  z). Defined.

Theorem isweqcoprodasstor (X Y Z:UU): isweq (coprodasstor X Y Z).
Proof. intros. set (f:= coprodasstor X Y Z). set (g:= coprodasstol X Y Z).
assert (egf: forall xyz:_, paths (g (f xyz)) xyz). intro xyz. destruct xyz as [ c | z ] .  destruct c. apply idpath. apply idpath. apply idpath. 
assert (efg: forall xyz:_, paths (f (g xyz)) xyz). intro xyz.  destruct xyz as [ x | c ] .  apply idpath.  destruct c. apply idpath. apply idpath.
apply (gradth  f g egf efg). Defined. 

Definition weqcoprodasstor ( X Y Z : UU ) := weqpair _ ( isweqcoprodasstor X Y Z ) .

Corollary isweqcoprodasstol (X Y Z:UU): isweq (coprodasstol X Y Z).
Proof. intros. apply (isweqinvmap ( weqcoprodasstor X Y Z)  ). Defined.

Definition weqcoprodasstol (X Y Z:UU):= weqpair  _ (isweqcoprodasstol X Y Z).

Definition coprodcomm (X Y:UU): coprod X Y -> coprod Y X := fun xy:_ => match xy with ii1 x => ii2  x | ii2 y => ii1  y end. 

Theorem isweqcoprodcomm (X Y:UU): isweq (coprodcomm X Y).
Proof. intros. set (f:= coprodcomm X Y). set (g:= coprodcomm Y X).
assert (egf: forall xy:_, paths (g (f xy)) xy). intro. destruct xy. apply idpath. apply idpath.
assert (efg: forall yx:_, paths (f (g yx)) yx). intro. destruct yx. apply idpath. apply idpath.
apply (gradth  f g egf efg). Defined. 

Definition weqcoprodcomm (X Y:UU):= weqpair  _ (isweqcoprodcomm X Y). 

Theorem isweqii1withneg  (X : UU) { Y : UU } (nf:Y -> empty): isweq (@ii1 X Y).
Proof. intros. set (f:= @ii1 X Y). set (g:= fun xy:coprod X Y => match xy with ii1 x => x | ii2 y => fromempty (nf y) end).  
assert (egf: forall x:X, paths (g (f x)) x). intro. apply idpath. 
assert (efg: forall xy: coprod X Y, paths (f (g xy)) xy). intro. destruct xy as [ x | y ] . apply idpath. apply (fromempty (nf y)).  
apply (gradth  f g egf efg). Defined.  

Definition weqii1withneg ( X : UU ) { Y : UU } ( nf : neg Y ) := weqpair _ ( isweqii1withneg X nf ) .

Theorem isweqii2withneg  { X  : UU } ( Y : UU ) (nf : X -> empty): isweq (@ii2 X Y).
Proof. intros. set (f:= @ii2 X Y). set (g:= fun xy:coprod X Y => match xy with ii1 x => fromempty (nf x) | ii2 y => y end).  
assert (egf: forall y : Y, paths (g (f y)) y). intro. apply idpath. 
assert (efg: forall xy: coprod X Y, paths (f (g xy)) xy). intro. destruct xy as [ x | y ] . apply (fromempty (nf x)).  apply idpath. 
apply (gradth  f g egf efg). Defined.  

Definition weqii2withneg { X : UU } ( Y : UU ) ( nf : neg X ) := weqpair _ ( isweqii2withneg Y nf ) .



Definition coprodf { X Y X' Y' : UU } (f: X -> X')(g: Y-> Y'): coprod X Y -> coprod X' Y' := fun xy: coprod X Y =>
match xy with
ii1 x => ii1  (f x)|
ii2 y => ii2  (g y)
end. 


Definition homotcoprodfcomp { X X' Y Y' Z Z' : UU } ( f : X -> Y ) ( f' : X' -> Y' ) ( g : Y -> Z ) ( g' : Y' -> Z' ) : homot ( funcomp ( coprodf f f' ) ( coprodf g g' ) ) ( coprodf ( funcomp f g ) ( funcomp f' g' ) ) .
Proof. intros . intro xx' . destruct xx' as [ x | x' ] . apply idpath . apply idpath . Defined .  


Definition homotcoprodfhomot { X X' Y Y' } ( f g : X -> Y ) ( f' g' : X' -> Y' ) ( h : homot f g ) ( h' : homot f' g' ) : homot ( coprodf f f') ( coprodf g g') := fun xx' : _ => match xx' with ( ii1 x ) => maponpaths ( @ii1 _ _ ) ( h x ) | ( ii2 x' ) => maponpaths ( @ii2 _ _ ) ( h' x' ) end  .


Theorem isweqcoprodf { X Y X' Y' : UU } ( w : weq X X' )( w' : weq Y Y' ) : isweq (coprodf w w' ).
Proof. intros. set (finv:= invmap w ). set (ginv:= invmap w' ). set (ff:=coprodf w w' ). set (gg:=coprodf   finv ginv). 
assert (egf: forall xy: coprod X Y, paths (gg (ff xy)) xy). intro. destruct xy as [ x | y ] . simpl. apply (maponpaths (@ii1 X Y)  (homotinvweqweq w x)).     apply (maponpaths (@ii2 X Y)  (homotinvweqweq w' y)).
assert (efg: forall xy': coprod X' Y', paths (ff (gg xy')) xy'). intro. destruct xy' as [ x | y ] . simpl.  apply (maponpaths (@ii1 X' Y')  (homotweqinvweq w x)).     apply (maponpaths (@ii2 X' Y')  (homotweqinvweq w' y)). 
apply (gradth  ff gg egf efg). Defined. 


Definition weqcoprodf { X Y X' Y' : UU } (w1: weq X Y)(w2: weq X' Y') : weq (coprod X X') (coprod Y Y') := weqpair _ ( isweqcoprodf w1 w2 ) .


Lemma negpathsii1ii2 { X Y : UU } (x:X)(y:Y): neg (paths (ii1  x) (ii2  y)).
Proof. intros. unfold neg. intro X0. set (dist:= fun xy: coprod X Y => match xy with ii1 x => unit | ii2 y => empty end). apply (transportf dist  X0 tt). Defined.

Lemma negpathsii2ii1 { X Y : UU } (x:X)(y:Y): neg (paths (ii2  y) (ii1  x)).
Proof. intros. unfold neg. intro X0. set (dist:= fun xy: coprod X Y => match xy with ii1 x => empty | ii2 y => unit end). apply (transportf dist  X0 tt). Defined.







(** *** Fibrations with only one non-empty fiber. 

Theorem saying that if a fibration has only one non-empty fiber then the total space is weakly equivalent to this fiber. *)



Theorem onefiber { X : UU } (P:X -> UU)(x:X)(c: forall x':X, coprod (paths x x') (P x' -> empty)) : isweq (fun p: P x => tpair P x p).
Proof. intros.  

set (f:= fun p: P x => tpair _ x p). 

set (cx := c x). 
set (cnew:=  fun x':X  =>
match cx with 
ii1 x0 =>
match c x' with 
ii1 ee => ii1  (pathscomp0   (pathsinv0  x0) ee)|
ii2 phi => ii2  phi
end |
ii2 phi => c x'
end).

set (g:= fun pp: total2 P => 
match (cnew (pr1  pp)) with
ii1 e => transportb P  e (pr2  pp) |
ii2 phi =>  fromempty (phi (pr2  pp))
end).


assert (efg: forall pp: total2 P, paths (f (g pp)) pp).  intro. destruct pp as [ t x0 ]. set (cnewt:= cnew t).  unfold g. unfold f. simpl. change (cnew t) with cnewt. destruct cnewt as [ x1 | y ].  apply (pathsinv0 (pr1  (pr2  (constr1 P (pathsinv0 x1))) x0)). destruct (y x0). 

 
set (cnewx:= cnew x). 
assert (e1: paths (cnew x) cnewx). apply idpath. 
unfold cnew in cnewx. change (c x) with cx in cnewx.  
destruct cx as [ x0 | e0 ].  
assert (e: paths (cnewx) (ii1  (idpath x))).  apply (maponpaths (@ii1 (paths x x) (P x -> empty))  (pathsinv0l x0)). 




assert (egf: forall p: P x, paths (g (f p)) p).  intro. simpl in g. unfold g.  unfold f.   simpl.   

set (ff:= fun cc:coprod (paths x x) (P x -> empty) => 
match cc with
     | ii1 e0 => transportb P e0 p
     | ii2 phi => fromempty  (phi p)
     end).
assert (ee: paths (ff (cnewx)) (ff (@ii1 (paths x x) (P x -> empty) (idpath x)))).  apply (maponpaths ff  e). 
assert (eee: paths  (ff (@ii1 (paths x x) (P x -> empty) (idpath x))) p). apply idpath.  fold (ff (cnew x)). 
assert (e2: paths (ff (cnew x)) (ff cnewx)). apply (maponpaths ff  e1). 
apply (pathscomp0   (pathscomp0   e2 ee) eee).
apply (gradth  f g egf efg).

unfold isweq.  intro y0. destruct (e0 (g y0)). Defined.





(** *** Pairwise coproducts as dependent sums of families over [ bool ] *)


Fixpoint coprodtobool { X Y : UU } ( xy : coprod X Y ) : bool :=
match xy with
ii1 x => true|
ii2 y => false
end.
 

Definition boolsumfun (X Y:UU) : bool -> UU := fun t:_ => 
match t with
true => X|
false => Y
end.

Definition coprodtoboolsum ( X Y : UU ) : coprod X Y -> total2 (boolsumfun X Y) := fun xy : _ =>
match xy with
ii1 x => tpair (boolsumfun X Y) true x|
ii2 y => tpair (boolsumfun X Y) false y
end .


Definition boolsumtocoprod (X Y:UU): (total2 (boolsumfun X Y)) -> coprod X Y := (fun xy:_ =>
match xy with 
tpair true x => ii1  x|
tpair false y => ii2  y
end).



Theorem isweqcoprodtoboolsum (X Y:UU): isweq (coprodtoboolsum X Y).
Proof. intros. set (f:= coprodtoboolsum X Y). set (g:= boolsumtocoprod X Y). 
assert (egf: forall xy: coprod X Y , paths (g (f xy)) xy). destruct xy. apply idpath. apply idpath. 
assert (efg: forall xy: total2 (boolsumfun X Y), paths (f (g xy)) xy). intro. destruct xy as [ t x ]. destruct t.  apply idpath. apply idpath. apply (gradth  f g egf efg). Defined.

Definition weqcoprodtoboolsum ( X Y : UU ) := weqpair _ ( isweqcoprodtoboolsum X Y ) .

Corollary isweqboolsumtocoprod (X Y:UU): isweq (boolsumtocoprod X Y ).
Proof. intros. apply (isweqinvmap ( weqcoprodtoboolsum X Y ) ) . Defined.

Definition weqboolsumtocoprod ( X Y : UU ) := weqpair _ ( isweqboolsumtocoprod X Y ) .








(** *** Splitting of [ X ] into a coproduct defined by a function [ X -> coprod Y Z ] *)


Definition weqcoprodsplit { X Y Z : UU } ( f : X -> coprod Y Z ) : weq  X  ( coprod ( total2 ( fun y : Y => hfiber f ( ii1 y ) ) ) ( total2 ( fun z : Z => hfiber f ( ii2 z ) ) ) ) .
Proof . intros . set ( w1 := weqtococonusf f ) .  set ( w2 := weqtotal2overcoprod ( fun yz : coprod Y Z => hfiber f yz ) ) . apply ( weqcomp w1 w2 ) .  Defined . 



(** *** Some properties of [ bool ] *)

Definition boolchoice ( x : bool ) : coprod ( paths x true ) ( paths x false ) .
Proof. intro . destruct x . apply ( ii1 ( idpath _ ) ) .  apply ( ii2 ( idpath _ ) ) . Defined . 

Definition curry :  bool -> UU := fun x : bool =>
match x  with
false => empty|
true => unit
end.


Theorem nopathstruetofalse: paths true false -> empty.
Proof. intro X.  apply (transportf curry  X tt).  Defined.

Corollary nopathsfalsetotrue: paths false true -> empty.
Proof. intro X. apply (transportb curry  X tt). Defined. 

Definition truetonegfalse ( x : bool ) : paths x true -> neg ( paths x false ) .
Proof . intros x e . rewrite e . unfold neg . apply nopathstruetofalse . Defined . 

Definition falsetonegtrue ( x : bool ) : paths x false -> neg ( paths x true ) .
Proof . intros x e . rewrite e . unfold neg . apply nopathsfalsetotrue . Defined .  













(** ** Basics about fibration sequences. *)



(** *** Fibrations sequences and their first "left shifts". 

The group of constructions related to fibration sequences forms one of the most important computational toolboxes of homotopy theory .   

Given a pair of functions [ ( f : X -> Y ) ( g : Y -> Z ) ] and a point [ z : Z ] , a structure of the complex on such a triple is a homotopy from the composition [ funcomp f g ] to the constant function [ X -> Z ] corresponding to [ z ] i.e. a term [ ez : forall x:X, paths ( g ( f x ) ) z ]. Specifing such a structure is essentially equivalent to specifing a structure of the form [ ezmap : X -> hfiber g z ]. The mapping in one direction is given in the definition of [ ezmap ] below. The mapping in another is given by [ f := fun x : X => pr1 ( ezmap x ) ] and [ ez := fun x : X => pr2 ( ezmap x ) ].

A complex is called a fibration sequence if [ ezmap ] is a weak equivalence. Correspondingly, the structure of a fibration sequence on [ f g z ] is a pair [ ( ez , is ) ] where [ is : isweq ( ezmap f g z ez ) ]. For a fibration sequence [ f g z fs ]  where [ fs : fibseqstr f g z ] and any [ y : Y ] there is defined a function [ diff1 : paths ( g y ) z -> X ] and a structure of the fibration sequence [ fibseqdiff1 ] on the triple [ diff1 g y ]. This new fibration sequence is called the derived fibration sequence of the original one.  

The first function of the second derived of [ f g z fs ] corresponding to [ ( y : Y ) ( x : X ) ]  is of the form [ paths ( f x ) y -> paths ( g y ) z ] and it is homotopic to the function defined by [ e => pathscomp0 ( maponpaths g  ( pathsinv0 e) ) ( ez x ) ]. The first function of the third derived of [ f g z fs ] corresponding to [ ( y : Y ) ( x : X ) ( e : paths ( g y ) z ) ] is of the form [ paths ( diff1 e ) x -> paths ( f x ) y ]. Therefore, the third derived of a sequence based on [ X Y Z ] is based entirely on paths types of [ X ], [ Y ] and [ Z ]. When this construction is applied to types of finite h-level (see below) and combined with the fact that the h-level of a path type is strictly lower than the h-level of the ambient type it leads to the possibility of building proofs about types by induction on h-level.  

There are three important special cases in which fibration sequences arise:

( pr1 - case ) The fibration sequence [ fibseqpr1 P z ] defined by family [ P : Z -> UU ] and a term [ z : Z ]. It is based on the sequence of functions [ ( tpair P z : P z -> total2 P ) ( pr1 : total2 P -> Z ) ]. The corresponding [ ezmap ] is defined by an obvious rule and the fact that it is a weak equivalence is proved in [ isweqfibertohfiber ].

( g - case ) The fibration sequence [ fibseqg g z ]  defined by a function [ g : Y -> Z ] and a term [ z : Z ]. It is based on the sequence of functions [ ( hfiberpr1 : hfiber g z -> Y ) ( g : Y -> Z ) ] and the corresponding [ ezmap ] is the function which takes a term [ ye : hfiber ] to [ hfiberpair g ( pr1 ye ) ( pr2 ye ) ]. If we had eta-concersion for the depndent sums it would be the identiry function. Since we do not have this conversion in Coq this function is only homotopic to the identity function by [ tppr ] which is sufficient to ensure that it is a weak equivalence. The first derived of [ fibseqg g z ] corresponding to [ y : Y ] coincides with [ fibseqpr1 ( fun y' : Y  => paths ( g y' ) z ) y ].

( hf -case ) The fibration sequence of homotopy fibers defined for any pair of functions [ ( f : X -> Y ) ( g : Y -> Z ) ] and any terms [ ( z : Z ) ( ye : hfiber g z ) ]. It is based on functions [ hfiberftogf : hfiber f ( pr1 ye ) -> hfiber ( funcomp f g ) z ] and [ hfibergftog : hfiber ( funcomp f g ) z -> hfiber g z ] which are defined below.    


*)


(** The structure of a complex structure on a composable pair of functions [ ( f : X -> Y ) ( g : Y -> Z ) ] relative to a term [ z : Z ]. *) 

Definition complxstr  { X Y Z : UU } (f:X -> Y) (g:Y->Z) ( z : Z ) := forall x:X, paths (g (f x)) z .

 

(** The structure of a fibration sequence on a complex. *)

Definition ezmap { X Y Z : UU } (f:X -> Y) (g:Y->Z) ( z : Z ) (ez : complxstr f g z ) : X -> hfiber  g z :=  fun x:X => hfiberpair  g (f x) (ez x).

Definition isfibseq { X Y Z : UU } (f:X -> Y) (g:Y->Z) ( z : Z ) (ez : complxstr f g z ) := isweq (ezmap f g z ez). 

Definition fibseqstr { X Y Z : UU } (f:X -> Y) (g:Y->Z) ( z : Z ) := total2 ( fun ez : complxstr f g z => isfibseq f g z ez ) .
Definition fibseqstrpair { X Y Z : UU } (f:X -> Y) (g:Y->Z) ( z : Z ) := tpair ( fun ez : complxstr f g z => isfibseq f g z ez ) .
Definition fibseqstrtocomplxstr  { X Y Z : UU } (f:X -> Y) (g:Y->Z) ( z : Z ) : fibseqstr f g z -> complxstr f g z := @pr1 _  ( fun ez : complxstr f g z => isfibseq f g z ez ) .
Coercion fibseqstrtocomplxstr : fibseqstr >-> complxstr . 

Definition ezweq { X Y Z : UU } (f:X -> Y) (g:Y->Z) ( z : Z ) ( fs : fibseqstr f g z ) : weq X ( hfiber g z ) := weqpair _ ( pr2 fs ) . 



(** Construction of the derived fibration sequence. *)


Definition d1 { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( fs : fibseqstr f g z ) ( y : Y ) : paths ( g y ) z ->  X := fun e : _ =>  invmap ( ezweq f g z fs ) ( hfiberpair g y e ) .

Definition ezmap1 { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( fs : fibseqstr f g z ) ( y : Y ) ( e : paths ( g y ) z ) :  hfiber f y  .
Proof . intros . split with ( d1 f g z fs y e ) . unfold d1 . change ( f ( invmap (ezweq f g z fs) (hfiberpair g y e) ) ) with ( hfiberpr1 _ _ ( ezweq f g z fs ( invmap (ezweq f g z fs) (hfiberpair g y e) ) ) )  . apply ( maponpaths ( hfiberpr1 g z ) ( homotweqinvweq ( ezweq f g z fs ) (hfiberpair g y e) ) ) .  Defined .      

Definition invezmap1 { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( ez : complxstr f g z ) ( y : Y ) : hfiber  f y -> paths (g y) z :=  
fun xe: hfiber  f y =>
match xe with
tpair x e => pathscomp0 (maponpaths g  ( pathsinv0 e ) ) ( ez x )
end.

Theorem isweqezmap1 { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( fs : fibseqstr f g z ) ( y : Y ) : isweq ( ezmap1 f g z fs y ) .
Proof . intros . set ( ff := ezmap1 f g z fs y ) . set ( gg := invezmap1 f g z ( pr1 fs ) y ) . 
assert ( egf : forall e : _ , paths ( gg ( ff e ) ) e ) . intro .  simpl . apply ( hfibertriangle1inv0 g (homotweqinvweq (ezweq f g z fs) (hfiberpair g y e)) ) . 
assert ( efg : forall xe : _ , paths ( ff ( gg xe ) ) xe ) . intro .  destruct xe as [ x e ] .  destruct e .  simpl . unfold ff . unfold ezmap1 . unfold d1 .   change (hfiberpair g (f x) ( pr1 fs x) ) with ( ezmap f g z fs x ) .  apply ( hfibertriangle2 f ( hfiberpair f ( invmap (ezweq f g z fs) (ezmap f g z fs x) ) _ ) ( hfiberpair f x ( idpath _ ) ) ( homotinvweqweq ( ezweq f g z fs ) x ) ) . simpl .  set ( e1 := pathsinv0 ( pathscomp0rid (maponpaths f (homotinvweqweq (ezweq f g z fs) x) ) ) ) . assert ( e2 : paths (maponpaths (hfiberpr1 g z) (homotweqinvweq (ezweq f g z fs) ( ( ezmap f g z fs ) x))) (maponpaths f (homotinvweqweq (ezweq f g z fs) x)) ) . set ( e3 := maponpaths ( fun e : _ => maponpaths ( hfiberpr1 g z ) e ) ( pathsinv0  ( homotweqinvweqweq ( ezweq f g z fs ) x ) ) ) .  simpl in e3 .  set ( e4 := maponpathscomp (ezmap f g z (pr1 fs)) (hfiberpr1 g z) (homotinvweqweq (ezweq f g z fs) x) ) .   simpl in e4 . apply ( pathscomp0 e3 e4 ) . apply ( pathscomp0 e2 e1 ) . 
apply ( gradth _ _ egf efg ) . Defined . 

Definition ezweq1 { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( fs : fibseqstr f g z ) ( y : Y ) := weqpair _ ( isweqezmap1 f g z fs y ) . 
Definition fibseq1 { X Y Z : UU } (f:X -> Y) (g:Y->Z) (z:Z) ( fs : fibseqstr f g z )(y:Y) : fibseqstr ( d1 f g z fs y) f y := fibseqstrpair _ _ _ _ ( isweqezmap1 f g z fs y ) . 



(** Explitcit description of the first map in the second derived sequence. *)

Definition d2 { X Y Z : UU } (f:X -> Y) (g:Y->Z) (z:Z) ( fs : fibseqstr f g z ) (y:Y) (x:X) ( e : paths (f x) y ) : paths (g y) z := pathscomp0 ( maponpaths g ( pathsinv0 e ) ) ( ( pr1 fs ) x ) . 
Definition ezweq2 { X Y Z : UU } (f:X -> Y) (g:Y->Z) (z:Z) ( fs : fibseqstr f g z ) (y:Y) (x:X) : weq ( paths (f x) y ) ( hfiber  (d1 f g z fs y) x ) := ezweq1 (d1 f g z fs y) f y ( fibseq1 f g z fs y )  x.
Definition fibseq2  { X Y Z : UU } (f:X -> Y) (g:Y->Z) (z:Z) ( fs : fibseqstr f g z ) (y:Y) (x:X) : fibseqstr ( d2 f g z fs y x ) ( d1 f g z fs y ) x := fibseqstrpair _ _ _ _ ( isweqezmap1 (d1 f g z fs y) f y ( fibseq1 f g z fs y ) x ) .





(** *** Fibration sequences based on [ ( tpair P z : P z -> total2 P ) ( pr1 : total2 P -> Z ) ] (  the "pr1-case" )    *) 



(** Construction of the fibration sequence. *)

Definition ezmappr1 { Z : UU } ( P : Z -> UU ) ( z : Z ) : P z -> hfiber ( @pr1 Z P ) z := fun p : P z => tpair _ ( tpair _  z p ) ( idpath z ).

Definition invezmappr1 { Z : UU } ( P : Z -> UU) ( z : Z ) : hfiber ( @pr1 Z P ) z  -> P z := fun te  : hfiber ( @pr1 Z P ) z =>
match te with 
tpair t e => transportf P e ( pr2 t ) 
end.

Definition isweqezmappr1 { Z : UU } ( P : Z -> UU ) ( z : Z ) : isweq ( ezmappr1 P z ).
Proof. intros. 
assert ( egf : forall x: P z , paths (invezmappr1 _ z ((ezmappr1 P z ) x)) x). intro. unfold ezmappr1. unfold invezmappr1. simpl. apply idpath. 
assert ( efg : forall x: hfiber  (@pr1 Z P) z , paths (ezmappr1 _ z (invezmappr1 P z x)) x). intros.  destruct x as [ x t0 ]. destruct t0. simpl in x.  simpl. destruct x. simpl. unfold transportf. unfold ezmappr1. apply idpath. 
apply (gradth _ _ egf efg ). Defined. 

Definition ezweqpr1 { Z : UU } ( P : Z -> UU ) ( z : Z ) := weqpair _ ( isweqezmappr1 P z ) .

Lemma isfibseqpr1 { Z : UU } ( P : Z -> UU ) ( z : Z ) : isfibseq  (fun p : P z => tpair _ z p) ( @pr1 Z P ) z (fun p: P z => idpath z ).
Proof. intros. unfold isfibseq. unfold ezmap.  apply isweqezmappr1. Defined.

Definition fibseqpr1 { Z : UU } ( P : Z -> UU ) ( z : Z ) : fibseqstr (fun p : P z => tpair _ z p) ( @pr1 Z P ) z := fibseqstrpair _ _ _ _ ( isfibseqpr1 P z ) .


(** The main weak equivalence defined by the first derived of [ fibseqpr1 ]. *)

Definition ezweq1pr1 { Z : UU } ( P : Z -> UU ) ( z : Z ) ( zp : total2 P ) : weq ( paths ( pr1 zp) z )  ( hfiber ( tpair P z ) zp ) := ezweq1 _ _ z ( fibseqpr1 P z ) zp .   







(** *** Fibration sequences based on [ ( hfiberpr1 : hfiber g z -> Y ) ( g : Y -> Z ) ] (the "g-case")  *)


Theorem isfibseqg { Y Z : UU } (g:Y -> Z) (z:Z) : isfibseq  (hfiberpr1  g z) g z (fun ye: _ => pr2  ye).
Proof. intros. assert (Y0:forall ye': hfiber  g z, paths ye' (ezmap (hfiberpr1  g z) g z (fun ye: _ => pr2  ye) ye')). intro. apply tppr. apply (isweqhomot  _ _ Y0 (idisweq _ )).  Defined.

Definition ezweqg { Y Z : UU } (g:Y -> Z) (z:Z) := weqpair _ ( isfibseqg g z ) .
Definition fibseqg { Y Z : UU } (g:Y -> Z) (z:Z) : fibseqstr (hfiberpr1  g z) g z := fibseqstrpair _ _ _ _ ( isfibseqg g z ) . 


(** The first derived of [ fibseqg ].  *)

Definition d1g  { Y Z : UU} ( g : Y -> Z ) ( z : Z ) ( y : Y ) : paths ( g y ) z -> hfiber g z := hfiberpair g y . 

(** note that [ d1g ] coincides with [ d1 _ _ _ ( fibseqg g z ) ] which makes the following two definitions possible. *)

Definition ezweq1g { Y Z : UU } (g:Y -> Z) (z:Z) (y:Y) : weq (paths (g y) z) (hfiber (hfiberpr1 g z) y) := weqpair _ (isweqezmap1 (hfiberpr1  g z) g z ( fibseqg g z ) y) .
Definition fibseq1g { Y Z : UU } (g:Y -> Z) (z:Z) ( y : Y) : fibseqstr (d1g g z y ) ( hfiberpr1 g z ) y := fibseqstrpair _ _ _ _ (isweqezmap1 (hfiberpr1  g z) g z  ( fibseqg g z ) y) . 


(** The second derived of [ fibseqg ]. *) 

Definition d2g { Y Z : UU } (g:Y -> Z) { z : Z } ( y : Y ) ( ye' : hfiber  g z ) ( e: paths (pr1 ye') y ) :  paths (g y) z := pathscomp0 ( maponpaths g ( pathsinv0 e ) ) ( pr2  ye' ) .

(** note that [ d2g ] coincides with [ d2 _ _ _ ( fibseqg g z ) ] which makes the following two definitions possible. *)

Definition ezweq2g { Y Z : UU } (g:Y -> Z) { z : Z } ( y : Y ) ( ye' : hfiber  g z ) : weq (paths (pr1 ye') y) (hfiber ( hfiberpair g y ) ye') := ezweq2 _ _ _ ( fibseqg g z ) _ _ .
Definition fibseq2g { Y Z : UU } (g:Y -> Z) { z : Z } ( y : Y ) ( ye' : hfiber  g z ) : fibseqstr ( d2g g y ye' ) ( hfiberpair g y ) ye' := fibseq2 _ _ _ ( fibseqg g z ) _ _ . 


(** The third derived of [ fibseqg ] and an explicit description of the corresponding first map. *)

Definition d3g { Y Z : UU } (g:Y -> Z) { z : Z } ( y : Y ) ( ye' : hfiber g z ) ( e : paths ( g y ) z ) : paths ( hfiberpair  g y e ) ye' -> paths ( pr1 ye' ) y := d2 (d1g  g z y) (hfiberpr1 g z) y ( fibseq1g g z y ) ye' e . 

Lemma homotd3g { Y Z : UU } ( g : Y -> Z ) { z : Z } ( y : Y ) ( ye' : hfiber  g z ) ( e : paths ( g y ) z ) ( ee : paths ( hfiberpair g y e) ye' ) : paths (d3g g y ye' e ee) ( maponpaths ( @pr1 _ _ ) ( pathsinv0 ee ) ) .
Proof. intros. unfold d3g . unfold d2 .  simpl .  apply pathscomp0rid. Defined .  

Definition ezweq3g { Y Z : UU } (g:Y -> Z) { z : Z } ( y : Y ) ( ye' : hfiber g z ) ( e : paths ( g y ) z ) := ezweq2 (d1g  g z y) (hfiberpr1 g z) y ( fibseq1g g z y ) ye' e . 
Definition fibseq3g { Y Z : UU } (g:Y -> Z) { z : Z } ( y : Y ) ( ye' : hfiber g z ) ( e : paths ( g y ) z ) := fibseq2 (d1g  g z y) (hfiberpr1 g z) y ( fibseq1g g z y ) ye' e .





(** *** Fibration sequence of h-fibers defined by a composable pair of functions (the "hf-case") 

We construct a fibration sequence based on [ ( hfibersftogf f g z ye : hfiber f ( pr1 ye )  -> hfiber gf z ) ( hfibersgftog f g z : hfiber gf z -> hfiber g z ) ]. *) 




Definition hfibersftogf { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( ye : hfiber g z ) ( xe : hfiber f ( pr1 ye ) ) : hfiber ( funcomp f g ) z .
Proof . intros . split with ( pr1 xe ) .  apply ( pathscomp0 ( maponpaths g ( pr2 xe ) ) ( pr2 ye ) ) .  Defined .  



Definition ezmaphf { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( ye : hfiber g z ) ( xe : hfiber f ( pr1 ye ) ) : hfiber ( hfibersgftog f g z ) ye .
Proof . intros . split with ( hfibersftogf f g z ye xe ) . simpl . apply ( hfibertriangle2 g (hfiberpair g (f (pr1 xe)) (pathscomp0 (maponpaths g (pr2 xe)) ( pr2 ye ) )) ye ( pr2 xe ) ) .  simpl . apply idpath .  Defined . 

Definition invezmaphf { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( ye : hfiber g z ) ( xee' : hfiber ( hfibersgftog f g z ) ye ) : hfiber f ( pr1 ye ) .
Proof . intros .  split with ( pr1 ( pr1 xee' ) ) .  apply ( maponpaths ( hfiberpr1 _ _ ) ( pr2 xee' ) ) . Defined . 

Definition ffgg { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( ye : hfiber g z ) ( xee' : hfiber  ( hfibersgftog f g z ) ye ) : hfiber  ( hfibersgftog f g z ) ye .
Proof . intros . destruct ye as [ y e ] . destruct e . unfold hfibersgftog .  unfold hfibersgftog in xee' . destruct xee' as [ xe e' ] . destruct xe as [ x e ] .  simpl in e' . split with ( hfiberpair ( funcomp f g ) x ( pathscomp0 ( maponpaths g (maponpaths (hfiberpr1 g (g y)) e') ) ( idpath (g y ))) ) .  simpl . apply ( hfibertriangle2 _ (hfiberpair g (f x) (( pathscomp0 ( maponpaths g (maponpaths (hfiberpr1 g (g y)) e') ) ( idpath (g y ))))) ( hfiberpair g y ( idpath _ ) ) ( maponpaths ( hfiberpr1 _ _ ) e' ) ( idpath _ ) )  .  Defined .

Definition homotffggid   { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( ye : hfiber g z ) ( xee' : hfiber  ( hfibersgftog f g z ) ye ) : paths ( ffgg f g z ye xee' ) xee' .
Proof . intros .  destruct ye as [ y e ] . destruct e .  destruct xee' as [ xe e' ] .  destruct e' .  destruct xe as [ x e ] . destruct e .  simpl . apply idpath . Defined . 

Theorem isweqezmaphf { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( ye : hfiber g z ) : isweq ( ezmaphf f g z ye ) . 
Proof . intros . set ( ff := ezmaphf f g z ye ) . set ( gg := invezmaphf f g z ye ) . 
assert ( egf : forall xe : _ , paths ( gg ( ff xe ) ) xe ) . destruct ye as [ y e ] . destruct e .  intro xe .   apply ( hfibertriangle2 f ( gg ( ff xe ) ) xe ( idpath ( pr1 xe ) ) ) . destruct xe as [ x ex ] . simpl in ex . destruct ( ex ) .  simpl .   apply idpath . 
assert ( efg : forall xee' : _ , paths ( ff ( gg xee' ) ) xee' ) . destruct ye as [ y e ] . destruct e .  intro xee' . 
assert ( hint : paths ( ff ( gg xee' ) ) ( ffgg f g ( g y ) ( hfiberpair g y ( idpath _ ) ) xee'  ) ) .  destruct xee' as [ xe e' ] .   destruct xe as [ x e ] .  apply idpath . 
apply ( pathscomp0 hint ( homotffggid _ _ _ _ xee' ) ) . 
apply ( gradth _ _ egf efg ) . Defined .  


Definition ezweqhf { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( ye : hfiber g z ) : weq ( hfiber f ( pr1 ye ) ) ( hfiber  ( hfibersgftog f g z ) ye ) := weqpair _ ( isweqezmaphf f g z ye ) . 
Definition fibseqhf  { X Y Z : UU } (f:X -> Y)(g: Y -> Z)(z:Z)(ye: hfiber  g z) : fibseqstr (hfibersftogf f g z ye) (hfibersgftog f g z) ye := fibseqstrpair _ _ _ _ ( isweqezmaphf f g z ye ) . 

Definition isweqinvezmaphf  { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( ye : hfiber g z ) : isweq ( invezmaphf f g z ye ) := pr2 ( invweq ( ezweqhf f g z ye ) ) .


Corollary weqhfibersgwtog { X Y Z : UU } ( w : weq X Y ) ( g : Y -> Z ) ( z : Z ) : weq ( hfiber ( funcomp w g ) z ) ( hfiber g z ) .
Proof. intros . split with ( hfibersgftog w g z ) .  intro ye . apply ( iscontrweqf ( ezweqhf w g z ye ) ( ( pr2 w ) ( pr1 ye ) ) ) . Defined .
























(** ** Fiber-wise weak equivalences. 


Theorems saying that a fiber-wise morphism between total spaces is a weak equivalence if and only if all the morphisms between the fibers are weak equivalences. *)


Definition totalfun { X : UU } ( P Q : X -> UU ) (f: forall x:X, P x -> Q x) := (fun z: total2 P => tpair Q (pr1  z) (f (pr1  z) (pr2  z))).


Theorem isweqtotaltofib { X : UU } ( P Q : X -> UU) (f: forall x:X, P x -> Q x):
isweq (totalfun _ _ f) -> forall x:X, isweq (f x).
Proof. intros X P Q f X0 x. set (totp:= total2 P). set (totq := total2 Q).  set (totf:= (totalfun _ _ f)). set (pip:= fun z: totp => pr1  z). set (piq:= fun z: totq => pr1  z). 

set (hfx:= hfibersgftog totf piq x).  simpl in hfx. 
assert (H: isweq hfx). unfold isweq. intro y. 
set (int:= invezmaphf totf piq x y). 
assert (X1:isweq int). apply (isweqinvezmaphf totf piq x y). destruct y as [ t e ]. 
assert (is1: iscontr (hfiber  totf t)). apply (X0 t). apply (iscontrweqb  ( weqpair int X1 ) is1).   
set (ip:= ezmappr1 P x). set (iq:= ezmappr1 Q x). set (h:= fun p: P x => hfx (ip p)).  
assert (is2: isweq h). apply (twooutof3c ip hfx (isweqezmappr1 P x) H). set (h':= fun p: P x => iq ((f x) p)). 
assert (ee: forall p:P x, paths (h p) (h' p)). intro. apply idpath.  
assert (X2:isweq h'). apply (isweqhomot   h h' ee is2). 
apply (twooutof3a (f x) iq X2). 
apply (isweqezmappr1 Q x). Defined.


Definition weqtotaltofib { X : UU } ( P Q : X -> UU ) ( f : forall x : X , P x -> Q x ) ( is : isweq ( totalfun _ _ f ) ) ( x : X ) : weq ( P x ) ( Q x ) := weqpair _ ( isweqtotaltofib P Q f is x ) . 
 

Theorem isweqfibtototal { X : UU } ( P Q : X -> UU) (f: forall x:X, weq ( P x ) ( Q x ) ) : isweq (totalfun _ _ f).
Proof. intros X P Q f . set (fpq:= totalfun P Q f). set (pr1p:= fun z: total2 P => pr1  z). set (pr1q:= fun z: total2 Q => pr1  z). unfold isweq. intro xq.   set (x:= pr1q xq). set (xqe:= hfiberpair  pr1q  xq (idpath _)). set (hfpqx:= hfibersgftog fpq pr1q x). 

assert (isint: iscontr (hfiber  hfpqx xqe)). 
assert (isint1: isweq hfpqx). set (ipx:= ezmappr1 P x). set (iqx:= ezmappr1 Q x).   set (diag:= fun p:P x => (iqx ((f x) p))). 
assert (is2: isweq diag).  apply (twooutof3c (f x) iqx (pr2 ( f x) ) (isweqezmappr1 Q x)).  apply (twooutof3b  ipx hfpqx (isweqezmappr1 P x) is2).  unfold isweq in isint1.  apply (isint1 xqe). 
set (intmap:= invezmaphf  fpq pr1q x xqe). apply (iscontrweqf  ( weqpair intmap (isweqinvezmaphf fpq pr1q x xqe) ) isint). 
Defined.

Definition weqfibtototal { X : UU } ( P Q : X -> UU) (f: forall x:X, weq ( P x ) ( Q x ) ) := weqpair _ ( isweqfibtototal P Q f ) .






(** ** Homotopy fibers of the function [fpmap: total2 X (P f) -> total2 Y P].

Given [ X Y ] in [ UU ], [ P:Y -> UU ] and [ f: X -> Y ] we get a function [ fpmap: total2 X (P f) -> total2 Y P ]. The main theorem of this section asserts that the homotopy fiber of fpmap over [ yp:total Y P ] is naturally weakly equivalent to the homotopy fiber of [ f ] over [ pr1 yp ]. In particular, if  [ f ] is a weak equivalence then so is [ fpmap ]. *)


Definition fpmap { X Y : UU } (f: X -> Y) ( P:Y-> UU) : total2 ( fun x => P ( f x ) ) -> total2 P := 
(fun z:total2 (fun x:X => P (f x)) => tpair P (f (pr1  z)) (pr2  z)).


Definition hffpmap2 { X Y : UU } (f: X -> Y) (P:Y-> UU):  total2 ( fun x => P ( f x ) ) -> total2 (fun u:total2 P => hfiber  f (pr1  u)).
Proof. intros X Y f P X0. set (u:= fpmap f P X0).  split with u. set (x:= pr1  X0).  split with x. simpl. apply idpath. Defined.


Definition hfiberfpmap { X Y : UU } (f:X -> Y)(P:Y-> UU)(yp: total2 P): hfiber  (fpmap f P) yp -> hfiber  f (pr1  yp).
Proof. intros X Y f P yp X0. set (int1:= hfibersgftog (hffpmap2  f P) (fun u: (total2 (fun u:total2 P => hfiber  f (pr1  u))) => (pr1  u)) yp).  set (phi:= invezmappr1 (fun u:total2 P => hfiber  f (pr1  u)) yp). apply (phi (int1 X0)).   Defined. 



Lemma centralfiber { X : UU } (P:X -> UU)(x:X): isweq (fun p: P x => tpair (fun u: coconusfromt X x => P ( pr1  u)) (coconusfromtpair X (idpath x)) p).
Proof. intros. set (f:= fun p: P x => tpair (fun u: coconusfromt X x => P(pr1  u)) (coconusfromtpair X (idpath x)) p). set (g:= fun z: total2 (fun u: coconusfromt X x => P ( pr1  u)) => transportf P (pathsinv0 (pr2  (pr1  z))) (pr2  z)).  

assert (efg: forall  z: total2 (fun u: coconusfromt X x => P ( pr1  u)), paths (f (g z)) z). intro. destruct z as [ t x0 ]. destruct t as [t x1 ].   simpl. destruct x1. simpl. apply idpath. 

assert (egf: forall p: P x , paths (g (f p)) p).  intro. apply idpath.  

apply (gradth f g egf efg). Defined. 


Lemma isweqhff { X Y : UU } (f: X -> Y)(P:Y-> UU): isweq (hffpmap2  f P). 
Proof. intros. set (int:= total2 (fun x:X => total2 (fun u: coconusfromt Y (f x) => P (pr1  u)))). set (intpair:= tpair (fun x:X => total2 (fun u: coconusfromt Y (f x) => P (pr1  u)))).  set (toint:= fun z: (total2 (fun u : total2 P => hfiber  f (pr1  u))) => intpair (pr1  (pr2  z)) (tpair  (fun u: coconusfromt Y (f (pr1  (pr2  z))) => P (pr1  u)) (coconusfromtpair _ (pr2  (pr2  z))) (pr2  (pr1  z)))). set (fromint:= fun z: int => tpair (fun u:total2 P => hfiber  f (pr1  u)) (tpair P (pr1  (pr1  (pr2  z))) (pr2  (pr2  z))) (hfiberpair  f  (pr1  z) (pr2  (pr1  (pr2  z))))). assert (fromto: forall u:(total2 (fun u : total2 P => hfiber  f (pr1  u))), paths (fromint (toint u)) u). simpl in toint. simpl in fromint. simpl. intro u. destruct u as [ t x ]. destruct x. destruct t as [ p0 p1 ] . simpl. unfold toint. unfold fromint. simpl. apply idpath. assert (tofrom: forall u:int, paths (toint (fromint u)) u). intro. destruct u as [ t x ]. destruct x as [ t0 x ]. destruct t0. simpl in x. simpl. unfold fromint. unfold toint. simpl. apply idpath. assert (is: isweq toint). apply (gradth  toint fromint fromto tofrom).  clear tofrom. clear fromto.  clear fromint.

set (h:= fun u: total2 (fun x:X => P (f x)) => toint ((hffpmap2  f P) u)). simpl in h. 

assert (l1: forall x:X, isweq (fun p: P (f x) => tpair  (fun u: coconusfromt _ (f x) => P (pr1  u)) (coconusfromtpair _ (idpath  (f x))) p)). intro. apply (centralfiber P (f x)).  

assert (X0:isweq h). apply (isweqfibtototal  (fun x:X => P (f x))  (fun x:X => total2 (fun u: coconusfromt _ (f x) => P (pr1  u))) (fun x:X =>  weqpair _  ( l1 x ) ) ).   

apply (twooutof3a (hffpmap2  f P) toint X0 is). Defined. 




Theorem isweqhfiberfp { X Y : UU } (f:X -> Y)(P:Y-> UU)(yp: total2 P): isweq (hfiberfpmap  f P yp).
Proof. intros. set (int1:= hfibersgftog (hffpmap2  f P) (fun u: (total2 (fun u:total2 P => hfiber  f (pr1  u))) => (pr1  u)) yp). assert (is1: isweq int1). simpl in int1 . apply ( pr2 ( weqhfibersgwtog ( weqpair _ ( isweqhff f P ) ) (fun u : total2 (fun u : total2 P => hfiber f (pr1 u)) => pr1 u) yp ) ) .  set (phi:= invezmappr1 (fun u:total2 P => hfiber  f (pr1  u)) yp). assert (is2: isweq phi).  apply ( pr2 ( invweq ( ezweqpr1 (fun u:total2 P => hfiber  f (pr1  u)) yp ) ) ) . apply (twooutof3c int1 phi is1 is2).   Defined. 


Corollary isweqfpmap { X Y : UU } ( w : weq X Y )(P:Y-> UU) :  isweq (fpmap w P).
Proof. intros. unfold isweq.   intro y.  set (h:=hfiberfpmap w P y). 
assert (X1:isweq h). apply isweqhfiberfp. 
assert (is: iscontr (hfiber w (pr1  y))). apply ( pr2 w ). apply (iscontrweqb  ( weqpair h X1 ) is). Defined. 

Definition weqfp { X Y : UU } ( w : weq X Y )(P:Y-> UU) := weqpair _ ( isweqfpmap w P ) .


(** *** Total spaces of families over a contractible base *)

Definition fromtotal2overunit ( P : unit -> UU ) ( tp : total2 P ) : P tt .
Proof . intros . destruct tp as [ t p ] . destruct t . apply p . Defined .

Definition tototal2overunit   ( P : unit -> UU ) ( p : P tt ) : total2 P  := tpair P tt p . 

Theorem weqtotal2overunit ( P : unit -> UU ) : weq ( total2 P ) ( P tt ) .
Proof. intro . set ( f := fromtotal2overunit P ) . set ( g := tototal2overunit P ) . split with f . 
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro a . destruct a as [ t p ] . destruct t . apply idpath .
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro a . apply idpath .    
apply ( gradth _ _ egf efg ) . Defined . 



(** ** The maps between total spaces of families given by a map between the bases of the families and maps between the corresponding members of the families *)


Definition bandfmap { X Y : UU }(f: X -> Y) ( P : X -> UU)(Q: Y -> UU)(fm: forall x:X, P x -> (Q (f x))): total2 P -> total2 Q:= fun xp:_ =>
match xp with
tpair x p => tpair Q (f x) (fm x p)
end.

Theorem isweqbandfmap { X Y : UU } (w : weq X Y ) (P:X -> UU)(Q: Y -> UU)( fw : forall x:X, weq ( P x) (Q (w x))) : isweq (bandfmap  _ P Q fw).
Proof. intros. set (f1:= totalfun P _ fw). set (is1:= isweqfibtototal P (fun x:X => Q (w x)) fw ).  set (f2:= fpmap w Q).  set (is2:= isweqfpmap w Q ). 
assert (h: forall xp: total2 P, paths (f2 (f1 xp)) (bandfmap  w P Q fw xp)). intro. destruct xp. apply idpath.  apply (isweqhomot  _ _ h (twooutof3c f1 f2 is1 is2)). Defined.

Definition weqbandf { X Y : UU } (w : weq X Y ) (P:X -> UU)(Q: Y -> UU)( fw : forall x:X, weq ( P x) (Q (w x))) := weqpair _ ( isweqbandfmap w P Q fw ) .






























(** ** Homotopy fiber squares *)




(** *** Homotopy commutative squares *)


Definition commsqstr { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) := forall ( z : Z ) , paths   ( f' ( g' z ) ) ( f ( g z ) ) .


Definition hfibersgtof'  { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( h : commsqstr f f' g g' ) ( x : X ) ( ze : hfiber g x ) : hfiber f' ( f x )  .
Proof. intros . destruct ze as [ z e ] . split with ( g' z ) .    apply ( pathscomp0  ( h z )  ( maponpaths f e )  ) . Defined . 

Definition hfibersg'tof  { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( h : commsqstr f f' g g' ) ( x' : X' ) ( ze : hfiber g' x' ) : hfiber f ( f' x' )  .
Proof. intros . destruct ze as [ z e ] . split with ( g z ) .    apply ( pathscomp0 ( pathsinv0 ( h z ) ) ( maponpaths f' e ) ) . Defined . 


Definition transposcommsqstr { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) : commsqstr f f' g g' -> commsqstr f' f g' g := fun h : _ => fun z : Z => ( pathsinv0 ( h z ) ) . 


(** *** Short complexes and homotopy commutative squares *)

Lemma complxstrtocommsqstr { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( h : complxstr f g z ) : commsqstr ( fun t : unit => z ) g ( fun x : X => tt ) f .
Proof. intros .  assumption .   Defined . 


Lemma commsqstrtocomplxstr { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( h : commsqstr ( fun t : unit => z ) g ( fun x : X => tt ) f ) : complxstr f g z .
Proof. intros . assumption .   Defined . 


(** *** Homotopy fiber products *)



Definition hfp {X X' Y:UU} (f:X -> Y) (f':X' -> Y):= total2 (fun xx' : dirprod X X'  => paths ( f' ( pr2 xx' ) ) ( f ( pr1 xx' ) ) ) .
Definition hfpg {X X' Y:UU} (f:X -> Y) (f':X' -> Y) : hfp f f' -> X := fun xx'e => ( pr1 ( pr1 xx'e ) ) .
Definition hfpg' {X X' Y:UU} (f:X -> Y) (f':X' -> Y) : hfp f f' -> X' := fun xx'e => ( pr2 ( pr1 xx'e ) ) .

Definition commsqZtohfp { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( h : commsqstr f f' g g' ) : Z -> hfp f f' := fun z : _ => tpair _ ( dirprodpair ( g z ) ( g' z ) ) ( h z ) .

Definition commsqZtohfphomot  { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( h : commsqstr f f' g g' ) : forall z : Z , paths ( hfpg _ _ ( commsqZtohfp _ _ _ _ h z ) ) ( g z ) := fun z : _ => idpath _ . 

Definition commsqZtohfphomot'  { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( h : commsqstr f f' g g' ) : forall z : Z , paths ( hfpg' _ _ ( commsqZtohfp _ _ _ _ h z ) ) ( g' z ) := fun z : _ => idpath _ . 


Definition hfpoverX {X X' Y:UU} (f:X -> Y) (f':X' -> Y) := total2 (fun x : X => hfiber  f' ( f x ) ) .
Definition hfpoverX' {X X' Y:UU} (f:X -> Y) (f':X' -> Y) := total2 (fun x' : X' => hfiber  f (f' x' ) ) .


Definition weqhfptohfpoverX {X X' Y:UU} (f:X -> Y) (f':X' -> Y) : weq ( hfp f f' ) ( hfpoverX f f' ) .
Proof. intros . apply ( weqtotal2asstor ( fun x : X => X' ) ( fun  xx' : dirprod X X'  => paths  ( f' ( pr2 xx' ) ) ( f ( pr1 xx' ) ) ) ) .   Defined . 


Definition weqhfptohfpoverX' {X X' Y:UU} (f:X -> Y) (f':X' -> Y) : weq ( hfp f f' ) ( hfpoverX' f f' ) .
Proof. intros .  set ( w1 := weqfp ( weqdirprodcomm X X' ) ( fun xx' : dirprod X' X  => paths ( f' ( pr1 xx' ) ) ( f ( pr2 xx' ) ) ) ) .  simpl in w1 .  
set ( w2 := weqfibtototal ( fun  x'x : dirprod X' X  => paths  ( f' ( pr1 x'x ) ) ( f ( pr2 x'x ) ) ) ( fun  x'x : dirprod X' X  => paths   ( f ( pr2 x'x ) ) ( f' ( pr1 x'x ) ) ) ( fun x'x : _ => weqpathsinv0  ( f' ( pr1 x'x ) ) ( f ( pr2 x'x ) ) ) ) . set ( w3 := weqtotal2asstor ( fun x' : X' => X ) ( fun  x'x : dirprod X' X  => paths   ( f ( pr2 x'x ) ) ( f' ( pr1 x'x ) ) ) ) .  simpl in w3 .  apply ( weqcomp ( weqcomp w1 w2 ) w3 )   .  Defined . 


Lemma weqhfpcomm { X X' Y : UU } ( f : X -> Y ) ( f' : X' -> Y ) : weq ( hfp f f' ) ( hfp f' f ) .
Proof . intros . set ( w1 :=  weqfp ( weqdirprodcomm X X' ) ( fun xx' : dirprod X' X  => paths ( f' ( pr1 xx' ) ) ( f ( pr2 xx' ) ) ) ) .  simpl in w1 .  set ( w2 := weqfibtototal ( fun  x'x : dirprod X' X  => paths  ( f' ( pr1 x'x ) ) ( f ( pr2 x'x ) ) ) ( fun  x'x : dirprod X' X  => paths   ( f ( pr2 x'x ) ) ( f' ( pr1 x'x ) ) ) ( fun x'x : _ => weqpathsinv0  ( f' ( pr1 x'x ) ) ( f ( pr2 x'x ) ) ) ) . apply ( weqcomp w1 w2 ) .     Defined . 


Definition commhfp {X X' Y:UU} (f:X -> Y) (f':X' -> Y) : commsqstr f f' ( hfpg f f' ) ( hfpg' f f' ) := fun xx'e : hfp f f' => pr2 xx'e . 


(** *** Homotopy fiber products and homotopy fibers *)

Definition  hfibertohfp { X Y : UU } ( f : X -> Y ) ( y : Y ) ( xe : hfiber f y ) : hfp ( fun t : unit => y ) f :=  tpair ( fun tx : dirprod unit X => paths ( f ( pr2 tx ) ) y ) ( dirprodpair tt ( pr1 xe ) ) ( pr2 xe )  . 

Definition hfptohfiber { X Y : UU } ( f : X -> Y ) ( y : Y ) ( hf : hfp ( fun t : unit => y ) f ) : hfiber f y := hfiberpair f ( pr2 ( pr1 hf ) ) ( pr2 hf ) .

Lemma weqhfibertohfp  { X Y : UU } ( f : X -> Y ) ( y : Y ) : weq ( hfiber f y )  ( hfp ( fun t : unit => y ) f ) .
Proof . intros . set ( ff := hfibertohfp f y ) . set ( gg := hfptohfiber f y ) . split with ff .
assert ( egf : forall xe : _ , paths ( gg ( ff xe ) ) xe ) . intro . destruct xe . apply idpath .
assert ( efg : forall hf : _ , paths ( ff ( gg hf ) ) hf ) . intro . destruct hf as [ tx e ] . destruct tx as [ t x ] . destruct t .   apply idpath .
apply ( gradth _ _ egf efg ) . Defined .  







(** *** Homotopy fiber squares *)


Definition ishfsq { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( h : commsqstr f f' g g' ) :=  isweq ( commsqZtohfp f f' g g' h ) .

Definition hfsqstr  { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) := total2 ( fun h : commsqstr f f' g g' => isweq ( commsqZtohfp f f' g g' h ) ) .
Definition hfsqstrpair { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) := tpair ( fun h : commsqstr f f' g g' => isweq ( commsqZtohfp f f' g g' h ) ) .
Definition hfsqstrtocommsqstr { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) : hfsqstr f f' g g' -> commsqstr f f' g g' := @pr1 _ ( fun h : commsqstr f f' g g' => isweq ( commsqZtohfp f f' g g' h ) ) .
Coercion hfsqstrtocommsqstr : hfsqstr >-> commsqstr . 

Definition weqZtohfp  { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( hf : hfsqstr f f' g g' ) : weq Z ( hfp f f' ) := weqpair _ ( pr2 hf ) .

Lemma isweqhfibersgtof' { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( hf : hfsqstr f f' g g' ) ( x : X ) : isweq ( hfibersgtof' f f' g g' hf x ) .
Proof. intros . set ( is := pr2 hf ) . set ( h := pr1 hf ) . 
set ( a := weqtococonusf g ) . set ( c := weqpair _ is ) .  set ( d := weqhfptohfpoverX f f' ) .  set ( b0 := totalfun _ _ ( hfibersgtof' f f' g g' h ) ) .    
assert ( h1 : forall z : Z , paths ( d ( c z ) ) ( b0 ( a z ) ) ) . intro . simpl .  unfold b0 . unfold a .   unfold weqtococonusf . unfold tococonusf .   simpl .  unfold totalfun . simpl . assert ( e : paths ( h  z ) ( pathscomp0 (h z) (idpath (f (g z))) ) ) . apply ( pathsinv0 ( pathscomp0rid _ ) ) .  destruct e .  apply idpath .
assert ( is1 : isweq ( fun z : _ => b0 ( a z ) ) ) . apply ( isweqhomot _ _ h1 ) .   apply ( twooutof3c _ _ ( pr2 c ) ( pr2 d ) ) .  
assert ( is2 : isweq b0 ) . apply ( twooutof3b _ _ ( pr2 a ) is1 ) .  apply ( isweqtotaltofib _ _ _ is2 x ) .   Defined . 

Definition weqhfibersgtof' { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( hf : hfsqstr f f' g g' ) ( x : X ) := weqpair _ ( isweqhfibersgtof' _ _ _ _ hf x ) .

Lemma ishfsqweqhfibersgtof' { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( h : commsqstr f f' g g' ) ( is : forall x : X , isweq ( hfibersgtof' f f' g g' h x ) ) :  hfsqstr f f' g g' . 
Proof .  intros . split with h . 
set ( a := weqtococonusf g ) . set ( c0 := commsqZtohfp f f' g g' h ) .  set ( d := weqhfptohfpoverX f f' ) .  set ( b := weqfibtototal _ _ ( fun x : X => weqpair _ ( is x ) ) ) .    
assert ( h1 : forall z : Z , paths ( d ( c0 z ) ) ( b ( a z ) ) ) . intro . simpl .  unfold b . unfold a .   unfold weqtococonusf . unfold tococonusf .   simpl .  unfold totalfun . simpl . assert ( e : paths ( h z ) ( pathscomp0 (h z) (idpath (f (g z))) ) ) . apply ( pathsinv0 ( pathscomp0rid _ ) ) .  destruct e .  apply idpath .
assert ( is1 : isweq ( fun z : _ => d ( c0 z ) ) ) . apply ( isweqhomot _ _ ( fun z : Z => ( pathsinv0 ( h1 z ) ) ) ) .   apply ( twooutof3c _ _ ( pr2 a ) ( pr2 b ) ) .  
 apply ( twooutof3a _ _ is1 ( pr2 d ) ) .    Defined .  


Lemma isweqhfibersg'tof { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( hf : hfsqstr f f' g g' ) ( x' : X' ) : isweq (  hfibersg'tof f f' g g' hf x' ) . 
Proof. intros . set ( is := pr2 hf ) . set ( h := pr1 hf ) .
set ( a' := weqtococonusf g' ) . set ( c' := weqpair _ is ) .  set ( d' := weqhfptohfpoverX' f f' ) .  set ( b0' := totalfun _ _ ( hfibersg'tof f f' g g' h ) ) .    
assert ( h1 : forall z : Z , paths ( d' ( c' z ) ) ( b0' ( a' z ) ) ) . intro .  unfold b0' . unfold a' .   unfold weqtococonusf . unfold tococonusf .   unfold totalfun . simpl .  assert ( e : paths ( pathsinv0 ( h  z ) ) ( pathscomp0 ( pathsinv0 (h z) ) (idpath (f' (g' z))) ) ) . apply (  pathsinv0 ( pathscomp0rid _ ) ) .  destruct e .  apply idpath .
assert ( is1 : isweq ( fun z : _ => b0' ( a' z ) ) ) . apply ( isweqhomot _ _ h1 ) .   apply ( twooutof3c _ _ ( pr2 c' ) ( pr2 d' ) ) .  
assert ( is2 : isweq b0' ) . apply ( twooutof3b _ _ ( pr2 a' ) is1 ) .  apply ( isweqtotaltofib _ _ _ is2 x' ) .   Defined . 

Definition weqhfibersg'tof { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( hf : hfsqstr f f' g g' ) ( x' : X' ) := weqpair _ ( isweqhfibersg'tof _ _ _ _ hf x' ) .

Lemma ishfsqweqhfibersg'tof { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( h : commsqstr f f' g g' ) ( is : forall x' : X' , isweq ( hfibersg'tof f f' g g' h x' ) ) :  hfsqstr f f' g g' . 
Proof .  intros . split with h . 
set ( a' := weqtococonusf g' ) . set ( c0' := commsqZtohfp f f' g g' h ) .  set ( d' := weqhfptohfpoverX' f f' ) .  set ( b' := weqfibtototal _ _ ( fun x' : X' => weqpair _ ( is x' ) ) ) .    
assert ( h1 : forall z : Z , paths ( d' ( c0' z ) ) ( b' ( a' z ) ) ) . intro . simpl .  unfold b' . unfold a' .   unfold weqtococonusf . unfold tococonusf .   unfold totalfun . simpl . assert ( e : paths ( pathsinv0 ( h z ) ) ( pathscomp0 ( pathsinv0 (h z) ) (idpath (f' (g' z))) ) ) . apply ( pathsinv0 ( pathscomp0rid _ ) ) .  destruct e .  apply idpath .
assert ( is1 : isweq ( fun z : _ => d' ( c0' z ) ) ) . apply ( isweqhomot _ _ ( fun z : Z => ( pathsinv0 ( h1 z ) ) ) ) .   apply ( twooutof3c _ _ ( pr2 a' ) ( pr2 b' ) ) .  
 apply ( twooutof3a _ _ is1 ( pr2 d' ) ) .    Defined .  

Theorem transposhfpsqstr { X X' Y Z : UU } ( f : X -> Y ) ( f' : X' -> Y ) ( g : Z -> X ) ( g' : Z -> X' ) ( hf : hfsqstr f f' g g' ) : hfsqstr f' f g' g .
Proof . intros . set ( is := pr2 hf ) . set ( h := pr1 hf ) . set ( th := transposcommsqstr f f' g g' h ) . split with th . 
set ( w1 := weqhfpcomm f f' ) . assert ( h1 : forall z : Z , paths (  w1 ( commsqZtohfp f f' g g' h z ) ) (  commsqZtohfp f' f g' g th z ) ) . intro . unfold commsqZtohfp .  simpl . unfold fpmap . unfold totalfun .   simpl .  apply idpath .  apply ( isweqhomot _ _ h1 ) .  apply ( twooutof3c _ _ is ( pr2 w1 ) ) . Defined . 

    
(** *** Fiber sequences and homotopy fiber squares *)

Theorem fibseqstrtohfsqstr { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( hf : fibseqstr f g z ) : hfsqstr ( fun t : unit => z ) g ( fun x : X => tt ) f .
Proof . intros . split with ( pr1 hf ) .  set ( ff := ezweq f g z hf ) . set ( ggff := commsqZtohfp ( fun t : unit => z ) g ( fun x : X => tt ) f ( pr1 hf )   ) .  set ( gg := weqhfibertohfp g z ) . 
apply ( weqcomp ff gg ) .  Defined . 


Theorem hfsqstrtofibseqstr  { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( hf :  hfsqstr ( fun t : unit => z ) g ( fun x : X => tt ) f ) : fibseqstr f g z .
Proof . intros . split with ( pr1 hf ) .  set ( ff := ezmap f g z ( pr1 hf ) ) . set ( ggff := weqZtohfp ( fun t : unit => z ) g ( fun x : X => tt ) f hf ) .  set ( gg := weqhfibertohfp g z ) . 
apply ( twooutof3a ff gg ( pr2 ggff ) ( pr2 gg ) ) .  Defined . 



















(** ** Basics about h-levels *)



(** *** h-levels of types *)


Fixpoint isofhlevel (n:nat) (X:UU): UU:=
match n with
O => iscontr X |
S m => forall x:X, forall x':X, (isofhlevel m (paths x x'))
end.


Theorem hlevelretract (n:nat) { X Y : UU } ( p : X -> Y ) ( s : Y -> X ) ( eps : forall y : Y , paths ( p ( s y ) ) y ) : isofhlevel n X -> isofhlevel n Y .
Proof. intro. induction n as [ | n IHn ].  intros X Y p s eps X0. unfold isofhlevel.  apply ( iscontrretract p s eps X0). 
 unfold isofhlevel. intros X Y p s eps X0 x x'. unfold isofhlevel in X0. assert (is: isofhlevel n (paths (s x) (s x'))).  apply X0. set (s':= @maponpaths _ _ s x x'). set (p':= pathssec2  s p eps x x').  set (eps':= @pathssec3 _ _  s p eps x x' ). simpl. apply (IHn  _ _ p' s' eps' is). Defined. 

Corollary  isofhlevelweqf (n:nat) { X Y : UU } ( f : weq X Y ) : isofhlevel n X  ->  isofhlevel n Y .
Proof. intros n X Y f X0.  apply (hlevelretract n  f (invmap f ) (homotweqinvweq  f )). assumption. Defined. 

Corollary  isofhlevelweqb (n:nat) { X Y : UU } ( f : weq X Y ) : isofhlevel n Y  ->  isofhlevel n X .
Proof. intros n X Y f X0 .  apply (hlevelretract n  (invmap  f ) f (homotinvweqweq  f )). assumption. Defined. 

Lemma isofhlevelsn ( n : nat ) { X : UU } ( f : X -> isofhlevel ( S n ) X ) : isofhlevel ( S n ) X.
Proof. intros . simpl . intros x x' . apply ( f x x x'). Defined.

Lemma isofhlevelssn (n:nat) { X : UU } ( is : forall x:X, isofhlevel (S n) (paths x x)) : isofhlevel (S (S n)) X.
Proof. intros . simpl.  intros x x'.  change ( forall ( x0 x'0 : paths x x' ), isofhlevel n ( paths x0 x'0 ) ) with ( isofhlevel (S n) (paths x x') ). 
assert ( X1 : paths x x' -> isofhlevel (S n) (paths x x') ) . intro X2. destruct X2. apply ( is x ). apply  ( isofhlevelsn n X1 ). Defined. 







(** *** h-levels of functions *)


Definition isofhlevelf ( n : nat ) { X Y : UU } ( f : X -> Y ) : UU := forall y:Y, isofhlevel n (hfiber  f y).


Theorem isofhlevelfhomot ( n : nat ) { X Y : UU }(f f':X -> Y)(h: forall x:X, paths (f x) (f' x)): isofhlevelf n f -> isofhlevelf n  f'.
Proof. intros n X Y f f' h X0. unfold isofhlevelf. intro y . apply ( isofhlevelweqf n ( weqhfibershomot f f' h y ) ( X0 y )) .   Defined .


Theorem isofhlevelfpmap ( n : nat ) { X Y : UU } ( f : X -> Y ) ( Q : Y -> UU ) : isofhlevelf n  f -> isofhlevelf n ( fpmap f Q ) .
Proof. intros n X Y f Q X0. unfold isofhlevelf. unfold isofhlevelf in X0.  intro y . set (yy:= pr1  y). set ( g := hfiberfpmap  f Q y). set (is:= isweqhfiberfp  f Q y). set (isy:= X0 yy).  apply (isofhlevelweqb n  ( weqpair g is ) isy). Defined. 



Theorem isofhlevelfffromZ ( n : nat ) { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( fs : fibseqstr f g z ) ( isz : isofhlevel ( S n ) Z ) : isofhlevelf n f .
Proof. intros . intro y .  assert ( w : weq ( hfiber f y ) ( paths ( g y ) z ) ) .  apply ( invweq ( ezweq1 f g z fs y ) ) .  apply ( isofhlevelweqb n w ( isz (g y ) z ) ) . Defined. 


Theorem isofhlevelXfromg ( n : nat ) { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( fs : fibseqstr f g z ) : isofhlevelf n g -> isofhlevel n X  .
Proof.  intros n X Y Z f g z fs isf . assert ( w : weq X ( hfiber g z ) ) . apply ( weqpair _ ( pr2 fs ) ) . apply ( isofhlevelweqb n w ( isf z ) ) . Defined .


Theorem isofhlevelffromXY ( n : nat ) { X Y : UU } ( f : X -> Y ) : isofhlevel n X -> isofhlevel (S n) Y -> isofhlevelf n f.
Proof. intro. induction n as [ | n IHn ] .  intros X Y f X0 X1.
assert (is1: isofhlevel O Y). split with ( f ( pr1 X0 ) ) . intro t .  unfold isofhlevel in X1 .  set ( is := X1 t ( f ( pr1 X0 ) ) ) . apply ( pr1 is ). 
apply (isweqcontrcontr  f X0 is1).

intros X Y f X0 X1.  unfold isofhlevelf. simpl.  
assert  (is1: forall x' x:X, isofhlevel n (paths x' x)). simpl in X0.  assumption.  
assert (is2: forall y' y:Y, isofhlevel (S n) (paths y' y)). simpl in X1.  simpl. assumption.
assert (is3: forall (y:Y)(x:X)(xe': hfiber  f y), isofhlevelf n  (d2g  f x xe')).  intros. apply (IHn  _ _ (d2g  f x xe') (is1 (pr1  xe') x) (is2 (f x) y)). 
assert (is4: forall (y:Y)(x:X)(xe': hfiber  f y)(e: paths (f x) y), isofhlevel n (paths (hfiberpair  f x e) xe')). intros.
apply (isofhlevelweqb n  ( ezweq3g f x xe' e)  (is3 y x xe' e)).
intros y xe xe' .  destruct xe as [ t x ]. apply (is4 y t xe' x). Defined.



Theorem isofhlevelXfromfY ( n : nat ) { X Y : UU } ( f : X -> Y ) : isofhlevelf n f -> isofhlevel n Y -> isofhlevel n X.
Proof. intro. induction n as [ | n IHn ] .  intros X Y f X0 X1.  apply (iscontrweqb ( weqpair f X0 ) X1). intros X Y f X0 X1. simpl.
assert (is1: forall (y:Y)(xe xe': hfiber  f y), isofhlevel n (paths xe xe')). intros. apply (X0 y). 
assert (is2: forall (y:Y)(x:X)(xe': hfiber  f y), isofhlevelf n  (d2g  f x xe')). intros. unfold isofhlevel. intro y0.
apply (isofhlevelweqf n ( ezweq3g  f x xe' y0 ) (is1 y (hfiberpair  f x y0) xe')). 
assert (is3: forall (y' y : Y), isofhlevel n (paths y' y)). simpl in X1. assumption.
intros x' x .  
set (y:= f x').  set (e':= idpath y). set (xe':= hfiberpair  f x' e').
apply (IHn  _ _ (d2g  f x xe') (is2 y x xe') (is3 (f x) y)). Defined. 






Theorem  isofhlevelffib ( n : nat ) { X : UU } ( P : X -> UU ) ( x : X ) ( is : forall x':X, isofhlevel n (paths x' x) ) : isofhlevelf n ( tpair P x ) .
Proof . intros . unfold isofhlevelf . intro xp .   apply (isofhlevelweqf n ( ezweq1pr1 P x xp) ( is ( pr1 xp ) ) ) . Defined . 



Theorem isofhlevelfhfiberpr1y ( n : nat ) { X Y : UU } ( f : X -> Y ) ( y : Y ) ( is : forall y':Y, isofhlevel n (paths  y' y) ) : isofhlevelf n ( hfiberpr1 f y).
Proof.  intros .  unfold isofhlevelf. intro x.  apply (isofhlevelweqf n ( ezweq1g f y x ) ( is ( f x ) ) ) . Defined. 






Theorem isofhlevelfsnfib (n:nat) { X : UU } (P:X -> UU)(x:X) ( is : isofhlevel (S n) (paths x x) ) : isofhlevelf (S n) ( tpair P x ).
Proof. intros .  unfold isofhlevelf. intro xp. apply (isofhlevelweqf (S n) ( ezweq1pr1 P x xp ) ).  apply isofhlevelsn . intro X1 . destruct X1 . assumption .  Defined .   




Theorem isofhlevelfsnhfiberpr1 ( n : nat ) { X Y : UU } (f : X -> Y ) ( y : Y ) ( is : isofhlevel (S n) (paths y y) ) : isofhlevelf (S n) (hfiberpr1 f y).
Proof.  intros .  unfold isofhlevelf. intro x. apply (isofhlevelweqf (S n)  ( ezweq1g f y x ) ). apply isofhlevelsn. intro X1. destruct X1.  assumption. Defined . 




Corollary isofhlevelfhfiberpr1 ( n : nat ) { X Y : UU }  ( f : X -> Y ) ( y : Y ) ( is : isofhlevel (S n) Y ) : isofhlevelf n ( hfiberpr1 f y ) .
Proof. intros. apply isofhlevelfhfiberpr1y. intro y' . apply (is y' y).   Defined. 






Theorem isofhlevelff ( n : nat ) { X Y Z : UU } (f : X -> Y ) ( g : Y -> Z ) : isofhlevelf n  (fun x : X => g ( f x) ) -> isofhlevelf (S n)  g -> isofhlevelf n  f.
Proof. intros n X Y Z f g X0 X1. unfold isofhlevelf. intro y . set (ye:= hfiberpair  g  y (idpath (g y))). 
apply (isofhlevelweqb n  ( ezweqhf  f g (g y) ye ) (isofhlevelffromXY n  _ (X0 (g y)) (X1 (g y)) ye)). Defined.



Theorem isofhlevelfgf ( n : nat ) { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) : isofhlevelf n  f -> isofhlevelf n  g -> isofhlevelf n  (fun x:X => g(f x)).
Proof. intros n X Y Z f g X0 X1.  unfold isofhlevelf. intro z. 
assert (is1: isofhlevelf n  (hfibersgftog  f g z)). unfold isofhlevelf. intro ye. apply (isofhlevelweqf n ( ezweqhf  f g z ye ) (X0 (pr1  ye))). 
assert (is2: isofhlevel n (hfiber  g z)). apply (X1 z).
apply (isofhlevelXfromfY n  _ is1 is2). Defined.



Theorem isofhlevelfgwtog (n:nat ) { X Y Z : UU } ( w : weq X Y ) ( g : Y -> Z ) ( is : isofhlevelf n  (fun x : X => g ( w x ) ) ) : isofhlevelf n g  .
Proof. intros . intro z . assert ( is' : isweq ( hfibersgftog w g z ) ) .  intro ye . apply ( iscontrweqf ( ezweqhf w g z ye ) ( pr2 w ( pr1 ye ) ) ) .  apply ( isofhlevelweqf _ ( weqpair _ is' ) ( is _ ) ) .  Defined . 



Theorem isofhlevelfgtogw (n:nat ) { X Y Z : UU } ( w : weq X Y ) ( g : Y -> Z ) ( is : isofhlevelf n g ) :  isofhlevelf n  (fun x : X => g ( w x ) ) .
Proof. intros . intro z . assert ( is' : isweq ( hfibersgftog w g z ) ) .  intro ye . apply ( iscontrweqf ( ezweqhf w g z ye ) ( pr2 w ( pr1 ye ) ) ) .  apply ( isofhlevelweqb _ ( weqpair _ is' ) ( is _ ) ) .  Defined . 



Corollary isofhlevelfhomot2 (n:nat) { X X' Y : UU } (f:X -> Y)(f':X' -> Y)(w : weq X X' )(h:forall x:X, paths (f x) (f' (w x))) : isofhlevelf n  f -> isofhlevelf n  f'.  
Proof. intros n X X' Y f f' w h X0.  assert (X1: isofhlevelf n  (fun x:X => f' (w x))). apply (isofhlevelfhomot n _ _ h X0). 
apply (isofhlevelfgwtog n  w f' X1). Defined.




Theorem isofhlevelfonpaths (n:nat) { X Y : UU }(f:X -> Y)(x x':X): isofhlevelf (S n)  f -> isofhlevelf n  (@maponpaths _ _ f x x').
Proof. intros n X Y f x x' X0. 
set (y:= f x'). set (xe':= hfiberpair  f x' (idpath _ )). 
assert (is1: isofhlevelf n  (d2g  f x xe')). unfold isofhlevelf. intro y0 .  apply (isofhlevelweqf n  ( ezweq3g  f x xe' y0  ) (X0 y (hfiberpair  f x y0) xe')). 
assert (h: forall ee:paths x' x, paths (d2g  f x xe' ee) (maponpaths f  (pathsinv0  ee))). intro.
assert (e0: paths (pathscomp0   (maponpaths f  (pathsinv0 ee)) (idpath _ ))  (maponpaths f  (pathsinv0  ee)) ). destruct ee.  simpl.  apply idpath. apply (e0). apply (isofhlevelfhomot2 n _ _  ( weqpair (@pathsinv0 _ x' x ) (isweqpathsinv0 _ _ ) ) h is1) . Defined. 



Theorem isofhlevelfsn (n:nat) { X Y : UU } (f:X -> Y): (forall x x':X, isofhlevelf n  (@maponpaths _ _ f x x')) -> isofhlevelf (S n)  f.
Proof. intros n X Y f X0.  unfold isofhlevelf. intro y .  simpl.  intros x x' . destruct x as [ x e ]. destruct x' as [ x' e' ].  destruct e' . set (xe':= hfiberpair  f x' ( idpath _ ) ).  set (xe:= hfiberpair  f x e). set (d3:= d2g  f x xe'). simpl in d3.  
assert (is1: isofhlevelf n  (d2g  f x xe')). 
assert (h: forall ee: paths x' x, paths (maponpaths f  (pathsinv0  ee)) (d2g  f x xe' ee)). intro. unfold d2g. simpl .  apply ( pathsinv0 ( pathscomp0rid _ ) ) . 
assert (is2: isofhlevelf n  (fun ee: paths x' x => maponpaths f  (pathsinv0  ee))).  apply (isofhlevelfgtogw n  ( weqpair _ (isweqpathsinv0  _ _  ) ) (@maponpaths _ _ f x x') (X0 x x')). 
apply (isofhlevelfhomot n  _ _  h is2). 
apply (isofhlevelweqb n  (  ezweq3g f x xe' e )  (is1 e)).  Defined.


Theorem isofhlevelfssn (n:nat) { X Y : UU } (f:X -> Y): (forall x:X, isofhlevelf (S n)  (@maponpaths _ _ f x x)) -> isofhlevelf (S (S n))  f.
Proof.  intros n X Y f X0.  unfold isofhlevelf. intro y .
assert (forall xe0: hfiber  f y, isofhlevel (S n) (paths xe0 xe0)). intro. destruct xe0 as [ x e ].  destruct e . set (e':= idpath ( f x ) ).  set (xe':= hfiberpair  f x e').  set (xe:= hfiberpair  f x e' ). set (d3:= d2g  f x xe'). simpl in d3.  
assert (is1: isofhlevelf (S n)  (d2g  f x xe')). 
assert (h: forall ee: paths x x, paths (maponpaths f  (pathsinv0  ee))  (d2g  f x xe' ee)). intro. unfold d2g . simpl . apply ( pathsinv0 ( pathscomp0rid _ ) ) .  
assert (is2: isofhlevelf (S n)  (fun ee: paths x x => maponpaths f  (pathsinv0  ee))).  apply (isofhlevelfgtogw ( S n )  ( weqpair _ (isweqpathsinv0  _ _  ) ) (@maponpaths _ _ f x x) ( X0 x )) . 
apply (isofhlevelfhomot (S n) _ _  h is2). 
apply (isofhlevelweqb (S n)  ( ezweq3g  f x xe' e' )  (is1 e')).  
apply (isofhlevelssn).  assumption. Defined.



(** ** h -levels of [ pr1 ], fiber inclusions, fibers, total spaces and bases of fibrations *)


(** *** h-levelf of [ pr1 ] *)


Theorem isofhlevelfpr1 (n:nat) { X : UU } (P:X -> UU)(is: forall x:X, isofhlevel n (P x)) : isofhlevelf n  (@pr1 X P).
Proof. intros. unfold isofhlevelf. intro x .  apply (isofhlevelweqf n  ( ezweqpr1  _ x)    (is x)). Defined.

Lemma isweqpr1 { Z : UU } ( P : Z -> UU ) ( is1 : forall z : Z, iscontr ( P z ) ) : isweq ( @pr1 Z P ) .
Proof. intros. unfold isweq.  intro y. set (isy:= is1 y). apply (iscontrweqf ( ezweqpr1 P y)) . assumption. Defined. 

Definition weqpr1 { Z : UU } ( P : Z -> UU ) ( is : forall z : Z , iscontr ( P z ) ) : weq ( total2 P ) Z := weqpair _ ( isweqpr1 P is ) . 




(** *** h-level of the total space [ total2 ] *)  

Theorem isofhleveltotal2 ( n : nat ) { X : UU } ( P : X -> UU ) ( is1 : isofhlevel n X )( is2 : forall x:X, isofhlevel n (P x) ) : isofhlevel n (total2 P).
Proof. intros. apply (isofhlevelXfromfY n  (@pr1 _ _ )). apply isofhlevelfpr1. assumption. assumption. Defined. 

Corollary isofhleveldirprod ( n : nat ) ( X Y : UU ) ( is1 : isofhlevel n X ) ( is2 : isofhlevel n Y ) : isofhlevel n (dirprod X Y).
Proof. intros. apply isofhleveltotal2. assumption. intro. assumption. Defined. 















(** ** Propositions, inclusions  and sets *)







(** *** Basics about types of h-level 1 - "propositions" *)


Definition isaprop  := isofhlevel (S O)  . 

Notation isapropunit := iscontrpathsinunit .

Notation isapropdirprod := ( isofhleveldirprod 1 ) . 

Lemma isapropifcontr { X : UU } ( is : iscontr X ) : isaprop X .
Proof. intros . set (f:= fun x:X => tt). assert (isw : isweq f). apply isweqcontrtounit.  assumption. apply (isofhlevelweqb (S O) ( weqpair f isw ) ).  intros x x' . apply iscontrpathsinunit. Defined.
Coercion isapropifcontr : iscontr >-> isaprop  .  

Theorem hlevelntosn ( n : nat ) ( T : UU )  ( is : isofhlevel n T ) : isofhlevel (S n) T.
Proof. intro.   induction n as [ | n IHn ] . intro. apply isapropifcontr. intro.  intro X. change (forall t1 t2:T, isofhlevel (S n) (paths t1 t2)). intros t1 t2 . change (forall t1 t2 : T, isofhlevel n (paths t1 t2)) in X. set (XX := X t1 t2). apply (IHn _ XX).  Defined.

Corollary isofhlevelcontr (n:nat) { X : UU } ( is : iscontr X ) : isofhlevel n X.
Proof. intro. induction n as [ | n IHn ] . intros X X0 . assumption. 
intros X X0. simpl. intros x x' . assert (is: iscontr (paths x x')). apply (isapropifcontr X0 x x'). apply (IHn _ is). Defined.

Lemma isofhlevelfweq ( n : nat ) { X Y : UU } ( f : weq X Y ) :  isofhlevelf n f .
Proof. intros n X Y f .  unfold isofhlevelf.   intro y . apply ( isofhlevelcontr n ). apply ( pr2 f ). Defined.

Corollary isweqfinfibseq  { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( fs : fibseqstr f g z  ) ( isz : iscontr Z ) : isweq f .
Proof. intros . apply ( isofhlevelfffromZ 0 f g z fs ( isapropifcontr isz ) ) .  Defined .

Corollary weqhfibertocontr { X Y : UU } ( f : X -> Y ) ( y : Y ) ( is : iscontr Y ) : weq ( hfiber f y ) X .
Proof. intros . split with ( hfiberpr1 f y ) . apply ( isofhlevelfhfiberpr1 0 f y ( hlevelntosn 0 _ is ) ) . Defined.



Corollary weqhfibertounit ( X : UU ) : weq ( hfiber ( fun x : X => tt ) tt ) X .
Proof.  intro . apply ( weqhfibertocontr _ tt iscontrunit ) . Defined.  

Corollary isofhleveltofun ( n : nat ) ( X : UU ) : isofhlevel n X -> isofhlevelf n ( fun x : X => tt ) .
Proof. intros n X is .  intro t . destruct t . apply ( isofhlevelweqb n ( weqhfibertounit X ) is ) .  Defined .

Corollary isofhlevelfromfun ( n : nat ) ( X : UU ) : isofhlevelf n ( fun x : X => tt ) ->  isofhlevel n X .
Proof. intros n X is .  apply ( isofhlevelweqf n ( weqhfibertounit X ) ( is tt ) ) .  Defined .







Lemma isofhlevelsnprop (n:nat) { X : UU } ( is : isaprop X ) : isofhlevel (S n) X.
Proof. intros n X X0. simpl. unfold isaprop in X0.  simpl in X0. intros x x' . apply isofhlevelcontr. apply (X0 x x'). Defined. 

Lemma iscontraprop1 { X : UU } ( is : isaprop X ) ( x : X ) : iscontr X .
Proof. intros . unfold iscontr. split with x . intro t .  unfold isofhlevel in is .  set (is' := is t x ). apply ( pr1 is' ). 
Defined. 

Lemma iscontraprop1inv { X : UU } ( f : X -> iscontr X ) : isaprop X .
Proof. intros X X0. assert ( H : X -> isofhlevel (S O) X). intro X1.  apply (hlevelntosn O _ ( X0 X1 ) ) . apply ( isofhlevelsn O H ) . Defined.

Lemma proofirrelevance ( X : UU ) ( is : isaprop X ) : forall x x' : X , paths x x' . 
Proof. intros . unfold isaprop in is . unfold isofhlevel in is .   apply ( pr1 ( is x x' ) ). Defined. 

Lemma invproofirrelevance ( X : UU ) ( ee : forall x x' : X , paths x x' ) : isaprop X.
Proof. intros . unfold isaprop. unfold isofhlevel .  intro x .  
assert ( is1 : iscontr X ).  split with x. intro t .  apply ( ee t x). assert ( is2 : isaprop X).  apply isapropifcontr. assumption.   
unfold isaprop in is2. unfold isofhlevel in is2.  apply (is2 x). Defined. 

Lemma isweqimplimpl { X Y : UU } ( f : X -> Y ) ( g : Y -> X ) ( isx : isaprop X ) ( isy : isaprop Y ) : isweq f.
Proof. intros. 
assert (isx0: forall x:X, paths (g (f x)) x). intro. apply proofirrelevance . apply isx . 
assert (isy0 : forall y : Y, paths (f (g y)) y). intro. apply proofirrelevance . apply isy . 
apply (gradth  f g isx0 isy0).  Defined. 

Definition weqimplimpl { X Y : UU } ( f : X -> Y ) ( g : Y -> X ) ( isx : isaprop X ) ( isy : isaprop Y ) := weqpair _ ( isweqimplimpl f g isx isy ) .

Theorem isapropempty: isaprop empty.
Proof. unfold isaprop. unfold isofhlevel. intros x x' . destruct x. Defined. 


Theorem isapropempty2 { X : UU } ( a : X -> empty ) : isaprop X .
Proof . intros . set ( w := weqpair _ ( isweqtoempty a ) ) . apply ( isofhlevelweqb 1 w isapropempty ) .  Defined .




Lemma isapropifnegtrue { X : UU } ( X0 : neg X ) : isaprop X.
Proof. intros X X0. assert (is:isweq X0). intro. apply (fromempty y).   apply (isofhlevelweqb (S O)  ( weqpair _ is ) isapropempty). Defined. 




(** *** Functional extensionality for functions to the empty type *)

Axiom funextempty : forall ( X : UU ) ( f g : X -> empty ) , paths f g . 



(** *** More results on propositions *)


Theorem isapropneg (X:UU): isaprop (X -> empty).
Proof. intro.  apply invproofirrelevance . intros x x' .   apply ( funextempty X x x' ) . Defined .  

(** See also [ isapropneg2 ] *) 


Corollary isapropdneg (X:UU): isaprop (dneg X).
Proof. intro. apply (isapropneg (neg X)). Defined.


Definition isaninvprop (X:UU) := isweq  (todneg X).

Definition invimpl (X:UU) (is: isaninvprop X) : (dneg X) -> X:= invmap  ( weqpair (todneg X) is ) . 


Lemma isapropaninvprop (X:UU): isaninvprop X -> isaprop X.
Proof. intros X X0. 
apply (isofhlevelweqb (S O) ( weqpair (todneg X) X0 ) (isapropdneg X)). Defined. 


Theorem isaninvpropneg (X:UU): isaninvprop (neg X).
Proof. intros. 
set (f:= todneg (neg X)). set (g:= negf  (todneg X)). set (is1:= isapropneg X). set (is2:= isapropneg (dneg X)). apply (isweqimplimpl  f g is1 is2).  Defined.


Theorem isapropdec (X:UU): (isaprop X) -> (isaprop (coprod X (X-> empty))).
Proof. intros X X0. 
assert (X1: forall (x x': X), paths x x'). apply (proofirrelevance _ X0).  
assert (X2: forall (x x': coprod X (X -> empty)), paths x x'). intros.  
destruct x as  [ x0 | y0 ].  destruct x' as [ x | y ].   apply (maponpaths (fun x:X => ii1  x)  (X1 x0 x)).    
apply (fromempty (y x0)).
destruct x' as [ x | y ].   apply (fromempty (y0 x)). 
assert (e: paths y0 y). apply (proofirrelevance _ (isapropneg X) y0 y). apply (maponpaths (fun f: X -> empty => ii2  f)  e).
apply (invproofirrelevance _ X2).  Defined. 



(** *** Inclusions - functions of h-level 1 *)


Definition isincl { X Y : UU } (f : X -> Y ) := isofhlevelf 1 f .

Definition incl ( X Y : UU ) := total2 ( fun f : X -> Y => isincl f ) .
Definition inclpair { X Y : UU } ( f : X -> Y ) ( is : isincl f ) : incl X Y := tpair _ f is . 
Definition pr1incl ( X Y : UU ) : incl X Y -> ( X -> Y ) := @pr1 _ _ .
Coercion pr1incl : incl >-> Funclass .

Lemma isinclweq ( X Y : UU ) ( f : X -> Y ) : isweq f -> isincl f .
Proof . intros X Y f is . apply ( isofhlevelfweq 1 ( weqpair _ is ) ) .  Defined .
Coercion isinclweq : isweq >-> isincl .

Lemma isofhlevelfsnincl (n:nat) { X Y : UU } (f:X -> Y)(is: isincl  f): isofhlevelf (S n)  f.
Proof. intros. unfold isofhlevelf.  intro y . apply isofhlevelsnprop. apply (is y). Defined.  

Definition weqtoincl ( X Y : UU ) : weq X Y -> incl X Y :=  fun w => inclpair ( pr1 w ) ( pr2 w ) .  
Coercion weqtoincl : weq >-> incl . 

Lemma isinclcomp { X Y Z : UU } ( f : incl X Y ) ( g : incl Y Z ) : isincl ( funcomp ( pr1 f ) ( pr1 g ) ) .
Proof . intros . apply ( isofhlevelfgf 1 f g ( pr2 f ) ( pr2 g ) ) . Defined .

Definition inclcomp { X Y Z : UU } ( f : incl X Y ) ( g : incl Y Z ) : incl X Z := inclpair ( funcomp ( pr1 f ) ( pr1 g ) ) ( isinclcomp f g ) . 

Lemma isincltwooutof3a { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( isg : isincl g ) ( isgf : isincl ( funcomp f g ) ) : isincl f .
Proof . intros . apply ( isofhlevelff 1 f g isgf ) .  apply ( isofhlevelfsnincl 1 g isg ) . Defined .

Lemma isinclgwtog { X Y Z : UU } ( w : weq X Y ) ( g : Y -> Z ) ( is : isincl ( funcomp w g ) ) : isincl g .
Proof . intros . apply ( isofhlevelfgwtog 1 w g is ) .  Defined . 

Lemma isinclgtogw { X Y Z : UU }  ( w : weq X Y ) ( g : Y -> Z ) ( is : isincl g ) : isincl ( funcomp w g ) .
Proof . intros . apply  ( isofhlevelfgtogw 1 w g is ) . Defined . 


Lemma isinclhomot { X Y : UU } ( f g : X -> Y ) ( h : homot f g ) ( isf : isincl f ) : isincl g .
Proof . intros . apply ( isofhlevelfhomot ( S O ) f g h isf ) . Defined . 



Definition isofhlevelsninclb (n:nat) { X Y : UU } (f:X -> Y)(is: isincl  f) : isofhlevel (S n) Y -> isofhlevel (S n) X:= isofhlevelXfromfY (S n)  f (isofhlevelfsnincl n  f is).  

Definition  isapropinclb { X Y : UU } ( f : X -> Y ) ( isf : isincl f ) : isaprop Y ->  isaprop X := isofhlevelXfromfY 1 _ isf .


Lemma iscontrhfiberofincl { X Y : UU } (f:X -> Y): isincl  f -> (forall x:X, iscontr (hfiber  f (f x))).
Proof. intros X Y f X0 x. unfold isofhlevelf in X0. set (isy:= X0 (f x)).  apply (iscontraprop1 isy (hfiberpair  f _ (idpath (f x)))). Defined.


Lemma isweqonpathsincl { X Y : UU } (f:X -> Y) (is: isincl  f)(x x':X): isweq (@maponpaths _ _ f x x').
Proof. intros. apply (isofhlevelfonpaths O  f x x' is). Defined.

Definition weqonpathsincl  { X Y : UU } (f:X -> Y) (is: isincl  f)(x x':X) := weqpair _ ( isweqonpathsincl f is x x' ) .

Definition invmaponpathsincl { X Y : UU } (f:X -> Y) (is: isincl  f)(x x':X): paths (f x) (f x') -> paths x x':= invmap  ( weqonpathsincl  f is x x') .


Lemma isinclweqonpaths { X Y : UU } (f:X -> Y): (forall x x':X, isweq (@maponpaths _ _ f x x')) -> isincl  f.
Proof. intros X Y f X0.  apply (isofhlevelfsn O  f X0). Defined.


Definition isinclpr1 { X : UU } (P:X -> UU)(is: forall x:X, isaprop (P x)): isincl  (@pr1 X P):= isofhlevelfpr1 (S O) P is.






Theorem samehfibers { X Y Z : UU } (f: X -> Y) (g: Y -> Z) (is1: isincl  g) ( y: Y): weq ( hfiber f y ) ( hfiber ( fun x => g ( f x ) ) ( g y ) ) .
Proof. intros. split with (@hfibersftogf  _ _ _ f g (g y) (hfiberpair  g y (idpath _ ))) .

set (z:= g y). set (ye:= hfiberpair  g y (idpath _ )).  unfold isweq. intro xe.  
set (is3:= isweqezmap1 _ _ _ ( fibseqhf f g z ye ) xe). 
assert (w1: weq (paths (hfibersgftog f g z xe) ye) (hfiber  (hfibersftogf  f g z ye) xe)). split with (ezmap (d1 (hfibersftogf f g z ye) (hfibersgftog f g z) ye ( fibseqhf f g z ye ) xe) (hfibersftogf f g z ye) xe ( fibseq1 (hfibersftogf f g z ye) (hfibersgftog f g z) ye ( fibseqhf f g z ye ) xe) ). apply is3. apply (iscontrweqf w1 ). 
assert (is4: iscontr (hfiber g z)). apply iscontrhfiberofincl. assumption.
apply ( isapropifcontr is4  ). Defined.








(** *** Basics about types of h-level 2 - "sets" *)

Definition isaset ( X : UU ) : UU := forall x x' : X , isaprop ( paths x x' ) . 

Notation isasetdirprod := ( isofhleveldirprod 2 ) .

Lemma isasetunit : isaset unit .
Proof . apply ( isofhlevelcontr 2 iscontrunit ) . Defined .

Lemma isasetempty : isaset empty .
Proof. apply ( isofhlevelsnprop 1 isapropempty ) .  Defined . 

Lemma isasetifcontr { X : UU } ( is : iscontr X ) : isaset X .
Proof . intros . apply ( isofhlevelcontr 2 is ) . Defined .

Lemma isasetaprop { X : UU } ( is : isaprop X ) : isaset X .
Proof . intros . apply ( isofhlevelsnprop 1 is ) . Defined . 

(** The following lemma assert "uniqueness of identity proofs" (uip) for sets. *)

Lemma uip { X : UU } ( is : isaset X ) { x x' : X } ( e e' : paths x x' ) : paths e e' .
Proof. intros . apply ( proofirrelevance _ ( is x x' ) e e' ) . Defined .  

(** For the theorem about the coproduct of two sets see [ isasetcoprod ] below. *)


Lemma isofhlevelssnset (n:nat) ( X : UU ) ( is : isaset X ) : isofhlevel ( S (S n) ) X.
Proof. intros n X X0. simpl. unfold isaset in X0.   intros x x' . apply isofhlevelsnprop. set ( int := X0 x x'). assumption . Defined. 

Lemma isasetifiscontrloops (X:UU): (forall x:X, iscontr (paths x x)) -> isaset X.
Proof. intros X X0. unfold isaset. unfold isofhlevel. intros x x' x0 x0' .   destruct x0. set (is:= X0 x). apply isapropifcontr. assumption.  Defined. 

Lemma iscontrloopsifisaset (X:UU): (isaset X) -> (forall x:X, iscontr (paths x x)).
Proof. intros X X0 x. unfold isaset in X0. unfold isofhlevel in X0.  change (forall (x x' : X) (x0 x'0 : paths x x'), iscontr (paths x0 x'0))  with (forall (x x':X),  isaprop (paths x x')) in X0.  apply (iscontraprop1 (X0 x x) (idpath x)). Defined.



(**  A monic subtype of a set is a set. *)

Theorem isasetsubset { X Y : UU } (f: X -> Y) (is1: isaset Y) (is2: isincl  f): isaset X.
Proof. intros. apply  (isofhlevelsninclb (S O)  f is2). apply is1. Defined. 



(** The morphism from hfiber of a map to a set is an inclusion. *)

Theorem isinclfromhfiber { X Y : UU } (f: X -> Y) (is : isaset Y) ( y: Y ) : @isincl (hfiber  f y) X ( @pr1 _ _  ).
Proof. intros. apply isofhlevelfhfiberpr1. assumption. Defined. 


(** Criterion for a function between sets being an inclusion.  *)


Theorem isinclbetweensets { X Y : UU } ( f : X -> Y ) ( isx : isaset X ) ( isy : isaset Y ) ( inj : forall x x' : X , ( paths ( f x ) ( f x' ) -> paths x x' ) ) : isincl f .
Proof. intros .  apply isinclweqonpaths .  intros x x' .  apply ( isweqimplimpl ( @maponpaths _ _ f x x' ) (  inj x x' ) ( isx x x' ) ( isy ( f x ) ( f x' ) ) ) . Defined .   

(** A map from [ unit ] to a set is an inclusion. *)

Theorem isinclfromunit { X : UU } ( f : unit -> X ) ( is : isaset X ) : isincl f .
Proof. intros . apply ( isinclbetweensets f ( isofhlevelcontr 2 ( iscontrunit ) )  is ) .  intros .  destruct x . destruct x' . apply idpath . Defined . 




(** ** Isolated points and types with decidable equality. *)


(** *** Basic results on complements to a point *)


Definition compl ( X : UU ) ( x : X ):= total2 (fun x':X => neg (paths x x' ) ) .
Definition complpair ( X : UU ) ( x : X ) := tpair (fun x':X => neg (paths x x' ) ) .
Definition pr1compl ( X : UU ) ( x : X ) := @pr1 _ (fun x':X => neg (paths x x' ) ) .


Lemma isinclpr1compl ( X : UU ) ( x : X ) : isincl ( pr1compl X x ) .
Proof. intros . apply ( isinclpr1 _ ( fun x' : X => isapropneg _ ) ) . Defined. 


Definition recompl ( X : UU ) (x:X): coprod (compl X x) unit -> X := fun u:_ =>
match u with
ii1 x0 => pr1  x0|
ii2 t => x
end.

Definition maponcomplincl { X Y : UU } (f:X -> Y)(is: isincl f)(x:X): compl X x -> compl Y (f x):= fun x0':_ =>
match x0' with
tpair x' neqx => tpair _ (f x') (negf  (invmaponpathsincl  _ is x x' ) neqx)
end.

Definition maponcomplweq { X Y : UU } (f : weq X Y ) (x:X):= maponcomplincl  f (isofhlevelfweq (S O) f ) x.


Theorem isweqmaponcompl { X Y : UU } ( f : weq X Y ) (x:X): isweq (maponcomplweq  f x).
Proof. intros.  set (is1:= isofhlevelfweq (S O)  f).   set (map1:= totalfun (fun x':X => neg (paths x x' )) (fun x':X => neg (paths (f x) (f x'))) (fun x':X => negf  (invmaponpathsincl  _ is1 x x' ))). set (map2:= fpmap  f (fun y:Y => neg (paths (f x) y ))). 
assert (is2: forall x':X, isweq  (negf  (invmaponpathsincl  _ is1 x x'))). intro. 
set (invimpll:= (negf  (@maponpaths _ _ f x x'))). apply (isweqimplimpl  (negf  (invmaponpathsincl  _ is1 x x')) (negf  (@maponpaths _ _ f x x')) (isapropneg _) (isapropneg _)). 
assert (is3: isweq map1).  unfold map1 . apply ( isweqfibtototal  _ _  (fun x':X => weqpair _  ( is2 x' )) ) .  
assert (is4: isweq map2). apply (isweqfpmap  f  (fun y:Y => neg (paths (f x) y )) ).
assert (h: forall x0':_, paths (map2 (map1 x0')) (maponcomplweq  f x x0')). intro.  simpl. destruct x0'. simpl. apply idpath.
apply (isweqhomot _ _ h (twooutof3c _ _ is3 is4)).
Defined.


Definition weqoncompl { X Y : UU } (w: weq X Y) ( x : X ) : weq (compl X x) (compl Y (pr1  w x)):= weqpair  _ (isweqmaponcompl w x).

Definition homotweqoncomplcomp { X Y Z : UU } ( f : weq X Y ) ( g : weq Y Z ) ( x : X ) : homot ( weqcomp ( weqoncompl f x ) ( weqoncompl g ( f x ) ) ) ( weqoncompl  ( weqcomp f g ) x ) .
Proof . intros . intro x' . destruct x' as [ x' nexx' ] . apply ( invmaponpathsincl _ ( isinclpr1compl Z _ ) _ _ ) . simpl .  apply idpath .    Defined . 





(** *** Basic results on types with an isolated point. *)




Definition isisolated (X:UU)(x:X):= forall x':X, coprod (paths x x' ) (paths x x' -> empty).

Definition isolated ( T : UU ) := total2 ( fun t : T => isisolated T t ) .
Definition isolatedpair ( T : UU ) := tpair ( fun t : T => isisolated T t ) . 
Definition pr1isolated ( T : UU )  := fun x : isolated T => pr1 x . 


Theorem isaproppathsfromisolated ( X : UU ) ( x : X ) ( is : isisolated X x ) : forall x' : X, isaprop ( paths x x' ) .
Proof. intros . apply iscontraprop1inv .  intro e .  destruct e . 
set (f:= fun e: paths x x => coconusfromtpair _ e). 
assert (is' : isweq f). apply (onefiber (fun x':X => paths x x' ) x (fun x':X => is x' )).
assert (is2: iscontr (coconusfromt _ x)). apply iscontrcoconusfromt. 
apply (iscontrweqb ( weqpair f is' ) ). assumption. Defined. 

Theorem isaproppathstoisolated  ( X : UU ) ( x : X ) ( is : isisolated X x ) : forall x' : X, isaprop ( paths x' x ) .
Proof . intros . apply ( isofhlevelweqf 1 ( weqpathsinv0 x x' ) ( isaproppathsfromisolated X x is x' ) ) . Defined . 


Lemma isisolatedweqf { X Y : UU } (  f : weq X Y ) (x:X) (is2: isisolated _ x) : isisolated _ (f x).
Proof.  intros. unfold isisolated. intro y.  set (g:=invmap  f ). set (x':= g y). destruct (is2 x') as [ x0 | y0 ].  apply (ii1  (pathsweq1'  f x y x0) ). 
assert (phi: paths y (f x)  -> empty). 
assert (psi: (paths (g y) x -> empty) -> (paths y (f x) -> empty)). intros X0 X1.  apply (X0  (pathsinv0 (pathsweq1  f x y (pathsinv0 X1)))). apply (psi ( ( negf ( @pathsinv0 _ _ _ ) ) y0) ) . apply (ii2  ( negf ( @pathsinv0 _ _ _ )  phi ) ). Defined.


Theorem isisolatedinclb { X Y : UU } ( f : X -> Y ) ( is : isincl f ) ( x : X ) ( is0 : isisolated _ ( f x ) ) : isisolated _ x .
Proof. intros .  unfold isisolated .  intro x' .  set ( a := is0 ( f x' ) ) .  destruct a as [ a1 | a2 ] . apply ( ii1 ( invmaponpathsincl f is _ _ a1 ) ) . apply ( ii2 ( ( negf ( @maponpaths _ _ f _ _ ) ) a2 ) ) .  Defined. 


Lemma disjointl1 (X:UU): isisolated (coprod X unit) (ii2  tt).
Proof. intros.  unfold isisolated. intros x' .  destruct x' as [ x | u ] . apply (ii2  (negpathsii2ii1 x tt )).  destruct u.  apply (ii1  (idpath _ )). Defined.


(** *** Weak equivalence [ weqrecompl ] from the coproduct of the complement to an isolated point with [ unit ] and the original type *)

Definition invrecompl (X:UU)(x:X)(is: isisolated X x): X -> coprod (compl X x) unit:=
fun x':X => match (is x') with
ii1 e => ii2  tt|
ii2 phi => ii1  (complpair _ _ x' phi)
end.



Theorem isweqrecompl (X:UU)(x:X)(is:isisolated X x): isweq (recompl _ x).
Proof. intros. set (f:= recompl _ x). set (g:= invrecompl X x is). unfold invrecompl in g. simpl in g. 

assert (efg: forall x':X, paths (f (g x')) x'). intro.   destruct (is x') as [ x0 | e ].   destruct x0. unfold f. unfold g. simpl. unfold recompl. simpl.  destruct (is x) as [ x0 | e ] .  simpl. apply idpath. destruct (e (idpath x)).  unfold f. unfold g. simpl. unfold recompl. simpl.  destruct  (is x') as [ x0 | e0 ].  destruct (e x0). simpl. apply idpath. 


assert (egf: forall u: coprod  (compl X x) unit, paths (g (f u)) u). unfold isisolated in is. intro. destruct (is (f u)) as [ p | e ] . destruct u as [ c | u].    simpl. destruct c as [ t x0 ]. simpl in p. destruct (x0 p). 

destruct u.   
assert (e1: paths  (g (f (ii2 tt))) (g x)). apply (maponpaths g  p). 
assert (e2: paths (g x) (ii2 tt)). unfold g.  destruct (is x) as [ i | e ].   apply idpath.  destruct (e (idpath x)). apply (pathscomp0   e1 e2). destruct u.  simpl. destruct c as [ t x0 ].  simpl. unfold isisolated in is.  unfold g.  destruct (is t) as [ p | e0 ] . destruct (x0 p). simpl in g. 
 unfold f. unfold recompl. simpl in e. 
assert (ee: paths e0 x0). apply (proofirrelevance _ (isapropneg (paths x t))). destruct ee.  apply idpath. 
unfold f. unfold g. simpl. destruct u. destruct (is x).  apply idpath. destruct (e (idpath x)).
apply (gradth  f g egf efg). Defined.

Definition weqrecompl ( X : UU ) ( x : X ) ( is : isisolated _ x ) : weq ( coprod ( compl X x ) unit ) X := weqpair _ ( isweqrecompl X x is ) .


(** *** Theorem saying that [ recompl ] commutes up to homotopy with [ maponcomplweq ] *)


Theorem homotrecomplnat { X Y : UU } ( w : weq X Y ) ( x : X ) : forall a : coprod ( compl X x ) unit , paths  ( recompl Y ( w x ) ( coprodf ( maponcomplweq w x ) ( fun x: unit => x ) a ) ) ( w ( recompl X x a ) )  .   
Proof . intros . destruct a as [ ane | t ] . destruct ane as [ a ne ] .  simpl . apply idpath . destruct t . simpl . apply idpath .  Defined . 



(** *** Recomplement on functions *)


Definition recomplf { X Y : UU } ( x : X ) ( y : Y ) ( isx : isisolated X x ) ( f : compl X x -> compl Y y )  := funcomp ( funcomp ( invmap ( weqrecompl X x isx ) ) ( coprodf f ( idfun unit ) ) )  ( recompl Y y ) .

Definition weqrecomplf { X Y : UU } ( x : X ) ( y : Y ) ( isx : isisolated X x ) ( isy : isisolated Y y ) ( w : weq ( compl X x ) ( compl Y y ) ) := weqcomp ( weqcomp ( invweq ( weqrecompl X x isx ) ) ( weqcoprodf w ( idweq unit ) ) ) ( weqrecompl Y y isy ) . 

Definition homotrecomplfhomot { X Y : UU } ( x : X ) ( y : Y ) ( isx : isisolated X x ) ( f f' : compl X x -> compl Y y ) ( h : homot f f' ) : homot ( recomplf x y isx f ) ( recomplf x y isx f') .
Proof . intros. intro a . unfold recomplf . apply ( maponpaths ( recompl Y y ) ( homotcoprodfhomot _ _ _ _ h ( fun t : unit => idpath t ) (invmap (weqrecompl X x isx) a) ) ) .  Defined .  

Lemma pathsrecomplfxtoy { X Y : UU } ( x : X ) ( y : Y ) ( isx : isisolated X x ) ( f : compl X x -> compl Y y ) : paths ( recomplf x y isx f x ) y .
Proof .  intros . unfold recomplf . unfold weqrecompl .  unfold invmap .   simpl . unfold invrecompl . unfold funcomp .  destruct ( isx x ) as [ i1 | i2 ] .  simpl . apply idpath . destruct ( i2 ( idpath _ ) ) .  Defined . 

Definition homotrecomplfcomp { X Y Z : UU } ( x : X ) ( y : Y ) ( z : Z ) ( isx : isisolated X x ) ( isy : isisolated Y y ) ( f :  compl X x -> compl Y y )  ( g :  compl Y y -> compl Z z ) : homot ( funcomp ( recomplf x y isx f ) ( recomplf y z isy g ) ) ( recomplf x z isx ( funcomp f g ) ) .
Proof . intros. intro x' . unfold recomplf . set ( e := homotinvweqweq ( weqrecompl Y y isy ) (coprodf f ( idfun unit) (invmap ( weqrecompl X x isx ) x')) ) . unfold funcomp .   simpl in e .  simpl . rewrite e . set ( e' := homotcoprodfcomp f ( idfun unit ) g ( idfun unit ) (invmap (weqrecompl X x isx) x') ) . unfold funcomp in e' .  rewrite e' .  apply idpath .  Defined . 


Definition homotrecomplfidfun { X : UU } ( x : X ) ( isx : isisolated X x ) : homot ( recomplf x x isx ( idfun ( compl X x ) ) ) ( idfun _ ) .
Proof . intros . intro x' . unfold recomplf . unfold weqrecompl . unfold invmap .   simpl .   unfold invrecompl . unfold funcomp. destruct ( isx x' ) as [ e | ne ] .  simpl . apply e .  simpl . apply idpath .  Defined . 



Lemma ishomotinclrecomplf { X Y : UU } ( x : X ) ( y : Y ) ( isx : isisolated X x ) ( f : compl X x -> compl Y y ) ( x'n : compl X x ) ( y'n : compl Y y ) ( e : paths ( recomplf x y isx f ( pr1 x'n ) ) ( pr1 y'n ) ) : paths ( f x'n ) y'n .
Proof . intros . destruct x'n as [ x' nexx' ] . destruct y'n as [ y' neyy' ] . simpl in e  . apply ( invmaponpathsincl _ ( isinclpr1compl _ _ ) ) .   simpl .  rewrite ( pathsinv0 e ) . unfold recomplf. unfold invmap . unfold coprodf .   simpl .  unfold funcomp .  unfold invrecompl . destruct ( isx x' ) as [ exx' | nexx'' ] .   destruct ( nexx' exx' ) .  simpl . assert ( ee : paths nexx' nexx'' ) .    apply ( proofirrelevance _ ( isapropneg _ ) ) .   rewrite ee . apply idpath .  Defined . 
 




(** *** Standard weak equivalence between [ compl T t1 ] and [ compl T t2 ] for isolated [ t1 t2 ] *) 

Definition funtranspos0 { T : UU } ( t1 t2 : T ) ( is2 : isisolated T t2 ) ( x :compl T t1 ) : compl T t2  :=  match ( is2 ( pr1 x ) ) with 
ii1 e => match ( is2 t1 ) with ii1 e' => fromempty ( pr2 x ( pathscomp0 ( pathsinv0 e' ) e ) ) | ii2 ne' => complpair T t2 t1 ne' end | 
ii2 ne => complpair T t2 ( pr1 x ) ne end .

Definition homottranspos0t2t1t1t2 { T : UU } ( t1 t2 : T ) ( is1 : isisolated T t1 ) ( is2 : isisolated T t2 ) : homot ( funcomp ( funtranspos0 t1 t2 is2 ) ( funtranspos0 t2 t1 is1 ) ) ( idfun _ ) .
Proof. intros. intro x . unfold funtranspos0 . unfold funcomp . destruct x as [ t net1 ] .  simpl .  destruct ( is2 t ) as [ et2 | net2 ] . destruct ( is2 t1 ) as [ et2t1 | net2t1 ] . destruct (net1 (pathscomp0 (pathsinv0 et2t1) et2)) .  simpl . destruct ( is1 t1 ) as [ e | ne ] .  destruct ( is1 t2 ) as [ et1t2 | net1t2 ] .  destruct (net2t1 (pathscomp0 (pathsinv0 et1t2) e)) . apply ( invmaponpathsincl _ ( isinclpr1compl _ _ ) _ _ ) . simpl . apply et2 . destruct ( ne ( idpath _ ) ) .  simpl . destruct ( is1 t ) as [ et1t | net1t ] .   destruct ( net1 et1t ) .  apply ( invmaponpathsincl _ ( isinclpr1compl _ _ ) _ _ ) . simpl .  apply idpath . Defined . 

Definition weqtranspos0 { T : UU } ( t1 t2 : T ) ( is1 : isisolated T t1 ) ( is2 : isisolated T t2 ) : weq ( compl T t1 ) ( compl T t2 ) . 
Proof . intros . set ( f := funtranspos0 t1 t2 is2 ) . set ( g := funtranspos0 t2 t1 is1 ) . split with f .
assert ( egf : forall x : _ , paths ( g ( f x ) ) x ) . intro x . apply ( homottranspos0t2t1t1t2 t1 t2 is1 is2 ) . 
assert ( efg : forall x : _ , paths ( f ( g x ) ) x ) . intro x . apply ( homottranspos0t2t1t1t2 t2 t1 is2 is1 ) . 
apply ( gradth _ _ egf efg ) . Defined .


(** *** Transposition of two isolated points *)


Definition funtranspos { T : UU } ( t1 t2 : isolated T )  : T -> T := recomplf ( pr1 t1 ) ( pr1 t2 ) ( pr2 t1 ) ( funtranspos0 ( pr1 t1 ) ( pr1 t2 ) ( pr2 t2 ) ) .

Definition homottranspost2t1t1t2  { T : UU } ( t1 t2 : T ) ( is1 : isisolated T t1 ) ( is2 : isisolated T t2 ) : homot ( funcomp ( funtranspos ( tpair _ t1 is1 ) ( tpair _ t2 is2 ) ) ( funtranspos ( tpair _ t2 is2 ) ( tpair _ t1 is1 ) ) ) ( idfun _ ) .
Proof. intros. intro t . unfold funtranspos .  rewrite ( homotrecomplfcomp t1 t2 t1 is1 is2 _ _  t ) . set ( e:= homotrecomplfhomot t1 t1 is1 _ ( idfun _ ) ( homottranspos0t2t1t1t2 t1 t2 is1 is2 ) t ) . set ( e' := homotrecomplfidfun t1 is1 t ) .   apply ( pathscomp0 e e' ) .  Defined . 


Theorem weqtranspos { T : UU } ( t1 t2 : T ) ( is1 : isisolated T t1 ) ( is2 : isisolated T t2 ) : weq T T .
Proof . intros . set ( f := funtranspos ( tpair _ t1 is1) ( tpair _ t2 is2 ) ) . set ( g := funtranspos ( tpair _ t2 is2 ) ( tpair _ t1 is1 ) ) . split with f .
assert ( egf : forall t : T , paths ( g ( f t ) ) t ) . intro . apply homottranspost2t1t1t2 .
assert ( efg : forall t : T , paths ( f ( g t ) ) t ) . intro .  apply homottranspost2t1t1t2 .
apply ( gradth _ _ egf efg ) . Defined .  


Lemma pathsfuntransposoft1 { T : UU } ( t1 t2 : T ) ( is1 : isisolated T t1  ) ( is2 : isisolated T t2 ) : paths ( funtranspos ( tpair _ t1 is1 ) ( tpair _ t2 is2 ) t1 ) t2 .
Proof . intros . unfold funtranspos . rewrite ( pathsrecomplfxtoy t1 t2 is1 _ ) . apply idpath .  Defined .

Lemma pathsfuntransposoft2 { T : UU } ( t1 t2 : T ) ( is1 : isisolated T t1 ) ( is2 : isisolated T t2 ) : paths ( funtranspos ( tpair _ t1 is1 ) ( tpair _ t2 is2 ) t2 ) t1 .
Proof . intros .  unfold funtranspos . simpl . unfold funtranspos0 .   unfold recomplf .  unfold funcomp .  unfold coprodf . unfold invmap .  unfold weqrecompl .  unfold recompl .   simpl .  unfold invrecompl . destruct ( is1 t2 ) as [ et1t2 | net1t2 ] . apply ( pathsinv0 et1t2 ) .  simpl . destruct ( is2 t2 ) as [ et2t2 | net2t2 ] .  destruct ( is2 t1 ) as [ et2t1 | net2t1 ] . destruct (net1t2 (pathscomp0 (pathsinv0 et2t1) et2t2) ).  simpl . apply idpath . destruct ( net2t2 ( idpath _ ) ) .  Defined .  

Lemma pathsfuntransposofnet1t2 { T : UU } ( t1 t2 : T ) ( is1 : isisolated T t1 ) ( is2 : isisolated T t2 ) ( t : T ) ( net1t : neg ( paths t1 t ) ) ( net2t : neg ( paths t2 t ) ) : paths ( funtranspos ( tpair _ t1 is1 ) ( tpair _ t2 is2 ) t ) t .
Proof . intros .  unfold funtranspos . simpl . unfold funtranspos0 .   unfold recomplf .  unfold funcomp .  unfold coprodf . unfold invmap .  unfold weqrecompl .  unfold recompl .   simpl .  unfold invrecompl . destruct ( is1 t ) as [ et1t | net1t' ] . destruct ( net1t et1t ) .  simpl .  destruct ( is2 t ) as [ et2t | net2t' ] . destruct ( net2t et2t ) . simpl . apply idpath . Defined . 

Lemma homotfuntranspos2 { T : UU } ( t1 t2 : T ) ( is1 : isisolated T t1 ) ( is2 : isisolated T t2 ) : homot ( funcomp ( funtranspos ( tpair _ t1 is1 ) ( tpair _ t2 is2 ) ) ( funtranspos ( tpair _ t1 is1 ) ( tpair _ t2 is2 ) ) ) ( idfun _ ) .
Proof . intros . intro t .   unfold funcomp . unfold idfun .   
destruct ( is1 t ) as [ et1t | net1t ] .  rewrite ( pathsinv0 et1t ) .  rewrite ( pathsfuntransposoft1 _ _ ) .   rewrite ( pathsfuntransposoft2 _ _ ) .  apply idpath . 
destruct ( is2 t ) as [ et2t | net2t ] .  rewrite ( pathsinv0 et2t ) .  rewrite ( pathsfuntransposoft2 _ _ ) .   rewrite ( pathsfuntransposoft1 _ _ ) .  apply idpath .
rewrite ( pathsfuntransposofnet1t2 _ _ _ _ _ net1t net2t ) . rewrite ( pathsfuntransposofnet1t2 _ _ _ _ _ net1t net2t ) . apply idpath . Defined . 





(** *** Types with decidable equality *)


Definition isdeceq (X:UU) : UU :=  forall (x x':X), coprod (paths x x' ) (paths x x' -> empty).

Lemma isdeceqweqf { X Y : UU } ( w : weq X Y ) ( is : isdeceq X ) : isdeceq Y .
Proof. intros . intros y y' . set ( w' := weqonpaths ( invweq w ) y y' ) .  set ( int := is ( ( invweq w ) y ) ( ( invweq w ) y' ) ) . destruct int as [ i | ni ] .    apply ( ii1 ( ( invweq w' ) i ) ) . apply ( ii2 ( ( negf w' ) ni ) ) .  Defined . 

Lemma isdeceqweqb { X Y : UU } ( w : weq X Y ) ( is : isdeceq Y ) : isdeceq X .
Proof . intros . apply ( isdeceqweqf ( invweq w ) is ) . Defined . 

Theorem isdeceqinclb { X Y : UU } ( f : X -> Y ) ( is : isdeceq Y ) ( is' : isincl f ) : isdeceq X .
Proof.  intros .  intros x x' . set ( w := weqonpathsincl f is' x x' ) .  set ( int := is ( f x ) ( f x' ) ) . destruct int as [ i | ni ] . apply ( ii1 ( ( invweq w ) i ) ) .   apply ( ii2 ( ( negf w ) ni ) ) .  Defined . 
 
Lemma isdeceqifisaprop ( X : UU ) : isaprop X -> isdeceq X .
Proof. intros X is . intros x x' . apply ( ii1 ( proofirrelevance _ is x x' ) ) .  Defined .

Theorem isasetifdeceq (X:UU): isdeceq X -> isaset X.
Proof. intro X . intro is. intros x x' . apply ( isaproppathsfromisolated X x ( is x ) ) .   Defined . 



Definition booleq { X : UU } ( is : isdeceq X ) ( x x' : X ) : bool .
Proof . intros . destruct ( is x x' ) . apply true . apply false . Defined .    


Lemma eqfromdnegeq (X:UU)(is: isdeceq X)(x x':X): dneg ( paths x x' ) -> paths x x'.
Proof. intros X is x x' X0. destruct ( is x x' ) . assumption .   destruct ( X0 e ) . Defined .




(** *** [ bool ] is a [ deceq ] type and a set *)


Theorem isdeceqbool: isdeceq bool.
Proof. unfold isdeceq. intros x' x . destruct x. destruct x'. apply (ii1  (idpath true)). apply (ii2  nopathsfalsetotrue). destruct x'.  apply (ii2  nopathstruetofalse). apply (ii1  (idpath false)). Defined. 

Theorem isasetbool: isaset bool.
Proof. apply (isasetifdeceq _ isdeceqbool). Defined. 




(** *** Splitting of [ X ] into a coproduct defined by a function [ X -> bool ] *)


Definition subsetsplit { X : UU } ( f : X -> bool ) ( x : X ) : coprod ( hfiber f true ) ( hfiber f false ) .
Proof . intros . destruct ( boolchoice ( f x ) ) as [ a | b ] .  apply ( ii1 ( hfiberpair f x a ) ) . apply ( ii2 ( hfiberpair f x b ) ) .  Defined . 

Definition subsetsplitinv { X : UU } ( f : X -> bool ) ( ab : coprod (hfiber f true) (hfiber f false) )  : X :=  match ab with ii1 xt => pr1  xt | ii2 xf => pr1  xf end.


Theorem weqsubsetsplit { X : UU } ( f : X -> bool ) : weq X (coprod ( hfiber f true) ( hfiber f false) ) .
Proof . intros . set ( ff := subsetsplit f ) . set ( gg := subsetsplitinv f ) . split with ff .
assert ( egf : forall a : _ , paths ( gg ( ff a ) ) a ) . intros .   unfold ff .  unfold subsetsplit . destruct ( boolchoice ( f a ) ) as [ et | ef ] . simpl .  apply idpath .  simpl .  apply idpath . 
assert ( efg : forall a : _ , paths ( ff ( gg a ) ) a ) . intros . destruct a as [ et | ef ] .  destruct et as [ x et' ] .  simpl . unfold ff . unfold subsetsplit . destruct ( boolchoice ( f x ) ) as [ e1 | e2 ] .   apply ( maponpaths ( @ii1 _ _  ) ) .  apply ( maponpaths ( hfiberpair f x ) ) .  apply uip . apply isasetbool . destruct ( nopathstruetofalse ( pathscomp0 ( pathsinv0 et' ) e2 ) ) .    destruct ef as [ x et' ] .  simpl . unfold ff . unfold subsetsplit . destruct ( boolchoice ( f x ) ) as [ e1 | e2 ] . destruct ( nopathsfalsetotrue ( pathscomp0 ( pathsinv0 et' ) e1 ) ) .     apply ( maponpaths ( @ii2 _ _  ) ) .  apply ( maponpaths ( hfiberpair f x ) ) .  apply uip . apply isasetbool . 
apply ( gradth _ _ egf efg ) . Defined . 




(** ** Semi-boolean hfiber of functions over isolated points *)


Definition eqbx ( X : UU ) ( x : X ) ( is : isisolated X x ) : X -> bool .
Proof. intros X x is x' . destruct ( is x' ) . apply true . apply false . Defined .

Lemma iscontrhfibereqbx ( X : UU ) ( x : X ) ( is : isisolated X x ) : iscontr ( hfiber ( eqbx X x is ) true ) .
Proof. intros . assert ( b : paths  ( eqbx X x is x ) true ) . unfold eqbx .   destruct ( is x ) .  apply idpath .  destruct ( e ( idpath _ ) ) .  set ( i := hfiberpair ( eqbx X x is ) x b ) .  split with i . 
unfold eqbx . destruct ( boolchoice ( eqbx X x is x ) ) as [ b' | nb' ] .  intro t .  destruct t as [ x' e ] .  assert ( e' : paths x' x ) .  destruct ( is x' ) as [ ee | nee ] .  apply ( pathsinv0 ee ) . destruct ( nopathsfalsetotrue e )  . apply ( invmaponpathsincl _ ( isinclfromhfiber ( eqbx X x is ) isasetbool true ) ( hfiberpair _ x' e ) i e' ) .  destruct ( nopathstruetofalse ( pathscomp0 ( pathsinv0 b ) nb' ) ) . Defined . 

Definition bhfiber { X Y : UU } ( f : X -> Y ) ( y : Y ) ( is : isisolated Y y ) := hfiber ( fun x : X => eqbx Y y is ( f x ) ) true .

Lemma weqhfibertobhfiber { X Y : UU } ( f : X -> Y ) ( y : Y ) ( is : isisolated Y y ) : weq ( hfiber f y ) ( bhfiber f y is ) .
Proof . intros . set ( g := eqbx Y y is ) . set ( ye := pr1 ( iscontrhfibereqbx Y y is ) ) . split with ( hfibersftogf f g true ye ) . apply ( isofhlevelfffromZ 0 _ _ ye ( fibseqhf f g true ye ) ) .  apply ( isapropifcontr ) . apply ( iscontrhfibereqbx _ y is ) . Defined .  















(** *** h-fibers of [ ii1 ] and [ ii2 ] *)


Theorem isinclii1 (X Y:UU): isincl  (@ii1 X Y).
Proof. intros. set (f:= @ii1 X Y). set (g:= coprodtoboolsum X Y). set (gf:= fun x:X => (g (f x))). set (gf':= fun x:X => tpair (boolsumfun X Y) true x). 
assert (h: forall x:X , paths (gf' x) (gf x)). intro. apply idpath. 
assert (is1: isofhlevelf (S O)  gf'). apply (isofhlevelfsnfib O (boolsumfun X Y) true (isasetbool true true)).
assert (is2: isofhlevelf (S O)  gf). apply (isofhlevelfhomot (S O)  gf' gf h is1).  
apply (isofhlevelff (S O) _ _ is2  (isofhlevelfweq (S (S O) )  (weqcoprodtoboolsum X Y))). Defined. 


Corollary iscontrhfiberii1x ( X Y : UU ) ( x : X ) : iscontr ( hfiber ( @ii1 X Y ) ( ii1 x ) ) .
Proof. intros . set ( xe1 :=  hfiberpair ( @ii1 _ _ ) x ( idpath ( @ii1 X Y x ) ) ) . apply ( iscontraprop1 ( isinclii1 X Y ( ii1 x ) ) xe1 ) .  Defined .

Corollary neghfiberii1y ( X Y : UU ) ( y : Y ) : neg ( hfiber ( @ii1 X Y ) ( ii2 y ) ) .
Proof. intros . intro xe . destruct xe as [ x e ] . apply ( negpathsii1ii2 _ _ e ) .  Defined. 





Theorem isinclii2 (X Y:UU): isincl  (@ii2 X Y).
Proof. intros. set (f:= @ii2 X Y). set (g:= coprodtoboolsum X Y). set (gf:= fun y:Y => (g (f y))). set (gf':= fun y:Y => tpair (boolsumfun X Y) false y). 
assert (h: forall y:Y , paths (gf' y) (gf y)). intro. apply idpath. 
assert (is1: isofhlevelf (S O)  gf'). apply (isofhlevelfsnfib O (boolsumfun X Y) false (isasetbool false false)).
assert (is2: isofhlevelf (S O)  gf). apply (isofhlevelfhomot (S O)  gf' gf h is1).  
apply (isofhlevelff (S O)  _ _ is2 (isofhlevelfweq (S (S O)) ( weqcoprodtoboolsum X Y))). Defined. 


Corollary iscontrhfiberii2y ( X Y : UU ) ( y : Y ) : iscontr ( hfiber ( @ii2 X Y ) ( ii2 y ) ) .
Proof. intros . set ( xe1 :=  hfiberpair ( @ii2 _ _ ) y ( idpath ( @ii2 X Y y ) ) ) . apply ( iscontraprop1 ( isinclii2 X Y ( ii2 y ) ) xe1 ) .  Defined .

Corollary neghfiberii2x ( X Y : UU ) ( x : X ) : neg ( hfiber ( @ii2 X Y ) ( ii1 x ) ) .
Proof. intros . intro ye . destruct ye as [ y e ] . apply ( negpathsii2ii1 _ _ e ) .  Defined. 




Lemma negintersectii1ii2 { X Y : UU } (z: coprod X Y): hfiber  (@ii1 X Y) z -> hfiber  (@ii2 _ _) z -> empty.
Proof. intros X Y z X0 X1. destruct X0 as [ t x ]. destruct X1 as [ t0 x0 ].  
set (e:= pathscomp0   x (pathsinv0 x0)). apply (negpathsii1ii2 _ _  e). Defined. 


(** *** [ ii1 ] and [ ii2 ] map isolated points to isoloated points *)

Lemma isolatedtoisolatedii1 (X Y:UU)(x:X)(is:isisolated _ x): isisolated ( coprod X Y ) (ii1 x).
Proof. intros. unfold isisolated .   intro x' .  destruct x' as [ x0 | y ] . destruct (is x0) as [ p | e ] .  apply (ii1  (maponpaths (@ii1 X Y)  p)). apply (ii2  (negf  (invmaponpathsincl  (@ii1 X Y) (isinclii1 X Y) _ _ ) e)). apply (ii2  (negpathsii1ii2  x y)). Defined. 


Lemma isolatedtoisolatedii2 (X Y:UU)(y:Y)(is:isisolated _ y): isisolated ( coprod X Y ) (ii2 y).
Proof. intros.  intro x' .  destruct x' as [ x | y0 ] . apply (ii2  (negpathsii2ii1  x y)). destruct (is y0) as [ p | e ] .  apply (ii1  (maponpaths (@ii2 X Y)  p)). apply (ii2  (negf  (invmaponpathsincl  (@ii2 X Y) (isinclii2 X Y) _ _ ) e)).  Defined. 























(** *** h-fibers of [ coprodf ] of two functions *)


Theorem weqhfibercoprodf1 { X Y X' Y' : UU } (f: X -> X')(g:Y -> Y')(x':X'): weq (hfiber  f x') (hfiber  (coprodf   f g) (ii1  x')).
Proof. intros.  set ( ix := @ii1 X Y ) . set ( ix' := @ii1 X' Y' ) . set ( fpg := coprodf f g ) . set ( fpgix := fun x : X => ( fpg ( ix x ) ) ) .

assert ( w1 : weq ( hfiber f x' ) ( hfiber fpgix ( ix' x' ) ) ) . apply ( samehfibers f ix' ( isinclii1 _ _ ) x' ) .
assert ( w2 : weq ( hfiber fpgix ( ix' x' ) ) ( hfiber fpg ( ix' x' ) ) ) . split with (hfibersgftog  ix fpg ( ix' x' ) ) . unfold isweq. intro y .  

set (u:= invezmaphf ix fpg ( ix' x' ) y).
assert (is: isweq u). apply isweqinvezmaphf. 

apply  (iscontrweqb  ( weqpair u is ) ) . destruct y as [ xy e ] .  destruct xy as [ x0 | y0 ] . simpl .  apply iscontrhfiberofincl . apply ( isinclii1 X Y ) .  apply ( fromempty ( ( negpathsii2ii1 x' ( g y0 ) ) e ) ) .

apply ( weqcomp w1 w2 ) .
Defined.


Theorem weqhfibercoprodf2 { X Y X' Y' : UU } (f: X -> X')(g:Y -> Y')(y':Y'): weq (hfiber  g y') (hfiber  (coprodf   f g) (ii2  y')).
Proof. intros.  set ( iy := @ii2 X Y ) . set ( iy' := @ii2 X' Y' ) . set ( fpg := coprodf f g ) . set ( fpgiy := fun y : Y => ( fpg ( iy y ) ) ) .

assert ( w1 : weq ( hfiber g y' ) ( hfiber fpgiy ( iy' y' ) ) ) . apply ( samehfibers g iy' ( isinclii2 _ _ ) y' ) .
assert ( w2 : weq ( hfiber fpgiy ( iy' y' ) ) ( hfiber fpg ( iy' y' ) ) ) . split with (hfibersgftog  iy fpg ( iy' y' ) ) . unfold isweq. intro y .  

set (u:= invezmaphf iy fpg ( iy' y' ) y).
assert (is: isweq u). apply isweqinvezmaphf. 

apply  (iscontrweqb  ( weqpair u is ) ) . destruct y as [ xy e ] .  destruct xy as [ x0 | y0 ] . simpl .   apply ( fromempty ( ( negpathsii1ii2 ( f x0 ) y' ) e ) ) .  simpl. apply iscontrhfiberofincl . apply ( isinclii2 X Y ) . 

apply ( weqcomp w1 w2 ) .
Defined.

 



(** *** Theorem saying that coproduct of two functions of h-level n is of h-level n *)



Theorem isofhlevelfcoprodf (n:nat) { X Y Z T : UU } (f : X -> Z ) ( g : Y -> T )( is1 : isofhlevelf n  f ) ( is2 : isofhlevelf n  g ) : isofhlevelf n (coprodf f g).
Proof. intros. unfold isofhlevelf .  intro y .  destruct y as [ z | t ] .  apply (isofhlevelweqf n (weqhfibercoprodf1  f g z) ). apply ( is1 z ) . apply (isofhlevelweqf n (weqhfibercoprodf2  f g t )). apply ( is2 t ) . Defined. 





(** *** Theorems about h-levels of coproducts and their component types *)


Theorem isofhlevelsnsummand1 ( n : nat ) ( X Y : UU ) : isofhlevel ( S n ) ( coprod X Y ) -> isofhlevel ( S n ) X .
Proof. intros n X Y is . apply ( isofhlevelXfromfY ( S n ) ( @ii1 X Y ) ( isofhlevelfsnincl n _ ( isinclii1 _ _ ) ) is ) .  Defined.


Theorem isofhlevelsnsummand2 ( n : nat ) ( X Y : UU ) : isofhlevel ( S n ) ( coprod X Y ) -> isofhlevel ( S n ) Y .
Proof. intros n X Y is . apply ( isofhlevelXfromfY ( S n ) ( @ii2 X Y ) ( isofhlevelfsnincl n _ ( isinclii2 _ _ ) ) is ) .  Defined.


Theorem isofhlevelssncoprod ( n : nat ) ( X Y : UU ) ( isx : isofhlevel ( S ( S n ) ) X ) ( isy : isofhlevel ( S ( S n ) ) Y ) : isofhlevel ( S ( S n ) ) ( coprod X Y ) .
Proof. intros . apply isofhlevelfromfun .  set ( f := coprodf ( fun x : X => tt ) ( fun y : Y => tt ) ) . assert ( is1 : isofhlevelf ( S ( S n ) ) f ) . apply ( isofhlevelfcoprodf ( S ( S n ) ) _ _ ( isofhleveltofun _ X isx ) ( isofhleveltofun _ Y isy ) ) .  assert ( is2 : isofhlevel ( S ( S n ) ) ( coprod unit unit ) ) .  apply ( isofhlevelweqb ( S ( S n ) ) boolascoprod ( isofhlevelssnset n _ ( isasetbool ) ) ) . apply ( isofhlevelfgf ( S ( S n ) ) _ _ is1 ( isofhleveltofun _ _ is2 ) ) .  Defined . 


Lemma isasetcoprod ( X Y : UU ) ( isx : isaset X ) ( isy : isaset Y ) : isaset ( coprod X Y ) .
Proof. intros . apply ( isofhlevelssncoprod 0 _ _ isx isy ) . Defined . 



(** *** h-fibers of the sum of two functions [ sumofmaps f g ] *)


Lemma coprodofhfiberstohfiber { X Y Z : UU } ( f : X -> Z ) ( g : Y -> Z ) ( z : Z ) : coprod ( hfiber f z ) ( hfiber g z ) -> hfiber ( sumofmaps f g ) z .
Proof. intros X Y Z f g z hfg .  destruct hfg as [ hf | hg ] .  destruct hf as [ x fe ] . split with ( ii1 x ) . simpl .  assumption .  destruct hg as [ y ge ] .  split with ( ii2 y ) . simpl .  assumption .  
Defined.

Lemma hfibertocoprodofhfibers { X Y Z : UU } ( f : X -> Z ) ( g : Y -> Z ) ( z : Z ) :  hfiber ( sumofmaps f g ) z ->  coprod ( hfiber f z ) ( hfiber g z ) .
Proof. intros X Y Z f g z hsfg . destruct hsfg as [ xy e ] .  destruct xy as [ x | y ] .  simpl in e .  apply ( ii1 ( hfiberpair _ x e ) ) .  simpl in e .  apply ( ii2 ( hfiberpair _ y e ) ) .  Defined .

Theorem weqhfibersofsumofmaps { X Y Z : UU } ( f : X -> Z ) ( g : Y -> Z ) ( z : Z ) : weq ( coprod ( hfiber f z ) ( hfiber g z ) ) ( hfiber ( sumofmaps f g ) z ) .
Proof. intros . set ( ff := coprodofhfiberstohfiber f g z ) . set ( gg := hfibertocoprodofhfibers f g z ) . split with ff .  
assert ( effgg : forall hsfg : _ , paths ( ff ( gg hsfg ) ) hsfg ) . intro .  destruct hsfg as [ xy e ] . destruct xy as [ x | y ] . simpl .  apply idpath .  simpl . apply idpath . 
assert ( eggff : forall hfg : _ , paths ( gg ( ff hfg ) ) hfg ) . intro . destruct hfg as [ hf | hg ] . destruct hf as [ x fe ] . simpl .  apply idpath .  destruct hg as [ y ge ] . simpl . apply idpath .
apply ( gradth _ _ eggff effgg ) . Defined .  




(** *** Theorem saying that the sum of two functions of h-level ( S ( S n ) ) is of hlevel ( S ( S n ) ) *)


Theorem isofhlevelfssnsumofmaps ( n : nat ) { X Y Z : UU } ( f : X -> Z ) ( g : Y -> Z ) ( isf : isofhlevelf ( S ( S n ) ) f ) ( isg : isofhlevelf ( S ( S n ) ) g ) : isofhlevelf ( S ( S n ) ) ( sumofmaps f g ) .
Proof . intros . intro z .  set ( w := weqhfibersofsumofmaps f g z ) .  set ( is := isofhlevelssncoprod n _ _ ( isf z ) ( isg z ) ) .  apply ( isofhlevelweqf _ w is ) .  Defined . 



(** *** Theorem saying that the sum of two functions of h-level n with non-intersecting images is of h-level n *)


Lemma noil1 { X Y Z : UU } ( f : X -> Z ) ( g : Y -> Z ) ( noi : forall ( x : X ) ( y : Y ) , neg ( paths ( f x ) ( g y ) ) ) ( z : Z ) : hfiber f z -> hfiber g z -> empty .
Proof. intros X Y Z f g noi z hfz hgz . destruct hfz as [ x fe ] . destruct hgz as [ y ge ] . apply ( noi x y ( pathscomp0 fe ( pathsinv0 ge ) ) ) .   Defined . 


Lemma weqhfibernoi1  { X Y Z : UU } ( f : X -> Z ) ( g : Y -> Z ) ( noi : forall ( x : X ) ( y : Y ) , neg ( paths ( f x ) ( g y ) ) ) ( z : Z ) ( xe : hfiber f z ) : weq ( hfiber ( sumofmaps f g ) z ) ( hfiber f z ) .
Proof. intros . set ( w1 := invweq ( weqhfibersofsumofmaps f g z ) ) .  assert ( a : neg ( hfiber g z ) ) . intro ye . apply ( noil1 f g noi z xe ye ) .    set ( w2 := invweq ( weqii1withneg ( hfiber f z ) a ) ) .  apply ( weqcomp w1 w2 ) . Defined .  

Lemma weqhfibernoi2  { X Y Z : UU } ( f : X -> Z ) ( g : Y -> Z ) ( noi : forall ( x : X ) ( y : Y ) , neg ( paths ( f x ) ( g y ) ) ) ( z : Z ) ( ye : hfiber g z ) : weq ( hfiber ( sumofmaps f g ) z ) ( hfiber g z ) .
Proof. intros . set ( w1 := invweq ( weqhfibersofsumofmaps f g z ) ) .  assert ( a : neg ( hfiber f z ) ) . intro xe . apply ( noil1 f g noi z xe ye ) .    set ( w2 := invweq ( weqii2withneg ( hfiber g z ) a ) ) .  apply ( weqcomp w1 w2 ) . Defined .  



Theorem isofhlevelfsumofmapsnoi ( n : nat ) { X Y Z : UU } ( f : X -> Z ) ( g : Y -> Z ) ( isf : isofhlevelf n f ) ( isg : isofhlevelf n g ) ( noi : forall ( x : X ) ( y : Y ) , neg ( paths ( f x ) ( g y ) ) ) : isofhlevelf n ( sumofmaps f g ) .
Proof. intros .  intro z .  destruct n as [ | n ] .   set ( zinx := invweq ( weqpair _ isf ) z ) . set ( ziny := invweq ( weqpair _ isg ) z ) . assert ( ex : paths ( f zinx ) z ) .  apply ( homotweqinvweq ( weqpair _ isf ) z ) . assert ( ey : paths ( g ziny ) z ) . apply ( homotweqinvweq ( weqpair _ isg ) z ) .   destruct ( ( noi zinx ziny ) ( pathscomp0 ex ( pathsinv0 ey ) ) ) . 
apply isofhlevelsn . intro hfgz .  destruct ( ( invweq ( weqhfibersofsumofmaps f g z ) hfgz ) ) as [ xe | ye ] .   apply ( isofhlevelweqb _ ( weqhfibernoi1 f g noi z xe ) ( isf z ) ) .   apply ( isofhlevelweqb _ ( weqhfibernoi2 f g noi z ye ) ( isg z ) ) . Defined . 







(** *** Coproducts and complements *)


Definition tocompltoii1x (X Y:UU)(x:X): coprod (compl X x) Y -> compl (coprod X Y) (ii1  x).
Proof. intros X Y x X0. destruct X0 as [ c | y ] .  split with (ii1  (pr1  c)). 
assert (e: neg(paths x (pr1 c) )). apply (pr2  c). apply (negf  (invmaponpathsincl  ( @ii1 _ _ ) (isinclii1 X Y) _ _) e). 
split with (ii2  y). apply (negf  (pathsinv0 ) (negpathsii2ii1 x y)). Defined.


Definition fromcompltoii1x (X Y:UU)(x:X): compl (coprod X Y) (ii1  x) ->  coprod (compl X x) Y.
Proof. intros X Y x X0. destruct X0 as [ t x0 ].  destruct t as [ x1 | y ]. 
assert (ne: neg (paths x x1 )). apply (negf  (maponpaths ( @ii1 _ _ ) ) x0). apply (ii1  (complpair _ _ x1 ne )). apply (ii2  y). Defined. 


Theorem isweqtocompltoii1x (X Y:UU)(x:X): isweq (tocompltoii1x X Y x).
Proof. intros. set (f:= tocompltoii1x X Y x). set (g:= fromcompltoii1x X Y x).
assert (egf:forall nexy:_ , paths (g (f nexy)) nexy). intro. destruct nexy as [ c | y ]. destruct c as [ t x0 ]. simpl. 
assert (e: paths (negf (maponpaths (@ii1 X Y)) (negf (invmaponpathsincl  (@ii1 X Y) (isinclii1 X Y) x t) x0)) x0). apply (isapropneg (paths x t) ). 
apply (maponpaths (fun ee: neg (paths x t ) => ii1  (complpair X x t ee))  e). apply idpath.

assert (efg: forall neii1x:_, paths (f (g neii1x)) neii1x). intro.  destruct neii1x as [ t x0 ]. destruct t as [ x1 | y ].  simpl. 
assert (e: paths  (negf (invmaponpathsincl (@ii1 X Y) (isinclii1 X Y) x x1 ) (negf (maponpaths (@ii1 X Y) ) x0)) x0). apply (isapropneg (paths _ _ )  ).
apply (maponpaths (fun ee: (neg (paths (ii1 x) (ii1 x1))) => (complpair _ _ (ii1 x1) ee))  e). simpl. 
assert (e: paths (negf pathsinv0 (negpathsii2ii1 x y)) x0). apply (isapropneg (paths _ _ ) ).
apply (maponpaths   (fun ee: (neg (paths (ii1 x) (ii2 y) )) => (complpair _ _ (ii2 y) ee))  e). 
apply (gradth  f g egf efg). Defined.


Definition tocompltoii2y (X Y:UU)(y:Y): coprod X (compl Y y) -> compl (coprod X Y) (ii2  y).
Proof. intros X Y y X0. destruct X0 as [ x | c ]. split with (ii1  x). apply (negpathsii2ii1 x y ). 
split with (ii2  (pr1  c)). assert (e: neg(paths y (pr1  c) )). apply (pr2  c). apply (negf  (invmaponpathsincl  ( @ii2 _ _ ) (isinclii2 X Y) _ _ ) e). 
Defined.



Definition fromcompltoii2y (X Y:UU)(y:Y): compl (coprod X Y) (ii2  y) ->  coprod X (compl Y y).
Proof. intros X Y y X0. destruct X0 as [ t x ].  destruct t as [ x0 | y0 ]. apply (ii1  x0). 
assert (ne: neg (paths y y0 )). apply (negf  (maponpaths ( @ii2 _ _ ) ) x). apply (ii2  (complpair _ _ y0 ne)). Defined. 


Theorem isweqtocompltoii2y (X Y:UU)(y:Y): isweq (tocompltoii2y X Y y).
Proof. intros. set (f:= tocompltoii2y X Y y). set (g:= fromcompltoii2y X Y y).
assert (egf:forall nexy:_ , paths (g (f nexy)) nexy). intro. destruct nexy as [ x | c ]. 
apply idpath. destruct c as [ t x ]. simpl. 
assert (e: paths (negf (maponpaths (@ii2 X Y) ) (negf (invmaponpathsincl (@ii2 X Y) (isinclii2 X Y) y t) x)) x). apply (isapropneg (paths y t ) ). 
apply (maponpaths (fun ee: neg ( paths y t ) => ii2  (complpair _ y t ee))  e). 

assert (efg: forall neii2x:_, paths (f (g neii2x)) neii2x). intro.  destruct neii2x as [ t x ]. destruct t as [ x0 | y0 ].  simpl. 
assert (e: paths (negpathsii2ii1 x0 y) x). apply (isapropneg (paths _ _ ) ).
apply (maponpaths   (fun ee: (neg (paths (ii2 y) (ii1 x0)  )) => (complpair _ _ (ii1 x0) ee))  e). simpl.
assert (e: paths  (negf (invmaponpathsincl _ (isinclii2 X Y) y y0 ) (negf (maponpaths (@ii2 X Y) ) x)) x). apply (isapropneg (paths _ _ )  ).
apply (maponpaths (fun ee: (neg (paths (ii2 y) (ii2 y0)  )) => (complpair _ _ (ii2 y0) ee))  e). 
apply (gradth f g egf efg). Defined.







Definition tocompltodisjoint (X:UU): X -> compl (coprod X unit) (ii2  tt) := fun x:_ => complpair _ _ (ii1  x) (negpathsii2ii1 x tt).

Definition fromcompltodisjoint (X:UU): compl (coprod X unit) (ii2  tt) -> X.
Proof. intros X X0. destruct X0 as [ t x ].  destruct t as [ x0 | u ] . assumption.  destruct u. apply (fromempty (x (idpath (ii2 tt)))). Defined.


Lemma isweqtocompltodisjoint (X:UU): isweq (tocompltodisjoint X).
Proof. intros. set (ff:= tocompltodisjoint X). set (gg:= fromcompltodisjoint X). 
assert (egf: forall x:X, paths (gg (ff x)) x).  intro.  apply idpath.
assert (efg: forall xx:_, paths (ff (gg xx)) xx). intro. destruct xx as [ t x ].  destruct t as [ x0 | u ] .   simpl.  unfold ff. unfold tocompltodisjoint. simpl. assert (ee: paths  (negpathsii2ii1 x0 tt) x).  apply (proofirrelevance _ (isapropneg _) ). destruct ee. apply idpath. destruct u.  simpl. apply (fromempty (x (idpath _))). apply (gradth  ff gg egf efg).  Defined. 


Definition weqtocompltodisjoint ( X : UU ) := weqpair _ ( isweqtocompltodisjoint X ) .

Corollary isweqfromcompltodisjoint (X:UU): isweq (fromcompltodisjoint X).
Proof. intros. apply (isweqinvmap  ( weqtocompltodisjoint X ) ). Defined. 














(** ** Decidable propositions and decidable inclusions *)

(** *** Decidable propositions [ isdecprop ] *)

Definition isdecprop ( X : UU ) := iscontr ( coprod X ( neg X ) ) .


Lemma isdecproptoisaprop ( X : UU ) ( is : isdecprop X ) : isaprop X .
Proof. intros X is . apply ( isofhlevelsnsummand1 0 _ _ ( isapropifcontr is ) ) . Defined .  
Coercion isdecproptoisaprop : isdecprop >-> isaprop .

Lemma isdecpropif ( X : UU ) : isaprop X -> ( coprod X ( neg X ) ) -> isdecprop X .
Proof. intros X is a . assert ( is1 : isaprop ( coprod X ( neg X ) ) ) . apply isapropdec . assumption .   apply ( iscontraprop1 is1 a ) . Defined.

Lemma isdecpropfromiscontr { X : UU } ( is : iscontr X ) : isdecprop X .
Proof. intros . apply ( isdecpropif _ (  is ) ( ii1 ( pr1 is ) ) ) . Defined.

Lemma isdecpropempty : isdecprop empty .
Proof. apply ( isdecpropif _ isapropempty ( ii2 ( fun a : empty => a ) ) ) . Defined.

Lemma isdecpropweqf { X Y : UU } ( w : weq X Y ) ( is : isdecprop X ) : isdecprop Y .
Proof. intros . apply  isdecpropif . apply ( isofhlevelweqf 1 w ( isdecproptoisaprop _ is ) ) . destruct ( pr1 is ) as [ x | nx ] . apply ( ii1 ( w x ) ) .  apply ( ii2 ( negf ( invweq w ) nx ) ) . Defined .

Lemma isdecpropweqb { X Y : UU } ( w : weq X Y ) ( is : isdecprop Y ) : isdecprop X .
Proof. intros . apply  isdecpropif . apply ( isofhlevelweqb 1 w ( isdecproptoisaprop _ is ) ) . destruct ( pr1 is ) as [ y | ny ] . apply ( ii1 ( invweq w y ) ) .  apply ( ii2 ( ( negf w ) ny ) ) . Defined .

Lemma isdecproplogeqf { X Y : UU } ( isx : isdecprop X ) ( isy : isaprop Y ) ( lg : X <-> Y ) : isdecprop Y .
Proof . intros. set ( w := weqimplimpl ( pr1 lg ) ( pr2 lg ) isx isy ) . apply ( isdecpropweqf w isx ) . Defined .

Lemma isdecproplogeqb { X Y : UU } ( isx : isaprop X ) ( isy : isdecprop Y ) ( lg : X <-> Y ) : isdecprop X .
Proof . intros. set ( w := weqimplimpl ( pr1 lg ) ( pr2 lg ) isx isy ) . apply ( isdecpropweqb w isy ) . Defined .    



Lemma isdecpropfromneg { X : UU } ( ne : neg X ) : isdecprop X .
Proof. intros . apply ( isdecpropweqb ( weqtoempty ne ) isdecpropempty ) . Defined .  

Lemma isdecproppaths { X : UU } ( is : isdeceq X ) ( x x' : X ) : isdecprop ( paths x x' ) .
Proof. intros . apply ( isdecpropif _ ( isasetifdeceq _ is x x' ) ( is x x' ) ) .  Defined .

Lemma isdeceqif { X : UU } ( is : forall x x' : X , isdecprop ( paths x x' ) ) : isdeceq X .
Proof . intros . intros x x' . apply ( pr1 ( is x x' ) ) . Defined . 

Lemma isaninv1 (X:UU): isdecprop X  -> isaninvprop X.
Proof. intros X is1. unfold isaninvprop. set (is2:= pr1  is1). simpl in is2. 
assert (adjevinv: dneg X -> X). intro X0.  destruct is2 as [ a | b ].  assumption. destruct (X0 b). 
assert (is3: isaprop (dneg X)). apply (isapropneg (X -> empty)). apply (isweqimplimpl  (todneg X) adjevinv is1 is3). Defined. 


Theorem isdecpropfibseq1 { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( fs : fibseqstr f g z ) : isdecprop X -> isaprop Z -> isdecprop Y .
Proof . intros X Y Z f g z fs isx isz .  assert ( isc : iscontr Z ) . apply ( iscontraprop1 isz z ) .  assert ( isweq f ) . apply ( isweqfinfibseq f g z fs isc ) .  apply ( isdecpropweqf ( weqpair _ X0 ) isx ) . Defined .

Theorem isdecpropfibseq0 { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( z : Z ) ( fs : fibseqstr f g z ) : isdecprop Y -> isdeceq Z -> isdecprop X .
Proof . intros X Y Z f g z fs isy isz . assert ( isg : isofhlevelf 1 g ) . apply ( isofhlevelffromXY 1 g ( isdecproptoisaprop _ isy ) ( isasetifdeceq _ isz ) ) . 
assert ( isp : isaprop X ) . apply ( isofhlevelXfromg 1 f g z fs isg ) . 
destruct ( pr1 isy ) as [ y | ny ] .  apply ( isdecpropfibseq1 _ _ y ( fibseq1 f g z fs y ) ( isdecproppaths isz ( g y ) z ) ( isdecproptoisaprop _ isy ) ) . 
apply ( isdecpropif _ isp ( ii2  ( negf f ny ) ) ) . Defined. 

Theorem isdecpropdirprod { X Y : UU } ( isx : isdecprop X ) ( isy : isdecprop Y ) : isdecprop ( dirprod X Y ) .
Proof. intros . assert ( isp : isaprop ( dirprod X Y ) ) . apply ( isofhleveldirprod 1 _ _ ( isdecproptoisaprop _ isx ) ( isdecproptoisaprop _ isy ) ) .  destruct ( pr1 isx ) as [ x | nx ] . destruct ( pr1 isy ) as [ y | ny ] .  apply ( isdecpropif _ isp ( ii1 ( dirprodpair x y ) ) ) . assert ( nxy : neg ( dirprod X Y ) ) . intro xy . destruct xy as [ x0  y0 ] . apply ( ny y0 ) .  apply ( isdecpropif _ isp ( ii2 nxy ) ) .  assert ( nxy : neg ( dirprod X Y ) ) . intro xy . destruct xy as [ x0  y0 ] . apply ( nx x0 ) .  apply ( isdecpropif _ isp ( ii2 nxy ) ) . Defined.

Lemma fromneganddecx { X Y : UU } ( isx : isdecprop X ) ( nf : neg ( dirprod X Y ) ) : coprod ( neg X ) ( neg Y ) .
Proof . intros .  destruct ( pr1 isx ) as [ x | nx ] .  set ( ny := negf ( fun y : Y => dirprodpair x y ) nf ) . apply ( ii2 ny ) .   apply ( ii1 nx ) . Defined .

Lemma fromneganddecy { X Y : UU } ( isy : isdecprop Y ) ( nf : neg ( dirprod X Y ) ) : coprod ( neg X ) ( neg Y ) .
Proof . intros .  destruct ( pr1 isy ) as [ y | ny ] .  set ( nx := negf ( fun x : X => dirprodpair x y ) nf ) . apply ( ii1 nx ) . apply ( ii2 ny ) .   Defined .


(** *** Paths to and from an isolated point form a decidable proposition *)

Lemma isdecproppathsfromisolated ( X : UU ) ( x : X ) ( is : isisolated X x ) ( x' : X ) : isdecprop ( paths x x' ) .
Proof. intros . apply isdecpropif . apply isaproppathsfromisolated .   assumption .  apply ( is x' ) .  Defined .

Lemma isdecproppathstoisolated  ( X : UU ) ( x : X ) ( is : isisolated X x ) ( x' : X ) : isdecprop ( paths x' x ) .
Proof . intros . apply ( isdecpropweqf ( weqpathsinv0 x x' ) ( isdecproppathsfromisolated X x is x' ) ) . Defined .  


(** *** Decidable inclusions *)



Definition isdecincl {X Y:UU} (f :X -> Y) := forall y:Y, isdecprop ( hfiber f y ). 
Lemma isdecincltoisincl { X Y : UU } ( f : X -> Y ) : isdecincl f -> isincl f .
Proof. intros X Y f is . intro y . apply ( isdecproptoisaprop _ ( is y ) ) . Defined.
Coercion isdecincltoisincl : isdecincl >-> isincl .

Lemma isdecinclfromisweq { X Y : UU } ( f : X -> Y ) : isweq f -> isdecincl f .
Proof. intros X Y f iswf .  intro y .  apply ( isdecpropfromiscontr ( iswf y ) ) . Defined .

Lemma isdecpropfromdecincl { X Y : UU } ( f : X -> Y ) : isdecincl f -> isdecprop Y -> isdecprop X .
Proof. intros X Y f isf isy .  destruct ( pr1 isy ) as [ y | n ] . assert ( w : weq ( hfiber f y ) X ) . apply ( weqhfibertocontr f y ( iscontraprop1 ( isdecproptoisaprop _ isy )  y ) ) . apply ( isdecpropweqf w ( isf y ) ) .  apply isdecpropif . apply ( isapropinclb _ isf isy ) .  apply ( ii2 ( negf f n ) ) .  Defined . 


Lemma isdecinclii1 (X Y: UU): isdecincl ( @ii1 X Y ) .
Proof. intros. intro y . destruct y as [ x | y ] . apply ( isdecpropif _ ( isinclii1 X Y ( ii1 x ) ) ( ii1 (hfiberpair  (@ii1 _ _ )  x (idpath _ )) ) ) .   
 apply ( isdecpropif _ ( isinclii1 X Y ( ii2 y ) ) ( ii2 ( neghfiberii1y X Y y ) ) ) .  Defined. 

 
Lemma isdecinclii2 (X Y: UU): isdecincl ( @ii2 X Y ) .
Proof. intros. intro y . destruct y as [ x | y ] .  apply ( isdecpropif _ ( isinclii2 X Y ( ii1 x ) ) ( ii2 ( neghfiberii2x X Y x ) ) ) . 
apply ( isdecpropif _ ( isinclii2 X Y ( ii2 y ) ) ( ii1 (hfiberpair  (@ii2 _ _ )  y (idpath _ )) ) ) .   Defined. 


Lemma isdecinclpr1 { X : UU } ( P : X -> UU ) ( is : forall x : X , isdecprop ( P x ) ) : isdecincl ( @pr1 _ P ) .
Proof . intros . intro x . assert ( w : weq ( P x ) ( hfiber (@pr1 _ P )  x ) ) . apply ezweqpr1 .  apply ( isdecpropweqf w ( is x ) ) . Defined . 


Theorem isdecinclhomot { X Y : UU } ( f g : X -> Y ) ( h : forall x : X , paths ( f x ) ( g x ) ) ( is : isdecincl f ) : isdecincl g .
Proof. intros . intro y . apply ( isdecpropweqf ( weqhfibershomot f g h y ) ( is y ) ) . Defined . 


Theorem isdecinclcomp { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( isf : isdecincl f ) ( isg : isdecincl g ) : isdecincl ( fun x : X => g ( f x ) ) .
Proof. intros. intro z .  set ( gf := fun x : X => g ( f x ) ) . assert ( wy : forall ye : hfiber g z , weq ( hfiber f ( pr1 ye ) ) ( hfiber ( hfibersgftog f g z ) ye ) ) . apply  ezweqhf .  
assert ( ww : forall y : Y , weq ( hfiber f y ) ( hfiber gf ( g y ) ) ) . apply samehfibers . apply ( isdecincltoisincl _ isg ) .  
  destruct ( pr1 ( isg z ) ) as [ ye | nye ] . destruct ye as [ y e ] .  destruct e . apply ( isdecpropweqf ( ww y ) ( isf y ) ) .   assert ( wz : weq ( hfiber gf z ) ( hfiber g z ) ) . split with ( hfibersgftog f g z ) . intro ye .   destruct ( nye ye ) .  apply ( isdecpropweqb wz ( isg z ) ) .  Defined .

(** The conditions of the following theorem can be weakened by assuming only that the h-fibers of g satisfy [ isdeceq ] i.e. are "sets with decidable equality". *)

Theorem isdecinclf { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( isg : isincl g ) ( isgf : isdecincl ( fun x : X => g ( f x ) ) ) : isdecincl f .
Proof. intros . intro y . set ( gf := fun x : _ => g ( f x ) )  .  assert ( ww :  weq ( hfiber f y ) ( hfiber gf ( g y ) ) ) . apply samehfibers . assumption . apply ( isdecpropweqb ww ( isgf ( g y ) ) ) . Defined . 

(** *)


Theorem isdecinclg { X Y Z : UU } ( f : X -> Y ) ( g : Y -> Z ) ( isf : isweq f ) ( isgf : isdecincl ( fun x : X => g ( f x ) ) ) : isdecincl g .
Proof. intros . intro z . set ( gf := fun x : X => g ( f x ) ) . assert ( w : weq ( hfiber gf z ) ( hfiber g z ) ) . split with ( hfibersgftog f g z ) .  intro ye .  assert ( ww : weq ( hfiber f ( pr1 ye ) ) ( hfiber ( hfibersgftog f g z ) ye ) ) . apply  ezweqhf . apply ( iscontrweqf ww ( isf ( pr1 ye ) ) ) .    apply ( isdecpropweqf w ( isgf z ) ) . Defined . 



(** *** Decibadle inclusions and isolated points *)

Theorem isisolateddecinclf { X Y : UU } ( f : X -> Y ) ( x : X ) : isdecincl f -> isisolated X x -> isisolated Y ( f x ) .
Proof .  intros X Y f x isf isx .   assert ( is' : forall y : Y , isdecincl ( d1g  f y x ) ) . intro y .  intro xe .  set ( w := ezweq2g f x xe ) . apply ( isdecpropweqf w ( isdecproppathstoisolated X x isx _ ) ) .  assert ( is'' : forall y : Y , isdecprop ( paths ( f x ) y ) ) . intro .  apply ( isdecpropfromdecincl _ ( is' y ) ( isf y ) ) . intro y' .   apply ( pr1 ( is'' y' ) ) .  Defined . 



(** *** Decidable inclusions and coprojections *)


Definition negimage { X Y : UU } ( f : X -> Y ) := total2 ( fun y : Y => neg ( hfiber f y ) ) .
Definition negimagepair { X Y : UU } ( f : X -> Y ) := tpair ( fun y : Y => neg ( hfiber f y ) ) .

Lemma isinclfromcoprodwithnegimage { X Y : UU } ( f : X -> Y ) ( is : isincl f ) : isincl ( sumofmaps f ( @pr1 _ ( fun y : Y => neg ( hfiber f y ) ) ) ) . 
Proof .  intros . assert ( noi : forall ( x : X ) ( nx : negimage f ) , neg ( paths ( f x ) ( pr1 nx ) ) ) .  intros x nx e .  destruct nx as [ y nhf ] .  simpl in e .  apply ( nhf ( hfiberpair _ x e ) ) . assert ( is' : isincl ( @pr1 _ ( fun y : Y => neg ( hfiber f y ) ) ) ) .  apply isinclpr1 .   intro y .  apply isapropneg .  apply ( isofhlevelfsumofmapsnoi 1 f _ is is' noi ) .   Defined . 


Definition iscoproj { X Y : UU } ( f : X -> Y ) := isweq ( sumofmaps f ( @pr1 _ ( fun y : Y => neg ( hfiber f y ) ) ) ) . 

Definition weqcoproj { X Y : UU } ( f : X -> Y ) ( is : iscoproj f ) : weq ( coprod X ( negimage f ) ) Y := weqpair _ is . 

Theorem iscoprojfromisdecincl { X Y : UU } ( f : X -> Y ) ( is : isdecincl f ) : iscoproj f .
Proof. intros . set ( p := sumofmaps f ( @pr1 _ ( fun y : Y => neg ( hfiber f y ) ) ) ) .  assert ( is' : isincl p ) .  apply isinclfromcoprodwithnegimage .   apply ( isdecincltoisincl _ is ) . unfold iscoproj .   intro y . destruct ( pr1 ( is y ) ) as [ h | nh ] .   destruct h as [ x e ] .  destruct e .  change ( f x ) with ( p ( ii1 x ) ) . apply iscontrhfiberofincl .  assumption .  change y with ( p ( ii2 ( negimagepair _ y nh ) ) ) .  apply iscontrhfiberofincl .  assumption .  Defined . 

Theorem isdecinclfromiscoproj { X Y : UU } ( f : X -> Y ) ( is : iscoproj f ) : isdecincl f .
Proof . intros . set ( g := ( sumofmaps f ( @pr1 _ ( fun y : Y => neg ( hfiber f y ) ) ) ) ) . set ( f' :=  fun x : X => g ( ii1 x ) ) . assert ( is' : isdecincl f' ) . apply ( isdecinclcomp _ _ ( isdecinclii1 _ _ ) ( isdecinclfromisweq _ is ) ) .    assumption .  Defined . 

















(** ** Results using full form of the functional extentionality axioms. 

Summary: We consider two axioms which address functional extensionality. The first one is etacorrection  which compensates for the absense of eta-reduction in Coq8.3 Eta-reduction is expected to be included as a  basic property of the language in Coq8.4 which will make this axiom and related lemmas unnecessary. The second axiom [ funcontr ] is the functional extensionality for dependent functions formulated as the condition that the space of section of a family with contractible fibers is contractible.

Note : some of the results above this point in code use a very limitted form of functional extensionality . See [ funextempty ] .  

*)


(** *** Axioms and their basic corollaries *)

(** etacorrection *)

Axiom etacorrection: forall T:UU, forall P:T -> UU, forall f: (forall t:T, P t), paths f (fun t:T => f t). 

Lemma isweqetacorrection { T : UU } (P:T -> UU): isweq (fun f: forall t:T, P t => (fun t:T => f t)).
Proof. intros.  apply (isweqhomot  (fun f: forall t:T, P t => f) (fun f: forall t:T, P t => (fun t:T => f t)) (fun f: forall t:T, P t => etacorrection _ P f) (idisweq _)). Defined. 

Definition weqeta { T : UU } (P:T -> UU) := weqpair _ ( isweqetacorrection P ) .

Lemma etacorrectiononpaths { T : UU } (P:T->UU)(s1 s2 :forall t:T, P t) : paths (fun t:T => s1 t) (fun t:T => s2 t)-> paths s1 s2. 
Proof. intros T P s1 s2 X. set (ew := weqeta P). apply (invmaponpathsweq ew s1 s2 X). Defined. 

Definition etacor { X Y : UU } (f:X -> Y) : paths f (fun x:X => f x) := etacorrection _ (fun T:X => Y) f.

Lemma etacoronpaths { X Y : UU } (f1 f2 : X->Y) : paths (fun x:X => f1 x) (fun x:X => f2 x) -> paths f1 f2. 
Proof. intros X Y f1 f2 X0. set (ec:= weqeta (fun x:X => Y) ). apply (invmaponpathsweq  ec f1 f2 X0). Defined.


(** Dependent functions and sections up to homotopy I *)


Definition toforallpaths { T : UU }  (P:T -> UU) (f g :forall t:T, P t) : (paths f g) -> (forall t:T, paths (f t) (g t)).
Proof. intros T P f g X t. destruct X. apply (idpath (f t)). Defined. 


Definition sectohfiber { X : UU } (P:X -> UU): (forall x:X, P x) -> (hfiber (fun f:_ => fun x:_ => pr1  (f x)) (fun x:X => x)) := (fun a : forall x:X, P x => tpair _ (fun x:_ => tpair _ x (a x)) (idpath (fun x:X => x))).

Definition hfibertosec  { X : UU } (P:X -> UU):  (hfiber (fun f:_ => fun x:_ => pr1  (f x)) (fun x:X => x)) -> (forall x:X, P x):= fun se:_  => fun x:X => match se as se' return P x with tpair s e => (transportf P (toforallpaths (fun x:X => X)  (fun x:X => pr1 (s x)) (fun x:X => x) e x) (pr2  (s x))) end.

Definition sectohfibertosec { X : UU } (P:X -> UU): forall a: forall x:X, P x, paths (hfibertosec _  (sectohfiber _ a)) a := fun a:_ => (pathsinv0 (etacorrection _ _ a)).



(** *** Deduction of functional extnsionality for dependent functions (sections) from functional extensionality of usual functions *)

Axiom funextfunax : forall (X Y:UU)(f g:X->Y),  (forall x:X, paths (f x) (g x)) -> (paths f g). 

Lemma isweqlcompwithweq { X X' : UU} (w: weq X X') (Y:UU) : isweq (fun a:X'->Y => (fun x:X => a (w x))).
Proof. intros. set (f:= (fun a:X'->Y => (fun x:X => a (w x)))). set (g := fun b:X-> Y => fun x':X' => b ( invweq  w x')). 
set (egf:= (fun a:X'->Y => funextfunax X' Y (fun x':X' => (g (f a)) x') a (fun x': X' =>  maponpaths a  (homotweqinvweq w x')))).
set (efg:= (fun a:X->Y => funextfunax X Y (fun x:X => (f (g a)) x) a (fun x: X =>  maponpaths a  (homotinvweqweq w x)))). 
apply (gradth  f g egf efg). Defined.



Lemma isweqrcompwithweq { Y Y':UU } (w: weq Y Y')(X:UU): isweq (fun a:X->Y => (fun x:X => w (a x))).
Proof. intros. set (f:= (fun a:X->Y => (fun x:X => w (a x)))). set (g := fun a':X-> Y' => fun x:X => (invweq  w (a' x))). 
set (egf:= (fun a:X->Y => funextfunax X Y (fun x:X => (g (f a)) x) a (fun x: X => (homotinvweqweq w (a x))))).
set (efg:= (fun a':X->Y' => funextfunax X Y' (fun x:X => (f (g a')) x) a' (fun x: X =>  (homotweqinvweq w (a' x))))). 
apply (gradth  f g egf efg). Defined.



Theorem funcontr { X : UU } (P:X -> UU) : (forall x:X, iscontr (P x)) -> iscontr (forall x:X, P x).
Proof. intros X P X0 . set (T1 := forall x:X, P x). set (T2 := (hfiber (fun f: (X -> total2 P)  => fun x: X => pr1  (f x)) (fun x:X => x))). assert (is1:isweq (@pr1 X P)). apply isweqpr1. assumption.  set (w1:= weqpair  (@pr1 X P) is1).  
assert (X1:iscontr T2).  apply (isweqrcompwithweq  w1 X (fun x:X => x)). 
apply ( iscontrretract  _ _  (sectohfibertosec P ) X1). Defined. 

Corollary funcontrtwice { X : UU } (P: X-> X -> UU)(is: forall (x x':X), iscontr (P x x')): iscontr (forall (x x':X), P x x').
Proof. intros. 
assert (is1: forall x:X, iscontr (forall x':X, P x x')). intro. apply (funcontr _ (is x)). apply (funcontr _ is1). Defined. 


(** Proof of the fact that the [ toforallpaths ] from [paths s1 s2] to [forall t:T, paths (s1 t) (s2 t)] is a weak equivalence - a strong form 
of functional extensionality for sections of general families. The proof uses only [funcontr] which is an axiom i.e. its type satisfies [ isaprop ].  *)


Lemma funextweql1 { T : UU } (P:T -> UU)(g: forall t:T, P t): iscontr (total2 (fun f:forall t:T, P t => forall t:T, paths (f t) (g t))).
Proof. intros. set (X:= forall t:T, coconustot _ (g t)). assert (is1: iscontr X). apply (funcontr  (fun t:T => coconustot _ (g t)) (fun t:T => iscontrcoconustot _ (g t))).  set (Y:= total2 (fun f:forall t:T, P t => forall t:T, paths (f t) (g t))). set (p:= fun z: X => tpair (fun f:forall t:T, P t => forall t:T, paths (f t) (g t)) (fun t:T => pr1  (z t)) (fun t:T => pr2  (z t))).  set (s:= fun u:Y => (fun t:T => coconustotpair _ ((pr2  u) t))).  set (etap:= fun u: Y => tpair (fun f:forall t:T, P t => forall t:T, paths (f t) (g t)) (fun t:T => ((pr1  u) t)) (pr2  u)).

assert (eps: forall u:Y, paths (p (s u)) (etap u)).  intro.  destruct u as [ t x ]. unfold p. unfold s. unfold etap.   simpl. assert (ex: paths x (fun t0:T => x t0)). apply etacorrection.  destruct ex. apply idpath. 

assert (eetap: forall u:Y, paths (etap u) u). intro. unfold etap. destruct u as [t x ]. simpl.


set (ff:= fun fe: (total2  (fun f : forall t0 : T, P t0 => forall t0 : T, paths (f t0) (g t0))) => tpair (fun f : forall t0 : T, P t0 => forall t0 : T, paths (f t0) (g t0)) (fun t0:T => (pr1  fe) t0) (pr2  fe)). 

assert (isweqff: isweq ff). apply (isweqfpmap  ( weqeta P ) (fun f: forall t:T, P t => forall t:T, paths (f t) (g t)) ). 

assert (ee: forall fe: (total2 (fun f : forall t0 : T, P t0 => forall t0 : T, paths (f t0) (g t0))), paths (ff (ff fe)) (ff fe)). intro. apply idpath.  assert (eee: forall fe: (total2 (fun f : forall t0 : T, P t0 => forall t0 : T, paths (f t0) (g t0))), paths (ff  fe) fe). intro. apply (invmaponpathsweq ( weqpair ff isweqff )  _ _ (ee fe)).  

apply (eee (tpair _ t x)). assert (eps0: forall u: Y, paths (p (s u)) u). intro. apply (pathscomp0   (eps u) (eetap u)). 
 
apply ( iscontrretract p s eps0). assumption. Defined. 



Theorem isweqtoforallpaths { T : UU } (P:T -> UU)( f g: forall t:T, P t) : isweq (toforallpaths P f g). 
Proof. intros. set (tmap:= fun ff: total2 (fun f0: forall t:T, P t, paths f0 g) => tpair (fun f0:forall t:T, P t => forall t:T, paths (f0 t) (g t)) (pr1  ff) (toforallpaths P (pr1  ff) g (pr2  ff))). assert (is1: iscontr (total2 (fun f0: forall t:T, P t, paths f0 g))). apply (iscontrcoconustot _ g).   assert (is2:iscontr (total2 (fun f0:forall t:T, P t => forall t:T, paths (f0 t) (g t)))). apply funextweql1.  
assert (X: isweq tmap).  apply (isweqcontrcontr  tmap is1 is2).  apply (isweqtotaltofib (fun f0: forall t:T, P t, paths f0 g) (fun f0:forall t:T, P t => forall t:T, paths (f0 t) (g t)) (fun f0:forall t:T, P t =>  (toforallpaths P f0 g)) X f).  Defined. 


Theorem weqtoforallpaths { T : UU } (P:T -> UU)(f g : forall t:T, P t) : weq (paths f g) (forall t:T, paths (f t) (g t)) .
Proof. intros. split with (toforallpaths P f g). apply isweqtoforallpaths. Defined. 


Definition funextsec { T : UU } (P: T-> UU) (s1 s2 : forall t:T, P t) : (forall t:T, paths (s1 t) (s2 t)) -> paths s1 s2 := invmap  (weqtoforallpaths _ s1 s2) .

Definition funextfun { X Y:UU } (f g:X->Y) : (forall x:X, paths (f x) (g x)) -> (paths f g):= funextsec (fun x:X => Y) f g.

(** I do not know at the moment whether [funextfun] is equal (homotopic) to [funextfunax]. It is advisable in all cases to use [funextfun] or, equivalently, [funextsec], since it can be produced from [funcontr] and therefore is well defined up to a canonbical equivalence.  In addition it is a homotopy inverse of [toforallpaths] which may be true or not for [funextsecax]. *) 

Theorem isweqfunextsec { T : UU } (P:T -> UU)(f g : forall t:T, P t) : isweq (funextsec P f g).
Proof. intros. apply (isweqinvmap ( weqtoforallpaths _  f g ) ). Defined. 

Definition weqfunextsec { T : UU } (P:T -> UU)(f g : forall t:T, P t) : weq  (forall t:T, paths (f t) (g t)) (paths f g) := weqpair _ ( isweqfunextsec P f g ) .



 


(** ** Sections of "double fibration" [(P: T -> UU)(PP: forall t:T, P t -> UU)] and pairs of sections *)



(** *** General case *)

Definition totaltoforall { X : UU } (P : X -> UU ) ( PP : forall x:X, P x -> UU ) : total2 (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)) -> forall x:X, total2 (PP x).
Proof. intros X P PP X0 x. destruct X0 as [ t x0 ]. split with (t x). apply (x0 x). Defined.


Definition foralltototal  { X : UU } ( P : X -> UU ) ( PP : forall x:X, P x -> UU ):  (forall x:X, total2 (PP x)) -> total2 (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)).
Proof. intros X P PP X0. split with (fun x:X => pr1  (X0 x)). apply (fun x:X => pr2  (X0 x)). Defined.

Lemma lemmaeta1 { X : UU } (P:X->UU) (Q:(forall x:X, P x) -> UU)(s0: forall x:X, P x)(q: Q (fun x:X => (s0 x))): paths (tpair (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) s0 q) (tpair (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) (fun x:X => (s0 x)) q). 
Proof. intros. set (ff:= fun tp:total2 (fun s: (forall x:X, P x) => Q (fun x:X => (s x))) => tpair _ (fun x:X => pr1  tp x) (pr2  tp)). assert (X0 : isweq ff).  apply (isweqfpmap  ( weqeta P ) Q ). 
assert (ee: paths (ff (tpair (fun s : forall x : X, P x => Q (fun x : X => s x)) s0 q)) (ff (tpair (fun s : forall x : X, P x => Q (fun x : X => s x)) (fun x : X => s0 x) q))). apply idpath. 

apply (invmaponpathsweq ( weqpair ff X0 ) _ _ ee). Defined. 



Definition totaltoforalltototal { X : UU } ( P : X -> UU ) ( PP : forall x:X, P x -> UU )( ss : total2 (fun s0: forall x:X, P x => forall x:X, PP x (s0 x)) ): paths (foralltototal _ _ (totaltoforall  _ _ ss)) ss.
Proof. intros.  destruct ss as [ t x ]. unfold foralltototal. unfold totaltoforall.  simpl.  set (et:= fun x:X => t x). 

assert (paths (tpair (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) t x) (tpair (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) et x)). apply (lemmaeta1 P (fun s: forall x:X, P x =>  forall x:X, PP x (s x)) t x).  

assert (ee: paths (tpair (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) et x) (tpair (fun s0 : forall x0 : X, P x0 => forall x0 : X, PP x0 (s0 x0)) et (fun x0 : X => x x0))). 
assert (eee: paths x (fun x0:X => x x0)). apply etacorrection. destruct eee. apply idpath. destruct ee. apply pathsinv0. assumption. Defined. 



Definition foralltototaltoforall { X : UU } ( P : X -> UU ) ( PP : forall x:X, P x -> UU ) ( ss : forall x:X, total2 (PP x)): paths (totaltoforall _ _ (foralltototal _ _ ss)) ss.
Proof. intros. unfold foralltototal. unfold totaltoforall.  simpl. assert (ee: forall x:X, paths (tpair (PP x) (pr1 (ss x)) (pr2 (ss x))) (ss x)).  intro. apply (pathsinv0   (tppr  (ss x))).  apply (funextsec). assumption. Defined.

Theorem isweqforalltototal { X : UU } ( P : X -> UU ) ( PP : forall x:X, P x -> UU ) : isweq (foralltototal P PP).
Proof. intros.  apply (gradth  (foralltototal P PP) (totaltoforall P PP) (foralltototaltoforall P PP) (totaltoforalltototal P PP)). Defined. 

Theorem isweqtotaltoforall { X : UU } (P:X->UU)(PP:forall x:X, P x -> UU): isweq (totaltoforall P PP).
Proof. intros.  apply (gradth   (totaltoforall P PP) (foralltototal P PP)  (totaltoforalltototal P PP) (foralltototaltoforall P PP)). Defined. 

Definition weqforalltototal { X : UU } ( P : X -> UU ) ( PP : forall x:X, P x -> UU ) := weqpair _ ( isweqforalltototal P PP ) .

Definition weqtotaltoforall { X : UU } ( P : X -> UU ) ( PP : forall x:X, P x -> UU ) := invweq ( weqforalltototal P PP ) . 



(** *** Functions to a dependent sum (to a [ total2 ]) *)

Definition weqfuntototaltototal ( X : UU ) { Y : UU } ( Q : Y -> UU ) : weq ( X -> total2 Q ) ( total2 ( fun f : X -> Y => forall x : X , Q ( f x ) ) ) := weqforalltototal ( fun x : X => Y ) ( fun x : X => Q ) .


(** *** Functions to direct product *)

(** Note: we give direct proofs for this special case. *)


Definition funtoprodtoprod { X Y Z : UU } ( f : X -> dirprod Y Z ) : dirprod ( X -> Y ) ( X -> Z ) := dirprodpair ( fun x : X => pr1 ( f x ) ) ( fun x : X => ( pr2 ( f x ) ) ) .

Definition prodtofuntoprod { X Y Z : UU } ( fg : dirprod ( X -> Y ) ( X -> Z ) ) : X -> dirprod Y Z := match fg with tpair f g => fun x : X => dirprodpair ( f x ) ( g x ) end .

Theorem weqfuntoprodtoprod ( X Y Z : UU ) : weq ( X -> dirprod Y Z ) ( dirprod ( X -> Y ) ( X -> Z ) ) .
Proof. intros. set ( f := @funtoprodtoprod X Y Z ) . set ( g := @prodtofuntoprod X Y Z ) . split with f . 
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro a . apply funextfun .  intro x .  simpl . apply pathsinv0 . apply tppr . 
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro a . destruct a as [ fy fz ] . apply pathsdirprod .  simpl . apply pathsinv0 . apply etacorrection . simpl . apply pathsinv0 . apply etacorrection .
apply ( gradth _ _ egf efg ) . Defined .    
  






(** ** Homotopy fibers of the map [forall x:X, P x -> forall x:X, Q x] *) 

(** *** General case *)

Definition maponsec { X:UU }  (P Q : X -> UU) (f: forall x:X, P x -> Q x): (forall x:X, P x) -> (forall x:X, Q x) := 
fun s: forall x:X, P x => (fun x:X => (f x) (s x)).

Definition maponsec1 { X Y : UU } (P:Y -> UU)(f:X-> Y): (forall y:Y, P y) -> (forall x:X, P (f x)) := fun sy: forall y:Y, P y => (fun x:X => sy (f x)).



Definition hfibertoforall { X : UU } (P Q : X -> UU) (f: forall x:X, P x -> Q x)(s: forall x:X, Q x): hfiber  (@maponsec _ _ _ f) s -> forall x:X, hfiber  (f x) (s x).
Proof. intro. intro. intro. intro. intro.  unfold hfiber. 

set (map1:= totalfun (fun pointover : forall x : X, P x =>
      paths (fun x : X => f x (pointover x)) s) (fun pointover : forall x : X, P x =>
      forall x:X, paths  ((f x) (pointover x)) (s x))  (fun pointover: forall x:X, P x => toforallpaths _ (fun x : X => f x (pointover x)) s )).

set (map2 := totaltoforall P (fun x:X => (fun pointover : P x => paths (f x pointover) (s x)))).  

set (themap := fun a:_ => map2 (map1 a)). assumption. Defined. 



Definition foralltohfiber  { X : UU } ( P Q : X -> UU) (f: forall x:X, P x -> Q x)(s: forall x:X, Q x): (forall x:X, hfiber  (f x) (s x)) -> hfiber  (maponsec _ _ f) s.
Proof.  intro. intro. intro. intro.   intro. unfold hfiber. 

set (map2inv := foralltototal P (fun x:X => (fun pointover : P x => paths (f x pointover) (s x)))).
set (map1inv :=  totalfun (fun pointover : forall x : X, P x =>
      forall x:X, paths  ((f x) (pointover x)) (s x)) (fun pointover : forall x : X, P x =>
      paths (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => funextsec _ (fun x : X => f x (pointover x)) s)).
set (themap := fun a:_=> map1inv (map2inv a)). assumption. Defined. 


Theorem isweqhfibertoforall  { X : UU } (P Q :X -> UU) (f: forall x:X, P x -> Q x)(s: forall x:X, Q x): isweq (hfibertoforall _ _ f s).
Proof. intro. intro. intro. intro. intro. 

set (map1:= totalfun (fun pointover : forall x : X, P x =>
      paths  (fun x : X => f x (pointover x)) s) (fun pointover : forall x : X, P x =>
      forall x:X, paths  ((f x) (pointover x)) (s x))  (fun pointover: forall x:X, P x => toforallpaths _ (fun x : X => f x (pointover x)) s)).

set (map2 := totaltoforall P (fun x:X => (fun pointover : P x => paths (f x pointover) (s x)))).  

assert (is1: isweq map1). apply (isweqfibtototal _ _ (fun pointover: forall x:X, P x => weqtoforallpaths _ (fun x : X => f x (pointover x)) s )).

assert (is2: isweq map2). apply isweqtotaltoforall.

apply (twooutof3c map1 map2 is1 is2). Defined.


Definition weqhfibertoforall  { X : UU } (P Q :X -> UU) (f: forall x:X, P x -> Q x)(s: forall x:X, Q x) := weqpair _ ( isweqhfibertoforall P Q f s ) .



Theorem isweqforalltohfiber  { X : UU } (P Q : X -> UU) (f: forall x:X, P x -> Q x)(s: forall x:X, Q x): isweq (foralltohfiber  _ _ f s).
Proof. intro. intro. intro. intro. intro. 

set (map2inv := foralltototal P (fun x:X => (fun pointover : P x => paths (f x pointover) (s x)))).

assert (is2: isweq map2inv). apply (isweqforalltototal P (fun x:X => (fun pointover : P x => paths (f x pointover) (s x)))).

set (map1inv :=  totalfun (fun pointover : forall x : X, P x =>
      forall x:X, paths  ((f x) (pointover x)) (s x)) (fun pointover : forall x : X, P x =>
      paths (fun x : X => f x (pointover x)) s) (fun pointover: forall x:X, P x => funextsec _  (fun x : X => f x (pointover x)) s)).

assert (is1: isweq map1inv). apply (isweqfibtototal _ _ (fun pointover: forall x:X, P x => weqfunextsec _ (fun x : X => f x (pointover x)) s ) ).

apply (twooutof3c map2inv map1inv is2 is1). Defined. 

Definition weqforalltohfiber  { X : UU } (P Q : X -> UU) (f: forall x:X, P x -> Q x)(s: forall x:X, Q x) := weqpair _ ( isweqforalltohfiber P Q f s ) .



(** *** The weqk equivalence  between section spaces (dependent products) defined by a family of weak equivalences  [ weq ( P x ) ( Q x ) ] *)




Corollary isweqmaponsec { X : UU } (P Q : X-> UU) (f: forall x:X, weq ( P x ) ( Q x) ) : isweq (maponsec _ _ f). 
Proof. intros. unfold isweq.  intro y.
assert (is1: iscontr (forall x:X, hfiber  (f x) (y x))). assert (is2: forall x:X, iscontr (hfiber  (f x) (y x))). intro x. apply ( ( pr2 ( f x ) )  (y x)). apply funcontr. assumption. 
apply (iscontrweqb  (weqhfibertoforall P Q f y) is1 ). Defined. 

Definition weqonseqfibers { X : UU } (P Q : X-> UU) (f: forall x:X, weq ( P x ) ( Q x )) := weqpair _ ( isweqmaponsec P Q f ) .


(** *** Composition of functions with a weak equivalence on the right *)

Definition  weqffun ( X : UU ) { Y Z : UU } ( w : weq Y Z ) : weq ( X -> Y ) ( X -> Z ) := weqonseqfibers _ _ ( fun x : X => w ) . 








(** ** The map between section spaces (dependent products) defined by the map between the bases [ f: Y -> X ] *)


(** *** General case *)


Definition maponsec1l0 { X : UU } (P:X -> UU)(f:X-> X)(h: forall x:X, paths (f x) x)(s: forall x:X, P x): (forall x:X, P x) := (fun x:X => transportf P  (h x) (s (f x))).

Lemma maponsec1l1  { X : UU } (P:X -> UU)(x:X)(s:forall x:X, P x): paths (maponsec1l0 P (fun x:X => x) (fun x:X => idpath x) s x) (s x). 
Proof. intros. unfold maponsec1l0.   apply idpath. Defined. 


Lemma maponsec1l2 { X : UU } (P:X -> UU)(f:X-> X)(h: forall x:X, paths (f x) x)(s: forall x:X, P x)(x:X): paths (maponsec1l0 P f h s x) (s x).
Proof. intros.  

set (map:= fun ff: total2 (fun f0:X->X => forall x:X, paths (f0 x) x) => maponsec1l0 P (pr1  ff) (pr2  ff) s x).
assert (is1: iscontr (total2 (fun f0:X->X => forall x:X, paths (f0 x) x))). apply funextweql1. assert (e: paths (tpair  (fun f0:X->X => forall x:X, paths (f0 x) x) f h) (tpair  (fun f0:X->X => forall x:X, paths (f0 x) x) (fun x0:X => x0) (fun x0:X => idpath x0))). apply proofirrelevancecontr.  assumption.  apply (maponpaths map  e). Defined. 


Theorem isweqmaponsec1 { X Y : UU } (P:Y -> UU)(f: weq X Y ) : isweq (maponsec1 P f).
Proof. intros.
 
set (map:= maponsec1  P f).
set (invf:= invmap f). set (e1:= homotweqinvweq f). set (e2:= homotinvweqweq f ).
set (im1:= fun sx: forall x:X, P (f x) => (fun y:Y => sx (invf y))).
set (im2:= fun sy': forall y:Y, P (f (invf y)) => (fun y:Y => transportf _ (homotweqinvweq f y) (sy' y))).
set (invmapp := (fun sx: forall x:X, P (f x) => im2 (im1 sx))). 

assert (efg0: forall sx: (forall x:X, P (f x)), forall x:X, paths ((map (invmapp sx)) x) (sx x)).  intro. intro. unfold map. unfold invmapp. unfold im1. unfold im2. unfold maponsec1.  simpl. fold invf.  set (ee:=e2 x).  fold invf in ee.

set (e3x:= fun x0:X => invmaponpathsweq f (invf (f x0)) x0 (homotweqinvweq f (f x0))). set (e3:=e3x x). assert (e4: paths (homotweqinvweq f (f x)) (maponpaths f  e3)). apply (pathsinv0  (pathsweq4  f (invf (f x)) x _)).

assert  (e5:paths (transportf P  (homotweqinvweq f (f x)) (sx (invf (f x)))) (transportf P  (maponpaths f  e3) (sx (invf (f x))))). apply (maponpaths (fun e40:_ => (transportf P e40 (sx (invf (f x)))))  e4).

assert (e6: paths (transportf P (maponpaths f e3) (sx (invf (f x)))) (transportf (fun x:X => P (f x))  e3 (sx (invf (f x))))). apply (pathsinv0 (functtransportf  f P  e3 (sx (invf (f x))))).

set (ff:= fun x:X => invf (f x)).
assert (e7: paths (transportf (fun x : X => P (f x)) e3 (sx (invf (f x)))) (sx x)). apply (maponsec1l2 (fun x:X => P (f x)) ff e3x sx x).  apply (pathscomp0   (pathscomp0   e5 e6) e7).

assert (efg: forall sx: (forall x:X, P (f x)), paths  (map (invmapp sx)) sx). intro. apply (funextsec _ _ _ (efg0 sx)).

assert (egf0: forall sy: (forall y:Y, P y), forall y:Y, paths ((invmapp (map sy)) y) (sy y)). intros. unfold invmapp. unfold map.  unfold im1. unfold im2. unfold maponsec1. 

set (ff:= fun y:Y => f (invf y)). fold invf. apply (maponsec1l2 P ff ( homotweqinvweq f ) sy y). 
assert (egf: forall sy: (forall y:Y, P y), paths  (invmapp (map sy)) sy). intro. apply (funextsec _ _ _ (egf0 sy)). 

apply (gradth  map invmapp egf efg). Defined. 

Definition weqonsecbase { X Y : UU } ( P : Y -> UU ) ( f : weq X Y ) := weqpair _ ( isweqmaponsec1 P f ) .  


(** *** Composition of functions with a weak equivalence on the left *)


Definition  weqbfun  { X Y : UU } ( Z : UU ) ( w : weq X Y ) : weq ( Y -> Z ) ( X -> Z ) := weqonsecbase _ w . 



















(** ** Sections of families over an empty type and over coproducts *)

(** *** General case *)

Definition iscontrsecoverempty ( P : empty -> UU ) : iscontr ( forall x : empty , P x ) .
Proof . intro . split with ( fun x : empty => fromempty x )  .  intro t .  apply funextsec .  intro t0 . destruct t0 . Defined . 

Definition iscontrsecoverempty2 { X : UU } ( P : X -> UU ) ( is : neg X ) : iscontr ( forall x : X , P x ) .
Proof . intros .  set ( w := weqtoempty is ) . set ( w' := weqonsecbase P ( invweq w ) ) .   apply ( iscontrweqb w' ( iscontrsecoverempty _ ) ) . Defined . 

Definition secovercoprodtoprod { X Y : UU } ( P : coprod X Y -> UU ) ( a: forall xy : coprod X Y , P xy ) : dirprod ( forall x : X , P ( ii1 x ) ) ( forall y : Y , P ( ii2 y ) ) := dirprodpair ( fun x : X => a ( ii1 x ) ) ( fun y : Y => a ( ii2 y ) )  .

Definition prodtosecovercoprod { X Y : UU } ( P : coprod X Y -> UU ) ( a : dirprod ( forall x : X , P ( ii1 x ) ) ( forall y : Y , P ( ii2 y ) ) ) :  forall xy : coprod X Y , P xy .
Proof . intros . destruct xy as [ x | y ] . apply ( pr1 a x ) .    apply ( pr2 a y ) . Defined . 


Definition weqsecovercoprodtoprod { X Y : UU } ( P : coprod X Y -> UU ) : weq ( forall xy : coprod X Y , P xy ) ( dirprod ( forall x : X , P ( ii1 x ) ) ( forall y : Y , P ( ii2 y ) ) ) .
Proof . intros . set ( f := secovercoprodtoprod P ) .  set ( g := prodtosecovercoprod P ) . split with f . 
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro . apply funextsec .  intro t .  destruct t as [ x | y ] .  apply idpath . apply idpath . 
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro .  destruct a as [ ax ay ] . apply ( pathsdirprod ) .  apply funextsec . intro x . apply idpath .  apply funextsec . intro y . apply idpath .
apply ( gradth _ _ egf efg ) . Defined .



(** *** Functions from the empty type *)

Theorem iscontrfunfromempty ( X : UU ) : iscontr ( empty -> X ) .
Proof . intro . split with fromempty . intro t .  apply funextfun .  intro x . destruct x . Defined .

Theorem iscontrfunfromempty2 ( X : UU ) { Y : UU } ( is : neg Y ) : iscontr ( Y -> X ) .
Proof. intros . set ( w := weqtoempty is ) . set ( w' := weqbfun X ( invweq w ) ) .  apply ( iscontrweqb w' ( iscontrfunfromempty X ) ) . Defined . 



(** *** Functions from a coproduct *)

Definition funfromcoprodtoprod { X Y Z : UU } ( f : coprod X Y -> Z ) : dirprod ( X -> Z ) ( Y -> Z ) := dirprodpair ( fun x : X => f ( ii1 x ) ) ( fun y : Y => f ( ii2 y ) ) .

Definition prodtofunfromcoprod { X Y Z : UU } ( fg : dirprod ( X -> Z ) ( Y -> Z ) ) : coprod X Y -> Z := match fg with tpair f g => sumofmaps f g end .

Theorem weqfunfromcoprodtoprod ( X Y Z : UU ) : weq ( coprod X Y -> Z ) ( dirprod ( X -> Z ) ( Y -> Z ) ) .
Proof. intros . set ( f := @funfromcoprodtoprod X Y Z ) . set ( g := @prodtofunfromcoprod X Y Z ) . split with f . 
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) .  intro a . apply funextfun .   intro xy .  destruct xy as [ x | y ] .  apply idpath . apply idpath . 
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro a . destruct a as [ fx fy ] . simpl . apply pathsdirprod .  simpl . apply pathsinv0 . apply etacorrection . simpl . apply pathsinv0 . apply etacorrection .
apply ( gradth _ _ egf efg ) . Defined .
















(** ** Sections of families over contractible types and over [ total2 ] (over dependent sums) *)



(** *** General case *)


Definition tosecoverunit ( P : unit -> UU ) ( p : P tt ) : forall t : unit , P t .
Proof . intros . destruct t . apply p . Defined .   
 
Definition weqsecoverunit ( P : unit -> UU ) : weq ( forall t : unit , P t ) ( P tt ) .
Proof . intro. set ( f := fun a : forall t : unit , P t => a tt ) . set ( g := tosecoverunit P ) . split with f . 
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro . apply funextsec .  intro t . destruct t . apply idpath .  
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intros . apply idpath .
apply ( gradth _ _ egf efg ) . Defined .   


Definition weqsecovercontr { X : UU } ( P : X -> UU ) ( is : iscontr X ) : weq ( forall x : X , P x ) ( P ( pr1 is ) ) .
Proof . intros . set ( w1 := weqonsecbase P ( wequnittocontr is ) ) . apply ( weqcomp w1 ( weqsecoverunit _ ) ) .  Defined . 

Definition tosecovertotal2 { X : UU } ( P : X -> UU ) ( Q : total2 P -> UU ) ( a : forall x : X , forall p : P x , Q ( tpair _ x p ) ) : forall xp : total2 P , Q xp .
Proof . intros . destruct xp as [ x p ] . apply ( a x p ) . Defined .  


Definition weqsecovertotal2 { X : UU } ( P : X -> UU ) ( Q : total2 P -> UU ) : weq ( forall xp : total2 P , Q xp ) ( forall x : X , forall p : P x , Q ( tpair _ x p ) ) .
Proof . intros . set  ( f := fun a : forall xp : total2 P , Q xp => fun x : X => fun p : P x => a ( tpair _ x p ) ) . set ( g := tosecovertotal2 P Q ) . split with f .
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro . apply funextsec .  intro xp . destruct xp as [ x p ] . apply idpath .  
assert ( efg : forall a : _ , paths ( f ( g a ) ) a ) . intro . apply funextsec . intro x . apply funextsec . intro p . apply idpath .  
apply ( gradth _ _ egf efg ) . Defined .


(** *** Functions from [ unit ] and from contractible types *) 


Definition weqfunfromunit ( X : UU ) : weq ( unit -> X ) X := weqsecoverunit _ . 

Definition  weqfunfromcontr { X : UU } ( Y : UU ) ( is : iscontr X ) : weq ( X -> Y ) Y := weqsecovercontr _ is . 


(** *** Functions from [ total2 ] *)

Definition weqfunfromtotal2 { X : UU } ( P : X -> UU ) ( Y : UU ) : weq ( total2 P -> Y ) ( forall x : X , P x -> Y ) := weqsecovertotal2 P _ .

(** *** Functions from direct product *)

Definition weqfunfromdirprod ( X X' Y : UU ) : weq ( dirprod X X' -> Y ) ( forall x : X , X' -> Y ) := weqsecovertotal2 _ _ . 
















(** ** Theorem saying that if each member of a family is of h-level n then the space of sections of the family is of h-level n. *)

(** *** General case *)

Theorem impred (n:nat) { T : UU } (P:T -> UU): (forall t:T, isofhlevel n (P t)) -> (isofhlevel n (forall t:T, P t)).
Proof. intro. induction n as [ | n IHn ] . intros T P X.  apply (funcontr P X). intros T P X. unfold isofhlevel in X.  unfold isofhlevel. intros x x' . 

assert (is: forall t:T, isofhlevel n (paths (x t) (x' t))).  intro. apply (X t (x t) (x' t)).  
assert (is2: isofhlevel n (forall t:T, paths (x t) (x' t))). apply (IHn _ (fun t0:T => paths (x t0) (x' t0)) is).
set (u:=toforallpaths P x x').  assert (is3:isweq u). apply isweqtoforallpaths.  set (v:= invmap ( weqpair u is3) ). assert (is4: isweq v). apply isweqinvmap. apply (isofhlevelweqf n  ( weqpair v is4 )). assumption. Defined.

Corollary impredtwice  (n:nat) { T T' : UU } (P:T -> T' -> UU): (forall (t:T)(t':T'), isofhlevel n (P t t')) -> (isofhlevel n (forall (t:T)(t':T'), P t t')).
Proof.  intros n T T' P X. assert (is1: forall t:T, isofhlevel n (forall t':T', P t t')). intro. apply (impred n _ (X t)). apply (impred n _ is1). Defined.


Corollary impredfun (n:nat)(X Y:UU)(is: isofhlevel n Y) : isofhlevel n (X -> Y).
Proof. intros. apply (impred n (fun x:_ => Y) (fun x:X => is)). Defined. 


Theorem impredtech1 (n:nat)(X Y: UU) : (X -> isofhlevel n Y) -> isofhlevel n (X -> Y).
Proof. intro. induction n as [ | n IHn ] . intros X Y X0. simpl. split with (fun x:X => pr1  (X0 x)).  intro t . 
assert (s1: forall x:X, paths (t x) (pr1  (X0 x))). intro. apply proofirrelevancecontr. apply (X0 x). 
apply funextsec. assumption. 

intros X Y X0. simpl. assert (X1: X -> isofhlevel (S n) (X -> Y)). intro X1 . apply impred. assumption. intros x x' .
assert (s1: isofhlevel n (forall xx:X, paths (x xx) (x' xx))). apply impred. intro t . apply (X0 t). 
assert (w: weq (forall xx:X, paths (x xx) (x' xx)) (paths x x')). apply (weqfunextsec  _ x x' ). apply (isofhlevelweqf n w s1). Defined. 



(** ***  Functions to a contractible type *)

Theorem iscontrfuntounit ( X : UU ) : iscontr ( X -> unit ) .
Proof . intro . split with ( fun x : X => tt ) . intro f .   apply funextfun . intro x . destruct ( f x ) .  apply idpath . Defined .

Theorem iscontrfuntocontr ( X : UU ) { Y : UU } ( is : iscontr Y ) : iscontr ( X -> Y ) .
Proof . intros . set ( w := weqcontrtounit is ) .   set ( w' := weqffun X w ) .  apply ( iscontrweqb w' ( iscontrfuntounit X ) ) . Defined .  


(** *** Functions to a proposition *)

Lemma isapropimpl ( X Y : UU ) ( isy : isaprop Y ) : isaprop ( X -> Y ) .
Proof. intros. apply impred. intro.   assumption.  Defined. 



(** *** Functions to an empty type (generalization of [ isapropneg ]) *)


Theorem isapropneg2 ( X : UU ) { Y : UU } ( is : neg Y ) : isaprop ( X -> Y ) .
Proof . intros .  apply impred . intro . apply ( isapropempty2 is ) . Defined .   





(** ** Theorems saying that  [ iscontr T ], [ isweq f ] etc. are of h-level 1 *)



Theorem iscontriscontr { X : UU } ( is : iscontr X ) : iscontr ( iscontr X ).
Proof. intros X X0 . 

assert (is0: forall (x x':X), paths x x'). apply proofirrelevancecontr. assumption.

assert (is1: forall cntr:X, iscontr (forall x:X, paths x cntr)). intro. 
assert (is2: forall x:X, iscontr (paths x cntr)). 
assert (is2: isaprop X). apply isapropifcontr. assumption.  
unfold isaprop in is2. unfold isofhlevel in is2. intro x . apply (is2 x cntr).
apply funcontr. assumption. 

set (f:= @pr1 X (fun cntr:X => forall x:X, paths x cntr)). 
assert (X1:isweq f).  apply isweqpr1. assumption. change (total2 (fun cntr : X => forall x : X, paths x cntr)) with (iscontr X) in X1.  apply (iscontrweqb ( weqpair f X1 ) ) . assumption.  Defined. 



Theorem isapropiscontr (T:UU): isaprop (iscontr T).
Proof. intros.  unfold isaprop.  unfold isofhlevel. intros x x' . assert (is: iscontr(iscontr T)). apply iscontriscontr. apply x. assert (is2: isaprop (iscontr T)). apply ( isapropifcontr is  ) . apply (is2 x x'). Defined.  


Theorem isapropisweq { X Y : UU } (f:X-> Y) : isaprop (isweq f).
Proof. intros. unfold isweq.  apply (impred (S O) (fun y:Y => iscontr (hfiber f y)) (fun y:Y => isapropiscontr (hfiber  f y))).  Defined. 


Theorem isapropisisolated ( X : UU ) ( x : X ) : isaprop ( isisolated X x ) .
Proof. intros . apply isofhlevelsn .  intro is . apply impred . intro x' .  apply ( isapropdec _ ( isaproppathsfromisolated X x is x' ) ) .  Defined .  

Theorem isapropisdeceq (X:UU): isaprop (isdeceq X).
Proof. intro. apply ( isofhlevelsn 0 ) .  intro is . unfold isdeceq. apply impred . intro x .  apply ( isapropisisolated X x ) .   Defined . 

Definition isapropisdecprop ( X : UU ) : isaprop ( isdecprop X ) := isapropiscontr ( coprod X ( neg X ) ) .



Theorem isapropisofhlevel (n:nat)(X:UU): isaprop (isofhlevel n X).
Proof. intro.  unfold isofhlevel.    induction n as [ | n IHn ] . apply isapropiscontr.  intro X . 
assert (X0: forall (x x':X), isaprop  ((fix isofhlevel (n0 : nat) (X0 : UU) {struct n0} : UU :=
         match n0 with
         | O => iscontr X0
         | S m => forall x0 x'0 : X0, isofhlevel m (paths x0 x'0)
         end) n (paths x x'))). intros. apply (IHn (paths x x')). 
assert (is1: 
     (forall x:X, isaprop (forall  x' : X,
      (fix isofhlevel (n0 : nat) (X1 : UU) {struct n0} : UU :=
         match n0 with
         | O => iscontr X1
         | S m => forall x0 x'0 : X1, isofhlevel m (paths x0 x'0)
         end) n (paths x x')))). intro.  apply (impred ( S O ) _  (X0 x)). apply (impred (S O) _ is1). Defined. 

Corollary isapropisaprop (X:UU) : isaprop (isaprop X).
Proof. intro. apply (isapropisofhlevel (S O)). Defined. 

Corollary isapropisaset (X:UU): isaprop (isaset X).
Proof. intro. apply (isapropisofhlevel (S (S O))). Defined.


Theorem isapropisofhlevelf ( n : nat ) { X Y : UU } ( f : X -> Y ) : isaprop ( isofhlevelf n f ) .
Proof . intros . unfold isofhlevelf .    apply impred . intro y . apply isapropisofhlevel .  Defined .

Definition isapropisincl { X Y : UU } ( f : X -> Y ) := isapropisofhlevelf 1 f . 




(** ** Theorems saying that various [ pr1 ] maps are inclusions *)


Theorem isinclpr1weq ( X Y : UU ) : isincl ( @pr1 _ ( fun f : X -> Y => isweq f ) ) .
Proof. intros . apply isinclpr1 . intro f.   apply isapropisweq .  Defined . 

Theorem isinclpr1isolated ( T : UU ) : isincl ( pr1isolated T ) .
Proof . intro . apply ( isinclpr1 _ ( fun t : T => isapropisisolated T t ) ) . Defined . 













(** ** Various weak equivalences between spaces of weak equivalences *)

(** *** Composition with a weak quivalence is a weak equivalence on weak equivalences *)

Theorem weqfweq ( X : UU ) { Y Z : UU } ( w : weq Y Z ) : weq ( weq X Y ) ( weq X Z ) .
Proof. intros . set ( f := fun a : weq X Y => weqcomp a w ) . set ( g := fun b : weq X Z  => weqcomp b ( invweq w ) ) . split with f . 
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro a . apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) ) . apply funextfun .  intro x .  apply ( homotinvweqweq w ( a x ) ) .   
assert ( efg : forall b : _ , paths ( f ( g b ) ) b ) . intro b .  apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) ) . apply funextfun . intro x . apply ( homotweqinvweq w ( b x ) ) .  
apply ( gradth _ _ egf efg ) . Defined .

Theorem weqbweq  { X Y : UU } ( Z : UU ) ( w : weq X Y ) : weq ( weq Y Z ) ( weq X Z ) .
Proof. intros . set ( f := fun a : weq Y Z =>  weqcomp w a ) . set ( g := fun b : weq X Z  => weqcomp ( invweq w ) b ) . split with f . 
assert ( egf : forall a : _ , paths ( g ( f a ) ) a ) . intro a .  apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) ) . apply funextfun .  intro y .  apply ( maponpaths a ( homotweqinvweq w y ) ) .   
assert ( efg : forall b : _ , paths ( f ( g b ) ) b ) . intro b .  apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) ) . apply funextfun . intro x . apply ( maponpaths b ( homotinvweqweq w x ) ) .  
apply ( gradth _ _ egf efg ) . Defined . 



(** *** Invertion on weak equivalences as a weak equivalence *)

(** Comment : note that full form of [ funextfun ] is only used in the proof of this theorem in the form of [ isapropisweq ]. The rest of the proof can be completed using eta-conversion . *)

Theorem weqinvweq ( X Y : UU ) : weq ( weq X Y ) ( weq Y X ) .
Proof . intros . set ( f := fun w : weq X Y => invweq w ) . set ( g := fun w : weq Y X => invweq w ) . split with f .
assert ( egf : forall w : _ , paths ( g ( f w ) ) w ) . intro . apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) ) . apply funextfun . intro x .   unfold f.  unfold g . unfold invweq . simpl . unfold invmap . simpl . apply idpath . 
assert ( efg : forall w : _ , paths ( f ( g w ) ) w ) . intro . apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) ) . apply funextfun . intro x .   unfold f.  unfold g . unfold invweq . simpl . unfold invmap . simpl . apply idpath .
apply ( gradth _ _ egf efg ) . Defined .  



(** ** h-levels of spaces of weak equivalences *)


(** *** Weak equivalences to and from types of h-level ( S n ) *)

Theorem isofhlevelsnweqtohlevelsn ( n : nat ) ( X Y : UU ) ( is : isofhlevel ( S n ) Y ) : isofhlevel ( S n ) ( weq X Y ) .
Proof . intros .  apply ( isofhlevelsninclb n _ ( isinclpr1weq _ _ ) ) .  apply impred . intro .  apply is .  Defined .  

Theorem isofhlevelsnweqfromhlevelsn ( n : nat ) ( X Y : UU ) ( is : isofhlevel ( S n ) Y ) : isofhlevel ( S n ) ( weq Y X ) .
Proof. intros .  apply ( isofhlevelweqf ( S n ) ( weqinvweq X Y ) ( isofhlevelsnweqtohlevelsn n X Y is ) ) .  Defined . 




(** *** Weak equivalences to and from contractible types *)

Theorem isapropweqtocontr ( X : UU ) { Y : UU } ( is : iscontr Y ) : isaprop ( weq X Y ) .
Proof . intros .  apply ( isofhlevelsnweqtohlevelsn 0 _ _ ( isapropifcontr is ) ) . Defined .  

Theorem isapropweqfromcontr ( X : UU ) { Y : UU } ( is : iscontr Y ) : isaprop ( weq Y X ) .
Proof. intros .  apply ( isofhlevelsnweqfromhlevelsn 0 X _ ( isapropifcontr is ) ) . Defined . 


(** *** Weak equivalences to and from propositions *)


Theorem isapropweqtoprop ( X  Y : UU ) ( is : isaprop Y ) : isaprop ( weq X Y ) .
Proof . intros .  apply ( isofhlevelsnweqtohlevelsn 0 _ _ is ) . Defined .  

Theorem isapropweqfromprop ( X Y : UU )( is : isaprop Y ) : isaprop ( weq Y X ) .
Proof. intros .  apply ( isofhlevelsnweqfromhlevelsn 0 X _ is ) . Defined . 


(** *** Weak equivalences to and from sets *)

Theorem isasetweqtoset ( X  Y : UU ) ( is : isaset Y ) : isaset ( weq X Y ) .
Proof . intros .  apply ( isofhlevelsnweqtohlevelsn 1 _ _ is ) . Defined .  

Theorem isasetweqfromset ( X Y : UU )( is : isaset Y ) : isaset ( weq Y X ) .
Proof. intros .  apply ( isofhlevelsnweqfromhlevelsn 1 X _ is ) . Defined . 



(** *** Weak equivalences to an empty type *)

Theorem isapropweqtoempty  ( X : UU ) : isaprop ( weq X empty ) .
Proof . intro . apply ( isofhlevelsnweqtohlevelsn 0 _ _ ( isapropempty ) ) . Defined . 


Theorem isapropweqtoempty2 ( X : UU ) { Y : UU } ( is : neg Y ) : isaprop ( weq X Y ) .
Proof. intros . apply ( isofhlevelsnweqtohlevelsn 0 _ _ ( isapropempty2 is ) ) . Defined . 


(** *** Weak equivalences from an empty type *)

Theorem isapropweqfromempty ( X : UU ) : isaprop ( weq empty X ) .
Proof . intro . apply ( isofhlevelsnweqfromhlevelsn 0 X _ ( isapropempty ) ) . Defined . 

Theorem isapropweqfromempty2 ( X : UU ) { Y : UU } ( is : neg Y ) : isaprop ( weq Y X ) .
Proof. intros .  apply ( isofhlevelsnweqfromhlevelsn 0 X _ ( isapropempty2 is ) ) .  Defined .



(** *** Weak equivalences to and from [ unit ] *)

Theorem isapropweqtounit ( X : UU ) : isaprop ( weq X unit ) .
Proof . intro .  apply ( isofhlevelsnweqtohlevelsn 0 _ _ ( isapropunit ) ) . Defined .  

Theorem isapropweqfromunit ( X : UU ) : isaprop ( weq unit X ) .
Proof. intros . apply ( isofhlevelsnweqfromhlevelsn 0 X _ ( isapropunit ) ) .  Defined . 








(** ** Weak auto-equivalences of a type with an isolated point *)



Definition cutonweq { T : UU } ( t : T ) ( is : isisolated T t ) ( w : weq T T ) : dirprod ( isolated T ) ( weq ( compl T t ) ( compl T t ) ) := dirprodpair  ( isolatedpair T ( w t ) ( isisolatedweqf w t is ) ) ( weqcomp ( weqoncompl w t ) ( weqtranspos0 ( w t ) t ( isisolatedweqf w t is ) is ) ) . 

Definition invcutonweq  { T : UU } ( t : T ) ( is : isisolated T t ) ( t'w : dirprod ( isolated T ) ( weq ( compl T t ) ( compl T t ) ) ) : weq T T := weqcomp ( weqrecomplf t t is is ( pr2 t'w ) ) ( weqtranspos t ( pr1 ( pr1 t'w ) ) is ( pr2 ( pr1 t'w ) ) ) .   

Lemma pathsinvcuntonweqoft  { T : UU } ( t : T ) ( is : isisolated T t ) ( t'w : dirprod ( isolated T ) ( weq ( compl T t ) ( compl T t ) ) ) : paths ( invcutonweq t is t'w t ) ( pr1 ( pr1 t'w ) ) .
Proof. intros .  unfold invcutonweq . simpl . unfold recompl . unfold coprodf . unfold invmap .    simpl .  unfold invrecompl . destruct ( is t ) as [ ett | nett ] .  apply pathsfuntransposoft1 . destruct ( nett ( idpath _ ) ) .  Defined . 

Definition weqcutonweq ( T : UU ) ( t : T ) ( is : isisolated T t ) : weq ( weq T T ) ( dirprod ( isolated T ) ( weq ( compl T t ) ( compl T t ) ) ) .
Proof . intros . set ( f := cutonweq t is  ) . set ( g := invcutonweq t is ) . split with f .

assert ( egf : forall w : _ , paths ( g ( f w ) ) w ) . intro w . apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) _ _ ) . apply funextfun .  intro t' .  simpl .  unfold invmap .  simpl . unfold coprodf . unfold invrecompl . destruct ( is t' ) as [ ett' | nett' ] .   simpl . rewrite ( pathsinv0 ett' ) .  apply pathsfuntransposoft1 .   simpl . unfold funtranspos0 .  simpl .  destruct ( is ( w t ) ) as [ etwt | netwt ] .  destruct ( is ( w t' ) ) as [ etwt' | netwt' ] . destruct (negf (invmaponpathsincl w (isofhlevelfweq 1 w) t t') nett' (pathscomp0 (pathsinv0 etwt) etwt')) .  simpl . assert ( newtt'' := netwt' ) .  rewrite etwt in netwt' .  apply ( pathsfuntransposofnet1t2 t ( w t ) is _ ( w t' ) newtt'' netwt' ) .  simpl .   destruct ( is ( w t' ) ) as [ etwt' | netwt' ] . simpl . change ( w t' ) with ( pr1 w t' ) in etwt' . rewrite ( pathsinv0 etwt' ).  apply ( pathsfuntransposoft2 t ( w t ) is _ ) .  simpl . assert ( ne : neg ( paths ( w t ) ( w t' ) ) ) . apply ( negf ( invmaponpathsweq w _ _  ) nett' ) .  apply ( pathsfuntransposofnet1t2 t ( w t ) is _  ( w t' ) netwt' ne ) . 

assert ( efg : forall xw : _ , paths ( f ( g xw ) ) xw ) . intro . destruct xw as [ x w ] .  destruct x as [ t' is' ] .  simpl in w .  apply pathsdirprod .

apply ( invmaponpathsincl _ ( isinclpr1isolated _ ) ) .  simpl .   unfold recompl . unfold coprodf . unfold invmap .    simpl .  unfold invrecompl . destruct ( is t ) as [ ett | nett ] .  apply pathsfuntransposoft1 . destruct ( nett ( idpath _ ) ) .

simpl .  apply ( invmaponpathsincl _ ( isinclpr1weq _ _ ) _ _ ) . apply funextfun . intro x .  destruct x as [ x netx ] .  unfold g . unfold invcutonweq .  simpl . 

set ( int := funtranspos ( tpair _ t is ) ( tpair _ t' is' ) (recompl T t (coprodf w (fun x0 : unit => x0) (invmap (weqrecompl T t is) t))) ) . 
assert ( eee : paths int t' ) . unfold int .  unfold recompl . unfold coprodf . unfold invmap .    simpl .  unfold invrecompl . destruct ( is t ) as [ ett | nett ] .  apply ( pathsfuntransposoft1 ) . destruct ( nett ( idpath _ ) ) .   

assert ( isint : isisolated _ int ) . rewrite eee . apply is' .    

apply ( ishomotinclrecomplf _ _ isint ( funtranspos0 _ _ _ ) _ _ ) .  simpl .  change ( recomplf int t isint (funtranspos0 int t is) ) with ( funtranspos ( tpair _ int isint ) ( tpair _ t is ) ) .

assert ( ee : paths ( tpair _ int isint) ( tpair _ t' is' ) ) . apply ( invmaponpathsincl _ ( isinclpr1isolated _ ) _ _ ) .  simpl . apply eee . 

rewrite ee . set ( e := homottranspost2t1t1t2 t t' is is' (recompl T t (coprodf w (fun x0 : unit => x0) (invmap (weqrecompl T t is) x))) ) .  unfold funcomp in e . unfold idfun in e .   rewrite e . unfold recompl . unfold coprodf . unfold invmap .    simpl .  unfold invrecompl . destruct ( is x ) as [ etx | netx' ] . destruct ( netx etx ) .  apply ( maponpaths ( @pr1 _ _ ) ) . apply ( maponpaths w ) .  apply ( invmaponpathsincl _ ( isinclpr1compl _ _ ) _ _  ) .   simpl . apply idpath .

apply ( gradth _ _ egf efg ) . Defined .
  






(* Coprojections i.e. functions which are weakly equivalent to functions of the form ii1: X -> coprod X Y 


Definition locsplit (X:UU)(Y:UU)(f:X -> Y):= forall y:Y, coprod (hfiber  f y) (hfiber  f y -> empty).

Definition dnegimage (X:UU)(Y:UU)(f:X -> Y):= total2 Y (fun y:Y => dneg(hfiber  f y)).
Definition dnegimageincl (X Y:UU)(f:X -> Y):= pr1 Y (fun y:Y => dneg(hfiber  f y)).

Definition xtodnegimage (X:UU)(Y:UU)(f:X -> Y): X -> dnegimage  f:= fun x:X => tpair  (f x) ((todneg _) (hfiberpair  f (f x) x (idpath (f x)))). 

Definition locsplitsec (X:UU)(Y:UU)(f:X->Y)(ls: locsplit  f): dnegimage  f -> X := fun u: _ =>
match u with
tpair y psi =>
match (ls y) with 
ii1 z => pr1  z|
ii2 phi => fromempty  (psi phi)
end
end.


Definition locsplitsecissec  (X Y:UU)(f:X->Y)(ls: locsplit  f)(u:dnegimage  f): paths (xtodnegimage  f (locsplitsec  f ls u)) u.
Proof. intros.  set (p:= xtodnegimage  f). set (s:= locsplitsec  f ls).  
assert (paths (pr1  (p (s u))) (pr1  u)). unfold p. unfold xtodnegimage. unfold s. unfold locsplitsec. simpl. induction u. set (lst:= ls t). induction lst.  simpl. apply (pr2  x0). induction (x y).  
assert (is: isofhlevelf (S O)  (dnegimageincl  f)). apply (isofhlevelfpr1 (S O)  (fun y:Y => isapropdneg (hfiber  f y))).  
assert (isw: isweq (maponpaths (dnegimageincl  f) (p (s u)) u)). apply (isofhlevelfonpaths O   _ is). 
apply (invmap  _ isw X0). Defined.



Definition negimage (X:UU)(Y:UU)(f:X -> Y):= total2 Y (fun y:Y => neg(hfiber  f y)).
Definition negimageincl (X Y:UU)(f:X -> Y):= pr1 Y (fun y:Y => neg(hfiber  f y)).


Definition imsum (X:UU)(Y:UU)(f:X -> Y): coprod (dnegimage  f) (negimage  f) -> Y:= fun u:_ =>
match u with
ii1 z => pr1  z|
ii2 z => pr1  z
end.

*)
 





(* End of the file uu0.v *)






(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)


