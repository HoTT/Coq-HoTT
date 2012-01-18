(** * Finite sets. Vladimir Voevodsky . Apr. - Sep. 2011.

This file contains the definition and main properties of finite sets. At the end of the file there are several elementary examples which are used as test cases to check that our constructions do not prevent Coq from normalizing terms of type nat to numerals. 

*)





(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)



(** Imports. *)

Require Export hProp .
Require Export stnfsets .
Require Export hSet .  




(** ** Sets with a given number of elements. *)

(** *** Structure of a set with [ n ] elements on [ X ] defined as a term in [ weq ( stn n ) X ]  *)

Definition nelstruct ( n : nat ) ( X : UU0 ) := weq ( stn n ) X . 

Definition nelstructonstn ( n : nat ) : nelstruct n ( stn n ) := idweq _ . 

Definition nelstructweqf { X Y : UU0 } { n : nat } ( w : weq X Y ) ( sx : nelstruct n X ) : nelstruct n Y := weqcomp sx w .

Definition nelstructweqb { X Y : UU0 } { n : nat } ( w : weq X Y ) ( sy : nelstruct n Y ) : nelstruct n X := weqcomp sy ( invweq w ) . 

Definition nelstructonempty : nelstruct 0 empty := weqstn0toempty . 

Definition nelstructonempty2 { X : UU0 } ( is : neg X ) : nelstruct 0 X :=  weqcomp weqstn0toempty ( invweq ( weqtoempty is ) ) . 

Definition nelstructonunit : nelstruct 1 unit := weqstn1tounit .

Definition nelstructoncontr { X : UU0 } ( is : iscontr X ) : nelstruct 1 X := weqcomp weqstn1tounit ( invweq ( weqcontrtounit is ) ) .

Definition nelstructonbool : nelstruct 2 bool := weqstn2tobool .

Definition nelstructoncoprodwithunit { X : UU0 } { n : nat } ( sx : nelstruct n X ) : nelstruct ( S n ) ( coprod X unit ) :=  weqcomp ( invweq ( weqdnicoprod n ( lastelement n ) ) ) ( weqcoprodf sx ( idweq unit ) ) .

Definition nelstructoncompl { X : UU0 } { n : nat } ( x : X ) ( sx : nelstruct ( S n ) X ) : nelstruct n ( compl X x ) :=  weqcomp ( weqdnicompl n ( invweq sx x ) ) ( invweq ( weqoncompl ( invweq sx ) x ) ) . 

Definition nelstructoncoprod { X  Y : UU0 } { n m : nat } ( sx : nelstruct n X ) ( sy : nelstruct m Y ) : nelstruct ( n + m ) ( coprod X Y ) := weqcomp ( invweq ( weqfromcoprodofstn n m ) ) ( weqcoprodf sx sy ) .

Definition nelstructontotal2 { X : UU0 } ( P : X -> UU0 ) ( f : X -> nat ) { n : nat } ( sx : nelstruct n X ) ( fs : forall x : X , nelstruct ( f x ) ( P x ) ) : nelstruct ( stnsum ( funcomp ( pr1 sx ) f ) ) ( total2 P )  := weqcomp ( invweq ( weqstnsum ( funcomp ( pr1 sx ) P ) ( funcomp ( pr1 sx ) f ) ( fun i : stn n => fs ( ( pr1 sx ) i ) ) ) )  ( weqfp sx P )  .  

Definition nelstructondirprod { X Y : UU0 } { n m : nat } ( sx : nelstruct n X ) ( sy : nelstruct m Y ) : nelstruct ( n * m ) ( dirprod X Y ) := weqcomp ( invweq ( weqfromprodofstn n m ) ) ( weqdirprodf sx sy ) .

(** For a generalization of [ weqfromdecsubsetofstn ] see below *) 

Definition nelstructonfun { X Y : UU0 } { n m : nat } ( sx : nelstruct n X ) ( sy : nelstruct m Y ) : nelstruct ( natpower m n ) ( X -> Y ) := weqcomp ( invweq ( weqfromfunstntostn n m ) ) ( weqcomp ( weqbfun _ ( invweq sx ) ) ( weqffun _ sy ) )  .

Definition nelstructonforall { X : UU0 } ( P : X -> UU0 ) ( f : X -> nat ) { n : nat } ( sx : nelstruct n X ) ( fs : forall x : X , nelstruct ( f x ) ( P x ) ) : nelstruct ( stnprod ( funcomp ( pr1 sx ) f ) ) ( forall x : X , P x )  := invweq ( weqcomp ( weqonsecbase P sx ) ( weqstnprod ( funcomp ( pr1 sx ) P ) ( funcomp ( pr1 sx ) f ) ( fun i : stn n => fs ( ( pr1 sx ) i ) ) ) )  . 

Definition nelstructonweq { X : UU0 } { n : nat } ( sx : nelstruct n X ) : nelstruct ( factorial n ) ( weq X X ) := weqcomp ( invweq ( weqfromweqstntostn n ) ) ( weqcomp ( weqbweq _ ( invweq sx ) ) ( weqfweq _ sx ) ) .



(** *** The property of [ X ] to have [ n ] elements *) 

Definition isofnel ( n : nat ) ( X : UU0 ) : hProp := ishinh ( weq ( stn n ) X ) . 

Lemma isofneluniv { n : nat} { X : UU0 }  ( P : hProp ) : ( ( nelstruct n X ) -> P ) -> ( isofnel n X -> P ) .
Proof. intros.  apply @hinhuniv with ( weq ( stn n ) X ) . assumption. assumption. Defined. 

Definition isofnelstn ( n : nat ) : isofnel n ( stn n ) := hinhpr _ ( nelstructonstn n ) . 

Definition isofnelweqf { X Y : UU0 } { n : nat } ( w : weq X Y ) ( sx : isofnel n X ) : isofnel n Y := hinhfun ( fun sx0 : _ =>  nelstructweqf w sx0 ) sx . 

Definition isofnelweqb { X Y : UU0 } { n : nat } ( w : weq X Y ) ( sy : isofnel n Y ) : isofnel n X :=  hinhfun ( fun sy0 : _ => nelstructweqb w sy0 ) sy . 

Definition isofnelempty : isofnel 0 empty := hinhpr _ nelstructonempty . 

Definition isofnelempty2 { X : UU0 } ( is : neg X ) : isofnel 0 X :=  hinhpr _ ( nelstructonempty2 is ) . 

Definition isofnelunit : isofnel 1 unit := hinhpr _ nelstructonunit  .

Definition isofnelcontr { X : UU0 } ( is : iscontr X ) : isofnel 1 X := hinhpr _ ( nelstructoncontr is ) .

Definition isofnelbool : isofnel 2 bool := hinhpr _ nelstructonbool .

Definition isofnelcoprodwithunit { X : UU0 } { n : nat } ( sx : isofnel n X ) : isofnel ( S n ) ( coprod X unit ) :=   hinhfun ( fun sx0 : _ =>  nelstructoncoprodwithunit sx0 ) sx . 

Definition isofnelcompl { X : UU0 } { n : nat } ( x : X ) ( sx : isofnel ( S n ) X ) : isofnel n ( compl X x ) := hinhfun ( fun sx0 : _ =>  nelstructoncompl x sx0 ) sx . 

Definition isofnelcoprod { X  Y : UU0 } { n m : nat } ( sx : isofnel n X ) ( sy : isofnel m Y ) : isofnel ( n + m ) ( coprod X Y ) :=  hinhfun2 ( fun sx0 : _ => fun sy0 : _ =>  nelstructoncoprod sx0 sy0 ) sx sy . 

(** For a result corresponding to [ nelstructontotal2 ] see below . *)

Definition isofnelondirprod { X Y : UU0 } { n m : nat } ( sx : isofnel n X ) ( sy : isofnel m Y ) : isofnel ( n * m ) ( dirprod X Y ) := hinhfun2 ( fun sx0 : _ => fun sy0 : _ =>  nelstructondirprod sx0 sy0 ) sx sy . 

Definition isofnelonfun { X Y : UU0 } { n m : nat } ( sx : isofnel n X ) ( sy : isofnel m Y ) : isofnel ( natpower m n ) ( X -> Y ) := hinhfun2 ( fun sx0 : _ => fun sy0 : _ =>  nelstructonfun sx0 sy0 ) sx sy . 

(** For a result corresponding to [ nelstructonforall ] see below . *)

Definition isofnelonweq { X : UU0 } { n : nat } ( sx : isofnel n X ) : isofnel ( factorial n ) ( weq X X ) := hinhfun ( fun sx0 : _ =>  nelstructonweq sx0 ) sx . 




(** ** General finite sets. *)

(** *** Finite structure on a type [ X ] defined as a pair [ ( n , w ) ] where [ n : nat ] and [ w : weq ( stn n ) X ] *)


Definition finstruct  ( X : UU0 ) := total2 ( fun n : nat => nelstruct n X ) .
Definition fintructpair  ( X : UU0 )  := tpair ( fun n : nat => nelstruct n X ) .

Definition finstructonstn ( n : nat ) : finstruct ( stn n ) := tpair _ n ( nelstructonstn n ) . 

Definition finstructweqf { X Y : UU0 } ( w : weq X Y ) ( sx : finstruct X ) : finstruct Y := tpair _ ( pr1 sx ) ( nelstructweqf w ( pr2 sx ) ) .

Definition finstructweqb { X Y : UU0 } ( w : weq X Y ) ( sy : finstruct Y ) : finstruct X :=  tpair _ ( pr1 sy ) ( nelstructweqb w ( pr2 sy ) ) .

Definition finstructonempty : finstruct empty := tpair _ 0 nelstructonempty .

Definition finstructonempty2 { X : UU0 } ( is : neg X ) : finstruct X :=  tpair _ 0 ( nelstructonempty2 is ) . 

Definition finstructonunit : finstruct unit := tpair _ 1 nelstructonunit .

Definition finstructoncontr { X : UU0 } ( is : iscontr X ) : finstruct X := tpair _ 1 ( nelstructoncontr is ) .

(** It is not difficult to show that a direct summand of a finite set is a finite set . As a corrolary it follows that a proposition ( a type of h-level 1 ) is a finite set if and only if it is decidable . *)   

Definition finstructonbool : finstruct bool := tpair _ 2 nelstructonbool .

Definition finstructoncoprodwithunit { X : UU0 }  ( sx : finstruct X ) : finstruct ( coprod X unit ) :=  tpair _ ( S ( pr1 sx ) ) ( nelstructoncoprodwithunit ( pr2 sx ) ) .

Definition finstructoncompl { X : UU0 } ( x : X ) ( sx : finstruct X ) : finstruct ( compl X x ) .
Proof . intros . unfold finstruct .  unfold finstruct in sx . destruct sx as [ n w ] . destruct n as [ | n ] .  destruct ( negstn0 ( invweq w x ) ) . split with n .   apply ( nelstructoncompl x w ) .  Defined . 

Definition finstructoncoprod { X  Y : UU0 } ( sx : finstruct X ) ( sy : finstruct Y ) : finstruct ( coprod X Y ) := tpair _ ( ( pr1 sx ) + ( pr1 sy ) ) ( nelstructoncoprod ( pr2 sx ) ( pr2 sy ) ) . 

Definition finstructontotal2 { X : UU0 } ( P : X -> UU0 )   ( sx : finstruct X ) ( fs : forall x : X , finstruct ( P x ) ) : finstruct ( total2 P ) := tpair _ ( stnsum ( funcomp ( pr1 ( pr2 sx ) ) ( fun x : X =>  pr1 ( fs x ) ) ) ) ( nelstructontotal2 P ( fun x : X => pr1 ( fs x ) ) ( pr2 sx ) ( fun x : X => pr2 ( fs x ) ) ) . 

Definition finstructondirprod { X Y : UU0 } ( sx : finstruct X ) ( sy : finstruct Y ) : finstruct ( dirprod X Y ) := tpair _ ( ( pr1 sx ) * ( pr1 sy ) ) ( nelstructondirprod ( pr2 sx ) ( pr2 sy ) ) .

Definition finstructondecsubset { X : UU0 }  ( f : X -> bool ) ( sx : finstruct X ) : finstruct ( hfiber f true ) := tpair _ ( pr1 ( weqfromdecsubsetofstn ( funcomp ( pr1 ( pr2 sx ) ) f ) ) ) ( weqcomp ( invweq ( pr2 ( weqfromdecsubsetofstn ( funcomp ( pr1 ( pr2 sx ) ) f ) ) ) ) ( weqhfibersgwtog ( pr2 sx ) f true ) ) . 


Definition finstructonfun { X Y : UU0 } ( sx : finstruct X ) ( sy : finstruct Y ) : finstruct ( X -> Y ) := tpair _ ( natpower ( pr1 sy ) ( pr1 sx ) ) ( nelstructonfun ( pr2 sx ) ( pr2 sy ) ) .

Definition finstructonforall { X : UU0 } ( P : X -> UU0 )  ( sx : finstruct X ) ( fs : forall x : X , finstruct ( P x ) ) : finstruct ( forall x : X , P x )  := tpair _ ( stnprod ( funcomp ( pr1 ( pr2 sx ) ) ( fun x : X =>  pr1 ( fs x ) ) ) ) ( nelstructonforall P ( fun x : X => pr1 ( fs x ) ) ( pr2 sx ) ( fun x : X => pr2 ( fs x ) ) ) . 

Definition finstructonweq { X : UU0 }  ( sx : finstruct X ) : finstruct ( weq X X ) := tpair _ ( factorial ( pr1 sx ) ) ( nelstructonweq ( pr2 sx ) ) .




(** *** The property of being finite *)

Definition isfinite  ( X : UU0 ) := ishinh ( finstruct X ) .

Definition fincard { X : UU0 } ( is : isfinite X ) : nat .
Proof . intros . set ( int := carrier ( fun n : nat => isofnel n X ) ) .  set ( f1  := ( fun nw : finstruct X => tpair  ( fun n : nat => isofnel n X ) ( pr1 nw ) ( hinhpr _ ( pr2 nw ) ) ) : finstruct X -> int ) .  assert ( isp : isaprop int ) . apply isapropsubtype .   intros x1 x2 is1 is2 . apply ( @hinhuniv2 ( nelstruct x1 X ) ( nelstruct x2 X ) ( hProppair _ ( isasetnat x1 x2 ) ) ) .  intros sx1 sx2 . apply ( weqtoeqstn x1 x2 ( weqcomp sx1 ( invweq sx2 ) ) ) .  apply is1 .  apply is2 .  apply ( @hinhuniv _ ( hProppair _ isp ) f1 ) .  apply is .  Defined . 

Theorem ischoicebasefiniteset { X : UU0 } ( is : isfinite X ) : ischoicebase X . 
Proof . intros . apply ( @hinhuniv ( finstruct X ) ( ischoicebase X ) ) .  intro nw . destruct nw as [ n w ] .   apply ( ischoicebaseweqf w ( ischoicebasestn n ) ) .  apply is .  Defined . 


Definition isfinitestn ( n : nat ) : isfinite ( stn n ) := hinhpr _ ( finstructonstn n ) . 

Definition isfiniteweqf { X Y : UU0 } ( w : weq X Y ) ( sx : isfinite X ) : isfinite Y :=  hinhfun ( fun sx0 : _ =>  finstructweqf w sx0 ) sx .

Definition isfiniteweqb { X Y : UU0 } ( w : weq X Y ) ( sy : isfinite Y ) : isfinite X :=   hinhfun ( fun sy0 : _ =>  finstructweqb w sy0 ) sy .

Definition isfiniteempty : isfinite empty := hinhpr _ finstructonempty .

Definition isfiniteempty2 { X : UU0 } ( is : neg X ) : isfinite X :=  hinhpr _ ( finstructonempty2 is ) . 

Definition isfiniteunit : isfinite unit := hinhpr _ finstructonunit .

Definition isfinitecontr { X : UU0 } ( is : iscontr X ) : isfinite X := hinhpr _ ( finstructoncontr is ) .

Definition isfinitebool : isfinite bool := hinhpr _ finstructonbool .

Definition isfinitecoprodwithunit { X : UU0 } ( sx : isfinite X ) : isfinite ( coprod X unit ) :=  hinhfun ( fun sx0 : _ => finstructoncoprodwithunit sx0 ) sx .

Definition isfinitecompl { X : UU0 } ( x : X ) ( sx : isfinite X ) : isfinite ( compl X x ) := hinhfun ( fun sx0 : _ => finstructoncompl x sx0 ) sx .

Definition isfinitecoprod { X  Y : UU0 } ( sx : isfinite X ) ( sy : isfinite Y ) : isfinite ( coprod X Y ) := hinhfun2 ( fun sx0 : _ => fun sy0 : _ => finstructoncoprod sx0 sy0 ) sx sy . 

Definition isfinitetotal2 { X : UU0 } ( P : X -> UU0 ) ( sx : isfinite X ) ( fs : forall x : X , isfinite ( P x ) ) : isfinite ( total2 P ) .
Proof . intros . set ( fs' := ischoicebasefiniteset sx _ fs ) .  apply ( hinhfun2 ( fun fx0 : forall x : X , finstruct ( P x )  => fun sx0 : _ => finstructontotal2 P sx0 fx0 ) fs' sx ) .  Defined . 

Definition isfinitedirprod { X Y : UU0 } ( sx : isfinite X ) ( sy : isfinite Y ) : isfinite ( dirprod X Y ) := hinhfun2 ( fun sx0 : _ => fun sy0 : _ => finstructondirprod sx0 sy0 ) sx sy . 

Definition isfinitedecsubset { X : UU0 } ( f : X -> bool ) ( sx : isfinite X ) : isfinite ( hfiber f true ) := hinhfun ( fun sx0 : _ =>  finstructondecsubset f sx0 ) sx .

Definition isfinitefun { X Y : UU0 } ( sx : isfinite X ) ( sy : isfinite Y ) : isfinite ( X -> Y ) := hinhfun2 ( fun sx0 : _ => fun sy0 : _ => finstructonfun sx0 sy0 ) sx sy . 

Definition isfiniteforall { X : UU0 } ( P : X -> UU0 ) ( sx : isfinite X ) ( fs : forall x : X , isfinite ( P x ) ) : isfinite ( forall x : X , P x ) .
Proof . intros . set ( fs' := ischoicebasefiniteset sx _ fs ) .  apply ( hinhfun2 ( fun fx0 : forall x : X , finstruct ( P x )  => fun sx0 : _ => finstructonforall P sx0 fx0 ) fs' sx ) .  Defined . 

Definition isfiniteweq { X : UU0 } ( sx : isfinite X ) : isfinite ( weq X X ) := hinhfun ( fun sx0 : _ =>  finstructonweq sx0 ) sx .











(*

(* The cardinality of finite sets using double negation and decidability of equality in nat. *)

Definition carddneg  ( X : UU0 ) (is: isfinite X): nat:= pr1 (isfiniteimplisfinite0 X is).

Definition preweq  ( X : UU0 ) (is: isfinite X): isofnel (carddneg X is) X.
Proof. intros X is X0.  set (c:= carddneg X is). set (dnw:= pr2 (isfiniteimplisfinite0 X is)). simpl in dnw. change (pr1 nat (fun n : nat => isofnel0 n X) (isfiniteimplisfinite0 X is)) with c in dnw. 

assert (f: dirprod (finitestruct X) (dneg (weq (stn c) X)) -> weq (stn c) X). intro H. destruct H as [ t x ].  destruct t as [ t x0 ]. 
assert (dw: dneg (weq (stn t) (stn c))). set (ff:= fun ab:dirprod (weq (stn t) X)(weq (stn c) X) => weqcomp _ _ _ (pr1 ab) (invweq (pr2 ab))).  apply (dnegf _ _ ff (inhdnegand _ _ (todneg _ x0) x)). 
assert (e:paths t c). apply (stnsdnegweqtoeq _ _  dw). clear dnw. destruct e. assumption. unfold isofnel. 
apply (hinhfun _ _ f (hinhand (finitestruct X) _ is (hinhpr _ dnw))). Defined. 

*)

(* to be completed 

Theorem carddnegweqf (X Y:UU0)(f: X -> Y)(isw:isweq f)(isx: isfinite X): paths  (carddneg _ isx) (carddneg _ (isfiniteweqf _ _ _ isw isx)).
Proof. intros. *) 

(* The cardinality of finite sets defined using the "impredicative" ishinh *)



(** ** Test computations. *)



(*Eval compute in carddneg _  (isfinitedirprod _ _ (isfinitestn (S (S (S (S O)))))  (isfinitestn (S (S (S O))))).*)

Eval compute in fincard (isfiniteempty).

Eval compute in fincard (isfiniteunit).

Eval compute in fincard (isfinitebool).




(*Eval lazy in   (pr1 (finitestructcomplement _ (dirprodpair _ _ tt tt) (finitestructdirprod _ _ (finitestructunit) (finitestructunit)))).*)
 



Eval lazy in fincard (isfinitecompl  true isfinitebool).

Eval compute in fincard (isfinitedirprod  isfinitebool isfinitebool).

Eval compute in fincard (isfinitedirprod  isfinitebool (isfinitedirprod  isfinitebool isfinitebool)).

Eval lazy in fincard (isfinitecompl (ii1 tt) (isfinitecoprod  (isfiniteunit) (isfinitebool))).

Eval lazy in  fincard (isfinitecompl (ii1 tt) (isfinitecoprod (isfiniteunit) (isfinitebool))). 

Eval lazy in fincard (isfinitecompl (dirprodpair tt tt) (isfinitedirprod  isfiniteunit isfiniteunit)).
 
Eval lazy in fincard (isfinitecompl (dirprodpair  true (dirprodpair  true false)) (isfinitedirprod  (isfinitebool) (isfinitedirprod  (isfinitebool) (isfinitebool)))).

Eval lazy in fincard ( isfiniteweq ( isfinitedirprod ( isfinitedirprod isfinitebool isfinitebool ) isfinitebool ) ) . 







(* End of the file finitesets.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)