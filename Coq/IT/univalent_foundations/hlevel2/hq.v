(** * Generalities on the type of rationals and rational arithmetic. Vladimir Voevodsky . Aug. - Sep. 2011.

In this file we introduce the type [ hq ] of rationals defined as the quotient set of [ dirprod nat nat ] by the standard equivalence relation and develop the main notions of the rational arithmetic using this definition . 


*)



(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (** This line has to be removed for the file to compile with Coq8.2 *)


(** Imports *)

Require Export hz .

Opaque hz . 

(** Upstream *)




(** ** The commutative ring [ hq ] of integres *)

(** *** General definitions *)


Definition hq : fld := fldfrac hzintdom isdeceqhz .
Definition hqaddabgr : abgr := rngaddabgr hq . 
Definition hqmultabmonoid : abmonoid := rngmultabmonoid hq .
Definition hqtype : UU0 := hq . 

Definition hzhztohq : hz -> ( intdomnonzerosubmonoid hzintdom ) -> hq := fun x a => setquotpr _ ( dirprodpair x a ) . 

Definition hqplus : hq -> hq -> hq := @op1 hq.
Definition hqsign : hq -> hq := grinv hqaddabgr .
Definition hqminus : hq -> hq -> hq := fun x y => hqplus x ( hqsign y ) .
Definition hqzero : hq := unel hqaddabgr .

Definition hqmult : hq -> hq -> hq := @op2 hq .
Definition hqone : hq := unel hqmultabmonoid .

Bind Scope hq_scope with hq . 
Notation " x + y " := ( hqplus x y ) : hq_scope .
Notation " 0 " := hqzero : hq_scope .
Notation " 1 " := hqone : hq_scope . 
Notation " - x " := ( hqsign x ) : hq_scope . 
Notation " x - y " := ( hqminus x y ) : hq_scope .
Notation " x * y " := ( hqmult x y ) : hq_scope .  

Delimit Scope hq_scope with hq .    


(** *** Properties of equlaity on [ hq ] *)

Definition isdeceqhq : isdeceq hq := isdeceqfldfrac hzintdom isdeceqhz . 

Definition isasethq := setproperty hq .

Definition hqeq ( x y : hq ) : hProp := hProppair ( paths x y ) ( isasethq _ _  )  .
Definition isdecrelhqeq : isdecrel hqeq  := fun a b => isdeceqhq a b .
Definition hqdeceq : decrel hq := decrelpair isdecrelhqeq . 
Canonical Structure hqdeceq. 

Definition hqbooleq := decreltobrel hqdeceq .  

Definition hqneq ( x y : hq ) : hProp := hProppair ( neg ( paths x y ) ) ( isapropneg _  )  .
Definition isdecrelhqneq : isdecrel hqneq  := isdecnegrel _ isdecrelhqeq . 
Definition hqdecneq : decrel hq := decrelpair isdecrelhqneq . 
Canonical Structure hqdecneq.  

Definition hqboolneq := decreltobrel hqdecneq .  

(** Computation test *)

Open Local Scope hz_scope .

Transparent hz .

Eval lazy in ( hqbooleq ( hzhztohq ( natnattohz 4 0 ) ( tpair _ ( natnattohz 3 0 ) ( ct ( hzneq , ( natnattohz 3 0 ) , 0 ) ) ) )  ( hzhztohq ( natnattohz 13 1 ) ( tpair _ ( natnattohz 11 2 ) ( ct ( hzneq , ( natnattohz 11 2 ) , 0 ) ) ) ) ) . 

Opaque hz . 

(** *)



(** *** Properties of addition and subtraction on [ hq ] *) 

Open Local Scope hq_scope .

Lemma hqplusr0 ( x : hq ) : paths ( x + 0 ) x .
Proof . intro . apply ( rngrunax1 _ x ) .  Defined . 

Lemma hqplusl0 ( x : hq ) : paths ( 0 + x ) x .
Proof . intro . apply ( rnglunax1 _ x ) . Defined . 

Lemma hqplusassoc ( x y z : hq ) : paths ( ( x + y ) + z ) ( x + ( y + z ) ) .
Proof . intros . apply ( rngassoc1 hq x y z ) . Defined .   

Lemma hqpluscomm ( x y : hq ) : paths ( x + y ) ( y + x ) .
Proof . intros .  apply ( rngcomm1 hq x y ) . Defined .

Lemma hqlminus ( x : hq ) : paths ( -x + x ) 0 .
Proof . intro. apply ( rnglinvax1 hq x ) . Defined .

Lemma hqrminus  ( x : hq ) : paths ( x - x ) 0 .
Proof . intro. apply ( rngrinvax1 hq x ) . Defined .

Lemma isinclhqplusr ( n : hq ) : isincl ( fun m : hq => m + n ) .
Proof. intro . apply ( pr2 ( weqtoincl _ _ ( weqrmultingr hqaddabgr n ) ) ) . Defined. 

Lemma isinclhqplusl ( n : hq ) : isincl ( fun m : hq => n + m ) .
Proof.  intro.  apply ( pr2 ( weqtoincl _ _ ( weqlmultingr hqaddabgr n ) ) ) . Defined . 


Lemma hqpluslcan ( a b c : hq ) ( is : paths ( c + a ) ( c + b ) ) : paths a b .
Proof . intros . apply ( @grlcan hqaddabgr a b c is ) .  Defined . 

Lemma hqplusrcan ( a b c : hq ) ( is : paths ( a + c ) ( b + c ) ) : paths a b .
Proof . intros . apply ( @grrcan hqaddabgr a b c is ) .  Defined . 

Definition hqinvmaponpathsminus { a b : hq } ( e :  paths ( - a ) ( - b ) ) : paths a b := grinvmaponpathsinv hqaddabgr e . 



(** *** Proparties of multiplication on [ hq ] *)


Lemma hqmultr1 ( x : hq ) : paths ( x * 1 ) x .
Proof . intro . apply ( rngrunax2 _ x ) .  Defined . 

Lemma hqmultl1 ( x : hq ) : paths ( 1 * x ) x .
Proof . intro . apply ( rnglunax2 _ x ) . Defined . 

Lemma hqmult0x ( x : hq ) : paths ( 0 * x ) 0 .
Proof . intro . apply ( rngmult0x _ x ) .  Defined . 

Lemma hqmultx0 ( x : hq ) : paths ( x * 0 ) 0 .
Proof . intro . apply ( rngmultx0 _ x ) . Defined . 

Lemma hqmultassoc ( x y z : hq ) : paths ( ( x * y ) * z ) ( x * ( y * z ) ) .
Proof . intros . apply ( rngassoc2 hq x y z ) . Defined .   

Lemma hqmultcomm ( x y : hq ) : paths ( x * y ) ( y * x ) .
Proof . intros .  apply ( rngcomm2 hq  x y ) . Defined .


(** *** Multiplicative inverse and division on [ hq ] 

Note : in our definition it is possible to divide by 0 . The result in this case is 0 . *)

Definition hqmultinv : hq -> hq := fun x => fldfracmultinv0 hzintdom isdeceqhz x . 

Lemma hqislinvmultinv ( x : hq ) ( ne : hqneq x 0 ) : paths ( ( hqmultinv x ) * x ) 1 .
Proof. intros .  apply ( islinvinfldfrac hzintdom isdeceqhz x ne ) . Defined .  

Lemma hqisrinvmultinv ( x : hq ) ( ne : hqneq x 0 ) : paths (  x * ( hqmultinv x ) ) 1 .
Proof. intros .  apply ( isrinvinfldfrac hzintdom isdeceqhz x ne ) . Defined .  

Definition hqdiv ( x y : hq ) : hq := hqmult x ( hqmultinv y ) . 




(** ** Definition and properties of "greater", "less", "greater or equal" and "less or equal" on [ hq ] . *)


(** *** Definitions and notations *)


Definition hqgth : hrel hq := fldfracgt hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth ( ct ( hzgth , 1%hz , 0%hz ) ) hzneqchoice .

Definition hqlth : hrel hq := fun a b => hqgth b a .

Definition hqleh : hrel hq := fun a b => hProppair ( neg ( hqgth a b ) ) ( isapropneg _ )  . 

Definition hqgeh : hrel hq := fun a b => hProppair ( neg ( hqgth b a ) ) ( isapropneg _ )  .


 

(** *** Decidability *)


Lemma isdecrelhqgth : isdecrel hqgth .
Proof . apply isdecfldfracgt . exact isasymmhzgth .   apply isdecrelhzgth . Defined .

Definition hqgthdec := decrelpair isdecrelhqgth .
Canonical Structure hqgthdec .

Definition isdecrelhqlth : isdecrel hqlth := fun x x' => isdecrelhqgth x' x . 

Definition hqlthdec := decrelpair isdecrelhqlth .
Canonical Structure hqlthdec .

Definition isdecrelhqleh : isdecrel hqleh := isdecnegrel _ isdecrelhqgth .

Definition hqlehdec := decrelpair isdecrelhqleh .
Canonical Structure hqlehdec .

Definition isdecrelhqgeh : isdecrel hqgeh := fun x x' => isdecrelhqleh x' x .

Definition hqgehdec := decrelpair isdecrelhqgeh .
Canonical Structure hqgehdec .

(** Computation test *)

Transparent hz .

Eval lazy in ( decreltobrel hqgthdec ( hzhztohq ( natnattohz 5 0 ) ( tpair _ ( natnattohz 3 0 ) ( ct ( hzneq , ( natnattohz 3 0 ) , hzzero ) ) ) )  ( hzhztohq ( natnattohz 13 1 ) ( tpair _ ( natnattohz 11 2 ) ( ct ( hzneq , ( natnattohz 11 2 ) , hzzero ) ) ) ) ) . 

Opaque hz . 


(** *** Properties of individual relations *)

(** [ hqgth ] *)



Lemma istranshqgth ( n m k : hq ) : hqgth n m -> hqgth m k -> hqgth n k .
Proof. apply istransfldfracgt . exact istranshzgth .  Defined . 

Lemma isirreflhqgth ( n : hq ) : neg ( hqgth n n ) .
Proof. apply isirreflfldfracgt . exact isirreflhzgth .   Defined . 

Lemma isasymmhqgth ( n m : hq ) : hqgth n m -> hqgth m n -> empty .
Proof. apply isasymmfldfracgt .  exact isasymmhzgth .  Defined .  

Lemma isantisymmneghqgth ( n m : hq ) : neg ( hqgth n m ) -> neg ( hqgth m n ) -> paths n m .
Proof . apply isantisymmnegfldfracgt . exact isirreflhzgth . exact isantisymmneghzgth .   Defined .     

Lemma isnegrelhqgth : isnegrel hqgth .
Proof . apply isdecreltoisnegrel . apply isdecrelhqgth . Defined . 

Lemma iscoantisymmhqgth ( n m : hq ) : neg ( hqgth n m ) -> coprod ( hqgth m n ) ( paths n m ) .
Proof . apply isantisymmnegtoiscoantisymm . apply isdecrelhqgth .  intros n m . apply isantisymmneghqgth . Defined .  

Lemma iscotranshqgth ( n m k : hq ) : hqgth n k -> hdisj ( hqgth n m ) ( hqgth m k ) .
Proof . intros x y z gxz .  destruct ( isdecrelhqgth x y ) as [ gxy | ngxy ] . apply ( hinhpr _ ( ii1 gxy ) ) . apply hinhpr .   apply ii2 .  destruct ( isdecrelhqgth y x ) as [ gyx | ngyx ] . apply ( istranshqgth _ _ _ gyx gxz ) .  set ( e := isantisymmneghqgth _ _ ngxy ngyx ) . rewrite e in gxz .  apply gxz .  Defined .   




(** [ hqlth ] *)


Definition istranshqlth ( n m k  : hq ) : hqlth n m -> hqlth m k -> hqlth n k := fun lnm lmk => istranshqgth _ _ _ lmk lnm . 

Definition isirreflhqlth ( n : hq ) : neg ( hqlth n n ) := isirreflhqgth n .  

Definition isasymmhqlth ( n m : hq ) : hqlth n m -> hqlth m n -> empty := fun lnm lmn => isasymmhqgth _ _ lmn lnm .

Definition isantisymmneghqtth  ( n m : hq ) : neg ( hqlth n m ) -> neg ( hqlth m n ) -> paths n m := fun nlnm nlmn => isantisymmneghqgth _ _ nlmn nlnm .

Definition isnegrelhqlth : isnegrel hqlth := fun n m => isnegrelhqgth m n .

Definition iscoantisymmhqlth ( n m : hq ) : neg ( hqlth n m ) -> coprod ( hqlth m n ) ( paths n m ) .
Proof . intros n m nlnm . destruct ( iscoantisymmhqgth m n nlnm ) as [ l | e ] . apply ( ii1 l ) . apply ( ii2 ( pathsinv0 e ) ) . Defined . 

Definition iscotranshqlth ( n m k : hq ) : hqlth n k -> hdisj ( hqlth n m ) ( hqlth m k ) . 
Proof . intros n m k lnk . apply ( ( pr1 islogeqcommhdisj ) ( iscotranshqgth _ _ _ lnk ) )  .  Defined .      



(**  [ hqleh ] *)


Definition  istranshqleh ( n m k : hq ) : hqleh n m -> hqleh m k -> hqleh n k .
Proof. apply istransnegrel . unfold iscotrans. apply iscotranshqgth .  Defined.   

Definition isreflhqleh ( n : hq ) : hqleh n n := isirreflhqgth n .  

Definition isantisymmhqleh ( n m : hq ) : hqleh n m -> hqleh m n -> paths n m := isantisymmneghqgth n m .   

Definition isnegrelhqleh : isnegrel hqleh .
Proof . apply isdecreltoisnegrel . apply isdecrelhqleh . Defined . 

Definition iscoasymmhqleh ( n m : hq ) ( nl : neg ( hqleh n m ) ) : hqleh m n := negf ( isasymmhqgth _ _ ) nl . 

Definition istotalhqleh : istotal hqleh . 
Proof . intros x y . destruct ( isdecrelhqleh x y ) as [ lxy | lyx ] . apply ( hinhpr _ ( ii1 lxy ) ) . apply hinhpr .   apply ii2 . apply ( iscoasymmhqleh _ _ lyx ) .   Defined . 



(**  [ hqgeh ] . *)


Definition istranshqgeh ( n m k : hq ) : hqgeh n m -> hqgeh m k -> hqgeh n k := fun gnm gmk => istranshqleh _ _ _ gmk gnm . 

Definition isreflhqgeh ( n : hq ) : hqgeh n n := isreflhqleh _ . 

Definition isantisymmhqgeh ( n m : hq ) : hqgeh n m -> hqgeh m n -> paths n m := fun gnm gmn => isantisymmhqleh _ _ gmn gnm . 

Definition isnegrelhqgeh : isnegrel hqgeh := fun n m => isnegrelhqleh m n . 

Definition iscoasymmhqgeh ( n m : hq ) ( nl : neg ( hqgeh n m ) ) : hqgeh m n := iscoasymmhqleh _ _ nl . 

Definition istotalhqgeh : istotal hqgeh := fun n m => istotalhqleh m n .




(** *** Simple implications between comparisons *)

Definition hqgthtogeh ( n m : hq ) : hqgth n m -> hqgeh n m .
Proof. intros n m g . apply iscoasymmhqgeh . apply ( todneg _ g ) . Defined .

Definition hqlthtoleh ( n m : hq ) : hqlth n m -> hqleh n m := hqgthtogeh _ _ . 

Definition hqlehtoneghqgth ( n m : hq ) : hqleh n m -> neg ( hqgth n m )  .
Proof. intros n m is is' . apply ( is is' ) .  Defined . 

Definition  hqgthtoneghqleh ( n m : hq ) : hqgth n m -> neg ( hqleh n m ) := fun g l  => hqlehtoneghqgth _ _ l g .   

Definition hqgehtoneghqlth ( n m : hq ) : hqgeh n m -> neg ( hqlth n m ) := fun gnm lnm => hqlehtoneghqgth _ _ gnm lnm . 

Definition hqlthtoneghqgeh ( n m : hq ) : hqlth n m -> neg ( hqgeh n m ) := fun gnm lnm => hqlehtoneghqgth _ _ lnm gnm .  

Definition neghqlehtogth ( n m : hq ) : neg ( hqleh n m ) -> hqgth n m := isnegrelhqgth n m .   

Definition neghqgehtolth ( n m : hq ) : neg ( hqgeh n m ) -> hqlth n m := isnegrelhqlth n m .

Definition neghqgthtoleh ( n m : hq ) : neg ( hqgth n m ) -> hqleh n m .
Proof . intros n m ng . destruct ( isdecrelhqleh n m ) as [ l | nl ] . apply l . destruct ( nl ng ) .  Defined . 

Definition neghqlthtogeh ( n m : hq ) : neg ( hqlth n m ) -> hqgeh n m := fun nl => neghqgthtoleh _ _ nl . 



(** *** Comparison alternatives *)


Definition hqgthorleh ( n m : hq ) : coprod ( hqgth n m ) ( hqleh n m ) .
Proof . intros . apply ( isdecrelhqgth n m ) .  Defined . 

Definition hqlthorgeh ( n m : hq ) : coprod ( hqlth n m ) ( hqgeh n m ) := hqgthorleh _ _ .

Definition hqneqchoice ( n m : hq ) ( ne : neg ( paths n m ) ) : coprod ( hqgth n m ) ( hqlth n m ) .
Proof . intros . destruct ( hqgthorleh n m ) as [ g | l ]  .  destruct ( hqlthorgeh n m ) as [ g' | l' ] . destruct ( isasymmhqgth _ _ g g' )  .  apply ( ii1 g ) . destruct ( hqlthorgeh n m ) as [ l' | g' ] . apply ( ii2 l' ) . destruct ( ne ( isantisymmhqleh _ _ l g' ) ) . Defined . 

Definition hqlehchoice ( n m : hq ) ( l : hqleh n m ) : coprod ( hqlth n m ) ( paths n m ) .
Proof .  intros . destruct ( hqlthorgeh n m ) as [ l' | g ] .   apply ( ii1 l' ) . apply ( ii2 ( isantisymmhqleh _ _ l g ) ) . Defined . 

Definition hqgehchoice ( n m : hq ) ( g : hqgeh n m ) : coprod ( hqgth n m ) ( paths n m ) .
Proof .  intros . destruct ( hqgthorleh n m ) as [ g' | l ] .  apply ( ii1 g' ) .  apply ( ii2 ( isantisymmhqleh _ _ l g ) ) .  Defined . 





(** *** Mixed transitivities *)



Lemma hqgthgehtrans ( n m k : hq ) : hqgth n m -> hqgeh m k -> hqgth n k .
Proof. intros n m k gnm gmk . destruct ( hqgehchoice m k gmk ) as [ g' | e ] . apply ( istranshqgth _ _ _ gnm g' ) .  rewrite e in gnm  .  apply gnm . Defined. 

Lemma hqgehgthtrans ( n m k : hq ) : hqgeh n m -> hqgth m k -> hqgth n k .
Proof. intros n m k gnm gmk . destruct ( hqgehchoice n m gnm ) as [ g' | e ] . apply ( istranshqgth _ _ _ g' gmk ) .  rewrite e .  apply gmk . Defined. 

Lemma hqlthlehtrans ( n m k : hq ) : hqlth n m -> hqleh m k -> hqlth n k .
Proof . intros n m k l1 l2 . apply ( hqgehgthtrans k m n l2 l1 ) . Defined . 

Lemma hqlehlthtrans ( n m k : hq ) : hqleh n m -> hqlth m k -> hqlth n k .
Proof . intros n m k l1 l2 . apply ( hqgthgehtrans k m n l2 l1 ) . Defined .




(** *** Addition and comparisons  *)



(** [ gth ] *)

Definition isrngaddhzgth : @isbinophrel hqaddabgr hqgth .
Proof . apply isrngaddfldfracgt . exact isirreflhzgth . Defined . 


Definition hqgthandplusl ( n m k : hq ) : hqgth n m -> hqgth ( k + n ) ( k + m ) := fun g => ( pr1 isrngaddhzgth ) n m k g . 

Definition hqgthandplusr ( n m k : hq ) : hqgth n m -> hqgth ( n + k ) ( m + k ) := fun g => ( pr2 isrngaddhzgth ) n m k g .

Definition hqgthandpluslinv  ( n m k : hq ) : hqgth ( k + n ) ( k + m ) -> hqgth n m  .
Proof. intros n m k g . set ( g' := hqgthandplusl _ _ ( - k ) g ) . clearbody g' . rewrite ( pathsinv0 ( hqplusassoc _ _ n ) ) in g' . rewrite ( pathsinv0 ( hqplusassoc _ _ m ) ) in g' .  rewrite ( hqlminus k ) in g' . rewrite ( hqplusl0 _ ) in g' .   rewrite ( hqplusl0 _ ) in g' . apply g' .  Defined .

Definition hqgthandplusrinv ( n m k : hq ) :  hqgth ( n + k ) ( m + k ) -> hqgth n m  . 
Proof. intros n m k l . rewrite ( hqpluscomm n k ) in l . rewrite ( hqpluscomm m k ) in l . apply ( hqgthandpluslinv _ _ _ l )  . Defined . 

Lemma hqgthsnn ( n : hq ) : hqgth ( n + 1 ) n . 
Proof . intro . set ( int := hqgthandplusl _ _ n ( ct ( hqgth , 1 , 0 ) ) ) . clearbody int . rewrite ( hqplusr0 n ) in int .   apply int . Defined . 


(** [ lth ] *)


Definition hqlthandplusl ( n m k : hq ) : hqlth n m -> hqlth ( k + n ) ( k + m )  := hqgthandplusl _ _ _ . 

Definition hqlthandplusr ( n m k : hq ) : hqlth n m -> hqlth ( n + k ) ( m + k ) := hqgthandplusr _ _ _ .

Definition hqlthandpluslinv  ( n m k : hq ) : hqlth ( k + n ) ( k + m ) -> hqlth n m := hqgthandpluslinv _ _ _ .

Definition hqlthandplusrinv ( n m k : hq ) :  hqlth ( n + k ) ( m + k ) -> hqlth n m := hqgthandplusrinv _ _ _ .

Definition hqlthnsn ( n : hq ) : hqlth n ( n + 1 ) := hqgthsnn n . 



(** [ leh ] *)


Definition hqlehandplusl ( n m k : hq ) : hqleh n m -> hqleh ( k + n ) ( k + m ) := negf ( hqgthandpluslinv n m k )  . 

Definition hqlehandplusr ( n m k : hq ) : hqleh n m -> hqleh ( n + k ) ( m + k ) := negf ( hqgthandplusrinv n m k )  . 

Definition hqlehandpluslinv  ( n m k : hq ) : hqleh ( k + n ) ( k + m ) -> hqleh n m := negf ( hqgthandplusl n m k )  .  

Definition hqlehandplusrinv ( n m k : hq ) :  hqleh ( n + k ) ( m + k ) -> hqleh n m :=  negf ( hqgthandplusr n m k ) . 



(** [ geh ] *)


Definition hqgehandplusl ( n m k : hq ) : hqgeh n m -> hqgeh ( k + n ) ( k + m ) := negf ( hqgthandpluslinv m n k ) .  

Definition hqgehandplusr ( n m k : hq ) : hqgeh n m -> hqgeh ( n + k ) ( m + k ) := negf ( hqgthandplusrinv m n k )  . 

Definition hqgehandpluslinv  ( n m k : hq ) : hqgeh ( k + n ) ( k + m ) -> hqgeh n m := negf ( hqgthandplusl m n k )  . 

Definition hqgehandplusrinv ( n m k : hq ) :  hqgeh ( n + k ) ( m + k ) -> hqgeh n m :=  negf ( hqgthandplusr m n k ) . 



(** *** Properties of [ hqgth ] in the terminology of  algebra1.v *)


Definition isplushrelhqgth : @isbinophrel hqaddabgr hqgth := isrngaddhzgth . 

Lemma isinvplushrelhqgth : @isinvbinophrel hqaddabgr hqgth . 
Proof . split . apply  hqgthandpluslinv .  apply hqgthandplusrinv .  Defined . 

Lemma isrngmulthqgth : isrngmultgt _ hqgth .
Proof . apply  isrngmultfldfracgt .  exact isirreflhzgth .  Defined .  

Lemma  isinvrngmulthqgth : isinvrngmultgt _ hqgth .
Proof . apply isinvrngmultgtif .  apply isplushrelhqgth .  apply isrngmulthqgth . exact hqneqchoice . exact isasymmhqgth . Defined . 



(** *** Negation and comparisons *)

(** [ hqgth ] *)

Lemma hqgth0andminus { n : hq } ( is : hqgth n 0 ) : hqlth ( - n ) 0 .
Proof . intros . unfold hqlth . apply ( rngfromgt0 hq isplushrelhqgth is ) .  Defined . 

Lemma hqminusandgth0 { n : hq } ( is : hqgth ( - n ) 0 ) : hqlth n 0 .
Proof . intros . unfold hqlth . apply ( rngtolt0 hq isplushrelhqgth is ) .  Defined . 


(** [ hqlth ] *)

Lemma hqlth0andminus { n : hq } ( is : hqlth n 0 ) : hqgth ( - n ) 0 .
Proof . intros .  unfold hqlth . apply ( rngfromlt0 hq isplushrelhqgth is ) .  Defined . 

Lemma hqminusandlth0 { n : hq } ( is : hqlth ( - n ) 0 ) : hqgth n 0 .
Proof . intros . unfold hqlth . apply ( rngtogt0 hq isplushrelhqgth is ) .  Defined .
 
(* ??? Coq slows down for no good reason at Defined in the previous four lemmas. *)

(** [ hqleh ] *)

Lemma hqleh0andminus { n : hq } ( is : hqleh n 0 ) : hqgeh ( - n ) 0 .
Proof . intro n . apply ( negf ( @hqminusandlth0 n ) ) . Defined .  

Lemma hqminusandleh0 { n : hq } ( is : hqleh ( - n ) 0 ) : hqgeh n 0 .
Proof . intro n . apply ( negf ( @hqlth0andminus n ) ) . Defined .  



(** [ hqgeh ] *)

Lemma hqgeh0andminus { n : hq } ( is : hqgeh n 0 ) : hqleh ( - n ) 0 .
Proof . intro n . apply ( negf ( @hqminusandgth0 n ) ) . Defined .  

Lemma hqminusandgeh0 { n : hq } ( is : hqgeh ( - n ) 0 ) : hqleh n 0 .
Proof . intro n . apply ( negf ( @hqgth0andminus n ) ) . Defined .  


(** *** Multiplication and comparisons  *)


(** [ gth ] *)
 

Definition hqgthandmultl ( n m k : hq ) ( is : hqgth k hqzero ) : hqgth n m -> hqgth ( k * n ) ( k * m ) .
Proof. apply ( isrngmultgttoislrngmultgt _ isplushrelhqgth isrngmulthqgth ) .   Defined . 

Definition hqgthandmultr ( n m k : hq ) ( is : hqgth k hqzero ) : hqgth n m -> hqgth ( n * k ) ( m * k )  .
Proof . apply ( isrngmultgttoisrrngmultgt _ isplushrelhqgth isrngmulthqgth ) . Defined .

Definition  hqgthandmultlinv ( n m k : hq ) ( is : hqgth k hqzero ) : hqgth ( k * n ) ( k * m ) -> hqgth n m .
Proof . intros n m k is is' .  apply ( isinvrngmultgttoislinvrngmultgt hq isplushrelhqgth isinvrngmulthqgth n m k is is' ) .  Defined . 

Definition hqgthandmultrinv ( n m k : hq ) ( is : hqgth k hqzero ) : hqgth ( n * k ) ( m * k ) -> hqgth n m .
Proof.   intros n m k is is' .  apply ( isinvrngmultgttoisrinvrngmultgt hq isplushrelhqgth isinvrngmulthqgth n m k is is' ) .  Defined . 



(** [ lth ] *)


Definition hqlthandmultl ( n m k : hq ) ( is : hqgth k 0 ) : hqlth n m -> hqlth ( k * n ) ( k * m )  := hqgthandmultl _ _ _ is .

Definition hqlthandmultr ( n m k : hq ) ( is : hqgth k 0 ) : hqlth n m -> hqlth ( n * k ) ( m * k ) := hqgthandmultr _ _ _ is .

Definition hqlthandmultlinv ( n m k : hq ) ( is : hqgth k 0 ) : hqlth ( k * n ) ( k * m ) -> hqlth n m := hqgthandmultlinv _ _ _ is .

Definition hqlthandmultrinv ( n m k : hq ) ( is : hqgth k 0 ) : hqlth ( n * k ) ( m * k ) -> hqlth n m := hqgthandmultrinv _ _ _ is .


(** [ leh ] *)


Definition hqlehandmultl ( n m k : hq ) ( is : hqgth k 0 ) : hqleh n m -> hqleh ( k * n ) ( k * m ) := negf ( hqgthandmultlinv _ _ _ is ) .

Definition hqlehandmultr ( n m k : hq ) ( is : hqgth k 0 ) : hqleh n m -> hqleh ( n * k ) ( m * k ) := negf ( hqgthandmultrinv _ _ _ is ) .

Definition hqlehandmultlinv ( n m k : hq ) ( is : hqgth k 0 ) : hqleh ( k * n ) ( k * m ) -> hqleh n m := negf ( hqgthandmultl _ _ _ is )  .

Definition hqlehandmultrinv ( n m k : hq ) ( is : hqgth k 0 ) : hqleh ( n * k ) ( m * k ) -> hqleh n m := negf ( hqgthandmultr _ _ _ is ) .


(** [ geh ] *)


Definition hqgehandmultl ( n m k : hq ) ( is : hqgth k 0 ) : hqgeh n m -> hqgeh ( k * n ) ( k * m ) := negf ( hqgthandmultlinv _ _ _ is ) .

Definition hqgehandmultr ( n m k : hq ) ( is : hqgth k 0 ) : hqgeh n m -> hqgeh ( n * k ) ( m * k )  := negf ( hqgthandmultrinv _ _ _ is ) .

Definition hqgehandmultlinv ( n m k : hq ) ( is : hqgth k 0 ) : hqgeh ( k * n ) ( k * m ) -> hqgeh n m := negf ( hqgthandmultl _ _ _ is )   .

Definition hqgehandmultrinv ( n m k : hq ) ( is : hqgth k 0 ) : hqgeh ( n * k ) ( m * k ) -> hqgeh n m := negf ( hqgthandmultr _ _ _ is )  .








(** Multiplication of positive with negative, negative with positive and two negatives. *)


Lemma hqmultgth0gth0 { m n : hq } ( ism : hqgth m 0 ) ( isn : hqgth n 0 ) : hqgth ( m * n ) 0 .
Proof . intros . apply isrngmulthqgth . apply ism . apply isn . Defined .  

Lemma hqmultgth0geh0 { m n : hq } ( ism : hqgth m 0 ) ( isn : hqgeh n 0 ) : hqgeh ( m * n ) 0 .
Proof . intros .  destruct ( hqgehchoice _ _ isn ) as [ gn | en ] . 

apply ( hqgthtogeh _ _ ( hqmultgth0gth0  ism gn ) ) . 

rewrite en .  rewrite ( hqmultx0 m ) . apply isreflhqgeh . Defined .


Lemma hqmultgeh0gth0 { m n : hq } ( ism : hqgeh m 0 ) ( isn : hqgth n 0 ) : hqgeh ( m * n ) 0 .
Proof .  intros .  destruct ( hqgehchoice _ _ ism ) as [ gm | em ] . 

apply ( hqgthtogeh _ _ ( hqmultgth0gth0 gm isn ) ) . 

rewrite em .  rewrite ( hqmult0x _ ) . apply isreflhqgeh . Defined .
 

Lemma hqmultgeh0geh0 { m n : hq } ( ism : hqgeh m 0 ) ( isn : hqgeh n 0 ) : hqgeh ( m * n ) 0 .
Proof . intros .   destruct ( hqgehchoice _ _ isn ) as [ gn | en ] . 

apply ( hqmultgeh0gth0 ism gn ) . 

rewrite en .  rewrite ( hqmultx0 m ) . apply isreflhqgeh . Defined .


Lemma hqmultgth0lth0 { m n : hq } ( ism : hqgth m 0 ) ( isn : hqlth n 0 ) : hqlth ( m * n ) 0 .
Proof . intros . apply ( rngmultgt0lt0 hq isplushrelhqgth isrngmulthqgth ) . apply ism . apply isn . Defined .  

Lemma hqmultgth0leh0 { m n : hq } ( ism : hqgth m 0 ) ( isn : hqleh n 0 ) : hqleh ( m * n ) 0 .
Proof . intros .  destruct ( hqlehchoice _ _ isn ) as [ ln | en ] . 

apply ( hqlthtoleh _ _ ( hqmultgth0lth0  ism ln ) ) . 

rewrite en .  rewrite ( hqmultx0 m ) . apply isreflhqleh . Defined .

Lemma hqmultgeh0lth0 { m n : hq } ( ism : hqgeh m 0 ) ( isn : hqlth n 0 ) : hqleh ( m * n ) 0 .
Proof .  intros .  destruct ( hqlehchoice _ _ ism ) as [ lm | em ] . 

apply ( hqlthtoleh _ _ ( hqmultgth0lth0 lm isn ) ) . 

destruct em .  rewrite ( hqmult0x _ ) . apply isreflhqleh . Defined .

Lemma hqmultgeh0leh0 { m n : hq } ( ism : hqgeh m 0 ) ( isn : hqleh n 0 ) : hqleh ( m * n ) 0 .
Proof . intros .   destruct ( hqlehchoice _ _ isn ) as [ ln | en ] . 

apply ( hqmultgeh0lth0 ism ln ) . 

rewrite en .  rewrite ( hqmultx0 m ) . apply isreflhqleh . Defined .



Lemma hqmultlth0gth0 { m n : hq } ( ism : hqlth m 0 ) ( isn : hqgth n 0 ) : hqlth ( m * n ) 0 .
Proof . intros . rewrite ( hqmultcomm ) .  apply hqmultgth0lth0 . apply isn . apply ism .  Defined .  

Lemma hqmultlth0geh0 { m n : hq } ( ism : hqlth m 0 ) ( isn : hqgeh n 0 ) : hqleh ( m * n ) 0 .
Proof . intros . rewrite ( hqmultcomm ) .  apply hqmultgeh0lth0 . apply isn . apply ism .  Defined .  


Lemma hqmultleh0gth0 { m n : hq } ( ism : hqleh m 0 ) ( isn : hqgth n 0 ) : hqleh ( m * n ) 0 .
Proof . intros . rewrite ( hqmultcomm ) .  apply hqmultgth0leh0 . apply isn . apply ism .  Defined .  


Lemma hqmultleh0geh0 { m n : hq } ( ism : hqleh m 0 ) ( isn : hqgeh n 0 ) : hqleh ( m * n ) 0 .
Proof . intros . rewrite ( hqmultcomm ) .  apply hqmultgeh0leh0 . apply isn . apply ism .  Defined .  


Lemma hqmultlth0lth0 { m n : hq } ( ism : hqlth m 0 ) ( isn : hqlth n 0 ) : hqgth ( m * n ) 0 .
Proof . intros . assert ( ism' := hqlth0andminus ism ) .  assert ( isn' := hqlth0andminus isn ) . assert ( int := isrngmulthqgth _ _ ism' isn' ) . rewrite ( rngmultminusminus hq ) in int .  apply int . Defined . 

Lemma hqmultlth0leh0 { m n : hq } ( ism : hqlth m 0 ) ( isn : hqleh n 0 ) : hqgeh ( m * n ) 0 .
Proof . intros . intros .  destruct ( hqlehchoice _ _ isn ) as [ ln | en ] . 

apply ( hqgthtogeh _ _ ( hqmultlth0lth0  ism ln ) ) . 

rewrite en .  rewrite ( hqmultx0 m ) . apply isreflhqgeh . Defined .

Lemma hqmultleh0lth0 { m n : hq } ( ism : hqleh m 0 ) ( isn : hqlth n 0 ) : hqgeh ( m * n ) 0 .
Proof . intros . destruct ( hqlehchoice _ _ ism ) as [ lm | em ] . 

apply ( hqgthtogeh _ _ ( hqmultlth0lth0 lm isn ) ) . 

rewrite em .  rewrite ( hqmult0x _ ) . apply isreflhqgeh .  Defined .
 
Lemma hqmultleh0leh0 { m n : hq } ( ism : hqleh m 0 ) ( isn : hqleh n 0 ) : hqgeh ( m * n ) 0 .
Proof . intros .  destruct ( hqlehchoice _ _ isn ) as [ ln | en ] . 

apply ( hqmultleh0lth0 ism ln ) . 

rewrite en .  rewrite ( hqmultx0 m ) . apply isreflhqgeh .   Defined .



(** *** Cancellation properties of multiplication on [ hq ] *)

Lemma hqmultlcan ( a b c : hq ) ( ne : neg ( paths c 0 ) ) ( e : paths ( c * a ) ( c * b ) ) : paths a b .
Proof . intros . apply ( intdomlcan hq _ _ _ ne e ) . Defined .

Lemma hqmultrcan ( a b c : hq ) ( ne : neg ( paths c 0 ) ) ( e : paths ( a * c ) ( b * c ) ) : paths a b .
Proof . intros . apply ( intdomrcan hq _ _ _ ne e ) . Defined .

 


(** *** Positive rationals *)

Definition hqpos : @subabmonoids hqmultabmonoid . 
Proof . split with ( fun x => hqgth x 0 ) . split .  intros x1 x2 . apply ( isrngmulthqgth ) . apply ( pr2 x1 ) .  apply ( pr2 x2 ) .  apply ( ct ( hqgth , 1 , 0 ) ) . Defined . 


(** *** Canonical ring homomorphism from [ hz ] to [ hq ] *)

Definition hztohq : hz -> hq := tofldfrac hzintdom isdeceqhz.

Definition isinclhztohq : isincl hztohq := isincltofldfrac hzintdom isdeceqhz . 

Definition hztohqandneq ( n m : hz ) ( is : hzneq n m ) : hqneq ( hztohq n ) ( hztohq m ) := negf ( invmaponpathsincl _ isinclhztohq n m ) is . 

Definition hztohqand0 : paths ( hztohq 0%hz ) 0 := idpath _ . 

Definition hztohqand1 : paths ( hztohq 1%hz ) 1 := idpath _ . 

Definition hztohqandplus ( n m : hz ) : paths ( hztohq ( n + m )%hz ) ( hztohq n + hztohq m ) := isbinop1funtofldfrac hzintdom isdeceqhz n m .

Definition hztohqandminus ( n m : hz ) : paths ( hztohq ( n - m )%hz ) ( hztohq n - hztohq m ) := tofldfracandminus hzintdom isdeceqhz n m . 

Definition hztohqandmult ( n m : hz ) : paths ( hztohq ( n * m )%hz ) ( hztohq n * hztohq m ) := isbinop2funtofldfrac hzintdom isdeceqhz n m . 

Definition hztohqandgth ( n m : hz ) ( is : hzgth n m ) : hqgth ( hztohq n ) ( hztohq m ) := iscomptofldfrac hzintdom isdeceqhz isplushrelhzgth isrngmulthzgth ( ct ( hzgth , 1 , 0 )%hz ) ( hzneqchoice ) ( isasymmhzgth ) n m is . 

Definition hztohqandlth ( n m : hz ) ( is : hzlth n m ) : hqlth ( hztohq n ) ( hztohq m ) := hztohqandgth m n is . 

Definition hztohqandleh ( n m : hz ) ( is : hzleh n m ) : hqleh ( hztohq n ) ( hztohq m ) .
Proof . intros . destruct ( hzlehchoice _ _ is ) as [ l | e ] .   apply ( hqlthtoleh _ _ ( hztohqandlth _ _ l ) ) .  rewrite e .  apply ( isreflhqleh ) .  Defined . 

Definition hztohqandgeh ( n m : hz ) ( is : hzgeh n m ) : hqgeh ( hztohq n ) ( hztohq m ) := hztohqandleh _ _ is . 




(** *** Integral part of a rational *)

Definition intpartint0 ( xa : dirprod hz ( intdomnonzerosubmonoid hzintdom ) ) : nat := natdiv ( hzabsval (pr1 xa ) ) ( hzabsval ( pr1 ( pr2 xa ) ) )  .

Lemma iscompintpartint0 : iscomprelfun ( eqrelabmonoidfrac hzmultabmonoid ( intdomnonzerosubmonoid hzintdom ) ) intpartint0 .
Proof . Opaque hq.  unfold iscomprelfun .  intros xa1 xa2 .  set ( x1 := pr1 xa1 ) . set ( aa1 := pr2 xa1 ) . set ( a1 := pr1 aa1 ) .  set ( x2 := pr1 xa2 ) . set ( aa2 := pr2 xa2 ) . set ( a2 := pr1 aa2 ) . simpl .  apply ( @hinhuniv _ ( hProppair _ ( setproperty natset _ _ ) ) ) .  intro t2 .  assert ( e := pr2 t2 ) . 

simpl in e .  assert ( e' := ( maponpaths hzabsval ( hzmultrcan _ _ _ ( pr2 ( pr1 t2 ) ) e ) ) : paths ( hzabsval ( x1 * a2 )%hz ) ( hzabsval ( x2 * a1 )%hz ) ) .  clear e . clear t2 . rewrite ( pathsinv0 ( hzabsvalandmult _ _ ) ) in e' . rewrite ( pathsinv0 ( hzabsvalandmult _ _ ) ) in e' .

unfold intpartint0 . simpl .  change ( paths ( natdiv ( hzabsval x1 ) ( hzabsval a1 ) ) ( natdiv ( hzabsval x2 ) ( hzabsval a2 ) ) ) . rewrite ( pathsinv0 ( natdivandmultr (hzabsval x1 ) (hzabsval a1 ) ( hzabsval a2 ) ( hzabsvalneq0  ( pr2 aa1 ) ) ( natneq0andmult _ _ ( hzabsvalneq0 (pr2 aa1) ) ( hzabsvalneq0  (pr2 aa2) ) ) ) ) .   rewrite ( pathsinv0 ( natdivandmultr (hzabsval x2 ) (hzabsval a2 ) ( hzabsval a1 ) ( hzabsvalneq0  ( pr2 aa2 ) ) ( natneq0andmult _ _ ( hzabsvalneq0 (pr2 aa2) ) ( hzabsvalneq0  (pr2 aa1) ) ) ) ) .  rewrite ( natmultcomm ( hzabsval a1 ) ( hzabsval a2 ) ) .  rewrite e' . apply idpath . Transparent hq .  Defined .  

Opaque iscompintpartint0 .

Definition intpart0 : hq -> nat := setquotuniv _ _ _ ( iscompintpartint0 ) .   

Definition intpart ( x : hq ) : hz .
Proof . intro . destruct ( hqlthorgeh x 0 ) as [ l | ge ] .  destruct ( isdeceqhq ( x + ( hztohq ( nattohz ( intpart0 x ) ) ) ) 0 ) as [ e | ne ] . 

apply ( - (nattohz (intpart0 x)))%hz . 

apply ( - ( 1 + (nattohz (intpart0 x)) ) )%hz .

apply (nattohz (intpart0 x)) . Defined .


(** Computation test *)

Transparent hz .

Eval lazy in ( hzabsval ( intpart ( hqdiv ( hztohq ( nattohz ( 10 ) ) )  ( - ( 1 + 1 + 1 ) ) ) ) ) . 


Opaque hz . 







   



(* End of the file hq.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)


  