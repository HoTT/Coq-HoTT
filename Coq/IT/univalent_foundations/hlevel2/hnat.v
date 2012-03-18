(** * Natural numbers and their properties. Vladimir Voevodsky . Apr. - Sep. 2011  

This file contains the formulations and proofs of general properties of natural numbers from the univalent perspecive. *)






(** ** Preambule *)

(** Settings *)

Add Rec LoadPath "../Generalities".
Add Rec LoadPath "../hlevel1".
Add Rec LoadPath "../hlevel2".

Unset Automatic Introduction. (* This line has to be removed for the file to compile with Coq8.2 *)



(** Imports. *)

Require Export algebra1d . 

(** To up-stream files  *)



(** ** Equality on [ nat ] *)


(** *** Basic properties of [ paths ] on [ nat ] and the proofs of [ isdeceq ] and [ isaset ] for [ nat ] .  *) 
   

Lemma negpaths0sx ( x : nat ) : neg ( paths O (S x) ) .
Proof. intro. set (f:= fun n : nat => match n with O => true | S m => false end ) . apply ( negf ( @maponpaths _ _ f 0 ( S x ) ) nopathstruetofalse ) . Defined. 

Lemma negpathssx0 ( x : nat ) : neg ( paths (S x) O ) .
Proof. intros x X. apply (negpaths0sx x (pathsinv0  X)). Defined. 

Lemma invmaponpathsS ( n m : nat ) : paths ( S n ) ( S m ) -> paths n m .
Proof. intros n m e . set ( f := fun n : nat => match n with O => O | S m => m end ) .   apply ( @maponpaths _ _ f ( S n ) ( S m ) e ) .  Defined.  

Lemma noeqinjS ( x x' : nat ) : neg ( paths x x' ) -> neg ( paths (S x) (S x') ) .
Proof. intros x x'. apply ( negf ( invmaponpathsS x x' ) ) .  Defined. 
 
Definition isdeceqnat: isdeceq nat.
Proof. unfold isdeceq.  intro x . induction x as [ | x IHx ] . intro x' .  destruct x'. apply ( ii1  ( idpath O ) ) . apply ( ii2  ( negpaths0sx x' ) ) . intro x' .  destruct x'.  apply ( ii2  (negpathssx0 x ) ) . destruct ( IHx x' ) as [ p | e ].   apply ( ii1 ( maponpaths S  p ) ) .  apply ( ii2 ( noeqinjS  _ _ e ) ) . Defined . 

Definition isisolatedn ( n : nat ) : isisolated _ n .
Proof. intro. unfold isisolated . intro x' . apply isdeceqnat . Defined. 

Theorem isasetnat: isaset nat.
Proof.  apply (isasetifdeceq _ isdeceqnat). Defined. 

Definition natset : hSet := hSetpair _ isasetnat . 
Canonical Structure natset . 

Definition nateq ( x y : nat ) : hProp := hProppair ( paths x y ) ( isasetnat _ _  )  .
Definition isdecrelnateq : isdecrel nateq  := fun a b => isdeceqnat a b .
Definition natdeceq : decrel nat := decrelpair isdecrelnateq . 
Canonical Structure natdeceq. 

Definition natbooleq := decreltobrel natdeceq .  

Definition natneq ( x y : nat ) : hProp := hProppair ( neg ( paths x y ) ) ( isapropneg _  )  .
Definition isdecrelnatneq : isdecrel natneq  := isdecnegrel _ isdecrelnateq . 
Definition natdecneq : decrel nat := decrelpair isdecrelnatneq . 
Canonical Structure natdecneq.  

Definition natboolneq := decreltobrel natdecneq .  

(** *** [ S : nat -> nat ] is a decidable inclusion . *)

Theorem isinclS : isincl S .
Proof. apply ( isinclbetweensets S isasetnat isasetnat invmaponpathsS ) .  Defined .

Theorem isdecinclS : isdecincl S .
Proof. intro n . apply isdecpropif . apply ( isinclS n ) .  destruct n as [ | n ] .  assert ( nh : neg ( hfiber S 0 ) ) .  intro hf .  destruct hf as [ m e ] .  apply ( negpathssx0 _ e ) .  apply ( ii2 nh ) .  apply ( ii1 ( hfiberpair _ n ( idpath _ ) ) ) .  Defined . 


(** ** Inequalities on [ nat ] . *)


(** *** Boolean "less or equal" and "greater or equal" on [ nat ] . *)

Fixpoint natgtb (n m : nat) : bool :=
match n , m with
 | S n , S m => natgtb n m
 | O, _ => false
 | _, _ => true
end.



(** *** Semi-boolean "greater" on [ nat ] or [ natgth ]  

1. Note that due to its definition [ natgth ] automatically has the property that [ natgth n m <-> natgth ( S n ) ( S m ) ] and the same applies to all other inequalities defined in this section.
2. We choose "greater" as the root relation from which we define all other relations on [ nat ] because it is more natural to extend "greater" to integers and then to rationals than it is to extend "less".   *) 


Definition natgth ( n m : nat ) := hProppair ( paths ( natgtb n m ) true ) ( isasetbool _ _ ) . 

Lemma negnatgth0n ( n : nat ) : neg ( natgth 0 n ) .
Proof. intro n . simpl . intro np . apply ( nopathsfalsetotrue np ) .  Defined . 

Lemma natgthsnn ( n : nat ) : natgth ( S n ) n .
Proof . intro . induction n as [ | n IHn ] . simpl . apply idpath .   apply IHn . Defined .

Lemma natgthsn0 ( n : nat ) : natgth ( S n ) 0 .
Proof . intro . simpl . apply idpath .  Defined . 

Lemma negnatgth0tois0 ( n : nat ) ( ng : neg ( natgth n 0 ) ) : paths n 0 .
Proof . intro. destruct n as [ | n ] . intro.   apply idpath.  intro ng .  destruct ( ng ( natgthsn0 _ ) ) . Defined . 

Lemma natneq0togth0 ( n : nat ) ( ne : neg ( paths n 0 ) ) : natgth n 0 .
Proof . intros . destruct n as [ | n ] . destruct ( ne ( idpath _ ) ) .  apply natgthsn0 .  Defined . 

Lemma nat1gthtois0 ( n : nat ) ( g : natgth 1 n ) : paths n 0 .
Proof . intro . destruct n as [ | n ] . intro . apply idpath . intro x .  destruct ( negnatgth0n n x ) .  Defined .

Lemma istransnatgth ( n m k : nat ) : natgth n m -> natgth m k -> natgth n k .
Proof. intro. induction n as [ | n IHn ] . intros m k g . destruct ( negnatgth0n _ g ) .  intro m . destruct m as [ | m ] . intros k g g' . destruct ( negnatgth0n _ g' ) . intro k . destruct k as [ | k ] . intros . apply natgthsn0 . apply ( IHn m k ) .  Defined. 

Lemma isirreflnatgth ( n : nat ) : neg ( natgth n n ) .
Proof. intro . induction n as [ | n IHn ] . apply ( negnatgth0n 0 ) .  apply IHn .  Defined . 

Lemma natgthtoneq ( n m : nat ) ( g : natgth n m ) : neg ( paths n m ) .
Proof . intros . intro e . rewrite e in g . apply ( isirreflnatgth _ g ) . Defined .  

Lemma isasymmnatgth ( n m : nat ) : natgth n m -> natgth m n -> empty .
Proof. intros n m is is' . apply ( isirreflnatgth n ( istransnatgth _ _ _ is is' ) ) . Defined .  

Lemma isantisymmnegnatgth ( n m : nat ) : neg ( natgth n m ) -> neg ( natgth m n ) -> paths n m .
Proof . intro n . induction n as [ | n IHn ] . intros m ng0m ngm0  .  apply ( pathsinv0 ( negnatgth0tois0 _ ngm0 ) ) . intro m . destruct m as [ | m ] . intros ngsn0 ng0sn . destruct ( ngsn0 ( natgthsn0 _ ) ) .  intros ng1 ng2 .   apply ( maponpaths S ( IHn m ng1 ng2 ) ) .  Defined .     

Lemma isdecrelnatgth : isdecrel natgth .
Proof. intros n m . apply ( isdeceqbool ( natgtb n m ) true ) .  Defined .

Definition natgthdec := decrelpair isdecrelnatgth .
Canonical Structure natgthdec .

Lemma isnegrelnatgth : isnegrel natgth .
Proof . apply isdecreltoisnegrel . apply isdecrelnatgth . Defined . 

Lemma iscoantisymmnatgth ( n m : nat ) : neg ( natgth n m ) -> coprod ( natgth m n ) ( paths n m ) .
Proof . apply isantisymmnegtoiscoantisymm . apply isdecrelnatgth .  intros n m . apply isantisymmnegnatgth . Defined .  

Lemma iscotransnatgth ( n m k : nat ) : natgth n k -> hdisj ( natgth n m ) ( natgth m k ) .
Proof . intros x y z gxz .  destruct ( isdecrelnatgth x y ) as [ gxy | ngxy ] . apply ( hinhpr _ ( ii1 gxy ) ) . apply hinhpr .   apply ii2 .  destruct ( isdecrelnatgth y x ) as [ gyx | ngyx ] . apply ( istransnatgth _ _ _ gyx gxz ) .  set ( e := isantisymmnegnatgth _ _ ngxy ngyx ) . rewrite e in gxz .  apply gxz .  Defined .   




(** *** Semi-boolean "less" on [ nat ] or [ natlth ] *)

Definition natlth ( n m : nat ) := natgth m n .

Definition negnatlthn0 ( n : nat ) : neg ( natlth n 0 ) := negnatgth0n n .

Definition natlthnsn ( n : nat ) : natlth n ( S n ) := natgthsnn n . 

Definition negnat0lthtois0 ( n : nat ) ( nl : neg ( natlth 0 n ) ) : paths n 0 := negnatgth0tois0 n nl .

Definition natneq0to0lth ( n : nat ) ( ne : neg ( paths n 0 ) ) : natlth 0 n := natneq0togth0 n ne .

Definition natlth1tois0 ( n : nat ) ( l : natlth n 1 ) : paths n 0 := nat1gthtois0 _ l . 

Definition istransnatlth ( n m k  : nat ) : natlth n m -> natlth m k -> natlth n k := fun lnm lmk => istransnatgth _ _ _ lmk lnm . 

Definition isirreflnatlth ( n : nat ) : neg ( natlth n n ) := isirreflnatgth n . 

Lemma natlthtoneq ( n m : nat ) ( g : natlth n m ) : neg ( paths n m ) .
Proof . intros . intro e . rewrite e in g . apply ( isirreflnatlth _ g ) . Defined .   

Definition isasymmnatlth ( n m : nat ) : natlth n m -> natlth m n -> empty := fun lnm lmn => isasymmnatgth _ _ lmn lnm .

Definition isantisymmnegnattth  ( n m : nat ) : neg ( natlth n m ) -> neg ( natlth m n ) -> paths n m := fun nlnm nlmn => isantisymmnegnatgth _ _ nlmn nlnm .

Definition isdecrelnatlth  : isdecrel natlth  := fun n m => isdecrelnatgth m n . 

Definition natlthdec := decrelpair isdecrelnatlth .
Canonical Structure natlthdec .

Definition isnegrelnatlth : isnegrel natlth := fun n m => isnegrelnatgth m n .

Definition iscoantisymmnatlth ( n m : nat ) : neg ( natlth n m ) -> coprod ( natlth m n ) ( paths n m ) .
Proof . intros n m nlnm . destruct ( iscoantisymmnatgth m n nlnm ) as [ l | e ] . apply ( ii1 l ) . apply ( ii2 ( pathsinv0 e ) ) . Defined . 

Definition iscotransnatlth ( n m k : nat ) : natlth n k -> hdisj ( natlth n m ) ( natlth m k ) . 
Proof . intros n m k lnk . apply ( ( pr1 islogeqcommhdisj ) ( iscotransnatgth _ _ _ lnk ) )  .  Defined .      



(** *** Semi-boolean "less or equal " on [ nat ] or [ natleh ] *)

Definition natleh ( n m : nat ) := hProppair ( neg ( natgth n m ) ) ( isapropneg _ )  .

Definition natleh0tois0 ( n : nat ) ( l : natleh n 0 ) : paths n 0 := negnatgth0tois0 _ l .

Definition natleh0n ( n : nat ) : natleh 0 n := negnatgth0n _ .

Definition negnatlehsn0 ( n : nat ) : neg ( natleh ( S n ) 0 ) := todneg _ ( natgthsn0 n ) . 

Definition negnatlehsnn ( n : nat ) : neg ( natleh ( S n ) n ) := todneg _ ( natgthsnn _ ) . 

Definition  istransnatleh ( n m k : nat ) : natleh n m -> natleh m k -> natleh n k .
Proof. apply istransnegrel . unfold iscotrans. apply iscotransnatgth .  Defined.   

Definition isreflnatleh ( n : nat ) : natleh n n := isirreflnatgth n .  

Definition isantisymmnatleh ( n m : nat ) : natleh n m -> natleh m n -> paths n m := isantisymmnegnatgth n m .   

Definition isdecrelnatleh : isdecrel natleh := isdecnegrel _ isdecrelnatgth . 

Definition natlehdec := decrelpair isdecrelnatleh .
Canonical Structure natlehdec .

Definition isnegrelnatleh : isnegrel natleh .
Proof . apply isdecreltoisnegrel . apply isdecrelnatleh . Defined . 

Definition iscoasymmnatleh ( n m : nat ) ( nl : neg ( natleh n m ) ) : natleh m n := negf ( isasymmnatgth _ _ ) nl . 

Definition istotalnatleh : istotal natleh . 
Proof . intros x y . destruct ( isdecrelnatleh x y ) as [ lxy | lyx ] . apply ( hinhpr _ ( ii1 lxy ) ) . apply hinhpr .   apply ii2 . apply ( iscoasymmnatleh _ _ lyx ) .   Defined . 



(** *** Semi-boolean "greater or equal" on [ nat ] or [ natgeh ] . *)


Definition natgeh ( n m : nat ) : hProp := hProppair ( neg ( natgth m n ) ) ( isapropneg _ ) .  

Definition nat0gehtois0 ( n : nat ) ( g : natgeh 0 n ) : paths n 0 := natleh0tois0 _ g . 

Definition natgehn0 ( n : nat ) : natgeh n 0 := natleh0n n .  

Definition negnatgeh0sn ( n : nat ) : neg ( natgeh 0 ( S n ) ) := negnatlehsn0 n . 

Definition negnatgehnsn ( n : nat ) : neg ( natgeh n ( S n ) ) := negnatlehsnn n . 

Definition istransnatgeh ( n m k : nat ) : natgeh n m -> natgeh m k -> natgeh n k := fun gnm gmk => istransnatleh _ _ _ gmk gnm . 

Definition isreflnatgeh ( n : nat ) : natgeh n n := isreflnatleh _ . 

Definition isantisymmnatgeh ( n m : nat ) : natgeh n m -> natgeh m n -> paths n m := fun gnm gmn => isantisymmnatleh _ _ gmn gnm . 

Definition isdecrelnatgeh : isdecrel natgeh := fun n m => isdecrelnatleh m n .

Definition natgehdec := decrelpair isdecrelnatgeh .
Canonical Structure natgehdec .

Definition isnegrelnatgeh : isnegrel natgeh := fun n m => isnegrelnatleh m n . 

Definition iscoasymmnatgeh ( n m : nat ) ( nl : neg ( natgeh n m ) ) : natgeh m n := iscoasymmnatleh _ _ nl . 

Definition istotalnatgeh : istotal natgeh := fun n m => istotalnatleh m n .




(** *** Simple implications between comparisons *)

Definition natgthtogeh ( n m : nat ) : natgth n m -> natgeh n m .
Proof. intros n m g . apply iscoasymmnatgeh . apply ( todneg _ g ) . Defined .

Definition natlthtoleh ( n m : nat ) : natlth n m -> natleh n m := natgthtogeh _ _ . 

Definition natlehtonegnatgth ( n m : nat ) : natleh n m -> neg ( natgth n m )  .
Proof. intros n m is is' . apply ( is is' ) .  Defined . 

Definition  natgthtonegnatleh ( n m : nat ) : natgth n m -> neg ( natleh n m ) := fun g l  => natlehtonegnatgth _ _ l g .   

Definition natgehtonegnatlth ( n m : nat ) : natgeh n m -> neg ( natlth n m ) := fun gnm lnm => natlehtonegnatgth _ _ gnm lnm . 

Definition natlthtonegnatgeh ( n m : nat ) : natlth n m -> neg ( natgeh n m ) := fun gnm lnm => natlehtonegnatgth _ _ lnm gnm .  

Definition negnatlehtogth ( n m : nat ) : neg ( natleh n m ) -> natgth n m := isnegrelnatgth n m .   

Definition negnatgehtolth ( n m : nat ) : neg ( natgeh n m ) -> natlth n m := isnegrelnatlth n m .

Definition negnatgthtoleh ( n m : nat ) : neg ( natgth n m ) -> natleh n m .
Proof . intros n m ng . destruct ( isdecrelnatleh n m ) as [ l | nl ] . apply l . destruct ( nl ng ) .  Defined . 

Definition negnatlthtogeh ( n m : nat ) : neg ( natlth n m ) -> natgeh n m := fun nl => negnatgthtoleh _ _ nl . 



(** *** Comparison alternatives *)


Definition natgthorleh ( n m : nat ) : coprod ( natgth n m ) ( natleh n m ) .
Proof . intros . apply ( isdecrelnatgth n m ) .  Defined . 

Definition natlthorgeh ( n m : nat ) : coprod ( natlth n m ) ( natgeh n m ) := natgthorleh _ _ .

Definition natneqchoice ( n m : nat ) ( ne : neg ( paths n m ) ) : coprod ( natgth n m ) ( natlth n m ) .
Proof . intros . destruct ( natgthorleh n m ) as [ l | g ]  .   apply ( ii1 l ) .  destruct ( natlthorgeh n m ) as [ l' | g' ] . apply ( ii2 l' ) .  destruct ( ne ( isantisymmnatleh _ _ g g' ) ) . Defined . 

Definition natlehchoice ( n m : nat ) ( l : natleh n m ) : coprod ( natlth n m ) ( paths n m ) .
Proof .  intros . destruct ( natlthorgeh n m ) as [ l' | g ] .  apply ( ii1 l' ) . apply ( ii2 ( isantisymmnatleh _ _ l g ) ) . Defined . 

Definition natgehchoice ( n m : nat ) ( g : natgeh n m ) : coprod ( natgth n m ) ( paths n m ) .
Proof .  intros . destruct ( natgthorleh n m ) as [ g' | l ] .  apply ( ii1 g' ) . apply ( ii2 ( isantisymmnatleh _ _ l g ) ) .  Defined . 




(** *** Mixed transitivities *)



Lemma natgthgehtrans ( n m k : nat ) : natgth n m -> natgeh m k -> natgth n k .
Proof. intros n m k gnm gmk . destruct ( natgehchoice m k gmk ) as [ g' | e ] . apply ( istransnatgth _ _ _ gnm g' ) .  rewrite e in gnm  .  apply gnm . Defined. 

Lemma natgehgthtrans ( n m k : nat ) : natgeh n m -> natgth m k -> natgth n k .
Proof. intros n m k gnm gmk . destruct ( natgehchoice n m gnm ) as [ g' | e ] . apply ( istransnatgth _ _ _ g' gmk ) .  rewrite e .  apply gmk . Defined. 

Lemma natlthlehtrans ( n m k : nat ) : natlth n m -> natleh m k -> natlth n k .
Proof . intros n m k l1 l2 . apply ( natgehgthtrans k m n l2 l1 ) . Defined . 

Lemma natlehlthtrans ( n m k : nat ) : natleh n m -> natlth m k -> natlth n k .
Proof . intros n m k l1 l2 . apply ( natgthgehtrans k m n l2 l1 ) . Defined . 



(** *** Two comparisons and [ S ] *)

Lemma natgthtogehsn ( n m : nat ) : natgth n m -> natgeh n ( S m ) .
Proof. intro n . induction n as [ | n IHn ] .  intros m X .  destruct ( negnatgth0n _ X ) . intros m X . destruct m as [ | m ] .  apply ( natgehn0 n ) .  apply ( IHn m X ) .  Defined . 

Lemma natlehsntolth ( n m : nat ) : natleh ( S n ) m -> natlth n m .
Proof.  intros n m X . apply ( natlthlehtrans _ _ _ ( natlthnsn n ) X ) .  Defined . 

Lemma natlthtolehsn ( n m : nat ) : natlth n m -> natleh ( S n ) m .
Proof. intros n m X . apply ( natgthtogehsn m n X ) . Defined .

Lemma natgehsntogth ( n m : nat ) : natgeh n ( S m ) -> natgth n m .
Proof. intros n m X . apply ( natlehsntolth m n X ) .  Defined .  


(** *** Comparsion alternatives and [ S ] *)


Lemma natlehchoice2 ( n m : nat ) : natleh n m -> coprod ( natleh ( S n ) m ) ( paths n m ) .
Proof . intros n m l . destruct ( natlehchoice n m l ) as [ l' | e ] .   apply ( ii1 ( natlthtolehsn _ _ l' ) ) . apply ( ii2 e ) .  Defined . 


Lemma natgehchoice2 ( n m : nat ) : natgeh n m -> coprod ( natgeh n ( S m ) ) ( paths n m ) .
Proof . intros n m g . destruct ( natgehchoice n m g ) as [ g' | e ] .   apply ( ii1 ( natgthtogehsn _ _ g' ) ) . apply ( ii2 e ) . Defined . 


Lemma natgthchoice2 ( n m : nat ) : natgth n m -> coprod ( natgth n ( S m ) ) ( paths n ( S m ) ) .
Proof.  intros n m g . destruct ( natgehchoice _ _ ( natgthtogehsn _ _ g ) ) as [ g' | e ] . apply ( ii1 g' ) .  apply ( ii2 e ) .  Defined . 


Lemma natlthchoice2 ( n m : nat ) : natlth n m -> coprod ( natlth ( S n ) m ) ( paths ( S n ) m ) .
Proof.  intros n m l . destruct ( natlehchoice _ _ ( natlthtolehsn _ _ l ) ) as [ l' | e ] . apply ( ii1 l' ) .  apply ( ii2 e ) .   Defined . 
   







(** ** Some properties of [ plus ] on [ nat ] 

Addition is defined in Init/Peano.v by the following code 

Fixpoint plus (n m:nat) : nat :=
  match n with
  | O => m
  | S p => S (p + m)
  end

where "n + m" := (plus n m) : nat_scope.
*)


(** *** The structure of the additive ablelian monoid on [ nat ] *) 


Lemma natplusl0 ( n : nat ) : paths ( 0 + n ) n .
Proof . intros . apply idpath . Defined .  

Lemma natplusr0 ( n : nat ) : paths ( n + 0 ) n .
Proof . intro . induction n as [ | n IH n ] . apply idpath .  simpl . apply ( maponpaths S IH ) . Defined .
Hint Resolve natplusr0: natarith .

Lemma natplusnsm ( n m : nat ) : paths ( n + S m ) ( S n + m ) .
Proof. intro . simpl . induction n as [ | n IHn ] .  auto with natarith . simpl . intro . apply ( maponpaths S ( IHn m ) ) .  Defined . 
Hint Resolve natplusnsm : natarith .

Lemma natpluscomm ( n m : nat ) : paths ( n + m ) ( m + n ) .
Proof. intro. induction n as [ | n IHn ] . intro . auto with natarith .  intro .  set ( int := IHn ( S m ) ) . set ( int2 := pathsinv0 ( natplusnsm n m ) ) . set ( int3 := pathsinv0 ( natplusnsm m n ) ) .  set ( int4 := pathscomp0 int2 int  ) .  apply ( pathscomp0 int4 int3 ) . Defined . 
Hint Resolve natpluscomm : natarith . 

Lemma natplusassoc ( n m k : nat ) : paths ( ( n + m ) + k ) ( n + ( m + k ) ) .
Proof . intro . induction n as [ | n IHn ] . auto with natarith . intros . simpl .  apply ( maponpaths S ( IHn m k ) ) . Defined. 
Hint Resolve natplusassoc : natarith .

Definition nataddabmonoid : abmonoid := abmonoidpair ( setwithbinoppair natset ( fun n m : nat => n + m ) ) ( dirprodpair ( dirprodpair natplusassoc ( @isunitalpair natset _ 0 ( dirprodpair natplusl0 natplusr0 ) ) ) natpluscomm ) .    




(** *** Addition and comparisons  *)



(** [ natgth ] *)



Definition natgthtogths ( n m : nat ) : natgth n m -> natgth ( S n ) m  .
Proof. intros n m is . apply ( istransnatgth _ _ _ ( natgthsnn n ) is ) . Defined .

Definition negnatgthmplusnm ( n m : nat ) : neg ( natgth m ( n + m ) ) .
Proof. intros . induction n as [ | n IHn ] .  apply isirreflnatgth . apply ( istransnatleh _ _ _ IHn ( ( natlthtoleh _ _ ( natlthnsn _ ) ) ) ) .  Defined . 

Definition negnatgthnplusnm ( n m : nat ) : neg ( natgth n ( n + m ) ) .
Proof. intros . rewrite ( natpluscomm n m ) .  apply ( negnatgthmplusnm m n ) .  Defined . 

Definition natgthandplusl ( n m k : nat ) : natgth n m -> natgth ( k + n ) ( k + m ) .
Proof. intros n m k l . induction k as [ | k IHk ] . assumption .  assumption .  Defined . 

Definition natgthandplusr ( n m k : nat ) : natgth n m -> natgth ( n + k ) ( m + k ) .
Proof. intros . rewrite ( natpluscomm n k ) . rewrite ( natpluscomm m k ) . apply natgthandplusl . assumption . Defined . 

Definition natgthandpluslinv  ( n m k : nat ) : natgth ( k + n ) ( k + m ) -> natgth n m  .
Proof. intros n m k l . induction k as [ | k IHk ] . assumption .  apply ( IHk l ) . Defined .

Definition natgthandplusrinv ( n m k : nat ) :  natgth ( n + k ) ( m + k ) -> natgth n m  . 
Proof. intros n m k l . rewrite ( natpluscomm n k ) in l . rewrite ( natpluscomm m k ) in l . apply ( natgthandpluslinv _ _ _ l )  . Defined . 
 

(** [ natlth ] *)


Definition natlthtolths ( n m : nat ) : natlth n m -> natlth n ( S m ) := natgthtogths _ _ . 

Definition negnatlthplusnmm ( n m : nat ) : neg ( natlth ( n + m ) m )  := negnatgthmplusnm _ _ .

Definition negnatlthplusnmn ( n m : nat ) : neg ( natlth ( n + m ) n )  := negnatgthnplusnm _ _ .

Definition natlthandplusl ( n m k : nat ) : natlth n m -> natlth ( k + n ) ( k + m )  := natgthandplusl _ _ _ . 

Definition natlthandplusr ( n m k : nat ) : natlth n m -> natlth ( n + k ) ( m + k ) := natgthandplusr _ _ _ .

Definition natlthandpluslinv  ( n m k : nat ) : natlth ( k + n ) ( k + m ) -> natlth n m := natgthandpluslinv _ _ _ .

Definition natlthandplusrinv ( n m k : nat ) :  natlth ( n + k ) ( m + k ) -> natlth n m := natgthandplusrinv _ _ _ . 



(** [ natleh ] *)


Definition natlehtolehs ( n m : nat ) : natleh n m -> natleh n ( S m ) .  
Proof . intros n m is . apply ( istransnatleh _ _ _ is ( natlthtoleh _ _ ( natlthnsn _ ) ) ) . Defined .

Definition natlehmplusnm ( n m : nat ) : natleh m ( n + m )  := negnatlthplusnmm _ _  .

Definition natlehnplusnm ( n m : nat ) : natleh n ( n + m ) := negnatlthplusnmn _ _  .

Definition natlehandplusl ( n m k : nat ) : natleh n m -> natleh ( k + n ) ( k + m ) := negf ( natgthandpluslinv n m k )  . 

Definition natlehandplusr ( n m k : nat ) : natleh n m -> natleh ( n + k ) ( m + k ) := negf ( natgthandplusrinv n m k )  . 

Definition natlehandpluslinv  ( n m k : nat ) : natleh ( k + n ) ( k + m ) -> natleh n m := negf ( natgthandplusl n m k )  .  

Definition natlehandplusrinv ( n m k : nat ) :  natleh ( n + k ) ( m + k ) -> natleh n m :=  negf ( natgthandplusr n m k ) . 




(** [ natgeh ] *)


Definition natgehtogehs ( n m : nat ) : natgeh n m -> natgeh ( S n ) m := natlehtolehs _ _  .
 
Definition natgehplusnmm ( n m : nat ) : natgeh ( n + m ) m := negnatgthmplusnm _ _ .

Definition natgehplusnmn ( n m : nat ) : natgeh ( n + m ) n := negnatgthnplusnm _ _  . 

Definition natgehandplusl ( n m k : nat ) : natgeh n m -> natgeh ( k + n ) ( k + m ) := negf ( natgthandpluslinv m n k ) .  

Definition natgehandplusr ( n m k : nat ) : natgeh n m -> natgeh ( n + k ) ( m + k ) := negf ( natgthandplusrinv m n k )  . 

Definition natgehandpluslinv  ( n m k : nat ) : natgeh ( k + n ) ( k + m ) -> natgeh n m := negf ( natgthandplusl m n k )  . 

Definition natgehandplusrinv ( n m k : nat ) :  natgeh ( n + k ) ( m + k ) -> natgeh n m :=  negf ( natgthandplusr m n k ) . 




(** *** Cancellation properties of [ plus ] on [ nat ] *)

Lemma pathsitertoplus ( n m : nat ) : paths ( iteration S n m ) ( n + m ) .
Proof. intros .  induction n as [ | n IHn ] . apply idpath . simpl .  apply ( maponpaths S IHn ) .  Defined .

Lemma isinclnatplusr ( n : nat ) : isincl ( fun m : nat => m + n ) .
Proof. intro . induction n as [ | n IHn ] . apply ( isofhlevelfhomot 1 _ _ ( fun m : nat => pathsinv0 ( natplusr0 m ) ) ) . apply ( isofhlevelfweq 1 ( idweq nat ) ) .  apply ( isofhlevelfhomot 1 _ _ ( fun m : nat => pathsinv0 ( natplusnsm m n ) ) ) . simpl .   apply ( isofhlevelfgf 1 _ _ isinclS IHn ) .  Defined. 

Lemma isinclnatplusl ( n : nat ) : isincl ( fun m : nat => n + m ) .
Proof. intro .  apply ( isofhlevelfhomot 1 _ _ ( fun m : nat => natpluscomm m n ) ( isinclnatplusr n ) ) . Defined . 

Lemma natplusrcan ( a b c : nat ) ( is : paths ( a + c ) ( b + c ) ) : paths a b .
Proof . intros . apply ( invmaponpathsincl _ ( isinclnatplusr c ) a b ) . apply is . Defined .  

Lemma natpluslcan ( a b c : nat ) ( is : paths ( c + a ) ( c + b ) ) : paths a b .
Proof . intros . rewrite ( natpluscomm _ _ ) in is . rewrite ( natpluscomm c b ) in is . apply ( natplusrcan a b c  is ) .  Defined .   


Lemma iscontrhfibernatplusr ( n m : nat ) ( is : natgeh m n ) : iscontr ( hfiber ( fun i : nat => i + n ) m ) .
Proof. intros . apply iscontraprop1 .    apply isinclnatplusr . induction m as [ | m IHm ] . set ( e := natleh0tois0 _ is ) .   split with 0 . apply e .  destruct ( natlehchoice2 _ _ is ) as [ l | e ] .  set ( j := IHm l ) .  destruct j as [ j e' ] . split with ( S j ) .  simpl . apply ( maponpaths S e' ) .  split with 0 . simpl .  assumption .  Defined . 

Lemma neghfibernatplusr ( n m : nat ) ( is : natlth m n ) : neg ( hfiber  ( fun i : nat => i + n ) m ) .
Proof. intros. intro h . destruct h as [ i e ] . rewrite ( pathsinv0 e )  in is . destruct ( natlehtonegnatgth _ _ ( natlehmplusnm i n ) is ) .  Defined .    

Lemma isdecinclnatplusr ( n : nat ) : isdecincl ( fun i : nat => i + n ) .
Proof. intros . intro m . apply isdecpropif . apply ( isinclnatplusr _ m ) . destruct ( natlthorgeh m n ) as [ ni | i ] .  apply ( ii2 ( neghfibernatplusr n m ni ) ) . apply ( ii1 ( pr1 ( iscontrhfibernatplusr n m i ) ) ) . Defined .  




(** *** Some properties of [ minus ] on [ nat ] 

Note : minus is defined in Init/Peano.v by the following code:

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O, _ => n
  | S k, O => n
  | S k, S l => k - l
  end

where "n - m" := (minus n m) : nat_scope.

*)

Lemma plusminusnmm ( n m : nat ) ( is : natgeh n m ) : paths ( ( n - m ) + m ) n .
Proof . intro n . induction n as [ | n IH n] . intro m . intro lh . simpl . apply ( natleh0tois0 _ lh ) . intro m . destruct m as [ | m ] . intro .   simpl . rewrite ( natplusr0 n ) .  apply idpath .  simpl . intro lh .  rewrite ( natplusnsm ( n - m ) m ) . apply ( maponpaths S ( IH m lh ) ) .  Defined . 




(** ** Some properties of [ mult ] on [ nat ] 

Note : multiplication is defined in Init/Peano.v by the following code:

Fixpoint mult (n m:nat) : nat :=
  match n with
  | O => 0
  | S p => m + p * m
  end

where "n * m" := (mult n m) : nat_scope.

*)

(** *** Basic algebraic properties of [ mult ] on [ nat ] *)

Lemma natmult0n ( n : nat ) : paths ( 0 * n ) 0 .
Proof. intro n . apply idpath . Defined . 
Hint Resolve natmult0n : natarith .

Lemma natmultn0 ( n : nat ) : paths ( n * 0 ) 0 .
Proof. intro n . induction n as [ | n IHn ] . apply idpath . simpl .   assumption .  Defined . 
Hint Resolve natmultn0 : natarith .

Lemma multsnm ( n m : nat ) : paths ( ( S n ) * m ) ( m + n * m ) .
Proof. intros . apply idpath . Defined .
Hint Resolve multsnm : natarith .

Lemma multnsm ( n m : nat ) : paths ( n * ( S m ) ) ( n + n * m ) .
Proof. intro n . induction n as [ | n IHn ] . intro .  simpl .  apply idpath .  intro m .  simpl . apply ( maponpaths S ) .  rewrite ( pathsinv0 ( natplusassoc n m ( n * m ) ) ) .  rewrite ( natpluscomm n m ) .  rewrite ( natplusassoc m n ( n * m ) ) .  apply ( maponpaths ( fun x : nat => m + x ) ( IHn m ) ) .  Defined . 
Hint Resolve multnsm : natarith .

Lemma natmultcomm ( n m : nat ) : paths ( n * m ) ( m * n ) .
Proof. intro . induction n as [ | n IHn ] . intro .  auto with natarith . intro m .  rewrite ( multsnm n m ) .  rewrite ( multnsm m n ) .  apply ( maponpaths ( fun x : _ => m + x ) ( IHn m ) ) .   Defined .

Lemma natrdistr ( n m k : nat ) : paths ( ( n + m ) * k ) ( n * k + m * k ) .
Proof . intros . induction n as [ | n IHn ] . auto with natarith .   simpl . rewrite ( natplusassoc k ( n * k ) ( m * k ) ) .   apply ( maponpaths ( fun x : _ => k + x ) ( IHn ) ) .  Defined . 
  
Lemma natldistr ( m k n : nat ) : paths ( n * ( m + k ) ) ( n * m + n * k ) .
Proof . intros m k n . induction m as [ | m IHm ] . simpl . rewrite ( natmultn0 n ) . auto with natarith .  simpl . rewrite ( multnsm n ( m + k ) ) . rewrite ( multnsm n m ) .  rewrite ( natplusassoc _ _ _ ) .  apply ( maponpaths ( fun x : _ => n + x ) ( IHm ) ) . Defined .

Lemma natmultassoc ( n m k : nat ) : paths ( ( n * m ) * k ) ( n * ( m * k ) ) .
Proof. intro . induction n as [ | n IHn ] . auto with natarith . intros . simpl . rewrite ( natrdistr m ( n * m ) k ) .  apply ( maponpaths ( fun x : _ => m * k + x ) ( IHn m k ) ) .   Defined . 

Lemma natmultl1 ( n : nat ) : paths ( 1 * n ) n .
Proof. simpl .  auto with natarith . Defined . 
Hint Resolve natmultl1 : natarith .

Lemma natmultr1 ( n : nat ) : paths ( n * 1 ) n .
Proof. intro n . rewrite ( natmultcomm n 1 ) . auto with natarith . Defined . 
Hint Resolve natmultr1 : natarith .

Definition natmultabmonoid : abmonoid :=  abmonoidpair ( setwithbinoppair natset ( fun n m : nat => n * m ) ) ( dirprodpair ( dirprodpair natmultassoc ( @isunitalpair natset _ 1 ( dirprodpair natmultl1 natmultr1 ) ) ) natmultcomm ) . 

    


(** *** [ nat ] as a commutative rig *)

Definition natcommrig : commrig .
Proof . split with ( setwith2binoppair natset ( dirprodpair  ( fun n m : nat => n + m ) ( fun n m : nat => n * m ) ) ) .  split . split . split with ( dirprodpair ( dirprodpair ( dirprodpair natplusassoc ( @isunitalpair natset _ 0 ( dirprodpair natplusl0 natplusr0 ) ) ) natpluscomm ) ( dirprodpair natmultassoc ( @isunitalpair natset _ 1 ( dirprodpair natmultl1 natmultr1 ) ) ) ) . apply ( dirprodpair natmult0n natmultn0 ) . apply ( dirprodpair natldistr natrdistr ) . unfold iscomm . apply natmultcomm . Defined .


(** *** Cancellation properties of [ mult ] on [ nat ] *)

Definition natneq0andmult ( n m : nat ) ( isn : natneq n 0 ) ( ism : natneq m 0 ) : natneq ( n * m ) 0 .
Proof . intros . destruct n as [ | n ] . destruct ( isn ( idpath _ ) ) .  destruct m as [ | m ] .  destruct ( ism ( idpath _ ) ) . simpl . apply ( negpathssx0 ) .  Defined . 

Definition natneq0andmultlinv ( n m : nat ) ( isnm : natneq ( n * m ) 0 ) : natneq n 0 := rigneq0andmultlinv natcommrig n m isnm . 

Definition natneq0andmultrinv ( n m : nat ) ( isnm : natneq ( n * m ) 0 ) : natneq m 0 := rigneq0andmultrinv natcommrig n m isnm .



(** *** Multiplication and comparisons  *)


(** [ natgth ] *)


Definition natgthandmultl ( n m k : nat ) ( is : natneq k 0 ) : natgth n m -> natgth ( k * n ) ( k * m ) .
Proof. intro n . induction n as [ | n IHn ] .  intros m k g g' . destruct ( negnatgth0n _ g' ) .  intro m . destruct m as [ | m ] . intros k g g' . rewrite ( natmultn0 k ) .  rewrite ( multnsm k n ) .  apply ( natgehgthtrans _ _ _ ( natgehplusnmn k ( k* n ) ) ( natneq0togth0 _ g ) ) .  intros k g g' . rewrite ( multnsm k n ) . rewrite ( multnsm k m ) . apply ( natgthandplusl _ _ _ ) . apply ( IHn m k g g' ) . Defined .  

Definition natgthandmultr ( n m k : nat ) ( is : natneq k 0 ) : natgth n m -> natgth ( n * k ) ( m * k )  .
Proof . intros n m k l . rewrite ( natmultcomm n k ) . rewrite ( natmultcomm m k ) . apply ( natgthandmultl n m k l ) . Defined .

Definition natgthandmultlinv ( n m k : nat ) : natgth ( k * n ) ( k * m ) -> natgth n m .
Proof . intro n . induction n as [ | n IHn ] . intros m k g . rewrite ( natmultn0 k ) in g . destruct ( negnatgth0n _ g ) .  intro m . destruct m as [ | m ] .  intros . apply ( natgthsn0 _ ) . intros k g . rewrite ( multnsm k n ) in g .  rewrite ( multnsm k m ) in g . apply ( IHn m k ( natgthandpluslinv _ _ k g ) ) .  Defined . 

Definition natgthandmultrinv ( n m k : nat ) : natgth ( n * k ) ( m * k ) -> natgth n m .
Proof.  intros n m k g . rewrite ( natmultcomm n k ) in g . rewrite ( natmultcomm m k ) in g . apply ( natgthandmultlinv n m k g ) . Defined .



(** [ natlth ] *)


Definition natlthandmultl ( n m k : nat ) ( is : natneq k 0 ) : natlth n m -> natlth ( k * n ) ( k * m )  := natgthandmultl _ _ _ is .

Definition natlthandmultr ( n m k : nat ) ( is : natneq k 0 ) : natlth n m -> natlth ( n * k ) ( m * k ) := natgthandmultr _ _ _ is .

Definition natlthandmultlinv ( n m k : nat ) : natlth ( k * n ) ( k * m ) -> natlth n m := natgthandmultlinv _ _ _  .

Definition natlthandmultrinv ( n m k : nat ) : natlth ( n * k ) ( m * k ) -> natlth n m := natgthandmultrinv _ _ _ .


(** [ natleh ] *)


Definition natlehandmultl ( n m k : nat ) : natleh n m -> natleh ( k * n ) ( k * m ) := negf ( natgthandmultlinv _ _ _ ) .

Definition natlehandmultr ( n m k : nat ) : natleh n m -> natleh ( n * k ) ( m * k ) := negf ( natgthandmultrinv _ _ _ ) .

Definition natlehandmultlinv ( n m k : nat ) ( is : natneq k 0 ) : natleh ( k * n ) ( k * m ) -> natleh n m := negf ( natgthandmultl _ _ _ is )  .

Definition natlehandmultrinv ( n m k : nat ) ( is : natneq k 0 ) : natleh ( n * k ) ( m * k ) -> natleh n m := negf ( natgthandmultr _ _ _ is ) .


(** [ natgeh ] *)


Definition natgehandmultl ( n m k : nat ) : natgeh n m -> natgeh ( k * n ) ( k * m ) := negf ( natgthandmultlinv _ _ _ ) .

Definition natgehandmultr ( n m k : nat ) : natgeh n m -> natgeh ( n * k ) ( m * k )  := negf ( natgthandmultrinv _ _ _ ) .

Definition natgehandmultlinv ( n m k : nat ) ( is : natneq k 0 ) : natgeh ( k * n ) ( k * m ) -> natgeh n m := negf ( natgthandmultl _ _ _ is )   .

Definition natgehandmultrinv ( n m k : nat ) ( is : natneq k 0 ) : natgeh ( n * k ) ( m * k ) -> natgeh n m := negf ( natgthandmultr _ _ _ is )  .






(** *** Properties of comparisons in the terminology of  algebra1.v *)

Open Scope rig_scope.

(** [ natgth ] *)

Lemma isplushrelnatgth : @isbinophrel nataddabmonoid natgth . 
Proof . split . apply  natgthandplusl .  apply natgthandplusr .  Defined . 

Lemma isinvplushrelnatgth : @isinvbinophrel nataddabmonoid natgth . 
Proof . split . apply  natgthandpluslinv .  apply natgthandplusrinv .  Defined . 

Lemma isinvmulthrelnatgth : @isinvbinophrel natmultabmonoid natgth . 
Proof . split .  intros a b c r . apply ( natlthandmultlinv _ _ _ r ) .   intros a b c r .  apply ( natlthandmultrinv _ _ _ r ) .  Defined . 

Lemma isrigmultgtnatgth : isrigmultgt natcommrig natgth .
Proof . change ( forall a b c d : nat , natgth a b -> natgth c d -> natgth ( a * c + b * d ) ( a * d + b * c ) ) .  intro a . induction a as [ | a IHa ] . intros b c d rab rcd . destruct ( negnatgth0n _ rab ) . 

intro b . induction b as [ | b IHb ] . intros c d rab rcd . rewrite ( natmult0n d ) .  rewrite ( natplusr0 _ ) .  rewrite ( natmult0n _ ) .        rewrite ( natplusr0 _ ) . apply ( natlthandmultl _ _ _ ( natgthtoneq _ _ rab ) rcd ) . intros c d rab rcd . simpl . set ( rer := ( abmonoidrer nataddabmonoid ) ) . simpl in rer .  rewrite ( rer _ _ d _ ) . rewrite ( rer _ _ c _ ) .  rewrite ( natpluscomm c d ) .  apply ( natlthandplusl (a * d + b * c)  (a * c + b * d) ( d + c ) ) . apply ( IHa _ _ _ rab rcd ) .  Defined . 

Lemma isinvrigmultgtnatgth : isinvrigmultgt natcommrig natgth .
Proof . set ( rer := abmonoidrer nataddabmonoid  ) .  simpl in rer .  apply isinvrigmultgtif . intros a b c d . generalize a b c . clear a b c .  induction d as [ | d IHd ] .  

intros a b c g gab . change ( pr1 ( natgth ( a * c + b * 0 ) ( a * 0 + b * c ) ) ) in g .   destruct c as [ | c ] .  rewrite ( natmultn0 _ ) in g .  destruct ( isirreflnatgth _ g ) .  apply natgthsn0 .   

intros a b c g gab .  destruct c as [ | c ] . change ( pr1 ( natgth ( a * 0 + b * S d ) ( a * S d + b * 0 ) ) ) in g . rewrite ( natmultn0 _ ) in g .  rewrite ( natmultn0 _ ) in g .  rewrite ( natplusl0 _ ) in g . rewrite ( natplusr0 _ ) in g .  set ( g' := natgthandmultrinv _ _ _ g ) .  destruct ( isasymmnatgth _ _ gab g' ) .  change ( pr1 ( natgth ( a * S c + b * S d ) ( a * S d + b * S c ) ) ) in g .  rewrite ( multnsm _ _ ) in g .   rewrite ( multnsm _ _ ) in g .  rewrite ( multnsm _ _ ) in g .  rewrite ( multnsm _ _ ) in g . rewrite ( rer _ ( a * c ) _ _ ) in g . rewrite ( rer _ ( a * d ) _ _ ) in g . set ( g' := natgthandpluslinv _ _ ( a + b ) g ) .  apply ( IHd a b c g' gab ) . Defined .  





(** [ natlth ] *)

Lemma isplushrelnatlth : @isbinophrel nataddabmonoid natlth . 
Proof . split . intros a b c . apply  ( natgthandplusl b a c ) . intros a b c . apply ( natgthandplusr b a c )  .  Defined . 

Lemma isinvplushrelnatlth : @isinvbinophrel nataddabmonoid natlth . 
Proof . split . intros a b c . apply  ( natgthandpluslinv b a c ) .  intros a b c . apply ( natgthandplusrinv b a c ) .  Defined . 

Lemma isinvmulthrelnatlth : @isinvbinophrel natmultabmonoid natlth . 
Proof . split . intros a b c r .  apply ( natlthandmultlinv  _ _ _ r ) .   intros a b c r .  apply ( natlthandmultrinv _ _ _ r ) .  Defined . 

(** [ natleh ] *)

Lemma isplushrelnatleh : @isbinophrel nataddabmonoid natleh . 
Proof . split . apply natlehandplusl .  apply natlehandplusr . Defined . 

Lemma isinvplushrelnatleh : @isinvbinophrel nataddabmonoid natleh . 
Proof . split . apply natlehandpluslinv .  apply natlehandplusrinv . Defined . 

Lemma ispartinvmulthrelnatleh : @ispartinvbinophrel natmultabmonoid ( fun x => natneq x 0 ) natleh . 
Proof . split . intros a b c s r . apply ( natlehandmultlinv _ _ _ s r ) .   intros a b c s r .  apply ( natlehandmultrinv _ _ _ s r ) .  Defined . 


(** [ natgeh ] *)

Lemma isplushrelnatgeh : @isbinophrel nataddabmonoid natgeh . 
Proof . split . intros a b c . apply ( natlehandplusl b a c ) .   intros a b c . apply ( natlehandplusr b a c ) . Defined . 

Lemma isinvplushrelnatgeh : @isinvbinophrel nataddabmonoid natgeh . 
Proof . split . intros a b c . apply ( natlehandpluslinv b a c ) .   intros a b c . apply ( natlehandplusrinv b a c ) . Defined . 

Lemma ispartinvmulthrelnatgeh : @ispartinvbinophrel natmultabmonoid ( fun x => natneq x 0 ) natgeh . 
Proof . split .  intros a b c s r . apply ( natlehandmultlinv _ _ _ s r ) .   intros a b c s r .  apply ( natlehandmultrinv _ _ _ s r ) .  Defined . 


Close Scope rig_scope . 



(** *** Submonoid of non-zero elements in [ nat ] *)

Definition natnonzero : @subabmonoids natmultabmonoid . 
Proof . split with ( fun a => natneq a 0 ) .  unfold issubmonoid .  split .  unfold issubsetwithbinop . intros a a' .  apply ( natneq0andmult _ _ ( pr2 a ) ( pr2 a' ) ) . apply ( ct ( natneq , 1 , 0 ) ) . Defined . 

Lemma natnonzerocomm ( a b : natnonzero ) : paths ( @op natnonzero a b ) ( @op natnonzero b a ) . 
Proof . intros . apply ( invmaponpathsincl _ ( isinclpr1carrier _ ) ( @op natnonzero a b ) ( @op natnonzero b a ) ) .  simpl . apply natmultcomm . Defined . 



(** *** Division with a remainder on [ nat ] 

For technical reasons it is more convenient to introduce divison with remainder for all pairs (n,m) including pairs of the form (n,0). *)


Definition natdivrem ( n m : nat ) : dirprod nat nat .
Proof. intros . induction n as [ | n IHn ] . intros . apply ( dirprodpair 0 0 ) . destruct ( natlthorgeh ( S ( pr2 IHn ) ) m )  . apply ( dirprodpair ( pr1 IHn ) ( S ( pr2 IHn ) ) ) .  apply ( dirprodpair ( S ( pr1 IHn ) ) 0 ) .   Defined . 

Definition natdiv ( n m : nat )  := pr1 ( natdivrem n m ) .
Definition natrem ( n m : nat )  := pr2 ( natdivrem n m ) .

Lemma lthnatrem ( n m : nat ) ( is : natneq m 0 ) : natlth ( natrem n m ) m .
Proof. intro . destruct n as [ | n ] . unfold natrem . simpl . intros.  apply ( natneq0togth0 _ is ) .  unfold natrem . intros m is . simpl .   destruct ( natlthorgeh (S (pr2 (natdivrem n m))) m )  as [ nt | t ] . simpl . apply nt . simpl .  apply ( natneq0togth0 _ is ) .   Defined . 


Theorem natdivremrule ( n m : nat ) ( is : natneq m 0 ) : paths n ( ( natrem n m ) + ( natdiv n m ) * m ) .
Proof. intro . induction n as [ | n IHn ] . simpl .  intros . apply idpath . intros m is .  unfold natrem . unfold natdiv . simpl .  destruct ( natlthorgeh ( S ( pr2 ( natdivrem n m  ) ) ) m )  as [ nt | t ] . 

simpl .  apply ( maponpaths S ( IHn m is ) ) .

simpl . set ( is' := lthnatrem n m is ) .  destruct ( natgthchoice2 _ _ is' ) as [ h | e ] .    destruct ( natlehtonegnatgth _ _ t h ) .  fold ( natdiv n m ) . set ( e'' := maponpaths S ( IHn m is ) ) .  change (S (natrem n m + natdiv n m * m) ) with (  S ( natrem n m ) + natdiv n m * m ) in  e'' . rewrite ( pathsinv0 e ) in e'' . apply e'' . 
Defined . 

Opaque natdivremrule . 


Lemma natlehmultnatdiv ( n m : nat ) ( is : natneq m 0 ) :  natleh ( mult ( natdiv n m ) m ) n .
Proof . intros . set ( e := natdivremrule n m ) . set ( int := ( natdiv n m ) * m ) . rewrite e . unfold int  .   apply ( natlehmplusnm _ _ ) .  apply is . Defined . 


Theorem natdivremunique ( m i j i' j' : nat ) ( lj : natlth j m ) ( lj' : natlth j' m ) ( e : paths ( j + i * m ) ( j' + i' * m ) ) : dirprod ( paths i i' ) ( paths j j' ) .
Proof. intros m i . induction i as [ | i IHi ] .

intros j i' j' lj lj' .  intro e .  simpl in e . rewrite ( natplusr0 j ) in e .  rewrite e in lj .  destruct i' . simpl in e .  rewrite ( natplusr0 j' ) in e .  apply ( dirprodpair ( idpath _ ) e ) .  simpl in lj . rewrite ( natpluscomm m ( i' * m ) ) in lj . rewrite ( pathsinv0 ( natplusassoc _ _ _ ) ) in lj .  destruct ( negnatgthmplusnm _ _ lj ) .

intros j i' j' lj lj' e . destruct i' as [ | i' ] .  simpl in e .  rewrite ( natplusr0 j' ) in e . rewrite ( pathsinv0 e ) in lj' .   rewrite ( natpluscomm m ( i * m ) ) in lj' .  rewrite ( pathsinv0 ( natplusassoc _ _ _ ) ) in lj' .  destruct ( negnatgthmplusnm _ _ lj' ) .  

simpl in e .  rewrite ( natpluscomm m ( i * m ) ) in e .  rewrite ( natpluscomm m ( i' * m ) ) in e .  rewrite ( pathsinv0 ( natplusassoc j _ _ ) ) in e .  rewrite ( pathsinv0 ( natplusassoc j' _ _ ) ) in e . set ( e' := invmaponpathsincl _ ( isinclnatplusr m ) _ _ e ) .  set ( ee := IHi j i' j' lj lj' e' ) .  apply ( dirprodpair ( maponpaths S ( pr1 ee ) ) ( pr2 ee )  ) .  Defined . 

Opaque natdivremunique .

Lemma natdivremandmultl ( n m k : nat ) ( ism : natneq m 0 ) ( iskm : natneq ( k * m ) 0 ) : dirprod ( paths ( natdiv ( k * n ) ( k * m ) ) ( natdiv n m ) ) ( paths ( natrem ( k * n ) ( k * m ) ) ( k * ( natrem n m ) ) ) . 
Proof . intros . set ( ak := natdiv ( k * n ) ( k * m ) ) . set ( bk := natrem ( k * n ) ( k * m ) ) . set ( a :=  natdiv n m ) . set ( b :=  natrem n m ) . assert ( e1 : paths ( bk + ak * ( k * m )  ) ( ( b * k ) + a * ( k * m ) ) ) . unfold ak. unfold bk .   rewrite ( pathsinv0 ( natdivremrule  ( k * n ) ( k * m ) iskm ) ) . rewrite ( natmultcomm k m ) .   rewrite ( pathsinv0 ( natmultassoc _ _ _ ) ) . rewrite ( pathsinv0 ( natrdistr _ _ _ ) ) .  unfold a . unfold b .  rewrite ( pathsinv0 ( natdivremrule  n m ism ) ) . apply ( natmultcomm k n ) . assert ( l1 := lthnatrem  n m ism ) . assert ( l1' := ( natlthandmultr _ _ _ ( natneq0andmultlinv _ _ iskm ) l1 ) )  .   rewrite ( natmultcomm m k ) in l1' . set ( int := natdivremunique _ _ _ _ _ ( lthnatrem ( k * n ) ( k * m ) iskm ) l1' e1 ) . 

split with ( pr1 int ) . 

rewrite ( natmultcomm k b ) . apply ( pr2 int ) .  Defined . 

Opaque natdivremandmultl .


Definition natdivandmultl ( n m k : nat ) ( ism : natneq m 0 ) ( iskm : natneq ( k * m ) 0 ) : paths ( natdiv ( k * n ) ( k * m ) ) ( natdiv n m ) := pr1 ( natdivremandmultl _ _ _ ism iskm ) .

  
Definition natremandmultl ( n m k : nat ) ( ism : natneq m 0 ) ( iskm : natneq ( k * m ) 0 ) : paths ( natrem ( k * n ) ( k * m ) ) ( k * ( natrem n m ) ) := pr2 ( natdivremandmultl _ _ _ ism iskm ) .


Lemma natdivremandmultr ( n m k : nat ) ( ism : natneq m 0 ) ( ismk : natneq ( m * k ) 0 ) : dirprod ( paths ( natdiv ( n * k ) ( m * k ) ) ( natdiv n m ) ) ( paths ( natrem ( n * k ) ( m * k) ) ( ( natrem n m ) * k  ) ) . 
Proof . intros . rewrite ( natmultcomm m k ) .   rewrite ( natmultcomm m k ) in ismk .  rewrite ( natmultcomm n k ) . rewrite ( natmultcomm ( natrem _ _ ) k ) .  apply ( natdivremandmultl _ _ _ ism ismk ) . Defined . 


Opaque natdivremandmultr .


Definition natdivandmultr ( n m k : nat ) ( ism : natneq m 0 ) ( ismk : natneq ( m * k ) 0 ) : paths ( natdiv ( n * k ) ( m * k ) ) ( natdiv n m ) := pr1 ( natdivremandmultr _ _ _ ism ismk ) .
 

Definition natremandmultr ( n m k : nat ) ( ism : natneq m 0 ) ( ismk : natneq ( m * k ) 0 ) : paths ( natrem ( n * k ) ( m * k ) ) ( ( natrem n m ) * k ) := pr2 ( natdivremandmultr _ _ _ ism ismk ) .





(** *** Exponentiation [ natpower n m ] ( " n to the power m " ) on [ nat ] *)

Fixpoint natpower ( n m : nat ) := match m with
O => 1 |
S m' => n * ( natpower n m' ) end .


(** *** Fcatorial on [ nat ] *)

Fixpoint factorial ( n : nat ) := match n with
0 => 1 |
S n' => ( S n' ) * ( factorial n' ) end .  





(** ** The order-preserving functions [ di i : nat -> nat ] whose image is the complement to one element [ i ] . *)




Definition di ( i : nat ) ( x : nat ) : nat :=
match natlthorgeh x i with 
ii1 _ => x |
ii2 _ => S x 
end .


Lemma natlehdinsn ( i n : nat ) : natleh ( di i n ) ( S n ) .
Proof . intros . unfold di . destruct ( natlthorgeh n i ) . apply natlthtoleh . apply natlthnsn . apply isreflnatleh .  Defined . 

Lemma natgehdinn ( i n : nat ) : natgeh ( di i n ) n .
Proof. intros . unfold di . destruct ( natlthorgeh n i ) .  apply isreflnatleh .  apply natlthtoleh . apply natlthnsn .   Defined . 


Lemma isincldi ( i : nat ) : isincl ( di i ) .
Proof. intro .   apply ( isinclbetweensets ( di i ) isasetnat isasetnat ) . intros x x' . unfold di . intro e. destruct  ( natlthorgeh x i )  as [ l | nel ] .  destruct  ( natlthorgeh x' i )   as [ l' | nel' ] . apply e .  rewrite e in l .  set ( e' := natgthtogths _ _  l ) . destruct ( nel' e' ) .   destruct  ( natlthorgeh x' i )  as [ l' | nel' ] .  destruct e.  set ( e' := natgthtogths _ _ l' ) . destruct ( nel e' ) .  apply ( invmaponpathsS _ _ e ) . Defined . 


Lemma neghfiberdi ( i : nat ) : neg ( hfiber ( di i ) i ) .
Proof. intros i hf . unfold di in hf . destruct hf as [ j e ] .  destruct ( natlthorgeh j i ) as [ l | g ] . destruct e . apply ( isirreflnatlth _ l) .  destruct e in g .  apply ( negnatgehnsn _ g ) .   Defined. 

Lemma iscontrhfiberdi ( i j : nat ) ( ne : neg ( paths i j ) ) : iscontr ( hfiber ( di i ) j ) .
Proof. intros . apply iscontraprop1 .   apply ( isincldi i j ) . destruct ( natlthorgeh j i ) as [ l | nel ]  .  split with j .  unfold di .   destruct ( natlthorgeh j i ) as [ l' | nel' ]  .  apply idpath .  destruct ( nel' l ) .   destruct ( natgehchoice2 _ _ nel ) as [ g | e ] . destruct j as [ | j ] . destruct ( negnatgeh0sn _ g ) .   split with j . unfold di .  destruct ( natlthorgeh j i ) as [ l' | g' ] .  destruct ( g l' ) .  apply idpath .  destruct ( ne ( pathsinv0 e ) ) . Defined . 
 

Lemma isdecincldi ( i : nat ) : isdecincl ( di i ) .
Proof. intro i . intro j . apply isdecpropif .   apply ( isincldi i j ) .  destruct ( isdeceqnat i j )  as [ eq | neq ] .    destruct eq .  apply ( ii2 ( neghfiberdi i ) ) . apply ( ii1 ( pr1 ( iscontrhfiberdi i j neq ) ) ) .   Defined .






(** ** Inductive types [ le ] with values in [ Type ] . 

This part is included for illustration purposes only . In practice it is easier to work with [ natleh ] than with [ le ] . 

*)

(** *** A generalization of [ le ] and its properties . *)

Inductive leF { T : Type } ( F : T -> T ) ( t : T ) : T -> Type := leF_O : leF F t t | leF_S : forall t' : T , leF F t t' -> leF F t ( F t' ) .

Lemma leFiter { T : UU } ( F : T -> T ) ( t : T ) ( n : nat ) : leF F t ( iteration F n t ) .
Proof. intros .   induction n as [ | n IHn ] . apply leF_O . simpl . unfold funcomp . apply leF_S .  assumption .  Defined . 

Lemma leFtototal2withnat { T : UU } ( F : T -> T ) ( t t' : T ) ( a : leF F t t' ) : total2 ( fun n : nat => paths ( iteration F n t ) t' ) .
Proof. intros. induction a as [ | b H0 IH0 ] . split with O . apply idpath .  split with  ( S ( pr1 IH0 ) ) . simpl . apply ( @maponpaths _ _ F ( iteration F ( pr1 IH0 ) t ) b ) . apply ( pr2 IH0 ) .  Defined. 
Lemma total2withnattoleF { T : UU } ( F : T -> T ) ( t t' : T ) ( a : total2 ( fun n : nat => paths ( iteration F n t ) t' ) ) : leF F t t' .
Proof. intros .  destruct a as [ n e ] .  destruct e .  apply leFiter.  Defined . 


Lemma leFtototal2withnat_l0 { T : UU } ( F : T -> T ) ( t : T ) ( n : nat ) : paths ( leFtototal2withnat F t _ (leFiter F t n)) ( tpair _  n ( idpath (iteration F n t) ) ) . 
Proof . intros . induction n as [ | n IHn ] .   apply idpath . simpl .  
set ( h := fun ne :  total2 ( fun n0 : nat => paths ( iteration F n0 t ) ( iteration F n t ) ) => tpair  ( fun n0 : nat => paths ( iteration F n0 t ) ( iteration F ( S n ) t ) ) ( S ( pr1 ne ) ) ( maponpaths F ( pr2 ne ) ) ) . apply ( @maponpaths _ _ h  _ _ IHn ) . Defined. 


Lemma isweqleFtototal2withnat { T : UU } ( F : T -> T ) ( t t' : T ) : isweq ( leFtototal2withnat F t t' ) .
Proof . intros .  set ( f := leFtototal2withnat F t t' ) . set ( g :=  total2withnattoleF  F t t' ) . 
assert ( egf : forall x : _ , paths ( g ( f x ) ) x ) . intro x .  induction x as [ | y H0 IHH0 ] . apply idpath . simpl . simpl in IHH0 .  destruct (leFtototal2withnat F t y H0 ) as [ m e ] .   destruct e .  simpl .   simpl in IHH0.  apply (  @maponpaths _ _ ( leF_S F t (iteration F m t) ) _ _ IHH0 ) .
assert ( efg : forall x : _ , paths ( f ( g x ) ) x ) . intro x .  destruct x as [ n e ] .  destruct e . simpl .  apply  leFtototal2withnat_l0 . 
apply ( gradth _ _ egf efg ) . Defined.

Definition weqleFtototalwithnat { T : UU } ( F : T -> T ) ( t t' : T ) : weq ( leF F t t' ) (  total2 ( fun n : nat => paths ( iteration F n t ) t' ) ) := weqpair _ ( isweqleFtototal2withnat F t t' ) .


(** *** Inductive types [ le ] with values in [ Type ] are in [ hProp ] *)

Definition le ( n : nat ) : nat -> Type := leF S n .
Definition le_n := leF_O S .
Definition le_S := leF_S S . 



Theorem isaprople ( n m : nat ) : isaprop ( le n m ) .
Proof. intros .  apply ( isofhlevelweqb 1 ( weqleFtototalwithnat S n m ) ) . apply invproofirrelevance .  intros x x' .  set ( i := @pr1 _ (fun n0 : nat => paths (iteration S n0 n) m) ) . assert ( is : isincl i ) . apply ( isinclpr1 _ ( fun n0 : nat => isasetnat (iteration S n0 n) m ) ) . apply ( invmaponpathsincl _  is ) .  destruct x as [ n1 e1 ] . destruct x' as [ n2 e2 ] . simpl .   set ( int1 := pathsinv0 ( pathsitertoplus n1 n ) ) . set ( int2 := pathsinv0 (pathsitertoplus n2 n ) ) . set ( ee1 := pathscomp0 int1 e1 ) . set ( ee2 := pathscomp0 int2 e2 ) . set ( e := pathscomp0 ee1 ( pathsinv0 ee2 ) ) .   apply ( invmaponpathsincl _ ( isinclnatplusr n ) n1 n2 e ) .    Defined . 

(** *** Comparison between [ le ] with values in [ Type ] and [ natleh ] . *)


Lemma letoleh ( n m : nat ) : le n m -> natleh n m .
Proof .  intros n m H . induction H as [ | m H0 IHH0 ] . apply isreflnatleh .  apply natlehtolehs .  assumption .  Defined . 

Lemma natlehtole ( n m : nat ) : natleh n m ->  le n m .
Proof. intros n m H .  induction m .  assert ( int := natleh0tois0 n H ) .   clear H . destruct int . apply le_n . 
 set ( int2 := natlehchoice2 n ( S m ) H ) .  destruct int2 as [ isnatleh | iseq ] . apply ( le_S n m ( IHm isnatleh ) ) . destruct iseq .   apply le_n . Defined .

Lemma isweqletoleh ( n m : nat ) : isweq ( letoleh n m ) .
Proof. intros . set ( is1 := isaprople n m ) . set ( is2 := pr2 ( natleh n m )  ) . apply ( isweqimplimpl ( letoleh n m ) ( natlehtole n m ) is1 is2 ) .  Defined . 

Definition weqletoleh ( n m : nat ) := weqpair _ ( isweqletoleh n m ) .




(* End of the file hnat.v *)





(* 
*** Local Variables: ***
*** coq-prog-name: "/opt/local/bin/coqtop" ***
*** coq-prog-args: ("-emacs-U") ***
*** End: ***
 *)