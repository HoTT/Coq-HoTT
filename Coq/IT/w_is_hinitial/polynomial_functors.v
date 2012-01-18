Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Unset Automatic Introduction.
Require Export uu0.
Require Export identity.

(** * Polynomial functors and their algebras *) 

Section Polynomial_Functors.

Variable A : U.
Variable B : A -> U.

(** The action of P on types *)

Definition P_0 : U -> U :=
 (fun X : U => Sigma (fun a : A => (B a -> X))).

(** The action of P on functions *)

Definition P_1  {X Y : U}(f : X -> Y) : (P_0 X) -> (P_0  Y) :=
(fun x => dpair _ (p1 x) ( funcomp (p2 x) f )).

(** Action of P on paths *) 

Definition P_2 {X Y : U}{f g : X -> Y}: 
 Id f g -> Id (P_1 f) (P_1 g).
Proof. 
intros X Y f g e.
destruct e.
apply refl.
Defined.

(** Functoriality of P *) 

Definition functorPcomp  {X Y Z : U}(f : X -> Y)(g : Y -> Z) :
 Id (funcomp (P_1 f) (P_1 g)) (P_1 (funcomp f g)).
Proof.
intros.
unfold P_1.
apply funextfun.
intro c.
destruct c as [x u].
simpl.
unfold funcomp.
simpl.
apply refl.
Defined.

Definition functorPid (X : U) : Id (P_1 (idfun X)) (idfun (P_0 X)).
Proof.
intros.
unfold P_1.
apply funextfun.
intro c.
destruct c as [x u].
simpl.
unfold funcomp.
unfold idfun.
apply (idfibertoidsigma).
apply (pathsinv0 (eta_path u)).
Defined.



(** We define an action of P also on the 2-category of types, functions and homotopies 
The only thing to define is the action of P on homotopies For this we need an auxiliary map. *)

Definition tau : forall (X Y : U)( f g : X -> Y)(x : A)(u : B x -> X) ( v : forall (y : B x), Id ( f (u y))  (g (u y))  ), 
  Id (dpair _ x (funcomp u f)) (dpair (fun a : A => (B a -> Y)) x (funcomp u g)).
Proof. 
intros. 
apply idfibertoidsigma. 
unfold funcomp. 
apply funextfun. 
apply v.
Defined.

(** We record the effect of the computation rules on tau *) 

Definition tau_comp  (X Y : U)( f : X -> Y)(x : A)(u : B x -> X) :
 Id (tau X Y f f x u (fun y : B x => refl (f (u y)))) (refl (dpair _ x (funcomp u f))).
Proof.
intros.
unfold tau.
assert (e :  Id  (refl (funcomp u f)) (funextfun _ _ (fun y : B x => refl (f (u y))))).
apply (homotinvweqweq0 (weqtoforallpaths _ (funcomp u f) (funcomp u f)) (refl (funcomp u f))).
set (C := (fun p : (Id (funcomp u f) (funcomp u f))  => 
Id (idfibertoidsigma (fun a : A => B a -> Y) x (funcomp u f) (funcomp u f) p)
   (refl (dpair (fun a : A => B a -> Y) x (funcomp u f))))).
apply (transportf C e).
apply refl.
Defined.

(** The action of P on homotopies *) 

Definition P_2_h {X Y : U}{f g : X -> Y} :
 Hom f g -> Hom (P_1 f) (P_1 g).
Proof. 
intros X Y f g alpha.
unfold Hom.
intro c.
destruct c as [x u].
apply (tau X Y f g x u (fun y : B x => (alpha (u y)))).
Defined.

(** The result of applying toforallpaths to P(e), where e is a path *) 

Definition compareP2withP2h {X Y : U}{f g : X -> Y}(e : Id f g) : 
 Id (toforallpaths _ _ _ ( P_2 e )) (P_2_h (toforallpaths _ _ _ e)).
Proof.
intros.
destruct e.
simpl.
unfold toforallpaths.
unfold P_2_h.
apply funextsec.
intro c.
destruct c as [x u].
apply (transportb (fun e => Id (refl (P_1 f (dpair (fun a : A => B a -> X) x u))) e) (tau_comp _ _ f x u)).
apply refl.
Defined.

(** The result of applying P_h(alpha), where alpha is a homotopy *) 

Definition compareP2withP2h2 {X Y : U}{f g : X -> Y}(alpha : Hom f g) : 
 Id (P_2 (funextfun _ _ alpha)) (funextfun _ _ (P_2_h alpha)).
Proof.
intros.
set (e := (funextfun _ _ alpha)).
set (e_flat := (toforallpaths _ _ _ e)).
assert (p_1 : Id e_flat alpha ). 
apply (homotweqinvweq (weqtoforallpaths _ f g) alpha).
assert (p_2 : Id   (funextfun _  _ (P_2_h alpha)) (funextfun _  _ (P_2_h e_flat))).
apply (maponpaths (funextfun (P_1 f) (P_1 g))).
apply (maponpaths P_2_h).
apply (pathsinv0 p_1).
apply (transportb (fun u => Id (P_2 e) u) p_2).
assert (p_3 : Id  (funextfun _ _ (P_2_h e_flat)) (funextfun _ _ (toforallpaths _ _ _ (P_2 e)))).
apply maponpaths.
apply (pathsinv0 (compareP2withP2h e)).
apply (transportb (fun u => Id (P_2 e) u) p_3).
apply (homotinvweqweq0 (weqtoforallpaths _ (P_1 f) (P_1 g)) (P_2 e)).
Defined.

(** The type of algebras of the functor *)

Definition isalg := (fun X => (P_0 X -> X)).

Definition P_Alg := Sigma isalg.

(** The type of algebra maps between two algebras. An algebra map consists of 
 a function between the underying types and a path witnessing the commutativity   
of the usual diagram *) 

Definition isalgmap (XX YY : P_Alg)(f : (p1 XX) -> (p1 YY)) : U := 
 Id (funcomp (p2 XX) f) (funcomp (P_1 f) (p2 YY)).

Definition P_Alg_Map (XX YY : P_Alg) : U := 
 Sigma (fun f : (p1 XX) -> (p1 YY) => (isalgmap XX YY f)).

(**   The type of algebra 2-cells between two  algebra maps. An algebra 2-cell is a pair
 consisting of a path between the underlying functions and a path witnessing a coherence 
condition *) 

Definition isalg2cell {XX YY : P_Alg}(ff gg : P_Alg_Map XX YY)(e : Id (p1 ff) (p1 gg)) := 
 Id (pathscomp0 (p2 ff) (comppathwithfun (P_2 e) (p2 YY)))
     (pathscomp0 (compfunwithpath (p2 XX) e) (p2 gg)).


Definition P_Alg_2cell {XX YY : P_Alg}(ff gg : P_Alg_Map XX YY) : U := 
 Sigma (fun e : Id (p1 ff) (p1 gg) => (isalg2cell _ _  e)).

(** We prove that identity functions have the structure of algebra maps. 
We also establish some useful facts about their structure paths      *) 

Definition aux_construction (XX : P_Alg)(x : A)(u : B x -> (p1 XX))(v : B x -> (p1 XX))(e : Id u v) : 
 Id ((p2 XX) (dpair _ x u)) ((p2 XX) (dpair _ x v)).
Proof.
intros.
destruct XX as [X s_X].
apply maponpaths.
apply maponpaths.
apply e.
Defined.

Definition aux_comparison (XX : P_Alg)(x : A)(u : B x -> (p1 XX))(v : B x -> (p1 XX))(e : Id u v)(E : (p1 XX) -> U) : 
 Id (transportb E (aux_construction XX x u v e)) (transportb (fun z => E ((p2 XX) (dpair _ x z))) e).
Proof.
intros.
destruct XX as [X s_X].
destruct e.
unfold transportf.
simpl.
apply refl.
Defined.
  
Definition homotopyforidfunisalgmap (XX : P_Alg) : 
 forall c : (P_0 (p1 XX)), Id ((funcomp (p2 XX) (idfun (p1 XX))) c) ((funcomp (P_1 (idfun (p1 XX))) (p2 XX)) c).
Proof.
intros.
destruct XX as [X s_X].
destruct c as [x u].
unfold funcomp.
unfold idfun.
unfold P_1.
simpl.
apply (aux_construction (dpair _ X s_X) x u (funcomp u (idfun X)) (eta_path u)).
Defined.

Definition idfunisalgmap : forall XX : P_Alg, isalgmap _ _ (idfun (p1 XX)).
Proof.
intro XX.
apply (funextfun _ _ (homotopyforidfunisalgmap XX)).
Defined.

Definition idalgmap (XX : P_Alg) : P_Alg_Map XX XX := 
 dpair _ (idfun (p1 XX)) (idfunisalgmap XX).

(** We establish a simple fact regarding the transport along 
 the 2-cell witnessing that identities are algebra maps   *) 

Definition first_fact (XX : P_Alg)(E : (p1 XX) -> U)(x : A)(u : B x -> (p1 XX)) : 
  Id  
   (transportb E (homotopyforidfunisalgmap XX (dpair _ x u)))
   (transportb (fun z => E ((p2 XX) (dpair _ x z))) (eta_path u)).
Proof.
intros.
destruct XX as [X s_X]. 
unfold homotopyforidfunisalgmap.
apply (aux_comparison (dpair _ X s_X) x u (funcomp u (idfun X)) (eta_path u)).
Defined.

Definition second_fact (XX : P_Alg)(E : (p1 XX) -> U)(x : A)(u : B x -> (p1 XX)) : 
  Id  
   (transportb E (homotopyforidfunisalgmap XX (dpair _ x u)))
   (transportb (fun z => E (z (dpair _ x u))) (idfunisalgmap XX)).
Proof.
intros.
unfold idfunisalgmap.
apply (pointwisetransportbhomotopy _ _ E (homotopyforidfunisalgmap XX)).
Defined.

Definition first_and_second_fact (XX : P_Alg)(E : (p1 XX) -> U)(x : A)(u : B x -> (p1 XX)) :
   Id
   (transportb (fun z => E (z (dpair _ x u))) (idfunisalgmap XX))
   (transportb (fun z => E ((p2 XX) (dpair _ x z))) (eta_path u)).
Proof.
intros.
apply (pathscomp0 (pathsinv0 (second_fact XX E x u)) (first_fact XX E x u)).
Defined.



(** Composition of algebra maps *) 

Definition isalgmapfuncomp {XX YY ZZ : P_Alg} :  
 forall (ff : P_Alg_Map XX YY)(gg :  P_Alg_Map YY ZZ), 
   isalgmap XX ZZ (funcomp (p1 ff) (p1 gg)).


Proof.
intros XX YY ZZ ff gg.
destruct XX as [X s_X].
destruct YY as [Y s_Y].
destruct ZZ as [Z s_Z].
destruct ff as [f s_f].
destruct gg as [g s_g].
unfold p1 in f.
unfold p1 in g.
unfold isalgmap in s_f.
unfold p2 in s_f.
unfold isalgmap in s_g.
unfold p2 in s_g.
unfold isalgmap.
unfold p2.
apply (transportf (fun z => Id _ (funcomp z s_Z)) (functorPcomp f g)).
change (funcomp (funcomp (P_1 f) (P_1 g)) s_Z) with (funcomp (P_1 f) (funcomp (P_1 g) s_Z)).
apply (transportf (fun z => Id _ (funcomp (P_1 f) z)) s_g).
change (funcomp s_X (funcomp f g)) with (funcomp (funcomp s_X f) g).
apply (transportb (fun z => Id (funcomp z g) _) s_f).
apply refl.
Defined.

Definition algmapcomp {XX YY ZZ : P_Alg} : 
   (P_Alg_Map XX YY) -> (P_Alg_Map YY ZZ ->  P_Alg_Map XX ZZ).
Proof.
intros XX YY ZZ ff gg.
split with (funcomp (p1 ff) (p1 gg)).
apply isalgmapfuncomp.
Defined.

(** The structure map of an algebra is an algebra map *) 

Definition PP : P_Alg -> P_Alg := 
 fun XX => (dpair _ (P_0 (p1 XX)) (P_1 (p2 XX))).

Definition isalgmapstructuremap (XX : P_Alg) : 
 isalgmap (PP XX) XX (p2 XX).
Proof.
intros.
destruct XX as [X s_X].
simpl.
apply refl.
Defined.

Definition structurealgmap (XX : P_Alg) : P_Alg_Map (PP XX) XX.
Proof. 
intros.
split with (p2 XX).
apply isalgmapstructuremap.
Defined.

(** We show that the identity path is an algebra 2-cell *) 

Definition idpathisalg2cell {XX YY : P_Alg}(ff : P_Alg_Map XX YY) : 
 isalg2cell _ _ (refl (p1 ff)).
Proof. 
intros. 
destruct XX as [X s_X]. 
destruct YY as [Y s_Y]. 
destruct ff as [f s_f]. 
simpl. 
unfold isalg2cell.
simpl.
apply pathscomp0rid.
Defined.

Definition idpath2cell {XX YY : P_Alg}(ff : P_Alg_Map XX YY) :  P_Alg_2cell ff ff.
Proof. 
intros. 
split with (refl (p1 ff)). 
apply (idpathisalg2cell ff).
Defined.

(** ** H-initiality and Lambek's lemma *) 

Definition ishinitial (XX : P_Alg) : Type := forall YY : P_Alg, iscontr (P_Alg_Map XX YY).

(** Lambek's lemma *) 

Definition lambekslemma (XX : P_Alg) :
 ishinitial XX -> isweq (p2 XX).
Proof.
intros XX is.
set (X := p1 XX).
set (s_X := p2 XX).
set (iscontr_hom_XX_PP_XX := is (PP XX)).
set (tt := p1 iscontr_hom_XX_PP_XX).
set (t := p1 tt).
set (s_t := p2 tt).
set (iscontr_hom_XX_XX := is  XX).
set (ss := structurealgmap XX).
set (ttss := algmapcomp tt ss).
set (id := idalgmap XX).
assert (ee : Id ttss id).
apply (proofirrelevance _ iscontr_hom_XX_XX ttss id).
assert (p : Id (funcomp t s_X) (idfun X)).
unfold ttss in ee.
apply (idsigmatobase _  ttss id ee).
assert (q : Id (funcomp s_X t) (idfun (P_0 X))).
change ((fun f : p1 XX -> p1 (PP XX) => isalgmap XX (PP XX) f) (p1 tt)) with (isalgmap _ _ t) in s_t.
apply (transportb (fun z => Id z _) s_t).
change (p2 (PP XX)) with (P_1 s_X).
apply (transportb (fun z => Id z _) (functorPcomp t s_X)).
apply (transportb (fun z => Id (P_1 z) _) p).
apply (functorPid X).
apply (gradth s_X t).
apply (toforallpaths _ _ _ q).
apply (toforallpaths _ _ _ p).
Defined.

(** Uniquness up to weak equivalence of h-initial algebra *) 

Definition hinitialuniqueuptoweq {XX YY : P_Alg} :
 ishinitial XX -> (ishinitial YY -> weq (p1 XX) (p1 YY)).
Proof.
intros XX YY isX isY.
set (iscontr_XX_YY := isX YY).
set (iscontr_YY_XX := isY XX).
set (ff := p1 (iscontr_XX_YY)).
set (gg := p1 (iscontr_YY_XX)).
assert (pp : Id (algmapcomp ff gg) (idalgmap XX)).
apply (proofirrelevance _ (isX XX)).
assert (qq : Id (algmapcomp gg ff) (idalgmap YY)).
apply (proofirrelevance _ (isY YY)). 
set (X := p1 XX).
set (Y := p1 YY).
set (f := p1 ff).
set (g := p1 gg).
set (p := idsigmatobase _ _ _  pp).
set (q := idsigmatobase _ _ _  qq).
split with f.
apply (gradth f g).
apply (toforallpaths _ _ _ p).
apply (toforallpaths _ _ _ q).
Defined.


(** ** Analysis of algebra 2-cells   

We compare
                       
 - Paths between algebra maps                             
 - Pairs of paths involving transport                     
 - Algebra 2-cells   
                                     
 Using this one shows that two algebra maps are equal iff 
 there is an algebra 2-cell between them                  *) 


(** Alternative definition of algebra 2-cell. An alternative  
 algebra 2-cell from (f,s_f) to (g,s_g) is a pair (e,s_e)  
 where e : Id(f, g) and s_e : Id( e_!(s_f), s_g).   *)      

Definition isalg2cellalt {XX YY : P_Alg}(ff gg : P_Alg_Map XX YY) :=
  (fun e : Id (p1 ff) (p1 gg) =>
    Id (transportf (isalgmap XX YY) e (p2 ff)) (p2 gg)).

Definition P_Alg_2cellalt {XX YY : P_Alg}(ff gg : P_Alg_Map XX YY) := 
  Sigma (isalg2cellalt ff gg).

(** For each e : Id(f,g), the map isalg2cell(e) --> Id(e_!(s_f), s_g) *) 

Definition fiberwise2cellto2cellalt {XX YY : P_Alg}(ff gg : P_Alg_Map XX YY) : 
 forall e : Id (p1 ff) (p1 gg), (isalg2cell ff gg e) -> (isalg2cellalt ff gg e).
Proof.
intros XX YY ff gg.
destruct XX as [X s_X].
destruct YY as [Y s_Y].
destruct ff as [f s_f].
destruct gg as [g s_g].
simpl.
intro e.
destruct e.
simpl.
intro p.
unfold isalg2cellalt.
simpl.
change (Id s_f s_g).
apply (transportf (fun u => Id u s_g) (pathscomp0rid s_f)).
apply p.
Defined.

(** For each e, the map constructed above is a weak equivalence *) 

Definition isweqfiberwise2cellto2cellalt  {XX YY : P_Alg}(ff gg : P_Alg_Map XX YY) :
 forall e : Id (p1 ff) (p1 gg), isweq (fiberwise2cellto2cellalt ff gg e).
Proof. 
intros XX YY ff gg.
destruct XX as [X s_X].
destruct YY as [Y s_Y].
destruct ff as [f s_f].
destruct gg as [g s_g].
simpl.
intro e.
unfold fiberwise2cellto2cellalt.
destruct e.
simpl.
apply 
(isweqtransportf (fun u => Id u s_g) (pathscomp0rid s_f)).
Defined.

Definition weqfiberwise2cellto2cellalt  {XX YY : P_Alg}(ff gg : P_Alg_Map XX YY) : 
 forall e : Id (p1 ff) (p1 gg), weq (isalg2cell ff gg e) (isalg2cellalt ff gg e).
Proof.
intros.
split with (fiberwise2cellto2cellalt ff gg e).
apply (isweqfiberwise2cellto2cellalt ff gg e).
Defined.

(** The map from standard to alternative 2-cells, taking total spaces *) 

Definition from2cellto2cellalt  {XX YY : P_Alg} : 
 forall (ff gg : P_Alg_Map XX YY), P_Alg_2cell ff gg -> P_Alg_2cellalt ff gg.
Proof.
intros XX YY ff gg ee.
apply (totalfun _ _ (fiberwise2cellto2cellalt ff gg) ee).
Defined.

Definition isweqfrom2cellto2cellalt {XX YY : P_Alg}  : 
  forall (ff gg : P_Alg_Map XX YY), isweq (from2cellto2cellalt ff gg).
Proof.
intros.
apply (isweqfibtototal _ _ (weqfiberwise2cellto2cellalt ff gg)).
Defined.

(** This map is a weak equivalence because it is fiberwise a weak equivalence *) 

Definition weqfrom2cellto2cellalt {XX YY : P_Alg} : 
 forall (ff gg : P_Alg_Map XX YY), weq (P_Alg_2cell ff gg) (P_Alg_2cellalt ff gg).
Proof.
intros.
split with (from2cellto2cellalt ff gg).
apply  (isweqfrom2cellto2cellalt ff gg).
Defined.

(** As a special case of the general results obtained before for Id/Sigma we get  
 that there is a weak equivalence between alternative algebra 2-cells and paths 
 between algebra maps     *)                                                      

Definition weqfrom2cellalttoidalgmap {XX YY : P_Alg} : 
 forall (ff gg : P_Alg_Map XX YY), weq (P_Alg_2cellalt ff gg) (Id ff gg).
Proof.
intros.
apply (weqsigmaidtoidsigma (isalgmap XX YY)).
Defined.

(* Composing with the previous weak equivalence, we obtain that there is a weak 
 equivalence between algebra 2-cells and paths between algebra maps           *)

Definition weqfromalg2celltoidalgmap {XX YY : P_Alg} : 
 forall (ff gg : P_Alg_Map XX YY), weq (P_Alg_2cell ff gg) (Id ff gg).
Proof. 
intros.
apply (weqcomp (weqfrom2cellto2cellalt ff gg) (weqfrom2cellalttoidalgmap ff gg)).
Defined.

Definition weqfromaidalgmaptoalg2cell {XX YY : P_Alg} : 
 forall (ff gg : P_Alg_Map XX YY), weq (Id ff gg) (P_Alg_2cell ff gg).

Proof. 
intros.
apply (invweq (weqfromalg2celltoidalgmap ff gg)).
Defined.




(** For an algebra map ff, a map g and a path e : Id(f,g), we prove that there
is an essentially unique way of of making g into an algebra map so that e  
 becomes an algebra 2-cell. To do so, we define a type whose elements are all
the possible such ways and prove it is contractible. *) 
(** 
Definition T  {XX YY : P_Alg}(ff : P_Alg_Map XX YY)(g : (p1 XX) -> (p1 YY))(e : Id (p1 ff) g) : U := 
 Sigma (fun s_g : (isalgmap _ _ g) => (isalg2cell ff (dpair _ g s_g) e)).

(** Construction of an element of T *)

Definition transportfalgmap {XX YY : P_Alg}(ff : P_Alg_Map XX YY)(g : (p1 XX) -> (p1 YY)) :
 forall (e : Id (p1 ff) g), (isalgmap _ _ g).
Proof. 
intros.  
apply (transportf (isalgmap XX YY) e). 
apply (p2 ff).
Defined.

Definition transportfalgmapwith2cell {XX YY : P_Alg}(ff : P_Alg_Map XX YY)(g : (p1 XX) -> (p1 YY)) :
 forall (e : Id (p1 ff) g), T ff g e.
Proof. 
intros. 
split with (transportfalgmap ff g e). 
destruct e. 
destruct ff as [f s_f]. 
simpl. 
unfold transportfalgmap. 
unfold transportf. 
simpl. unfold idfun. 
apply (idpathisalg2cell (dpair _ f s_f)). 
Defined.

(* We now prove that T is contractible. To do this we define a type T' that is contractible 
by Vladimir Voevodsky's results and then show that T and T' are weakly equivalent *) 

Definition T' {XX YY : P_Alg}(ff : P_Alg_Map XX YY)(g : (p1 XX) -> (p1 YY))(e : Id (p1 ff) g) : Type := 
coconusfromt 
(isalgmap  _ _ g) 
(pathscomp0 (pathsinv0 (compfunwithpath (p2 XX) e)) (pathscomp0 (p2 ff) (comppathwithfun (P_2 e) (p2 YY)))).

Definition T'_is_contractible {XX YY : P_Alg}(ff : P_Alg_Map XX YY)(g : (p1 XX) -> (p1 YY))(e : Id (p1 ff) g) :  
 iscontr (T' ff g e).
Proof. intros. 
apply 
(iscontrcoconusfromt (isalgmap _ _ g)
(pathscomp0  (pathsinv0 (compfunwithpath (p2 XX) e)) (pathscomp0 (p2 ff) (comppathwithfun (P_2 e) (p2 YY))))).
Defined.

(* The weak equivalence between T and T' is given by the fact that they are dependent sums 
 over the same type of families of types that are fiberwise weakly equivalent. The fiberwise 
 weak equivalence is simply given by the fact that path composition is a weak equivalence *) 

Definition weqfromTtoT'  {XX YY : P_Alg}(ff : P_Alg_Map XX YY)(g : (p1 XX) -> (p1 YY))(e : Id (p1 ff) g) : 
 weq (T  ff g e )  (T' ff g e).
Proof. 
intros XX YY ff g e. 
destruct XX as [X s_X]. 
destruct YY as [Y s_Y]. 
destruct ff as [f s_f]. 
simpl. 
apply weqfibtototal. 
intro s_g. 
simpl. 
apply weqleftcancellationlaw.
Defined.

Definition T_is_contractible {XX YY : P_Alg}(ff : P_Alg_Map XX YY)(g : (p1 XX) -> (p1 YY))(e : Id (p1 ff) g) :  
 iscontr (T ff g e).
Proof. intros. 
set (w := invweq (weqfromTtoT' ff g e)).
apply (iscontrweqf  w).
apply (T'_is_contractible ff g e).
Defined.

(** We show that if we have an algebra 2-cell we find an element of T *) 

Definition fromalgebra2cellstoT {XX YY : P_Alg}{ff gg : P_Alg_Map XX YY}(ee : P_Alg_2cell ff gg) : 
 T ff (p1 gg) (p1 ee).
Proof. 
intros. 
split with (p2 gg). 
destruct gg as [g s_g]. 
apply (p2 ee).
Defined.

(** We use this to establish that for an algebra map ff, a map g and a path e : Id(f,g), all the paths s_g 
making g into an algebra map such that e becomes an algebra 2-cell are propositionally equal to the 
canonical way of making s_g into an algebra map, as given in transportfalgmap *) 

Definition fromcontrTtoessentialuniqueness {XX YY : P_Alg}(ff : P_Alg_Map XX YY)(g : (p1 XX) -> (p1 YY))(e : Id (p1 ff) g) :
 forall (s_g : isalgmap XX YY g), (isalg2cell ff (dpair _ g s_g) e) -> Id ( transportfalgmap ff g e) s_g.
Proof. 
intros XX YY ff g e s_g s_e.
set (gg := (dpair _ g s_g) : (P_Alg_Map XX YY)).
set (ee := (dpair _ e s_e) : (P_Alg_2cell ff gg)).
set (t_1 := (transportfalgmapwith2cell ff g e) : T ff g e).
set (t_2 := (dpair _ s_g s_e) : T ff g e).
assert (p : Id t_1 t_2).
apply (proofirrelevancecontr (T_is_contractible ff g e) t_1 t_2).
set (q := idsigmatosigmaid _ t_1 t_2 p).
apply (p1 q).
Defined. **)

(** The type of algebra map homotopies *) 

Definition isalgmaphomotopy {X : U}{s_X : (P_0 X) -> X}{Y : U}{s_Y : (P_0 Y -> Y)}(f : X -> Y)(sigma_f : Hom (funcomp s_X f) (funcomp (P_1 f) s_Y))
(g : X -> Y) (sigma_g : Hom (funcomp s_X g) (funcomp (P_1 g) s_Y)) (alpha : Hom f g) : U :=  
 (forall c : (P_0 X), Id 
 ((homcomp0 (compfunwithhomotopy s_X alpha) (sigma_g)) c) 
 ((homcomp0 (sigma_f) (comphomotopywithfun (P_2_h alpha) s_Y)) c)).

Definition immisalghomotopy {X : U}{s_X : (P_0 X) -> X}{Y : U}{s_Y : (P_0 Y -> Y)}(f : X -> Y)(sigma_f : Hom (funcomp s_X f) (funcomp (P_1 f) s_Y))
(g : X -> Y) (sigma_g : Hom (funcomp s_X g) (funcomp (P_1 g) s_Y)) (alpha : Hom f g) :
 (isalgmaphomotopy f sigma_f g sigma_g alpha) -> 
 Id (homcomp0 (compfunwithhomotopy s_X alpha) (sigma_g))
    (homcomp0 (sigma_f) (comphomotopywithfun (P_2_h alpha) s_Y)).
Proof. 
intros X s_X Y s_Y f sigma_f g sigma_g alpha.
intro is.
apply funextsec.
intro c.
apply (is c).
Defined.

(* We show that if we have an algebra map homotopy we can construct an algebra 2-cell 
 This is a long equational reasoning, which uses what has been done on relating paths  
and homotopies *) 

Definition alghomotopytoalg2cell : forall 
(X : U)(s_X : (P_0 X) -> X)
(Y : U)(s_Y : (P_0 Y -> Y))
(f : X -> Y)(sigma_f : Hom (funcomp s_X f) (funcomp (P_1 f) s_Y))
(g : X -> Y)(sigma_g : Hom (funcomp s_X g) (funcomp (P_1 g) s_Y)) (alpha : Hom f g), 
(isalgmaphomotopy f sigma_f g sigma_g alpha) -> 
 isalg2cell (dpair (isalgmap (dpair _ X s_X) (dpair _ Y s_Y))  f (funextfun _ _ sigma_f)) (dpair _ g (funextfun _ _ sigma_g))  (funextfun f g alpha).
Proof. 
intros X s_X Y s_Y f sigma_f g sigma_g alpha. intro is. 
set (s_alpha :=  (immisalghomotopy f sigma_f g sigma_g alpha is)).
change (p1 (dpair (fun X0 : U => P_0 X0 -> X0) X s_X)) with X.
change (p1 (dpair (fun X0 : U => P_0 X0 -> X0) Y s_Y)) with Y.
set (XX := (dpair (fun X0 : U => P_0 X0 -> X0) X s_X)).
set (YY := (dpair (fun X0 : U => P_0 X0 -> X0) Y s_Y)).
change (dpair (fun f0 : X -> Y => isalgmap XX YY f0) g
        (funextfun (funcomp s_X g) (funcomp (P_1 g) s_Y) sigma_g))
    with (dpair  (isalgmap XX YY) g
        (funextfun (funcomp s_X g) (funcomp (P_1 g) s_Y) sigma_g)).
set (sigma_f_sharp := (funextfun (funcomp s_X f) (funcomp (P_1 f) s_Y) sigma_f)).
set (sigma_g_sharp := (funextfun (funcomp s_X g) (funcomp (P_1 g) s_Y) sigma_g)).
set (alpha_sharp := (funextfun f g alpha)).
change (Id (pathscomp0 sigma_f_sharp (comppathwithfun (P_2 alpha_sharp ) s_Y)) (pathscomp0 (compfunwithpath s_X alpha_sharp) sigma_g_sharp)). 
assert (e_1 : Id (P_2 alpha_sharp) (funextfun _ _ (P_2_h alpha))).
apply (compareP2withP2h2 alpha).
apply (transportb (fun u =>  Id (pathscomp0 sigma_f_sharp (comppathwithfun u s_Y))
     (pathscomp0 (compfunwithpath s_X alpha_sharp) sigma_g_sharp)) e_1).
assert (e_2 : Id  (funextfun _ _  (compfunwithhomotopy s_X alpha))
(compfunwithpath s_X alpha_sharp)).
apply (comparehomotopycompwithfunwithpathcompwithfun s_X alpha).
apply (transportf (fun u => Id
     (pathscomp0 sigma_f_sharp
        (comppathwithfun (funextfun (P_1 f) (P_1 g) (P_2_h alpha)) s_Y))
     (pathscomp0 u sigma_g_sharp)) e_2).
unfold sigma_g_sharp.
assert (e_3 : Id 
(funextfun _ _ (homcomp0 (compfunwithhomotopy s_X alpha) sigma_g))
((pathscomp0 (funextfun _ _ (compfunwithhomotopy s_X alpha))) (funextfun _ _ sigma_g))).
apply (compcomphomcomppath _ _ _ (compfunwithhomotopy s_X alpha) sigma_g).
apply (transportf (fun u => Id
     (pathscomp0 sigma_f_sharp
        (comppathwithfun (funextfun (P_1 f) (P_1 g) (P_2_h alpha)) s_Y)) u) e_3).
assert (e_4 : Id 
(funextfun _ _ (comphomotopywithfun (P_2_h alpha) s_Y))
(comppathwithfun (funextfun _ _ (P_2_h alpha)) s_Y)).
apply (comparefuncompwithpathwithfuncompwithhomot2 s_Y (P_2_h alpha)).
apply (transportf (fun u =>  Id
     (pathscomp0 sigma_f_sharp
        u)
     (funextfun (funcomp s_X f) (funcomp (P_1 g) s_Y)
        (homcomp0 (compfunwithhomotopy s_X alpha) sigma_g))) e_4).
assert (e_5 : Id 
(pathscomp0 sigma_f_sharp (funextfun _ _ (comphomotopywithfun (P_2_h alpha) s_Y)))
(funextfun _ _ (homcomp0 sigma_f (comphomotopywithfun (P_2_h alpha) s_Y)))).
apply (pathsinv0 (compcomphomcomppath _ _ _ sigma_f (comphomotopywithfun (P_2_h alpha) s_Y))).
apply (transportb (fun u => Id
     u 
     (funextfun (funcomp s_X f) (funcomp (P_1 g) s_Y)
        (homcomp0 (compfunwithhomotopy s_X alpha) sigma_g))) e_5).
apply maponpaths.
apply (pathsinv0 s_alpha).
Defined.

End Polynomial_Functors.