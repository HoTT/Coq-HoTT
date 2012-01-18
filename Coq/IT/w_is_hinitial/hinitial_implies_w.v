Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Unset Automatic Introduction.
Require Export uu0.
Require Export identity.
Require Export polynomial_functors.

(** * Preliminaries                      *) 

Section Preliminaries.

Definition pullbackalongeval {X Y : U}(E : Y -> U) : 
 forall (x : X), (X -> Y) -> U.
Proof.
intros X Y E x.
apply (fun f : X -> Y => E (f x)).
Defined.

Variable A : U.
Variable B : A -> U.

Definition lemma_on_transportf {X : U}(s_X : (P_0 _ B X) -> X)(E : X -> U)(x : A)(u : B x -> X){f_1 f_2 : X -> X}(e : Id f_1 f_2) :  
 Id 
  (transportf (pullbackalongeval E (dpair _ x u)) (comppathwithfun (P_2 _ _ e) s_X)) 
  (transportf (fun f => E (s_X (dpair _ x (funcomp u f)))) e). 
Proof.
intros.
destruct e.
unfold transportf.
simpl.
unfold P_1.
unfold idfun.
simpl.
apply funextfun.
intro t.
apply refl.
Defined.

Definition lemma_on_transportb {X : U}(s_X : (P_0 _ B X) -> X)(E : X -> U)(x : A)(u : B x -> X){f_1 f_2 : (P_0 _ _ X) -> X}(e : Id f_1 f_2) :
Id 
  (transportb (pullbackalongeval E (dpair _ x u)) e)
  (transportb (fun z : (P_0 _ _ X) -> X => E (z (dpair _ x u))) e).
Proof.
intros.
destruct e.
unfold transportb.
unfold transportf.
simpl.
unfold idfun.
apply refl.
Defined.

Definition second_lemma_on_transportf {X : U}(s_X : (P_0 _ B X) -> X)(E : X -> U)(x : A)(u : B x -> X){f_1 f_2 : X -> X}(e : Id f_1 f_2) :  
 forall (y : E (f_1 (s_X (dpair _ x u)))), Id 
  (transportf (fun z : X -> X => E (z (s_X (dpair _ x u)))) e y)
  (transportf (fun z : (P_0 _ B X) -> X => E (z (dpair _ x u))) (compfunwithpath s_X e) y).
Proof.
intros.
destruct e.
unfold transportf.
simpl.
unfold idfun.
apply refl.
Defined.

(** General version of diagram (G) *) 

Definition general_diagram_G (XX YY : P_Alg _ B)(ff gg : P_Alg_Map _ _ XX YY)
  (ee : P_Alg_2cell _ _ ff gg)(E : (p1 YY) -> U) : forall c : (P_0 _ _ (p1 XX)), Id 
   (funcomp 
      (transportb (pullbackalongeval E c) (p2 ff))  
      (transportf (pullbackalongeval E c) (compfunwithpath (p2 XX) (p1 ee))))
   (funcomp 
      (transportf (pullbackalongeval E c) (comppathwithfun (P_2 _ _ (p1 ee)) (p2 YY)))
      (transportb (pullbackalongeval E c) (p2 gg))).

Proof. 
intros XX YY ff gg ee E c.
apply (beck_chevalley_for_paths (pullbackalongeval E c) ).
apply (pathsinv0).
apply (p2 ee).
Defined.


(** General version of diagram (H) *) 
 

Definition top_shift (XX : P_Alg _ B)(E : (p1 XX) -> U) :
 forall (x : A)(u : B x -> (p1 XX)), (B x -> (p1 XX)) -> U.
Proof. 
intros XX E x u.
apply (fun f : B x -> (p1 XX) => forall y : B x, E (f y)).
Defined.

Definition bottom_shift (XX : P_Alg _ B)(E : (p1 XX) -> U) :
 forall (x : A)(u : B x -> (p1 XX)), (B x -> (p1 XX)) -> U.
Proof. 
intros XX E x u.
apply (fun f : B x -> (p1 XX) => E ((p2 XX) (dpair _ x f))).
Defined.

Definition general_diagram_H  (XX : P_Alg _ B)(E : (p1 XX) -> U)(d :  forall (x : A)(u : B x -> (p1 XX))(v : forall y : B x, E (u y)), E( (p2 XX) (dpair _ x u))) :
 forall (x : A)(u : B x -> (p1 XX)),
  Id 
  (funcomp (transportb (top_shift XX E x u) (eta_path u)) (d x u))
  (funcomp (d x (funcomp u (idfun (p1 XX)))) (transportb (bottom_shift XX E x u) (eta_path u))).

Proof.
intros.
set (X := (p1 XX)).
set (s_X := (p2 XX) : (P_0 _ B X) -> X).
set (P :=  (top_shift XX E x u)).
set (Q :=  (bottom_shift XX E x u)).
set (s := fun f : B x -> X => (d x f)).
apply (naturalityoftransportb P Q s (eta_path u)).
Defined.

(** We combine the previous observations on 
 transport along etapath to simplify the  
 expression of diagram (H)     *) 

Definition lemma_to_simplify_general_diagram_H  
 (XX : P_Alg _ B)
 (E : (p1 XX) -> U)
 (d :  forall (x : A)(u : B x -> (p1 XX))(v : forall y : B x, E (u y)), E( (p2 XX) (dpair _ x u))) :
 forall (x : A)(u : B x -> (p1 XX)), Id (transportb (top_shift XX E x u) (eta_path u)) (idfun (top_shift XX E x u u)).
Proof.
intros.
set (X := (p1 XX)).
set (s_X := (p2 XX) : (P_0 _ B X) -> X).
set (P :=  (top_shift XX E x u)).
Check  (transportb P (eta_path u)).
assert (e_1 : Id 
         (transportb P (eta_path u))
         (pathsectiontransportb (B x) X E (eta_path u))).
unfold pathsectiontransportb.
apply funextsec.
intro s.
unfold P.
unfold top_shift.
unfold transportb.
apply refl.
apply (transportb (fun z =>  Id z (idfun (P u))) e_1).
unfold P.
apply (pathtransportbalongetaisidentity (B x) X E).
Defined.


Definition simplified_general_diagram_H 
 (XX : P_Alg _ B)
 (E : (p1 XX) -> U)
 (d :  forall (x : A)(u : B x -> (p1 XX))(v : forall y : B x, E (u y)), E( (p2 XX) (dpair _ x u))) :
 forall (x : A)(u : B x -> (p1 XX)),
 Id  
  (funcomp (d x (funcomp u (idfun (p1 XX)))) (transportb (bottom_shift XX E x u) (eta_path u)))
  (d x u).

Proof.
intros.
apply (transportf (fun z => Id z _ ) (general_diagram_H XX E d x u)).
apply (transportb (fun z => Id (funcomp z _ ) _ ) (lemma_to_simplify_general_diagram_H XX E d x u)).
unfold funcomp.
unfold idfun.
simpl.
apply funextfun.
intro v.
apply refl.
Defined.


Definition super_simplified_general_diagram_H  (XX : P_Alg _ B)
 (E : (p1 XX) -> U)
 (d :  forall (x : A)(u : B x -> (p1 XX))(v : forall y : B x, E (u y)), E( (p2 XX) (dpair _ x u))) :
 forall (x : A)(u : B x -> (p1 XX)),
 Id  
  (funcomp (d x (funcomp u (idfun (p1 XX)))) (transportb (fun z => E (z (dpair _ x u))) (idfunisalgmap _ _ XX)))
  (d x u).
Proof.
intros.
set (e_1 := (transportb (fun z => E (z (dpair _ x u))) (idfunisalgmap _ _ XX))).
set (e_2 := (transportb (bottom_shift XX E x u) (eta_path u))).
assert (p : Id e_1 e_2).
unfold e_1.
unfold e_2.
unfold bottom_shift.
apply (first_and_second_fact _ _ XX E x u).
apply (transportb (fun z => Id (funcomp (d x (funcomp u (idfun (p1 XX)))) z) (d x u)) p).
apply (simplified_general_diagram_H XX E d x u).
Defined.

(**  General version of diagram (K) *) 

Definition general_diagram_K  (XX : P_Alg _ B)(E : (p1 XX) -> U)(d : forall (x : A)(u : B x -> (p1 XX))(v : forall y : B x, E (u y)), E( (p2 XX) (dpair _ x u))) : 
 forall (f g : (p1 XX) -> (p1 XX))(e : Id f g)(x : A)(u : B x -> (p1 XX)), 
 Id 
  (funcomp 
     (transportf (fun v : (p1 XX) -> (p1 XX) => forall y : B x, (E ( (funcomp u v) y))) e)
     (d x (funcomp u g)))
  (funcomp 
     (d x (funcomp u f))
     (transportf (fun v : (p1 XX) -> (p1 XX) => E ( (p2 XX) (dpair _ x (funcomp u v)))) e)).

Proof.
intros XX E d f g e x u.
set (X := (p1 XX)).
set (s_X := (p2 XX)).
set (P := (fun v : X -> X => forall y : B x, (E ( (funcomp u v) y)))).
set (Q := (fun v : X -> X => E (s_X (dpair _ x (funcomp u v))))).
set (s := (fun v : X -> X => d x (funcomp u v))).
apply (naturalityoftransportf P Q s e).
Defined.

Definition remark_on_general_diagram_K (XX : P_Alg _ B)(E : (p1 XX) -> U)(d : forall (x : A)(u : B x -> (p1 XX))(v : forall y : B x, E (u y)), E( (p2 XX) (dpair _ x u))) : 
 forall (f g : (p1 XX) -> (p1 XX))(e : Id f g)(x : A)(u : B x -> (p1 XX))(v : forall y : B x, E (f ( u  y))), 
 Id ((transportf (fun v : (p1 XX) -> (p1 XX) => forall y : B x, (E ( (funcomp u v) y))) e) v)
    (fun y : B x => ((transportf (fun z => E (z (u y))) e) (v y))).
Proof.
intros.
destruct e.
unfold transportf.
simpl.
unfold idfun.
apply funextsec.
intro y.
apply refl.
Defined.

End Preliminaries.

(** ** From h-initial algebras to W-types *) 


Section From_h_initial_algebra_to_W_types.

(** We fix the data for a polynomial functor *) 

Variable A : U.
Variable B : A -> U.

(** We assume to have a h-initial algebra *) 

Axiom WW : P_Alg _ B.
Axiom is : ishinitial _ B WW.

(** Some notation *) 

Definition W := p1 WW. 
Definition s_W := p2 WW : (P_0 _ B W) -> W.

(** We define the introduction terms *)
 

Definition sup (x : A)(u : B x -> W) : W := (s_W (dpair (fun a : A => (B a -> W)) x u)).

(** To derive the elimination rule, we 
 assume its premisses               *) 

Variable E : W -> U.
Variable d : forall (x : A)(u : B x -> W)(v : forall y : B x, E(u y)), E(sup x u).

(** We begin by constructing an algebra 
structure on (Sigma w : W) E w    *) 

Definition X := Sigma E.

Definition s_X : (P_0 _ B X) -> X.
Proof.
intro c.
destruct c as [x u].
split with (sup x (fun x => p1 (u x))).
apply (d x (fun x => p1 (u x)) (fun y : B x => p2 (u y))).
Defined.

Definition XX := (dpair (isalg _ B)  X s_X).

(** We apply the h-initiality of W to get 
 an algebra map from WW to XX          *) 


Definition jj : P_Alg_Map _ _  WW XX.
Proof.
apply (p1 (is XX)).
Defined.

Definition j : W -> X := (p1 jj).

Definition s_j : isalgmap _ _ WW XX j. 
Proof.
unfold isalgmap.
change (p2 WW) with s_W.
change (p2 XX) with s_X.
apply (p2 jj).
Defined.

Definition s_j_flat : forall w : (P_0 _ _ W), 
Id (j (s_W w)) (s_X (P_1 _ _ j w)).
Proof.
intros.
apply (toforallpaths _ _ _ s_j w). 
Defined.

(** We now show that the projection function    
 p1 : (Sigma w : W) --> W is an algebra map *)

Check p1.

Definition isalgmapp1 : isalgmap _ B XX WW (@p1 W E).
Proof.
intros.
unfold isalgmap.
apply funextfun.
intro c.
destruct c as [x u].
apply refl.
Defined.

Definition pp := (dpair (isalgmap _  _ XX WW) (@p1 W E) isalgmapp1).

(** By composition of j and p1 we get  
 an algebra map from W to itself.
 However, we construct a specific   
 proof that has good computational  
 properties    *)                     


Definition sigma_j : forall c : (P_0 _ B W), 
 Id (j (s_W c)) (s_X (P_1 _ _ j c)).
Proof.
apply (toforallpaths _ _ _ s_j).
Defined.

Definition sigma_j_1_2 : forall w : (P_0 _ B W),  
 Sigma (fun e :  Id (p1 (j (s_W w))) (p1 ((s_X (P_1 _ _ j w)))) =>
  Id (transportf E e (p2 (j (s_W w)))) (p2 ((s_X (P_1 _ _ j w))))).
Proof.
intros.
apply idsigmatosigmaid.
apply sigma_j.
Defined.

Definition sigma_j_1 : forall w : (P_0 _ B W),
 Id (p1 (j (s_W w))) (p1 ((s_X (P_1 _ _ j w)))).
Proof.
intros.
apply (p1 (sigma_j_1_2 w)).
Defined.

Definition sigma_j_2 : forall w : (P_0 _ B W),
  Id (transportf E (sigma_j_1 w) (p2 (j (s_W w)))) (p2 ((s_X (P_1 _ _ j w)))).
Proof.
intros.
apply (p2 (sigma_j_1_2 w)).
Defined.

Definition isalgmapjjpp : isalgmap _ _ _ _ (funcomp j (@p1 W E)) 
 := (funextfun _ _ sigma_j_1).


Definition jjpp := (dpair _ (funcomp j (@p1 W E))  isalgmapjjpp) : P_Alg_Map _ _ WW WW.

(** This will be useful in the following    
It is just a special case of the general 
 results on global vs pointwise transport *) 


Definition lemma_on_sigma_j : forall (w : P_0 _ B W)(t : E ( p1 ( j (s_W w)))), 
 Id 
(transportf (fun z : (P_0 _ _ W) -> W => E (z w))  isalgmapjjpp t)
(transportf E (sigma_j_1 w) t).
Proof.
intro w.
unfold isalgmapjjpp.
intro t.
apply pathsinv0.
set (e := toforallpaths _ _ _ (pointwisetransportfhomotopy _ _ E sigma_j_1 w)).
apply (e t).
Defined.
 
(** Exploiting again the h-initiality of W  
 we obtain that the composite of jj and 
 pp is equal to the identity map - and   
 so there is an algebra 2-cell between   
 them                                    *) 


Definition ee : P_Alg_2cell _ _ jjpp (idalgmap _ _ WW).
Proof. 
apply (weqfromaidalgmaptoalg2cell _ _ jjpp (idalgmap _ _ WW)).
apply (proofirrelevance _ (is WW) jjpp (idalgmap _ _ WW)).
Defined.

Definition e := (p1 ee) : Id (funcomp j (@p1 W E)) (idfun W).
Definition s_e := (p2 ee) : isalg2cell _ _  jjpp (idalgmap _ _ WW) e.

(** With the data constructed we can   
 define the elimination terms for W  *) 

Definition w_rec : forall w : W, E w := 
 (fun w : W => (transportf (fun z : W -> W => E (z w)) e (p2 (j w)))).

(** We now construct the special cases of the general 
 diagrams (G), (H) and (K) constructed above       *) 

Section Calculations.

Variable x : A.
Variable u : B x -> W.

(** Some useful abbreviations *) 

Definition v_1 := (fun y : B x => p2 ( j (u y))) : forall y : B x, E (p1 (j (u y))).
Definition v_2 := (transportf (fun z : W -> W => forall y : B x, E (funcomp u z y)) e v_1) : forall y : B x, E (u y).

Definition E_1 := (fun v : W -> W => forall y : B x, E (funcomp u v y)).
Definition E_2 (y : B x) := (fun z : W -> W => E (z (u y))).
Definition E_3 := (fun z : (P_0 _ _ W) -> W => E (z (dpair _ x u))).
Definition E_4 := (fun v : W -> W => E ( s_W (dpair _ x (funcomp u v)))).
Definition E_5 (w : W) := (fun z : W -> W => E (z w)).

(** The special case of diagram (G) *) 


Definition special_diagram_G :   
   Id
     (funcomp 
        (transportb E_3 isalgmapjjpp)
        (transportf E_3 (compfunwithpath s_W e)))
     (funcomp
        (transportf E_3 (comppathwithfun (P_2 _ _ e) s_W))
        (transportb E_3 (p2 (idalgmap A B WW)))).
Proof. 
intros.
unfold E_3.
set (p := (general_diagram_G _ _ WW WW jjpp (idalgmap _ _ WW) ee E)).
set (pxu := p (dpair _ x u)).
change     (fun z : P_0 A B W -> W =>
            E (z (dpair (fun a : A => B a -> W) x u))) with  (pullbackalongeval E (dpair (fun a : A => B a -> p1 WW) x u)).
change (p2 jjpp) with isalgmapjjpp in pxu.
change (p2 WW) with s_W in pxu.
change (p1 ee) with e in pxu.
apply pxu.
Admitted.

Definition simplified_special_diagram_G : 
   Id 
     (funcomp 
        (transportb E_3 isalgmapjjpp)
        (transportf E_3 (compfunwithpath s_W e)))
     (funcomp
        (transportf E_4 e)
        (transportb E_3 (p2 (idalgmap A B WW)))).
Proof.
intros.
apply (transportf (fun z => Id _ (funcomp z _)) (lemma_on_transportf A B s_W E x u e)).
apply (transportb (fun z => Id _ (funcomp _ z)) (lemma_on_transportb A B s_W E x u (p2 (idalgmap A B WW)))).
apply (special_diagram_G).
Defined.

(**  The special case of diagram (H) *) 


Definition super_simplified_special_diagram_H :
 Id  
  (funcomp (d x (funcomp u (idfun W))) (transportb E_3 (idfunisalgmap _ _ WW)))
  (d x u).
Proof.
intros.
apply (super_simplified_general_diagram_H _ _ WW E d x u).
Defined.


(** The special case of diagram (K) *) 

Definition special_diagram_K : 
 Id 
  (funcomp 
     (transportf E_1 e)
     (d x (funcomp u (idfun W))))
  (funcomp 
     (d x (funcomp u (funcomp j (@p1 W E))))
     (transportf E_4  e)).


Proof.
intros.
apply (general_diagram_K _ _ WW E d (funcomp j (@p1 W E)) (idfun W) e x u).
Defined.

Definition remark_on_special_diagram_K : 
 Id 
  (fun y : B x => transportf (E_2 y) e (p2 (j (u y))))
  (fun y : B x => w_rec (u y)). 
Proof.
intros.
apply refl.
Defined.

Definition second_remark_on_special_diagram_K : 
 Id 
 (transportf E_1 e (fun y : B x => p2 (j (u y))))
 (fun y : B x => w_rec ( u y)).
Proof.
intros.
apply (remark_on_general_diagram_K _ _ (dpair _ W s_W) E d  (funcomp j (@p1 W E)) (idfun W) e x u (fun y : B x => p2 (j ( u y)))).
Defined.

(** We now perform the long calculation that 
derives the propositional version of the  
 computation rule for W-types              *) 


(** Step 1 *) 

Definition step_1 : 
 Id (d x u (fun y => w_rec (u y))) 
    (d x u (fun y => transportf (E_2 y) e (v_1 y))).
Proof. 
apply refl.
Defined.

(** Step 2 *) 

Definition step_2 : 
 Id  
   (d x u (fun y => transportf (E_2 y) e (v_1 y)))
   (d x u v_2).
Proof.
assert (
p : Id 
  (transportf E_1 e v_1)
  (fun y => transportf (E_2 y) e (v_1 y))).
apply (remark_on_general_diagram_K _ _ (dpair _ W s_W) E d  (funcomp j (@p1 W E)) (idfun W) e x u v_1).
apply (transportf (fun z => Id (d x u z) _) p).
apply refl.
Defined.

(** Step 3 *) 

Definition step_3 : 
 Id 
   (d x u v_2)
   ((funcomp (d x (funcomp u (idfun W))) (transportb E_3 (idfunisalgmap _ _ WW))) v_2).
Proof. 
set (alpha := toforallpaths _ _ _ super_simplified_special_diagram_H).
apply (pathsinv0 (alpha (transportf E_1 e v_1))).
Defined.

(** Step 4 *) 

Definition step_4 : 
   Id  
     ((funcomp (d x (funcomp u (idfun W))) (transportb E_3 (idfunisalgmap _ _ WW))) v_2)
     ((transportb E_3 (idfunisalgmap _ _ WW))  (d x (funcomp u (idfun W)) v_2)).
Proof.
apply refl.
Defined.

(** Step 5 *) 

Definition lemma_for_step_5 : 
 Id  
   (d x (funcomp u (idfun W)) v_2)
   ((funcomp (d x (funcomp u (funcomp j (@p1 W E)))) (transportf E_4  e)) v_1).
Proof.
unfold v_1.
unfold v_2.
set (alpha := toforallpaths _ _ _ special_diagram_K).
apply (alpha v_1).
Defined.

Definition step_5 : 
  Id 
     ((transportb (fun z => E (z (dpair _ x u))) (idfunisalgmap _ _ WW)) 
         (d x (funcomp u (idfun W)) v_2))
     ((transportb (fun z => E (z (dpair _ x u))) (idfunisalgmap _ _ WW)) 
         ((funcomp (d x (funcomp u (funcomp j (@p1 W E)))) (transportf (fun v : W -> W => E ( s_W (dpair _ x (funcomp u v)))) e)) v_1)).
Proof.
apply maponpaths. 
apply lemma_for_step_5.
Defined.

(** Step 6 *) 

Definition step_6 :  
 Id  
   ((transportb E_3 (idfunisalgmap _ _ WW)) ((funcomp (d x (funcomp u (funcomp j (@p1 W E)))) (transportf E_4 e)) v_1))
   ((funcomp (transportf E_4 e) (transportb E_3 (idfunisalgmap _ _ WW))) (d x (funcomp u (funcomp j (@p1 W E))) v_1)).
Proof.
unfold funcomp.
simpl.
apply refl.
Defined.

(** Step 7 *) 

Definition step_7 : 
 Id 
    ((funcomp 
        (transportf E_4 e) 
        (transportb E_3 (idfunisalgmap _ _ WW))) 
            (d x (funcomp u (funcomp j (@p1 W E))) v_1))
    ((funcomp 
        (transportb E_3 isalgmapjjpp)
        (transportf E_3 (compfunwithpath s_W e))) 
            (d x (funcomp u (funcomp j (@p1 W E))) v_1)).
Proof.
set (s := (d x (funcomp u (funcomp j (@p1 W E))) v_1)).
set (alpha := (toforallpaths _ _ _ simplified_special_diagram_G)).
apply pathsinv0.
set (p := (alpha  s)).
change (P_0 A B W -> W) with (Sigma (fun a : A => B a -> p1 WW) -> (p1 WW)) in p.
change (p2 (idalgmap A B WW)) with (idfunisalgmap A B WW) in p.
apply p.
Admitted.

(** Step 8 *) 


Definition step_8 : 
 Id
  (transportf E_3 (compfunwithpath s_W e) ((transportb E_3 isalgmapjjpp) (d x (funcomp u (funcomp j (@p1 W E))) v_1)))
  (transportf E_3 (compfunwithpath s_W e) ((transportb E_3 isalgmapjjpp) (p2 (s_X (dpair _ x (funcomp u j)))))).
Proof.
unfold s_X.
apply refl.
Defined.

Definition steps_1_4 := pathscomp0 (pathscomp0 (pathscomp0 step_1 step_2) step_3) step_4.
Definition steps_1_8 := (pathscomp0 (pathscomp0 (pathscomp0 (pathscomp0 steps_1_4 step_5) step_6) step_7) step_8).

(** Step 9 *) 

Definition lemma_for_step_9 : 
  Id 
   (transportb E_3 isalgmapjjpp (p2 (s_X (dpair _ x (funcomp u j)))))
   (p2 (j (sup x u))).
Proof.
apply transposetransportfb.
set (e := (lemma_on_sigma_j (dpair _ x u) (p2 (j (s_W (dpair _ x u)))))).
apply (transportb (fun z => Id _ z) e).
apply (pathsinv0 (sigma_j_2 (dpair _ x u))).
Defined.

Definition step_9 : 
 Id 
   (transportf E_3 (compfunwithpath s_W e) ((transportb E_3 isalgmapjjpp) (p2 (s_X (dpair _ x (funcomp u j))))))
   (transportf E_3 (compfunwithpath s_W e) (p2 (j (sup x u)))).
Proof.
apply (transportf (fun z => Id _ (transportf E_3 (compfunwithpath s_W e) z)) lemma_for_step_9).
apply refl.
Defined.

(** Step 10 *) 

Definition step_10 : 
 Id 
  (transportf E_3 (compfunwithpath s_W e) (p2 (j (sup x u))))
  (w_rec (sup x u)).
Proof.
unfold w_rec.
unfold E_3.
apply pathsinv0.
change (fun z : W -> W => E (z (sup x u))) with (pullbackalongeval E (sup x u)).
unfold pullbackalongeval.
apply (second_lemma_on_transportf _ _ s_W E x u e (p2 (j (sup x u)))).
Defined.

(** Putting it all together *) 

Definition step_9_10 := (pathscomp0 step_9 step_10).

Definition w_comp_calculation := (pathscomp0 steps_1_8 step_9_10).

End Calculations.

(** The W-computation rule                *)


Definition w_comp : forall (x : A)(u : B x -> W), 
 Id (w_rec (sup x u)) (d x u (fun y : B x => w_rec ( u y))).

Proof. 
intros.
apply (pathsinv0 (w_comp_calculation x u)).
Defined.

End From_h_initial_algebra_to_W_types.


