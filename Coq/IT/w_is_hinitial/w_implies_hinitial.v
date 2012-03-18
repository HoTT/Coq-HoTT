Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".
Add Rec LoadPath "../inductive_types".

Unset Automatic Introduction.
Require Export uu0.
Require Export identity.
Require Export polynomial_functors.
Require Export w.

(** * From W-types to h-initiality *) 

Section From_W_types_to_h_initiality.

Variable A : U.
Variable B : A -> U.

Notation W := (W A B).

(** We prove that the rules for W-types give us a h-initial algebra *)

Definition s_W : (P_0 A B W) -> W := 
 fun c => match c with dpair x u => sup A B x u end.

Definition WW := (dpair _ W s_W) : P_Alg A B.

(** We consider another algebra. For simplicity we first prove the claim for algebras in canonical form *) 

Section Towards_contractibility.

Variable E : U.
Variable s_E : (P_0 _ B E) -> E.

Definition EE := (dpair _ E s_E) : P_Alg _ B.

(** The map j : W --> E, which we will show to be an algebra map 
It is defined by W-recursion, so we construct the eliminating term. *)


Definition d_j : forall (x : A)(u : B x -> W)(v : B x -> E), E := 
  fun (x : A)(u : B x -> W)(v : B x -> E) => s_E ( dpair _ x v ).

Definition j : W -> E :=  (fun w => w_rec A B (fun _ => E) d_j w).

(** The result of the W-computation rule on j. *)

Definition w_comp_j (x : A)(u : B x -> W) : Id  ( j ( sup A B x u ) )( d_j x u (funcomp u j )).
Proof. 
intros. 
apply (w_beta A B (fun _ : W => E) d_j x u).
Defined. 
 
(** Construction of a homotopy sigma_j which is used to show that j is an 
 algebra map. *)

Definition sigma_j : forall c : (P_0 _ B W), Id (j (s_W c)) ( s_E ((P_1 _ B j) c)).
Proof. 
intro.
destruct c as [x u].
apply (w_comp_j x u).
Defined.
 
Definition sigma_j_sharp : (isalgmap _ _ WW EE j).
Proof.
apply funextfun. 
apply sigma_j.
Defined.

(** We introduce a notation for the algebra map (j, sigma_j_sharp), which will be the center of the contraction *) 

Definition jj := (dpair _ j sigma_j_sharp) : (P_Alg_Map _ _ WW EE).

(** We now assume that to have a  algebra map kk : WW -> EE and we show that it is propositionally equal to jj 
For simplicity, we first prove this for algebra maps in canonical form *) 

Variable k : W -> E.
Variable s_k : isalgmap _ _ WW EE k.
Definition kk := (dpair _ k s_k) : P_Alg_Map _ _ WW EE.

(** The homotopy associated to s_k  *)

Definition s_k_flat : forall x : P_0 _ _ W, Id ( k  (s_W x)) ( s_E ( (P_1 _ _ k ) x)).
Proof. 
apply weqtoforallpaths. 
apply s_k.
Defined.

(** Construction of the homotopy from j to k by W-elimination *) 

Definition d_theta (x : A)(u : B x -> W)(v : forall (y : B x), Id (j (u y)) (k (u y))) : 
 Id (j ( sup A B x u)) (k ( sup A B x u )). 
Proof. 
intros.
assert (e_1 : Id ((j ( sup A B x u))) (s_E (dpair _ x (funcomp u j)))).
apply (sigma_j (dpair _ x u)).
assert (e_2 : Id (s_E (dpair _ x (funcomp u j))) (s_E (dpair _ x (funcomp u k)))).
apply maponpaths.
apply (tau _ _ _ _ j k x u v).
assert (e_3 : Id  (s_E (dpair _ x (funcomp u k)))  (k ( sup A B x u ))).
apply (pathsinv0  (s_k_flat ( dpair _ x u))).
apply (pathscomp0 (pathscomp0 e_1 e_2) e_3).
Defined.

(** The homotopy between j and k *)
 
Definition theta : forall w : W,  Id (j w) (k w) := 
 (fun w : W => (w_rec A B (fun w : W => Id (j w) (k w)) d_theta w)).

Definition theta_comp (x : A)(u : B x -> W) : 
 Id (theta (sup A B x u) ) (d_theta x u  (fun y : B x => theta ( u y )) ) :=
  (w_beta A B (fun w : W => Id (j w) (k w)) d_theta x u).

(** Verification that theta is a algebra map homotopy *) 

Definition s_theta : isalgmaphomotopy _ _ j sigma_j k s_k_flat theta.
Proof.
intros.
intro c.
destruct c as [x u].
apply cancellationlemma. 
apply (maponpaths (fun m : Id (j (sup A B x u)) (k (sup A B x u)) => (pathscomp0 m (s_k_flat (dpair _ x u))))).
apply (theta_comp x u).
Defined.

(** The path p : Id k j associated to theta *) 

Definition p := (funextfun _ _ theta) : Id j k.

(** The proof that p is an algebra 2-cell. This exploits the work on 
relating algebra map homotopies and algebra map 2-cells done earlier *) 

Definition s_p : isalg2cell _ _ jj kk p.
Proof. 
set (sigma_j_sharp := (funextfun (funcomp s_W j) (funcomp (P_1 _ _ j) s_E) sigma_j)).
set (s_k_flat_sharp := (funextfun (funcomp s_W k) (funcomp (P_1 _ _ k) s_E) s_k_flat)).
set (useful := (alghomotopytoalg2cell _ _ W s_W E s_E j sigma_j k s_k_flat theta s_theta)).
assert (almost_s_p : isalg2cell _ _ jj (dpair _ k s_k_flat_sharp) p).
unfold jj.
apply useful.
assert (e : Id s_k s_k_flat_sharp).
apply (homotinvweqweq0 (weqtoforallpaths _ (funcomp s_W k) (funcomp (P_1 _ _ k) s_E)) s_k).
set (C := (fun u => isalg2cell _ _ jj
                 (dpair (fun f : p1 WW -> p1 EE => isalgmap _ _ WW EE f) k
                    u) p)).
apply (transportb C e).
apply useful.
Defined.

(** Proof that (j,alpha) is propositionally equal to kk *) 

Definition pq : Id jj kk.
Proof.
(apply 
(weqfromalg2celltoidalgmap _ _ jj kk (dpair _ p s_p))).
Defined.



End Towards_contractibility.



(** Proof of h-initiality of W *)

Theorem w_types_are_h_initial : ishinitial _ _ WW.
Proof.  
unfold ishinitial. 
intro EE. 
destruct EE as [E s_E].
split with (jj E s_E). 
intro kk. 
destruct kk as [k s_k]. 
apply (pathsinv0 (pq E s_E k s_k)).
Defined.

End From_W_types_to_h_initiality.