(* We show that in the presence of function extensionality, W-types  *) 
(* allow us to define a type of natural numbers that satisfies the   *)  
(* usual introduction and elimination rules and a variant of the     *)
(* computation rules in which definition equalities are replaced by  *) 
(* propositional ones                                                *) 

(* The key step is to define propositional equalities expressing the *)
(* eta rule for maps out of the empty and unit type which reduce to  *)
(* reflexivity terms when applied to functions that are already in   *)
(* eta-expanded form                                                 *) 

Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".
Add Rec LoadPath "../inductive_types".
Add Rec LoadPath "../nat_as_w_type".

Unset Automatic Introduction.

Require Export nat_as_w_type.
Require Export uu0.
Require Export identity.
Require Export zero.
Require Export one.
Require Export two.
Require Export w.
Require Export nat_as_w_type.

Axiom Three : U.
Axiom left : Three.
Axiom center : Three.
Axiom right : Three.
Axiom three_rec : forall (E : Three -> Type)(e_l : E left)(e_c : E center)(e_r : E right)(x : Three), E x.
Axiom three_beta_l : forall (E : Three -> Type)(e_l : E left)(e_c : E center)(e_r : E right), 
 Id (three_rec E e_l e_c e_r left)(e_l). 
Axiom three_beta_c : forall (E : Three -> Type)(e_l : E left)(e_c : E center)(e_r : E right), 
 Id (three_rec E e_l e_c e_r center) e_c. 
Axiom three_beta_r : forall (E : Three -> Type)(e_l : E left)(e_c : E center)(e_r : E right), 
 Id (three_rec E e_l e_c e_r right) e_r. 

Definition transport_zero (X : U)(e : Id Nat X) : X.
Proof.
intros.
destruct e.
apply zero.
Defined.

Definition transport_suc (X : U)(e : Id Nat X) : X -> X.
Proof.
intros X e.
destruct e.
apply suc.
Defined.

Definition transport_rec (X : U)(e : Id Nat X)(E : X -> U)(c : E (transport_zero X e))(d : forall x : X, E x -> E (transport_suc X e x)) : 
 forall x : X, E x.
Proof.
intros X e E c d.
destruct e.
apply (nat_rec E c d).
Defined.

Definition transport_beta_z  (X : U)(e : Id Nat X)(E : X -> U)(c : E (transport_zero X e))(d : forall x : X, E x -> E (transport_suc X e x)) :
 Id (transport_rec X e E c d (transport_zero X e)) c.
Proof.
intros X e E c d.
destruct e.
apply (nat_beta_z E c d).
Defined.

Definition transport_beta_s  (X : U)(e : Id Nat X)(E : X -> U)(c : E (transport_zero X e))(d : forall x : X, E x -> E (transport_suc X e x)) :
 forall x : X, Id (transport_rec X e E c d (transport_suc X e x)) (d x (transport_rec X e E c d x)).
Proof.
intros X e E c d x.
destruct e.
apply (nat_beta_s E c d x).
Defined.

(* Second number class as a W-type *) 

Definition AA := Three.

Definition BB : AA -> U := 
 fun x : AA => (three_rec (fun _ : AA => U) Zero One Nat x).

Definition o2 := W AA BB.

(** The propositional computation rules for Bool give us proofs that 
 Empty is propositionally equal to (B false) and Unit is propositionally
 equal to (B true). We will use these paths to transport the structure 
 of h-initial and h-terminal *) 

Definition e_l : Id Zero (BB left).
Proof.
unfold BB.
apply (pathsinv0 (three_beta_l (fun _ : AA => U) Zero One Nat)).
Defined.

Definition e_c : Id One (BB center).
Proof.
unfold BB.
apply (pathsinv0 (three_beta_c (fun _ : AA => U) Zero One Nat)).
Defined.

Definition e_r : Id Nat (BB right).
Proof.
unfold BB.
apply (pathsinv0 (three_beta_r (fun _ : AA => U) Zero One Nat)).
Defined.

(** Some notation *) 

Definition BB_l := BB left.
Definition BB_c := BB center.
Definition BB_r := BB right.

(** We transport the structure from Zero to BB_l. *) 

Definition BB_l_rec := (zero_rec_transfer BB_l (e_l)).

(* The adjoint homotopy equivalence between (BB_l -> o2) and One *) 

Definition f_BB_l := f_initial BB_l o2.
Definition g_BB_l := g_initial BB_l BB_l_rec o2.
Definition e_gf_BB_l := e_gf_initial BB_l BB_l_rec o2.
Definition e_fg_BB_l := e_fg_initial B_f B_f_rec o2.
Definition first_triangular_law_BB_l := first_triangular_law_initial BB_l BB_l_rec o2.
Definition second_triangular_law_BB_l := second_triangular_law_initial BB_l BB_l_rec o2.

(* We transport the structure from One to BB_c *)

Definition unit_BB_c := transport_unit BB_c e_c.
Definition BB_c_rec := transport_one_rec BB_c e_c.
Definition BB_c_beta := transport_one_beta BB_c e_c.

(* The adjoint homotopy equivalence between (BB_c -> o2) and o2 *) 

Definition f_BB_c := (f_terminal BB_c unit_BB_c o2).
Definition g_BB_c := (g_terminal BB_c unit_BB_c  BB_c_rec o2).
Definition e_gf_BB_c := (e_gf_terminal BB_c unit_BB_c  BB_c_rec BB_c_beta o2).
Definition e_fg_BB_c := (e_fg_terminal BB_c unit_BB_c  BB_c_rec BB_c_beta o2).
Definition first_triangular_law_BB_c := (first_triangular_law_terminal  BB_c unit_BB_c  BB_c_rec BB_c_beta o2).
Definition second_triangular_law_BB_c := (second_triangular_law_terminal  BB_c unit_BB_c  BB_c_rec BB_c_beta o2).

(** We transport the structure from Nat to BB_right *) 

Definition zero_BB_r := transport_zero BB_r e_r.
Definition suc_BB_r := transport_suc BB_r e_r.
Definition rec_BB_r := transport_rec BB_r e_r.
Definition BB_r_z := transport_beta_z BB_r e_r.
Definition BB_r_s := transport_beta_s BB_r e_r.

Definition zero_o2 := 
  sup _ _ left (g_BB_l unit).

Definition succ_o2 : o2 -> o2 := 
 fun w : o2 => (sup AA BB center (g_BB_c w)).

Definition sup_o2 : (BB_r -> o2) -> o2 := 
 fun u : (BB_r -> o2) => sup AA BB right u.

(** Derivation of the elimination and computation rules *) 

Section Elimination_and_computation_rules_for_o2.

Variable E : o2 -> U.
Variable c : E zero_o2.
Variable d : forall x : o2, E x -> E (succ_o2 x).
Variable e : forall (u : BB_r -> o2)(v : forall y : BB_r, E (u y)), E (sup_o2 u).

(** We now derive the premisses of the W-elimination rule *) 

Definition e_zero_o2  :
 forall (u : BB_l -> o2)(v : forall y : BB_l, E (u y)), E (sup AA BB left u).
Proof. 
intros.
set (p_u := e_gf_BB_l u).
apply (transportf (fun z => E (sup AA BB left z)) p_u c).
Defined.

Definition e_suc_o2  :
 forall (u : BB_c -> o2)(v : forall y : BB_c, E (u y)), E (sup AA BB center u).
Proof.
intros.
set (p_u := e_gf_BB_c u).
apply (transportf (fun z => E (sup AA BB center z)) p_u (d (u unit_BB_c) (v unit_BB_c))).
Defined.

Definition e_sup_o2 : 
  forall (u : BB_r -> o2)(v : forall y : BB_r, E (u y)), E (sup AA BB right u).
Proof.
intros.
apply (e u v).
Defined.

Definition e_zero_suc_sup_o2 : 
 forall (x : AA)(u : BB x -> o2)(v : forall y : BB x, E (u y)), E (sup AA BB x u).
Proof.
intros.
set (E' := fun x : Three => forall (u : BB x -> o2)(v : forall y : BB x, E (u y)), E (sup AA BB x u)).
apply (three_rec E' (fun u v => (e_zero_o2 u v)) (fun u v => (e_suc_o2 u v))  (fun u v => (e_sup_o2 u v))).
apply v.
Defined.

(** The elimination rule *) 

Definition o2_rec : forall w : o2, E w := 
 fun w : o2 => (w_rec AA BB E e_zero_suc_sup_o2 w).

(** Derivation of the first computation rules *) 

Definition first_o2_comp  : 
 Id (o2_rec zero_o2) c.
Proof.
intros.
unfold o2_rec.
unfold zero_o2.
set (u := (g_BB_l unit)).
apply (transportb (fun z => Id z c) (w_beta AA BB E e_zero_suc_sup_o2 left u)).
set (v :=  (fun y : BB_l => w_rec AA BB E e_zero_suc_sup_o2 (u y))).
assert (p : Id  (e_zero_suc_sup_o2 left u v)  (e_zero_o2 u v)).
set (E' := fun x : Three => forall (u : BB x -> o2)(v : forall y : BB x, E (u y)), E (sup AA BB x u)).
set (p_1 := ((three_beta_l E' (fun u v => (e_zero_o2 u v)) (fun u v => (e_suc_o2 u v))  (fun u v => (e_sup_o2 u v))))).
set (phi_1 := (toforallpaths _ _ _ p_1)).
set (p_2 := phi_1 u).
set (phi_2 := toforallpaths _ _ _ p_2).
apply (phi_2 v).
apply (transportb (fun z => Id z c) p).
unfold e_zero_o2.
unfold u.
apply (transportb (fun e => Id
     (transportf (fun z : BB_l -> W AA BB => E (sup AA BB left z)) e c) c) (second_triangular_law_BB_l unit)).
change (W AA BB) with o2.
change (BB left) with BB_l.
change (g_initial BB_l BB_l_rec o2) with (g_BB_l).
change (e_fg_initial BB_l BB_l_rec o2) with (e_fg_BB_l).
assert (q : Id (e_fg_BB_l unit) (refl unit)).
unfold e_fg_BB_l.
unfold e_fg_BB_l.
apply (one_beta (fun z : One => Id unit z) (refl unit)).
rewrite q.
unfold maponpaths.
unfold transportf.
simpl.
apply refl.
Defined.


(* An auxiliary definition *) 

Definition EEE := (fun z : (BB_c -> o2) => E (sup AA BB center z)).

Definition w_rec_o2 := w_rec AA BB E e_zero_suc_sup_o2.
Definition w_comp_o2 := w_beta AA BB E e_zero_suc_sup_o2.

(** Two lemmas useful to derive the second computation rule *) 

Definition first_lemma_for_o2_beta : 
 forall (w w' : o2)(p : Id w w')(x : E w),
  Id (transportf EEE (maponpaths g_BB_c p) (d w x)) (d w' (transportf E p x)).
Proof.
intros.
destruct p.
apply refl.
Defined.

Definition second_lemma_for_o2_beta : 
 forall (w w' : o2)(p : Id w w'), 
  Id (d w' (transportf E p (w_rec_o2 w))) (d w' (w_rec_o2 w')).
Proof.
intros.
destruct p.
apply refl.
Defined.

(** The second computation rule *) 

Definition second_o2_comp  : 
 forall w : o2, Id (o2_rec (succ_o2 w)) (d w (o2_rec w)).
Proof.
intros.
unfold succ_o2.
unfold o2_rec.
apply (transportb (fun z => Id z _) (w_comp_o2 center (g_BB_c w))).
set (u_w := (g_BB_c w)).
set (v_w :=  (fun y : BB_c => w_rec_o2 (u_w y))).
assert (p : Id (e_zero_suc_sup_o2 center u_w v_w)  (e_suc_o2 u_w v_w)).
set (E' := fun x : Three => forall (u : BB x -> o2)(v : forall y : BB x, E (u y)), E (sup AA BB x u)).
set (p_1 := ((three_beta_c E' (fun u v => (e_zero_o2 u v)) (fun u v => (e_suc_o2 u v)) (fun u v => (e_sup_o2 u v))))).
set (phi_1 := (toforallpaths _ _ _ p_1)).
set (p_2 := phi_1 u_w).
set (phi_2 := toforallpaths _ _ _ p_2).
apply (phi_2 v_w).
change (w_rec AA BB E e_zero_suc_sup_o2) with w_rec_o2.
apply (transportb (fun z => Id z _) p).
unfold e_suc_o2.
change (fun z : BB_c -> W AA BB => E (sup AA BB center z)) with EEE.
change (v_w unit_BB_c) with (w_rec_o2 (f_BB_c (g_BB_c w))).
change (u_w unit_BB_c) with (f_BB_c (g_BB_c w)).
unfold u_w.
apply (transportb (fun z =>  (Id (transportf EEE z _) _))  (second_triangular_law_BB_c w)).
change (g_terminal BB_c unit_BB_c BB_c_rec o2) with g_BB_c.
change (e_fg_terminal BB_c unit_BB_c BB_c_rec BB_c_beta o2) with (e_fg_BB_c).
set (q_1 := (first_lemma_for_o2_beta  (f_BB_c (g_BB_c w)) w (e_fg_BB_c w) (w_rec_o2 (f_BB_c (g_BB_c w))))).
set (q_2 := (second_lemma_for_o2_beta (f_BB_c (g_BB_c w)) w (e_fg_BB_c w))).
apply (pathscomp0 q_1 q_2).
Defined.

Definition third_o2_comp  : 
 forall u : BB_r -> o2, Id (o2_rec (sup_o2 u)) (e u (fun y : BB_r => o2_rec (u y))).
Proof.
intros.
unfold o2_rec.
apply (transportb (fun z => Id z _) (w_beta AA BB E _ right _)).
set (E' := fun x : Three => forall (u : BB x -> o2)(v : forall y : BB x, E (u y)), E (sup AA BB x u)).
set (p_1 := ((three_beta_r E' (fun u v => (e_zero_o2 u v)) (fun u v => (e_suc_o2 u v))  (fun u v => (e_sup_o2 u v))))).
set (phi_1 := (toforallpaths _ _ _ p_1)).
set (p_2 := phi_1 u).
set (phi_2 := toforallpaths _ _ _ p_2).
set (v :=  (fun y : BB_r => w_rec AA BB E e_zero_suc_sup_o2 (u y))).
apply (phi_2 v).
Defined.

End Elimination_and_computation_rules_for_o2.