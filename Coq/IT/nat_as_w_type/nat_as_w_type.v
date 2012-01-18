(** We show that in the presence of the types

- Zero, One, Two with propositional computation rules
- W-types with propositional computation rules
- propositional function extensionality

we get

- Nat with propositional computation rules.

*)                                               


Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".
Add Rec LoadPath "../inductive_types".

Unset Automatic Introduction.
Require Export uu0.
Require Export identity.
Require Export zero.
Require Export one.
Require Export w.

(** * H-terminal types *) 

Section H_terminal_type.

(** We show that if a type X satisfies the rules for the h-initial type, then for every 
type Y there is an adjoint homotopy equivalence between (X -> Y) and Y *)

(** Axioms for a h-terminal type *)

Variable X : U.
Variable x_0 : X. 
Variable rec : forall (E : X -> U)(e : E x_0)(x : X), E x.
Variable comp : forall (E : X -> U)(e : E x_0), Id (rec E e x_0) e.

(** We show that for any type Y, there is an adjoint homotopy equivalence between X -> Y and Y *)

Variable Y : U.

Definition f_terminal : (X -> Y) -> Y := 
 fun (u : X -> Y) => u x_0.

(** Like any function between types, the map f extends in a canonical way to paths. Below, we give an 
explicit expression for it *) 

Definition f_terminal_on_paths {u u' : X -> Y} : 
 Id u u' -> Id (f_terminal u) (f_terminal u').
Proof.
intros u u' e.
unfold f_terminal.
apply (toforallpaths _ _ _ e x_0).
Defined.

Definition f_terminal_on_paths_vs_map_on_paths  {u u' : X -> Y} : 
 forall (e : Id u u'), Id (f_terminal_on_paths e) (maponpaths f_terminal e).
Proof.
intros.
destruct e.
simpl.
unfold f_terminal.
apply refl.
Defined.

Definition g_terminal   : Y -> (X -> Y) :=
 fun (y : Y) => rec (fun _ : X => Y) y.

(** Again, we need an expression for the canonical action of g on paths. We give
first a definition from paths to homotopies *) 

Definition g_terminal_from_paths_to_hom  {y y' : Y} : Id y y' -> Hom (g_terminal y) (g_terminal y').
Proof.
intros y y' e.
unfold g_terminal.
intro x.
apply (rec (fun z => Id (rec (fun _ : X => Y)  y z) (rec (fun _ : X => Y) y' z))).
apply (pathscomp0 (pathscomp0 (comp (fun _ : X => Y)  y) e) (pathsinv0 (comp (fun _ : X => Y) y'))).
Defined.

Definition g_terminal_from_paths_to_hom_vs_map_on_paths  {y y' : Y} : 
 forall (e : Id y y'), Id ( g_terminal_from_paths_to_hom e) (fun x : X => maponpaths (fun z => (g_terminal z x)) e).
Proof.
intros.
destruct e.
simpl.
apply funextsec.
intro x.
apply (rec (fun z =>  Id (g_terminal_from_paths_to_hom (refl y) z) (refl (g_terminal y z)))).
unfold g_terminal_from_paths_to_hom.
apply 
 (transportb (fun z => Id z (refl (g_terminal y x_0))) (comp (fun z : X => Id (rec (fun _ : X => Y) y z) (rec (fun _ : X => Y) y z))
        (pathscomp0 (pathscomp0 (comp (fun _ : X => Y) y) (refl y))
           (pathsinv0 (comp (fun _ : X => Y) y))))).
unfold g_terminal.
set (u_y := (rec (fun _ : X => Y) y x_0)).
set (E := (fun _ : X => Y)).
set (s := (comp E y)).
simpl.
apply (transportb (fun z =>  Id (pathscomp0 z (pathsinv0 s)) (refl u_y)) (pathscomp0rid s)).
apply (transportb (fun z => Id z _) (pathsinv0r s)).
apply refl.
Defined.

Definition g_terminal_on_paths  {y y' : Y} : 
 Id y y' -> Id (g_terminal y) (g_terminal y').
Proof.
intros y y' e.
unfold g_terminal.
apply funextfun.
apply (g_terminal_from_paths_to_hom e).
Defined.

Definition g_terminal_on_paths_vs_map_on_paths  {y y' : Y} : 
 forall (e : Id y y'), Id (g_terminal_on_paths e) (maponpaths g_terminal e).
Proof.
intros.
destruct e.
simpl.
unfold g_terminal_on_paths.
apply (transportb (fun z => Id (funextfun (rec (fun _ : X => Y) y) (rec (fun _ : X => Y) y) z) (refl (g_terminal y))) 
  (g_terminal_from_paths_to_hom_vs_map_on_paths (refl y))).
unfold maponpaths.
change (fun x : X => refl (g_terminal y x)) with (toforallpaths _ _ _ (refl (g_terminal y))).
apply (homotinvweqweq (weqtoforallpaths _ _ _) (refl (g_terminal y))).
Defined.

(** The counit e_fg_terminal : FG ==> 1 *) 

Definition e_fg_terminal   : forall (y : Y), Id (f_terminal (g_terminal y)) y.
Proof.
intros.
unfold g_terminal.
unfold f_terminal.
apply (comp (fun _ : X => Y) y).
Defined.

(** The unit e_gf_terminal : GF ==> 1 *) 

Definition hom_e_gf_terminal   : 
 forall (u : X -> Y)(x : X), Id ((g_terminal (f_terminal u)) x) (u x).
Proof.
intros u x.
apply (rec (fun z => Id (g_terminal (f_terminal u) z) (u z))).
unfold f_terminal.
unfold g_terminal.
apply (e_fg_terminal (u x_0)).
Defined.

Definition e_gf_terminal   : 
 forall (u : X -> Y), Id (g_terminal (f_terminal u)) u.
Proof.
intros.
apply (funextfun _ _ (hom_e_gf_terminal u)).
Defined.

(** From the homotopy equivalence, we get a weak equivalence *) 

Definition weq_terminal   : 
 weq (X -> Y) Y.
Proof.
intros.
apply (weqgradth f_terminal g_terminal e_gf_terminal e_fg_terminal).
Defined.

(** The first triangular law *) 

Definition towards_first_triangular_law_terminal   : 
 forall (u : X -> Y), Id (f_terminal_on_paths (e_gf_terminal u)) (e_fg_terminal (f_terminal u)).
Proof.
intros.
unfold e_gf_terminal.
unfold f_terminal_on_paths.
assert (p : Id (toforallpaths _ _ _ (funextfun _ _ (hom_e_gf_terminal u))) (hom_e_gf_terminal u)).
apply (homotweqinvweq (weqtoforallpaths _ _ _) (hom_e_gf_terminal u)).
apply (transportb (fun x => Id (x x_0) _) p).
unfold f_terminal.
unfold hom_e_gf_terminal.
set (E := (fun x : X => Id (g_terminal (f_terminal u) x) (u x))).
set (e := (comp (fun _ : X => Y) (u x_0))).
apply (comp E e).
Defined.

Definition first_triangular_law_terminal  : 
  forall (u : X -> Y), Id ((maponpaths f_terminal) (e_gf_terminal u)) (e_fg_terminal (f_terminal u)).
Proof.
intros.
set (p := (f_terminal_on_paths_vs_map_on_paths (e_gf_terminal u))).
apply (transportf (fun z =>  Id z (e_fg_terminal (f_terminal u))) p).
apply (towards_first_triangular_law_terminal u).
Defined.

Definition towards_second_triangular_law_terminal : 
 forall (y : Y), Id (e_gf_terminal (g_terminal y)) (g_terminal_on_paths (e_fg_terminal y)).
Proof.
intros.
unfold e_gf_terminal.
unfold g_terminal_on_paths.
apply maponpaths.
apply funextsec.
set (u_y := g_terminal y).
intro x.
apply (rec (fun z => Id (hom_e_gf_terminal u_y z) (g_terminal_from_paths_to_hom (e_fg_terminal y) z))).
assert (p_1 : Id  (hom_e_gf_terminal u_y x_0)  (e_fg_terminal (u_y x_0))).
apply (comp (fun z => Id (g_terminal (f_terminal u_y) z) (u_y z)) (e_fg_terminal (u_y x_0))).
apply (transportb (fun x => Id x _) p_1).
unfold g_terminal_from_paths_to_hom.
set (E_1 :=  (fun _ : X => Y)).
set (E_2 := (fun z : X => Id (rec E_1 (f_terminal (g_terminal y)) z) (rec E_1 y z))).
change  (Id (e_fg_terminal  (u_y x_0))
     (rec E_2 (pathscomp0 (pathscomp0 (comp E_1 (f_terminal (g_terminal y))) (e_fg_terminal y)) (pathsinv0 (comp E_1 y))) x_0)).
assert (p_2 : 
 Id (rec E_2 (pathscomp0 (pathscomp0 (comp E_1 (f_terminal (g_terminal y))) (e_fg_terminal y)) (pathsinv0 (comp E_1 y))) x_0) 
                  (pathscomp0 (pathscomp0 (comp E_1 (f_terminal (g_terminal y))) (e_fg_terminal y)) (pathsinv0 (comp E_1 y)))).
apply (comp E_2 _).
apply (transportb (fun z => Id _ z) p_2).
change (g_terminal y) with (u_y).
unfold e_fg_terminal.
change (fun _ : X => Y) with E_1.
unfold f_terminal.
set (s := (comp E_1 (u_y x_0))).
set (t := (comp E_1 y)).
apply (transportb (fun z => Id _ z) (pathsinv0 (pathscomp0assoc s t (pathsinv0 t)))). 
apply (transportb (fun z => Id _ (pathscomp0 s z)) (pathsinv0r t)).
apply (transportb (fun z => Id _ z) (pathscomp0rid s)).
apply refl.
Defined.

Definition second_triangular_law_terminal : 
 forall (y : Y), Id (e_gf_terminal (g_terminal y)) ((maponpaths g_terminal) (e_fg_terminal y)).
Proof.
intros.
set (p := (g_terminal_on_paths_vs_map_on_paths (e_fg_terminal y))).
apply (transportf (fun z => Id (e_gf_terminal (g_terminal y)) z) p).
apply (towards_second_triangular_law_terminal y).
Defined.

End H_terminal_type.

(* If we have a type X and a proof of Id(One, X), then X satisfies the axioms for a h-terminal type. 
This implies that for every type Y there is an adjoint homotopy equivalence between (X -> Y) and Y *) 

Definition transport_unit : 
 forall (X : U)(e : Id One X), X.
Proof.
intros.
destruct e.
apply unit.
Defined.

Definition transport_one_rec : 
 forall (X : U)(e : Id One X),  forall (E : X -> U)(y : E (transport_unit X e))(x : X), E x.
Proof.
intros.
destruct e.
apply (one_rec E y x).
Defined.

Definition transport_one_beta : 
 forall (X : U)(e : Id One X), forall (E : X -> U)(y : E (transport_unit X e)), Id (transport_one_rec X e E y (transport_unit X e)) y.
Proof.
intros.
destruct e.
apply (one_beta E y).
Defined.

(** We now consider a type X that satisfies the axioms for a h-initial type and show that for
every type Y there is is an adjoint homotopy equivalence between (X -> Y) and One *) 

Section Universal_property_of_h_initial.

Variable X : U.
Variable X_rec : forall (E : X -> U)(x : X), E x.

Variable Y : U.

Definition f_initial : (X -> Y) -> One := 
 fun _ : X -> Y => unit.

Definition f_initial_on_paths {u u' : X -> Y} : Id u u' -> Id (f_initial u) (f_initial u').
Proof.
intros u u' e.
apply (refl unit).
Defined.

Definition f_initial_on_paths_vs_maponpaths {u u' : X -> Y} : forall e : Id u u', Id (f_initial_on_paths e)(maponpaths f_initial e).
Proof.
intros.
destruct e.
apply refl.
Defined.

Definition g_initial : One -> (X -> Y) := 
 fun _ : One => (fun x : X => X_rec (fun _ : X => Y) x).

Definition g_initial_on_paths {x x' : One} : Id x x' -> Id (g_initial x) (g_initial x').
Proof.
intros x x' e.
unfold g_initial.
apply refl.
Defined.

Definition g_initial_on_paths_vs_maponpaths {x x' : One} : forall e : Id x x', Id (g_initial_on_paths e) (maponpaths g_initial e).
Proof.
intros.
destruct e.
apply refl.
Defined.

Definition e_gf_initial : forall u : X -> Y, Id (g_initial ( f_initial u)) u.
Proof.
intros.
apply funextfun.
intro x.
apply (X_rec (fun z => Id (g_initial (f_initial u) z) (u z)) x).
Defined.

Definition e_fg_initial : forall x : One, Id (f_initial (g_initial x)) x.
Proof.
intros.
unfold f_initial.
apply (one_rec (fun z => Id unit z) (refl unit)).
Defined.

Definition towards_first_triangular_law_initial : forall u : X -> Y, Id (f_initial_on_paths (e_gf_initial u)) (e_fg_initial (f_initial u)).
Proof.
intro u.
unfold f_initial.
unfold e_fg_initial.
apply (transportb (fun zz => Id (f_initial_on_paths (e_gf_initial u)) zz) (one_beta (fun z : One => Id unit z) (refl unit))).
unfold f_initial_on_paths.
apply refl.
Defined.

Definition first_triangular_law_initial : forall u : X -> Y, Id (maponpaths f_initial (e_gf_initial u)) (e_fg_initial (f_initial u)).
Proof.
intros.
rewrite (pathsinv0 (f_initial_on_paths_vs_maponpaths (e_gf_initial u))).
apply (towards_first_triangular_law_initial u).
Defined.

Definition towards_second_triangular_law_initial : forall x : One, Id (e_gf_initial (g_initial x)) (g_initial_on_paths (e_fg_initial x)).
Proof.
intros.
apply pathsinv0.
apply (one_rec (fun z => Id (g_initial_on_paths (e_fg_initial z)) (e_gf_initial (g_initial z)))). 
apply (transportb (fun z => Id (g_initial_on_paths z) (e_gf_initial (g_initial unit))) (one_beta (fun z => Id unit z) (refl unit))).
unfold g_initial_on_paths.
unfold g_initial.
set (u :=  (fun x0 : X => X_rec (fun _ : X => Y) x0)).
unfold e_gf_initial.
assert (p : Id (refl u) (funextfun (g_initial (f_initial u)) u (toforallpaths _ _ _ (refl u) ))).
apply (pathsinv0 (homotinvweqweq (weqtoforallpaths _ (g_initial (f_initial u)) u) (refl u))).
rewrite p.
apply maponpaths.
apply funextsec.
intro xx.
apply (X_rec (fun zz => Id (toforallpaths (fun _ : X => Y) u u (refl u) zz) 
                       (X_rec (fun z : X => Id (g_initial (f_initial u) z) (u z)) zz)) xx).
Defined.

Definition second_triangular_law_initial : forall x : One, Id (e_gf_initial (g_initial x)) (maponpaths g_initial ( e_fg_initial x)).
Proof.
intros.
apply (transportf (fun z => Id (e_gf_initial (g_initial x)) z) (g_initial_on_paths_vs_maponpaths  (e_fg_initial x))).
apply (towards_second_triangular_law_initial x).
Defined.

End Universal_property_of_h_initial.

Definition f_zero := f_initial.
Definition g_zero := (g_initial Zero zero_rec).
Definition e_fg_zero := (e_fg_initial Zero zero_rec).
Definition e_gf_zero := (e_gf_initial Zero zero_rec).  
Definition first_triangular_law_zero := (first_triangular_law_initial Zero zero_rec).
Definition second_triangular_law_zero := (second_triangular_law_initial Zero zero_rec).

(** We can transfer the structure to any type propositionally equal to Zero *)  

Definition zero_rec_transfer  (X : U)(e : Id Zero X)(E : X -> U)(x : X) : E x.
Proof.
intros.
destruct e.
apply (zero_rec E x).
Defined.

(* The type-level type Two. *)

Axiom Two : U.
Axiom false : Two.
Axiom true : Two. 
Axiom two_rec : forall (E : Two -> Type)(e_f : E false)(e_t : E true)(x : Two), E x.
Axiom two_beta_f : forall (E : Two -> Type)(e_f : E false)(e_t : E true), Id (two_rec E e_f e_t false) e_f.
Axiom two_beta_t : forall (E : Two -> Type)(e_f : E false)(e_t : E true), Id (two_rec E e_f e_t true) e_t.

(** Definition of Nat as a W-type *) 

Definition A := Two.

Definition B : A -> U := 
 fun x : A => two_rec (fun _ : A => U) Zero One x. 

Definition Nat := W A B.

(** The propositional computation rules for Two give us proofs that 
 Zero is propositionally equal to (B l) and One is propositionally
 equal to (B r). We will use these paths to transport the structure 
 of h-initial and h-terminal *)

Definition e_f : Id Zero (B false).
Proof.
unfold B.
apply (pathsinv0 (two_beta_f (fun _ : A => U) Zero One)).
Defined.

Definition e_t : Id One (B true).
Proof.
unfold B.
apply (pathsinv0 (two_beta_t (fun _ : A => U) Zero One)).
Defined.

(** Some notation *) 

Definition B_f := B false.
Definition B_f_rec := (zero_rec_transfer B_f (e_f)).

Definition B_t := B true.
Definition unit_B_t := transport_unit B_t e_t.
Definition B_t_rec := transport_one_rec B_t e_t.
Definition B_t_comp := transport_one_beta B_t e_t.

(** We consider the adjoint homotopy equivalence between (B r) -> Nat and Nat *) 

Definition f_B_t := (f_terminal B_t unit_B_t Nat).
Definition g_B_t := (g_terminal B_t unit_B_t B_t_rec Nat).
Definition e_gf_B_t := (e_gf_terminal B_t unit_B_t B_t_rec B_t_comp Nat).
Definition e_fg_B_t := (e_fg_terminal B_t unit_B_t B_t_rec B_t_comp Nat).
Definition first_triangular_law_B_t := (first_triangular_law_terminal B_t  unit_B_t B_t_rec B_t_comp Nat).
Definition second_triangular_law_B_t := (second_triangular_law_terminal B_t  unit_B_t B_t_rec B_t_comp Nat).

(** We consider the adjoint homotopy equivalence between (B l) -> Nat and One *) 

Definition f_B_f := ((f_initial B_f Nat) : (B_f -> Nat) -> One).
Definition g_B_f := ((g_initial B_f B_f_rec Nat) : One -> (B_f -> Nat)). 
Definition e_gf_B_f := (e_gf_initial B_f B_f_rec Nat).
Definition e_fg_B_f := (e_fg_initial B_f B_f_rec Nat).
Definition first_triangular_law_B_f := (first_triangular_law_initial B_f B_f_rec Nat).
Definition second_triangular_law_B_f := (second_triangular_law_initial B_f B_f_rec Nat).

Definition zero : Nat := 
 (sup A B false (g_B_f unit)).

Definition suc : Nat -> Nat := 
 fun w : Nat => (sup A B true (g_B_t w)).

(** To derive the elimination rule, we assume its premisses *)

Section nat_elim.

Variable E : Nat -> U.
Variable c : E zero.
Variable d : forall (u : Nat)(y : E u), E (suc u).

(** We now derive the premisses of the W-elimination rule *) 

Definition e_zero  :
 forall (u : B_f -> Nat)(v : forall y : B_f, E (u y)), E (sup A B false u).
Proof. 
intros.
set (p_u := e_gf_B_f u).
apply (transportf (fun z => E (sup A B false z)) p_u c).
Defined.

Definition e_suc :
 forall (u : B_t -> Nat)(v : forall y : B_t, E (u y)), E (sup A B true u).
Proof.
intros.
set (p_u := e_gf_B_t u).
apply (transportf (fun z => E (sup A B true z)) p_u (d (u unit_B_t) (v unit_B_t))).
Defined.

Definition e_zero_suc  : 
 forall (x : A)(u : B x -> Nat)(v : forall y : B x, E (u y)), E (sup A B x u).
Proof.
intros.
set (E' := fun x : Two => forall (u : B x -> Nat)(v : forall y : B x, E (u y)), E (sup A B x u)).
apply (two_rec E' (fun u v => (e_zero u v)) (fun u v => (e_suc u v))).
apply v.
Defined.

(** The elimination rule *) 

Definition nat_rec : forall w : Nat, E w := 
 fun w : Nat => (w_rec A B E e_zero_suc w).

(** Derivation of the first computation rules *) 

Definition nat_beta_z  : 
 Id (nat_rec zero) c.
Proof.
intros.
unfold nat_rec.
unfold zero.
set (u := (g_B_f unit)).
apply (transportb (fun z => Id z c) (w_beta A B E e_zero_suc false u)).
set (v :=  (fun y : B false => w_rec A B E e_zero_suc (u y))).
assert (p : Id  (e_zero_suc false u v) (e_zero u v)).
set (E' := fun x : Two => forall (u : B x -> Nat)(v : forall y : B x, E (u y)), E (sup A B x u)).
set (p_1 := ((two_beta_f E' (fun u v => (e_zero u v)) (fun u v => (e_suc u v))))).
set (phi_1 := (toforallpaths _ _ _ p_1)).
set (p_2 := phi_1 u).
set (phi_2 := toforallpaths _ _ _ p_2).
apply (phi_2 v).
apply (transportb (fun z => Id z c) p).
unfold e_zero.
unfold u.
apply (transportb (fun e => Id
     (transportf (fun z : B false -> W A B => E (sup A B false z)) e c) c) (second_triangular_law_B_f unit)).
change (W A B) with Nat.
change (B false) with B_f.
change (g_initial B_f B_f_rec Nat) with (g_B_f).
change (e_fg_initial B_f B_f_rec Nat) with (e_fg_B_f).
assert (q : Id (e_fg_B_f unit) (refl unit)).
unfold e_fg_B_t.
unfold e_fg_B_f.
apply (one_beta (fun z : One => Id unit z) (refl unit)).
rewrite q.
unfold maponpaths.
unfold transportf.
simpl.
apply refl.
Defined.
 
(** An auxiliary definition *) 

Definition EE := (fun z : (B_t -> Nat) => E (sup A B true z)).

Definition w_rec_nat := w_rec A B E e_zero_suc.
Definition w_beta_nat := w_beta A B E e_zero_suc.

(** Two lemmas useful to derive the second computation rule *) 

Definition first_lemma_for_nat_beta : 
 forall (w w' : Nat)(e : Id w w')(x : E w),
  Id (transportf EE (maponpaths g_B_t e) (d w x)) (d w' (transportf E e x)).
Proof.
intros.
destruct e.
apply refl.
Defined.

Definition second_lemma_for_nat_beta : 
 forall (w w' : Nat)(e : Id w w'), 
  Id (d w' (transportf E e (w_rec_nat w))) (d w' (w_rec_nat w')).
Proof.
intros.
destruct e.
apply refl.
Defined.

(** The second computation rule *)
Definition nat_beta_s  : 
 forall w : Nat, Id (nat_rec (suc w)) (d w (nat_rec w)).
Proof.
intros.
unfold suc.
unfold nat_rec.
apply (transportb (fun z => Id z _) (w_beta_nat true (g_B_t w))).
set (u_w := (g_B_t w)).
set (v_w :=  (fun y : B true => w_rec_nat (u_w y))).
assert (p : Id (e_zero_suc true u_w v_w)  (e_suc u_w v_w)).
set (E' := fun x : Two => forall (u : B x -> Nat)(v : forall y : B x, E (u y)), E (sup A B x u)).
set (p_1 := ((two_beta_t E' (fun u v => (e_zero u v)) (fun u v => (e_suc u v))))).
set (phi_1 := (toforallpaths _ _ _ p_1)).
set (p_2 := phi_1 u_w).
set (phi_2 := toforallpaths _ _ _ p_2).
apply (phi_2 v_w).
change (w_rec A B E e_zero_suc) with w_rec_nat.
apply (transportb (fun z => Id z _) p).
unfold e_suc.
change (fun z : B true -> W A B => E (sup A B true z)) with EE.
change (v_w unit_B_t) with (w_rec_nat (f_B_t (g_B_t w))).
change (u_w unit_B_t) with (f_B_t (g_B_t w)).
unfold u_w.
apply (transportb (fun z =>  (Id (transportf EE z _) _))  (second_triangular_law_B_t w)).
change (g_terminal B_t unit_B_t B_t_rec Nat) with g_B_t.
change (e_fg_terminal B_t unit_B_t B_t_rec B_t_comp Nat) with (e_fg_B_t).
assert (q_1 : 
Id  (transportf EE  (maponpaths g_B_t (e_fg_B_t w))  (d (f_B_t (g_B_t w)) (w_rec_nat (f_B_t (g_B_t w)))))
                (d w (transportf E (e_fg_B_t w)  (w_rec_nat (f_B_t (g_B_t w)))))).
apply (first_lemma_for_nat_beta  (f_B_t (g_B_t w)) w (e_fg_B_t w) (w_rec_nat (f_B_t (g_B_t w)))).
assert (q_2 : Id 
   (d w (transportf E (e_fg_B_t w) (w_rec_nat (f_B_t (g_B_t w)))))
   (d w (w_rec_nat w))).
apply (second_lemma_for_nat_beta (f_B_t (g_B_t w)) w (e_fg_B_t w)).
apply (pathscomp0 q_1 q_2).
Defined.

End nat_elim.