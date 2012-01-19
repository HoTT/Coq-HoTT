(* Goal: trying to derive dependent from non-dependent W-types, following the approach of Gambino-Hyland 2005 (and so not relying on the universe etc). *)

(* STATUS: INCOMPLETE. *)

(* This document derives dependent W-types, using :
(a) pi-types, sigma types, path types;
(b) W-types;
(c) functional extensionality, [funext]/[funext_comp] (‘Π-ext’, ‘Π-ext-comp’ in Richard Garner’s “On the strength of dependent products…”).
*)

Add Rec LoadPath "../".

Require Import Paths.
Require Import Fibrations.
Require Import Funext.

Axiom funext : funext_dep_statement.

Axiom funext_comp : funext_comp1_statement funext.

Inductive W (A : Type) (B : A -> Type) : Type :=
  | w_intro (a : A) (f : B a -> W A B) : W A B.

(*
W_rect
     : forall (A : Type) (B : A -> Type) (P : W A B -> Type),
       (forall (a : A) (f : B a -> W A B),
        (forall b : B a, P (f b)) -> P (w_intro A B a f)) ->
       forall w : W A B, P w
*)

Section dep_W_from_W.

Variable I : Type.
Variable A : I -> Type.
Variable B : forall i:I, A i -> Type.
Variable s : forall {i} {a}, B i a -> I.
Implicit Arguments s [i a].

(* Here’s a normal Coq specification of what we want: *)
Inductive dep_W : I -> Type
:=
  dep_w_intro (i:I) (a : A i) (f : forall (b : B i a), dep_W(s b))
            : dep_W i.

(* The recursor for this shows us what we are aiming for:
dep_W_rect
     : forall P : (forall i : I, dep_W i -> Type),
              (forall (i : I) (a : A i)
                      (f : forall b : B i a, dep_W (s b)),
                      (forall b : B i a, P (s b) (f b))
               -> P i (dep_w_intro i a f))
       -> forall (i : I) (d : dep_W i),
       P i d

Goal now: using just [W] above, construct a type with this recursor and the corresponding comp rule. 
*)

Definition W0 := W {i : I & A i} (fun ia => let (i,a) := ia in B i a).

Definition w0_intro (i:I) (a:A i) (t : forall b:B i a, W0) : W0.
Proof.
  exists (existT (fun i => A i) i a). 
  exact t.
Defined.

Definition w0_pr0 : W0 -> I.
Proof.
  intros [[i _] _].  exact i.
Defined.

Definition W1 := W {j : I & {i : I & A i}} (fun jia => let (_,ia) := jia in let (i,a) := ia in B i a).

Definition w1_intro (j i:I) (a:A i) (t : forall b:B i a, W1) : W1.
Proof.
  exists ((existT _ j (existT (fun j => A j) i a : {j : I & A j})) : {i : I & {j : I & A j}}). 
  exact t.
Defined.

Definition w1_pr0 : W1 -> I.
Proof.
  intros [[j _] _].  exact j.
Defined.

Definition w1_pr1 : W1 -> I.
Proof.
  intros [[_ [i a]] _].  exact i.
Defined.

Definition w1_pr2 : forall x : W1, A (w1_pr1 x).
Proof.
  intros [[j [i a]] t].  exact a.
Defined.

Definition w1_pr3 : forall (x : W1) (b : B (w1_pr1 x) (w1_pr2 x)), W1.
Proof.
  intros [[j [i a]] t].  exact t.
Defined.

(* Nomenclature follows Gambino-Hyland for now. *)
 
Definition zeta : W0 -> W1.
Proof.
  intro x.  induction x as [[i a] t t'].  unfold W1.
  exact (w1_intro i i a t'). 
Defined.

Definition phi : W1 -> I -> W1.
Proof.
  intro x.  induction x as [[_ [i a]] t t'].
  intro k.
  exact (w1_intro k i a (fun b => t' b (s b))).
Defined.

Definition psi : W1 -> W1
:= fun x => phi x (w1_pr0 x).

Definition zeta' : W0 -> W1
  := psi o zeta.

Definition xi : W1 -> W0.
Proof.
  intro x.  induction x as [[j [i a]] t t'].
  exact (w0_intro i a t').
Defined.

Lemma xi_phi (x : W1) (k:I) : xi (phi x k) == xi x.
Proof.
  generalize dependent k.
  induction x as [[j [i a]] t t_ind].  intro k.
  simpl xi.
  assert ((fun y : B i a => xi (phi (t y) (s y))) == (fun y : B i a => xi (t y))).
  apply funext.  intro b.  apply t_ind.  (* Assertion proved. *)
  path_simplify.
Defined.

Lemma xi_zeta (x : W0) : xi (zeta x) == xi (zeta' x).
Proof.
  unfold zeta'. 
  apply opposite.  apply xi_phi.
Defined.

Lemma pr0_zeta (x : W0) : w1_pr0 (zeta x) == w1_pr0 (zeta' x).
Proof.
  destruct x as [[i a] t].  simpl.  exact (idpath i).
Defined.

(* We give the record an odd name and then realias, since otherwise [new_dep_W_rect] would be taken. *)
Record new_dep_W_record {i:I} := 
  { undlg_w0 : W0
  ; in_fiber : w0_pr0 undlg_w0 == i
  ; is_good : zeta undlg_w0 == zeta' undlg_w0
  ; coh_xi : map xi is_good == xi_zeta undlg_w0
  ; coh_pr0 : map w1_pr0 is_good == pr0_zeta undlg_w0
  }.

Implicit Arguments new_dep_W_record [].

Definition new_dep_W i := new_dep_W_record i.

Lemma goodness_is_hereditary_W1  (j i:I) (a:A i) (t : forall b:B i a, W1)
  : psi (w1_intro j i a t) == (w1_intro j i a t)
  -> forall b:B i a, psi (t b) == t b.
Proof.
  intros H_eq b.  
  path_via (w1_pr3 (psi (w1_intro j i a t)) b).
  unfold psi at 2.  simpl.  admit.  
  path_via (w1_pr3 (w1_intro j i a t) b).
  path_simplify' H_eq.
  unfold w1_intro in H_eq.  simpl in H_eq.
  unfold w1_intro in H_eq.
  path_via  (w1_pr3 ). simpl in H_eq.

Definition new_dep_w_intro (i : I) (a : A i)
                     (f : forall b : B i a, new_dep_W (s b))
                   : new_dep_W i.
Proof.
  set (the_undlg_w0 := w0_intro i a (fun b => undlg_w0 (f b))).
  
Admitted.

Theorem new_dep_W_rect
  (P : forall i : I, new_dep_W i -> Type)
  (H_rect : forall (i : I) (a : A i)
                   (f : forall b : B i a, new_dep_W (s b)),
                   (forall b : B i a, P (s b) (f b))
                 -> P i (new_dep_w_intro i a f))
  (i : I) (d : new_dep_W i)
  : P i d.
Proof.
Admitted.


Theorem new_dep_W_comp
    (P : forall i : I, new_dep_W i -> Type)
    (H_rect : forall (i : I) (a : A i)
                     (g : forall b : B i a, new_dep_W (s b)),
                     (forall b : B i a, P (s b) (g b))
                   -> P i (new_dep_w_intro i a g))
    (i : I) (a : A i) (g : forall b : B i a, new_dep_W (s b))
  : new_dep_W_rect P H_rect i (new_dep_w_intro i a g) 
  == H_rect i a g (fun b => (new_dep_W_rect P H_rect (s b) (g b))).
Proof.
Admitted.

End dep_W_from_W.
