(** Dependent elim + beta for Two
       =====>
    Simple elim + beta + eta_1 + eta_2 for Two
**)

Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".
Add Rec LoadPath "../inductive_types".

Require Export identity.

(* We assume the dependent rules for Two. *)
Require Export two.

(* The simple rules are just special cases of the dependent ones. *)
Definition two_rec_simp (C : U) (c_f c_t : C) : forall (x : Two), C
  := two_rec (fun _ => C) c_f c_t.

Definition two_beta_simp_f (C : U) (c_f c_t : C) : Id (two_rec_simp C c_f c_t false) c_f
  := two_beta_f (fun _ => C) c_f c_t.

Definition two_beta_simp_t (C : U) (c_f c_t : C) : Id (two_rec_simp C c_f c_t true) c_t
  := two_beta_t (fun _ => C) c_f c_t.

Definition two_eta_simp_1 (C : U) (c_f c_t : C) (h : Two -> C) (p_f : Id (h false) c_f) (p_t : Id (h true) c_t) :
  forall (x : Two), Id (h x) (two_rec_simp C c_f c_t x)
  := two_eta_1 (fun _ => C) c_f c_t h p_f p_t.

Definition two_eta_simp_2_l (C : U) (c_f c_t : C) (h : Two -> C) (p_f : Id (h false) c_f) (p_t : Id (h true) c_t) :
  Id (two_eta_simp_1 C c_f c_t h p_f p_t false @ two_beta_simp_f C c_f c_t) p_f
  := two_eta_2_l (fun _ => C) c_f c_t h p_f p_t.

Definition two_eta_simp_2_r (C : U) (c_f c_t : C) (h : Two -> C) (p_f : Id (h false) c_f) (p_t : Id (h true) c_t) :
  Id (two_eta_simp_1 C c_f c_t h p_f p_t true @ two_beta_simp_t C c_f c_t) p_t
  := two_eta_2_r (fun _ => C) c_f c_t h p_f p_t.
