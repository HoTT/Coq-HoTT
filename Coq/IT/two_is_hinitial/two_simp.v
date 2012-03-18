(** Simple (non-dependent) rules for the inductive type Two. Eta rules are no
    longer derivable and hence are included as axioms. **)

Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Require Export identity.

(* Formation rule. *)
Axiom Two : U.

(* Introduction rules. *)
Axiom false : Two.
Axiom true : Two.

(* Elimination rule. *)
Axiom two_rec_simp : forall (C : U) (c_f c_t : C) (x : Two), C.

(* Beta rules. *)
Axiom two_beta_simp_f : forall (C : U) (c_f c_t : C),
  Id (two_rec_simp C c_f c_t false) c_f.

Axiom two_beta_simp_t : forall (C : U) (c_f c_t : C),
  Id (two_rec_simp C c_f c_t true) c_t.

(* First-order eta-rule. *)
Axiom two_eta_simp_1 : forall (C : U) (c_f c_t : C) (h : Two -> C) (p_f : Id (h false) c_f) (p_t : Id (h true) c_t)
  (x : Two), Id (h x) (two_rec_simp C c_f c_t x).

(* Second-order eta-rules. *)
Axiom two_eta_simp_2_f : forall (C : U) (c_f c_t : C) (h : Two -> C) (p_f : Id (h false) c_f) (p_t : Id (h true) c_t),
  Id (two_eta_simp_1 C c_f c_t h p_f p_t false @ two_beta_simp_f C c_f c_t) p_f.

Axiom two_eta_simp_2_t : forall (C : U) (c_f c_t : C) (h : Two -> C) (p_f : Id (h false) c_f) (p_t : Id (h true) c_t),
  Id (two_eta_simp_1 C c_f c_t h p_f p_t true @ two_beta_simp_t C c_f c_t) p_t.
