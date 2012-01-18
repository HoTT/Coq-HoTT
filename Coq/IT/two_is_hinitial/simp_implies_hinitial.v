(** Simple elim + beta + eta_1 + eta_2 for Two
       =====>
    Homotopy-initial two-algebra.
**)

Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Require Export identity.
Require Export two_algebras.

(* We assume the simple rules for Two. *)
Require Export two_simp.

(* We want to show the two-algebra (Two,l,r) is h-initial. *)
Section Two_is_h_initial.

(* Take another two-algebra. *)
Variable C : U.
Variable c_f : C.
Variable c_t : C.

(***********************************************************************)
(***********************************************************************)

(* We want to show the type of homomorphisms from Two to C is contractible. *)

(* Simp elim and beta determine the center of contraction.  *)
Definition u : Two -> C := two_rec_simp C c_f c_t.
Definition p_f : Id (u false) c_f := two_beta_simp_f C c_f c_t.
Definition p_t : Id (u true) c_t := two_beta_simp_t C c_f c_t.

Definition c : TwoHom Two false true C c_f c_t
  := dpair (P Two false true C c_f c_t) u (pair p_f p_t).

Section Contractibility.

(* Take another homomorphism. *)
Variable h : TwoHom Two false true C c_f c_t.

(* First- and second order eta determine a 2-cell from h to c. *)
Definition alpha : forall (x : Two), Id (p1 h x) (u x)
  := two_eta_simp_1 C c_f c_t (p1 h) (p1 (p2 h)) (p2 (p2 h)).

Definition gamma_f : Id (alpha false @ p_f) (p1 (p2 h))
  := two_eta_simp_2_f C c_f c_t (p1 h) (p1 (p2 h)) (p2 (p2 h)).

Definition gamma_t : Id (alpha true @ p_t) (p2 (p2 h))
  := two_eta_simp_2_t C c_f c_t (p1 h) (p1 (p2 h)) (p2 (p2 h)).

End Contractibility.

(***********************************************************************)
(***********************************************************************)

(* We thus have h-initiality as desired. *)
Lemma two_is_hinitial : iscontr (TwoHom Two false true C c_f c_t).
Proof.
split with c.
intro h.
apply two_cell_to_prop_eq.
split with (alpha h).
split.
apply (gamma_f h).
apply (gamma_t h).
Defined.

End Two_is_h_initial.