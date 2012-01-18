(** Homotopy-initial two-algebra
       =====>
    Simple elim + beta + eta_1 + eta_2 for Two
**)

Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Require Export identity.
Require Export two_algebras.

(* We assume there exists an h-initial two-algebra. *)
Hypothesis Two : U.
Hypothesis false : Two.
Hypothesis true : Two.

Parameter two_is_hinitial : two_hinitial Two false true.

(* We want to derive the simple rules for Two. *)
Section Simp_rules.

(***********************************************************************)
(***********************************************************************)

(* Simp elim + beta. *)

(* Assume the premises of the simp elim and beta rules. *)
Variable C : U.
Variable c_f : C.
Variable c_t : C.

(* By h-initiality there exists a homomorphism from Two to C. *)
Definition c : TwoHom Two false true C c_f c_t := p1 (two_is_hinitial C c_f c_t).

Definition two_rec_simp : Two -> C := p1 c.
Definition two_beta_simp_f : Id (two_rec_simp false) c_f := p1 (p2 c).
Definition two_beta_simp_t : Id (two_rec_simp true) c_t := p2 (p2 c).

(***********************************************************************)
(***********************************************************************)

(* First- and second-order eta. *)

(* Assume the additional premises for the eta rules. *)
Variable u : Two -> C.
Variable p_f : Id (u false) c_f.
Variable p_t : Id (u true) c_t.

(* This gives us another homomorphism from Two to C. *)
Definition h : TwoHom Two false true C c_f c_t
  := dpair (P Two false true C c_f c_t) u (pair p_f p_t).

(* By h-initiality h is propositionally equal to c and hence we have
   a 2-cell from h to c. *)
Definition cell : TwoCell h c.
Proof.
apply prop_eq_to_two_cell.
apply (p2 (two_is_hinitial C c_f c_t) h).
Defined.

Definition two_eta_simp_1 : forall (x : Two), Id (u x) (two_rec_simp x)
  := p1 cell.

Definition two_eta_simp_2_f : Id (two_eta_simp_1 false @ two_beta_simp_f) p_f
  := p1 (p2 cell).

Definition two_eta_simp_2_t : Id (two_eta_simp_1 true @ two_beta_simp_t) p_t
  := p2 (p2 cell).

End Simp_rules.