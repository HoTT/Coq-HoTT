(** Simple elim + beta + eta_1 + eta_2 for Two
       =====>
    Dependent elim + beta for Two
**)

Add Rec LoadPath "../univalent_foundations/Generalities".
Add Rec LoadPath "../identity".

Require Export identity.

(* We assume the simple rules for Two. *)
Require Export two_simp.

(* We derive the dep elim and beta rules. *)
Section Dep_rules.

(* We assume the premises of the dep elim and beta rules. *)
Variable E : Two -> U.
Variable e_f : E false.
Variable e_t : E true.

(***********************************************************************)
(***********************************************************************)

(* To obtain dep elim, we use simple elim with the type below. *)
Definition C : U := Sigma E.

(* For this we supply the terms below. *)
Definition c_f : C := dpair E false e_f.
Definition c_t : C := dpair E true e_t.

(* This gives us the following terms. *)
Definition u : Two -> C := two_rec_simp C c_f c_t.

Definition u_1 (x : Two) : Two := p1 (u x).
Definition u_2 (x : Two) : E (u_1 x) := p2 (u x).

(* Using simple beta on the term u constructed above yields the following. *)
Definition p_f : Id (u false) c_f := two_beta_simp_f C c_f c_t.
Definition p_t : Id (u true) c_t := two_beta_simp_t C c_f c_t.

(* Homotopy in a Sigma type is equivalent to a pair of homotopies in their
   respective component types: *)

(* Homotopy of functions. *)
Definition q_f_1 : Id (u_1 false) false := dp1id p_f.
Definition q_t_1 : Id (u_1 true) true := dp1id p_t.

(* Homotopy of proofs. *)
Definition q_f_2 : Id (transport E q_f_1 (u_2 false)) e_f := dp2id p_f.
Definition q_t_2 : Id (transport E q_t_1 (u_2 true)) e_t := dp2id p_t.

(***********************************************************************)
(***********************************************************************)

(* We now want to show that the function u_1 defined above is
   propositionally equal to the identity function on Two. *)

(* Using first-order simple eta twice gives us the terms below. *)
Definition alpha_1 (x : Two) : Id (u_1 x) (two_rec_simp Two false true x)
  := two_eta_simp_1 Two false true u_1 q_f_1 q_t_1 x.

Definition alpha_2 (x : Two) : Id x (two_rec_simp Two false true x)
  := two_eta_simp_1 Two false true (idfun Two) (refl false) (refl true) x.

Definition alpha (x : Two) : Id (u_1 x) x := (alpha_1 x) @ (alpha_2 x)!.

(* Using second-order simple eta on alpha_1 and alpha_2 gives us the following. *)
Definition gamma_1_f : Id (alpha_1 false @ two_beta_simp_f Two false true) q_f_1
  := two_eta_simp_2_f Two false true u_1 q_f_1 q_t_1.

Definition gamma_1_t : Id (alpha_1 true @ two_beta_simp_t Two false true) q_t_1
  := two_eta_simp_2_t Two false true u_1 q_f_1 q_t_1.

Definition gamma_2_f : Id (alpha_2 false @ two_beta_simp_f Two false true) (refl false)
  := two_eta_simp_2_f Two false true (idfun Two) (refl false) (refl true).

Definition gamma_2_t : Id (alpha_2 true @ two_beta_simp_t Two false true) (refl true)
  := two_eta_simp_2_t Two false true (idfun Two) (refl false) (refl true).

Definition gamma_f : Id (alpha false) q_f_1.
Proof.
apply trans with (b := alpha_1 false @ two_beta_simp_f Two false true).
apply concat_cong_left.
apply cancel_left_from_id.
apply gamma_2_f.
apply gamma_1_f.
Defined.

Definition gamma_t : Id (alpha true) q_t_1.
Proof.
apply trans with (b := alpha_1 true @ two_beta_simp_t Two false true).
apply concat_cong_left.
apply cancel_left_from_id.
apply gamma_2_t.
apply gamma_1_t.
Defined.

(***********************************************************************)
(***********************************************************************)

(* Dep elim. *)
Definition two_rec_dep (x : Two) : E x := transport E (alpha x) (u_2 x).

(* Dep beta. *)
Definition two_beta_dep_f : Id (two_rec_dep false) e_f.
Proof.
unfold two_rec_dep.
apply trans with (b := transport E (q_f_1) (u_2 false)).
apply appid.
apply transport_cong.
apply gamma_f.
apply q_f_2.
Defined.

Definition beta_dep_t : Id (two_rec_dep true) e_t.
Proof.
unfold two_rec_dep.
apply trans with (b := transport E (q_t_1) (u_2 true)).
apply appid.
apply transport_cong.
apply gamma_t.
apply q_t_2.
Defined.

End Dep_rules.