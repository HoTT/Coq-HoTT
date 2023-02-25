Require Import Basics.
Require Import Types.
Require Import Colimits.Pushout.
Require Import Colimits.SpanPushout.
Require Import HoTT.Truncations.
Require Import Homotopy.Suspension.
Require Import Homotopy.BlakersMassey.

(** * The Freudenthal Suspension Theorem *)

(** The Freudenthal suspension theorem is a fairly trivial corollary of the Blakers-Massey theorem.  The only real work is to relate the span-pushout that we used for Blakers-Massey to the naive pushout that we used to define suspension. *)
Local Definition freudenthal' `{Univalence} (n : trunc_index)
           (X : Type) `{IsConnected n.+1 X}
  : IsConnMap (n +2+ n) (@merid X).
Proof.
  snrapply cancelR_equiv_conn_map.
  2: { refine (equiv_ap' (B:=SPushout (fun (u v : Unit) => X)) _ North South).
       exact (equiv_pushout (equiv_contr_sigma (fun _ : Unit * Unit => X))^-1
                            (equiv_idmap Unit) (equiv_idmap Unit)
                            (fun x : X => idpath) (fun x : X => idpath)). }
  refine (conn_map_homotopic _ _ _ _
                             (blakers_massey n n (fun (u v:Unit) => X) tt tt)).
  intros x.
  refine (_ @ (equiv_pushout_pglue
                 (equiv_contr_sigma (fun _ : Unit * Unit => X))^-1
                 (equiv_idmap Unit) (equiv_idmap Unit)
                 (fun x : X => idpath) (fun x : X => idpath) x)^).
  exact ((concat_p1 _ @ concat_1p _)^).
Defined.

Definition freudenthal@{u v | u < v} := Eval unfold freudenthal' in @freudenthal'@{u u u u u v u u u}.

Global Existing Instance freudenthal.
