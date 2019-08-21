Require Import HoTT.Basics HoTT.Types.
Require Import HoTT.HIT.Pushout HoTT.HIT.SpanPushout HoTT.HIT.Join.
Require Import HoTT.HIT.Truncations HoTT.HIT.Connectedness HIT.Suspension.
Require Import BlakersMassey.

Import TrM.

(** * The Freudenthal Suspension Theorem *)

(** The Freudenthal suspension theorem is a fairly trivial corollary of the Blakers-Massey theorem.  The only real work is to relate the span-pushout that we used for Blakers-Massey to the naive pushout that we used to define suspension. *)

Global Instance freudenthal `{Univalence} (n : trunc_index)
           (X : Type) `{IsConnected n.+1 X}
  : IsConnMap (n +2+ n) (@merid X).
Proof.
  pose (blakers_massey n n (fun (u v:Unit) => X) tt tt).
  pose (f := equiv_pushout (equiv_contr_sigma (fun _ : Unit * Unit => X))^-1
                           (equiv_idmap Unit) (equiv_idmap Unit)
                           (fun x : X => idpath) (fun x : X => idpath)
        : Susp X <~> spushout (fun (u v:Unit) => X)).
  srefine (@cancelR_equiv_conn_map (n +2+ n) _ _ _ _
             (equiv_ap' f North South)
             (@conn_map_homotopic _ _ _ _ _ _
               (blakers_massey n n (fun (u v:Unit) => X) tt tt))).
  intros x.
  refine (_ @ (equiv_pushout_pp
                 (equiv_contr_sigma (fun _ : Unit * Unit => X))^-1
                 (equiv_idmap Unit) (equiv_idmap Unit)
                 (fun x : X => idpath) (fun x : X => idpath) x)^).
  exact ((concat_p1 _ @ concat_1p _)^).
Defined.
