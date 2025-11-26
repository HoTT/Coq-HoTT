From HoTT Require Import Basics Types Pointed.Core Pointed.pEquiv.

(** * Pointed sections of pointed maps *)

Local Open Scope pointed_scope.

(* The type of pointed sections of a pointed map. *)
Definition pSect {A B : pType} (f : A ->* B)
  := { s : B ->* A & f o* s ==* pmap_idmap }.

Definition issig_psect { A B : pType } (f : A ->* B)
  : { s : B -> A & { p : s pt = pt
                        & { H : f o s == idmap
                                & H pt = ap f p @ (point_eq f) } } }
  <~> pSect f.
Proof.
  transitivity
    {s : B -> A & {p : s pt = pt
                      & {H : f o s == idmap
                             & H pt = ap f p @ (point_eq f) @ 1 }}}.
  2: make_equiv.
  do 3 (napply equiv_functor_sigma_id; intro).
  rapply equiv_concat_r.
  exact (concat_p1 _)^.
Defined.

(** Any pointed equivalence over [A] induces an equivalence between pointed sections. *)
Definition equiv_pequiv_pslice_psect `{Funext} {A B C : pType}
  (f : B ->* A) (g : C ->* A) (t : B <~>* C) (h : f ==* g o* t)
  : pSect f <~> pSect g.
Proof.
  srapply equiv_functor_sigma'.
  1: exact (pequiv_pequiv_postcompose t).
  intro s; cbn.
  apply equiv_phomotopy_concat_l.
  refine ((pmap_compose_assoc _ _ _)^* @* _).
  apply pmap_prewhisker.
  exact h^*.
Defined.

(** Pointed sections of [psnd : A * B ->* B] correspond to pointed maps [B ->* A]. *)
Definition equiv_psect_psnd `{Funext} {A B : pType}
  : pSect (@psnd A B) <~> (B ->* A).
Proof.
  unfold pSect.
  transitivity {s : (B ->* A) * (B ->* B) & snd s ==* pmap_idmap}.
  { snrefine (equiv_functor_sigma'
                (equiv_pprod_coind (pfam_const A) (pfam_const B))^-1%equiv _).
    cbn. intro s.
    apply equiv_phomotopy_concat_l.
    srapply Build_pHomotopy.
    1: reflexivity.
    cbn.
    apply moveL_pV.
    exact (concat_1p _ @ concat_p1 _). }
  snrefine (_ oE equiv_functor_sigma_id (fun s => equiv_path_pforall _ _)).
  snrefine (_ oE (equiv_functor_sigma_pb (equiv_sigma_prod0 _ _))^-1%equiv); cbn.
  refine (_ oE (equiv_sigma_assoc _ _)^-1%equiv).
  rapply equiv_sigma_contr.
Defined.
