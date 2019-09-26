Require Import Basics.

(** * Comutative squares *)

(** Commutative squares compose.

      A --f--> B
      |    //  |
      h  comm  g
      |  //    |
      V //     V
      C --f'-> D
      |    //  |
      h' comm' g'
      |  //    |
      V //     V
      E --f''> F
*)
Lemma comm_square_comp {A B C D E F}
  {f : A -> B} {f': C -> D} {h : A -> C} {g : B -> D} (comm : f' o h == g o f)
  {f'': E -> F} {h' : C -> E} {g' : D -> F} (comm' : f'' o h' == g' o f')
  : f'' o (h' o h) == (g' o g) o f.
Proof.
  intros x.
  path_via (g' (f' (h x))).
  apply ap, comm.
Defined.

(** Given any commutative square from [f] to [f'] whose verticals
[wA, wB] are equivalences, the equiv_inv square from [f'] to [f] with verticals [wA ^-1, wB ^-1] also commutes. *)
Lemma comm_square_inverse
  {A B : Type} {f : A -> B}
  {A' B' : Type} {f' : A' -> B'}
  {wA : A <~> A'} {wB : B <~> B'}
  (wf : f' o wA == wB o f)
: f o (wA ^-1) == (wB ^-1) o f'.
Proof.
  intros a'.
  path_via (wB ^-1 (wB (f (wA ^-1 a')))).
  - apply inverse, eissect.
  - apply ap, (concat (wf _)^).
    apply ap, eisretr.
Defined.

(** Up to naturality, the result of [comm_square_inverse] really is a
retraction (aka left inverse); *)
Lemma comm_square_inverse_is_sect
  {A B : Type} {f : A -> B}
  {A' B' : Type} {f' : A' -> B'}
  (wA : A <~> A') (wB : B <~> B')
  (wf : f' o wA == wB o f) (a : A)
  : comm_square_comp wf (comm_square_inverse wf) a @ eissect wB (f a)
   = ap f (eissect wA a).
Proof.
  unfold comm_square_inverse, comm_square_comp; simpl.
  repeat apply (concat (concat_pp_p _ _ _)). apply moveR_Vp.
  transitivity (ap (wB ^-1 o wB) (ap f (eissect wA a)) @ eissect wB (f a)).
  2: apply (concat (concat_Ap (eissect wB) _)). 2: apply ap, ap_idmap.
  apply (concat (concat_p_pp _ _ _)), whiskerR.
  apply (concat (ap_pp (wB ^-1) _ _)^), (concatR (ap_compose wB _ _)^).
  apply ap, (concat (concat_pp_p _ _ _)), moveR_Vp.
  path_via (ap (f' o wA) (eissect wA a) @ wf a).
  - apply whiskerR.  apply (concatR (ap_compose wA f' _)^).
    apply ap, eisadj.
  - apply (concat (concat_Ap wf _)).
    apply whiskerL, (ap_compose f wB).
Defined.

(** and similarly, [comm_square_inverse] is a section (aka right equiv_inv). *)
Lemma comm_square_inverse_is_retr
  {A B : Type} {f : A -> B}
  {A' B' : Type} {f' : A' -> B'}
  (wA : A <~> A') (wB : B <~> B')
  (wf : f' o wA == wB o f) (a : A')
  : comm_square_comp (comm_square_inverse wf) wf a @ eisretr wB (f' a)
  = ap f' (eisretr wA a).
Proof.
  unfold comm_square_inverse, comm_square_comp; simpl.
  rewrite !ap_pp.
  rewrite <- !concat_pp_p.
  rewrite concat_pp_p.
  set (p := (ap wB (ap (wB ^-1) (ap f' (eisretr wA a)))
            @ eisretr wB (f' a))).
  path_via ((eisretr wB _)^ @ p).
  - apply whiskerR.
    apply moveR_pM.
    path_via ((eisretr wB (f' (wA (wA ^-1 a))))^ @
      ap (wB o wB ^-1) (wf ((wA ^-1) a))).
    + rewrite ap_V, <- eisadj.
      transitivity (ap idmap (wf ((wA ^-1) a))
                       @ (eisretr wB (wB (f ((wA ^-1) a))))^).
      * apply whiskerR, inverse, ap_idmap.
      * apply (concat_Ap (fun b' => (eisretr wB b')^) _).
    + apply ap.
      rewrite ap_compose, !ap_V.
      apply inverse, inv_V.
  - apply moveR_Vp.
    subst p.
    rewrite <- ap_compose.
    path_via (eisretr wB _ @ ap idmap (ap f' (eisretr wA a))).
    + apply (concat_Ap (eisretr wB) _).
    + apply ap, ap_idmap.
Defined.
