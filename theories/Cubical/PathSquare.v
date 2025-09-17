From HoTT Require Import Basics.
Require Import Types.Paths Types.Prod.
Require Import DPath.

Declare Scope square_scope.
Delimit Scope square_scope with square.

Local Unset Elimination Schemes.

(* Homogeneous squares *)

(* 
        x00 ----pi0---- x01
         |               |
         |               |
        p0i     ==>     p1i
         |               |
         |               |
        x01-----pi1-----x11
 *)

(** Contents:

  * Definition of [PathSquare]
  * Degenerate [PathSquare]s as paths between paths
  * Flipping squares horizontally and vertically
  * [PathSquare] transpose
  * [PathSquare] inverse
  * [PathSquare] rotations
  * Edge rewriting
  * Concatenation
  * Kan fillers
  * natural squares from [ap]

*)

(** Definition of [PathSquare] *)
(** [PathSquare] left right up down *)
Cumulative Inductive PathSquare {A} : forall a00 {a10 a01 a11 : A},
  a00 = a10 -> a01 = a11 -> a00 = a01 -> a10 = a11 -> Type
  := sq_id : forall {x : A},
    PathSquare x 1 1 1 1.

Arguments sq_id {A x}.
Arguments PathSquare {A _ _ _ _}.
Notation "1" := sq_id : square_scope.

(* TODO: ": rename" is needed because the default names changed in Rocq 9.2.0.  When the minimum supported version is >= 9.2.0, the ": rename" can be removed. *)
(* register=no: otherwise the scheme confuses the make_equiv tactic. When the minimum supported version is >= 9.2.0, the warning can be re-enabled. *)
#[warnings="-unsupported-attributes",register=no] Scheme PathSquare_ind := Induction for PathSquare Sort Type.
Arguments PathSquare_ind {A} P f {_ _ _ _ _ _ _ _} _ : rename.
#[warnings="-unsupported-attributes",register=no] Scheme PathSquare_rec := Minimality for PathSquare Sort Type.
Arguments PathSquare_rec {A} P f {_ _ _ _ _ _ _ _} _ : rename.

(** [PathSquare_ind] is an equivalence, similar to how [paths_ind] is *)
Instance isequiv_PathSquare_ind `{Funext} {A}
  (P : forall (a00 a10 a01 a11 : A) (p : a00 = a10) (p0 : a01 = a11)
    (p1 : a00 = a01) (p2 : a10 = a11),
    PathSquare p p0 p1 p2 -> Type) : IsEquiv (PathSquare_ind P).
Proof.
  srapply isequiv_adjointify.
  1: intros X ?; apply X.
  2: intro; reflexivity.
  intro.
  do 8 (apply path_forall; intro).
  apply path_forall.
  by intros [].
Defined.

(** [PathSquare]s can be given by 2-dimensional paths *)
Definition equiv_sq_path {A} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11}
  {p0x : a00 = a01} {p1x : a10 = a11}
  : px0 @ p1x = p0x @ px1 <~> PathSquare px0 px1 p0x p1x.
Proof.
  snapply Build_Equiv.
  { destruct p0x, p1x.
    intro e.
    generalize (e @ concat_1p _).
    intro e'.
    destruct e', px0.
    exact sq_id. }
  srapply isequiv_adjointify; try by intros [].
  destruct p0x, p1x.
  intros e.
  pattern e.
  pose (e' := e @ concat_1p _).
  pose (e'' := e' @ (concat_1p _)^).
  refine (@transport _ _ e'' e _ _).
  - subst e' e''; hott_simpl.
  - clearbody e'; clear e.
    destruct e', px0.
    reflexivity.
Defined.

Notation sq_path := equiv_sq_path.

(** Squares in (n+2)-truncated types are n-truncated *)
Instance istrunc_sq n
  {A} `{!IsTrunc n.+2 A} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11}
  {p0x : a00 = a01} {p1x : a10 = a11}
  : IsTrunc n (PathSquare px0 px1 p0x p1x).
Proof.
  exact (istrunc_equiv_istrunc _ sq_path).
Defined.

(* We can give degenerate squares *)
Section PathSquaresFromPaths.

  Context
    {A : Type} {a00 a10 a01 : A}
    {p p' : a00 = a10} {q q' : a00 = a01}.

  Definition equiv_sq_G1  : p = p' <~> PathSquare p p' 1 1
    := sq_path oE equiv_p1_1q.

  Definition equiv_sq_1G : q = q' <~> PathSquare 1 1 q q'
    := sq_path oE equiv_1p_q1 oE equiv_path_inverse _ _.

End PathSquaresFromPaths.

Notation sq_G1 := equiv_sq_G1.
Notation sq_1G := equiv_sq_1G.

Local Open Scope equiv_scope.
Local Open Scope path_scope.

(** [PathSquare] horizontal reflexivity *)
Definition sq_refl_h {A} {a0 a1 : A} (p : a0 = a1)
  : PathSquare p p 1 1 := sq_G1 1.

(** [PathSquare] vertical reflexivity *)
Definition sq_refl_v {A} {a0 a1 : A} (p : a0 = a1)
  : PathSquare 1 1 p p := sq_1G 1.

(** Horizontal flip *)
Definition equiv_sq_flip_h {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  : PathSquare px0 px1 p0x p1x <~> PathSquare px1 px0 p0x^ p1x^.
Proof.
  destruct p0x, p1x.
  refine (sq_G1 oE _).
  refine (equiv_path_inverse _ _ oE _).
  exact sq_G1^-1.
Defined.

Notation sq_flip_h := equiv_sq_flip_h.

(** Vertical flip *)
Definition equiv_sq_flip_v {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  : PathSquare px0 px1 p0x p1x <~> PathSquare px0^ px1^ p1x p0x.
Proof.
  destruct px0, px1.
  refine (sq_1G oE _).
  refine (equiv_path_inverse _ _ oE _).
  exact sq_1G^-1.
Defined.

Notation sq_flip_v := equiv_sq_flip_v.

(** Transpose of a square *)

(** We make a local definition that will never get unfolded *)
Local Definition tr {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  : PathSquare px0 px1 p0x p1x -> PathSquare p0x p1x px0 px1.
Proof.
  by intros [].
Defined.

Arguments tr : simpl never.

Definition equiv_sq_tr {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  : PathSquare px0 px1 p0x p1x <~> PathSquare p0x p1x px0 px1.
Proof.
  srapply (equiv_adjointify tr tr).
  1,2: by intros [].
Defined.

Notation sq_tr := equiv_sq_tr.

(* NOTE: sq_tr ought to be some sort of involution but it obviously isn't
   since it is not of the form A -> A. Perhaps there is a more general
   "involution" but between equivalent types? But then that very equivalence
   is given by sq_tr so it seems a bit circular... *)

Definition sq_tr_refl_h {A} {a b : A} {p : a = b}
  : sq_tr (sq_refl_h p) = sq_refl_v p.
Proof.
  by destruct p.
Defined.

Definition sq_tr_refl_v {A} {a b : A} {p : a = b}
  : sq_tr (sq_refl_v p) = sq_refl_h p.
Proof.
  by destruct p.
Defined.

(* Operations on squares *)
Section PathSquareOps.

  Context
    {A : Type}
    {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}.

  (* Inverse square *)
  Definition equiv_sq_V : PathSquare px0 px1 p0x p1x <~> PathSquare px1^ px0^ p1x^ p0x^.
  Proof.
    refine (sq_path oE _ ).
    refine (equiv_concat_lr (inv_pp _ _)^ (inv_pp _ _) oE _).
    refine (equiv_ap _ _ _ oE _).
    refine (sq_path^-1 oE _).
    exact sq_tr.
  Defined.

  (* Left rotation : left right top bottom  ->  top bottom right left *)
  Definition equiv_sq_rot_l : PathSquare px0 px1 p0x p1x <~> PathSquare p0x^ p1x^ px1 px0.
  Proof.
    refine (sq_path oE _).
    refine (equiv_moveR_Vp _ _ _ oE _).
    refine (equiv_concat_r (concat_pp_p _ _ _) _ oE _).
    refine (equiv_moveL_pV _ _ _ oE _).
    exact sq_path^-1.
  Defined.

  (* Right rotation : left right top bottom -> bottom top left right *)
  Definition equiv_sq_rot_r : PathSquare px0 px1 p0x p1x -> PathSquare p1x p0x px0^ px1^.
  Proof.
    refine (sq_path oE _).
    refine (equiv_moveL_Vp _ _ _ oE _).
    refine (equiv_concat_l (concat_p_pp _ _ _) _ oE _).
    refine (equiv_moveR_pV _ _ _ oE _).
    exact sq_path^-1.
  Defined.

End PathSquareOps.

Notation sq_V := equiv_sq_V.
Notation sq_rot_l:= equiv_sq_rot_l.
Notation sq_rot_r := equiv_sq_rot_r.

(* Lemmas for rewriting sides of squares *)
Section PathSquareRewriting.

  Context {A : Type}
    {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}.

  (* These are all special cases of the following "rewrite all sides"
     lemma which we prove is an equivalence giving us all special cases
     as equivalences too *)

  Definition equiv_sq_GGGG {px0' px1' p0x' p1x'} (qx0 : px0 = px0')
    (qx1 : px1 = px1') (q0x : p0x = p0x') (q1x : p1x = p1x')
    : PathSquare px0 px1 p0x p1x <~> PathSquare px0' px1' p0x' p1x'.
  Proof.
    by destruct qx0, qx1, q0x, q1x.
  Defined.

  Context {px0' px1' p0x' p1x'}
    (qx0 : px0 = px0') (qx1 : px1 = px1')
    (q0x : p0x = p0x') (q1x : p1x = p1x').

  Definition equiv_sq_Gccc := equiv_sq_GGGG qx0 1 1 1.
  Definition equiv_sq_cGcc := equiv_sq_GGGG 1 qx1 1 1.
  Definition equiv_sq_ccGc := equiv_sq_GGGG 1 1 q0x 1.
  Definition equiv_sq_cccG := equiv_sq_GGGG 1 1 1 q1x.
  Definition equiv_sq_GGcc := equiv_sq_GGGG qx0 qx1 1 1.
  Definition equiv_sq_GcGc := equiv_sq_GGGG qx0 1 q0x 1.
  Definition equiv_sq_GccG := equiv_sq_GGGG qx0 1 1 q1x.
  Definition equiv_sq_cGGc := equiv_sq_GGGG 1 qx1 q0x 1.
  Definition equiv_sq_cGcG := equiv_sq_GGGG 1 qx1 1 q1x.
  Definition equiv_sq_ccGG := equiv_sq_GGGG 1 1 q0x q1x.
  Definition equiv_sq_GGGc := equiv_sq_GGGG qx0 qx1 q0x 1.
  Definition equiv_sq_cGGG := equiv_sq_GGGG 1 qx1 q0x q1x.

End PathSquareRewriting.

Notation sq_GGGG := equiv_sq_GGGG.
Notation sq_Gccc := equiv_sq_Gccc.
Notation sq_cGcc := equiv_sq_cGcc.
Notation sq_ccGc := equiv_sq_ccGc.
Notation sq_cccG := equiv_sq_cccG.
Notation sq_GGcc := equiv_sq_GGcc.
Notation sq_GcGc := equiv_sq_GcGc.
Notation sq_GccG := equiv_sq_GccG.
Notation sq_cGGc := equiv_sq_cGGc.
Notation sq_cGcG := equiv_sq_cGcG.
Notation sq_ccGG := equiv_sq_ccGG.
Notation sq_GGGc := equiv_sq_GGGc.
Notation sq_cGGG := equiv_sq_cGGG.

Section MovePaths.
  Context {A : Type} {x x00 x20 x02 x22 : A}
  {f10 : x00 = x20} {f12 : x02 = x22} {f01 : x00 = x02} {f21 : x20 = x22}.
  (** Operations to move paths around a square. We define all these operations immediately as equivalences. The naming first number indicates in which argument the path that moves is on the left of the equivalence, and the second number where it is on the right. The equivalences are all set up so that on the right, there is no path inversion. For the [24] and [13] equivalences there is a path inverse on the left. The corresponding equivalences [42] and [31] are the symmetric versions of these, but the path inverse is in another place. *)

  Definition equiv_sq_move_23 {f12'' : x02 = x} {f12' : x = x22} 
    : PathSquare f10 (f12'' @ f12') f01 f21 <~> PathSquare f10 f12' (f01 @ f12'') f21.
  Proof.
    clear f12. destruct f12''.
    refine (sq_cGcc (concat_1p _) oE _).
    exact (sq_ccGc (concat_p1 _)^).
  Defined.

  Definition equiv_sq_move_14 {f10'' : x00 = x} {f10' : x = x20} 
    : PathSquare (f10'' @ f10') f12 f01 f21 <~> PathSquare f10'' f12 f01 (f10' @ f21).
  Proof.
    clear f10. destruct f10'.
    refine (sq_cccG (concat_1p _)^ oE _).
    exact (sq_Gccc (concat_p1 _)).
  Defined.

  Definition equiv_sq_move_24 {f12'' : x02 = x} {f12' : x22 = x} 
    : PathSquare f10 (f12'' @ f12'^) f01 f21 <~> PathSquare f10 f12'' f01 (f21 @ f12').
  Proof.
    clear f12. destruct f12'.
    refine (sq_cccG (concat_p1 _)^ oE _).
    exact (sq_cGcc (concat_p1 _)).
  Defined.

  Definition equiv_sq_move_42 {f12'' : x02 = x} {f12' : x = x22} 
    : PathSquare f10 f12'' f01 (f21 @ f12'^) <~> PathSquare f10 (f12'' @ f12') f01 f21.
  Proof.
    clear f12. destruct f12'.
    refine (sq_cGcc (concat_p1 _)^ oE _).
    exact (sq_cccG (concat_p1 _)).
  Defined.

  Definition equiv_sq_move_13 {f10'' : x = x00} {f10' : x = x20} 
    : PathSquare (f10''^ @ f10') f12 f01 f21 <~> PathSquare f10' f12 (f10'' @ f01) f21.
  Proof.
    clear f10. destruct f10''.
    refine (sq_ccGc (concat_1p _)^ oE _).
    exact (sq_Gccc (concat_1p _)).
  Defined.

  Definition equiv_sq_move_31 {f10'' : x00 = x} {f10' : x = x20} 
    : PathSquare f10' f12 (f10''^ @ f01) f21 <~> PathSquare (f10'' @ f10') f12 f01 f21.
  Proof.
    clear f10. destruct f10''.
    refine (sq_Gccc (concat_1p _)^ oE _).
    exact (sq_ccGc (concat_1p _)).
  Defined.

End MovePaths.

Notation sq_move_23 := equiv_sq_move_23.
Notation sq_move_14 := equiv_sq_move_14.
Notation sq_move_24 := equiv_sq_move_24.
Notation sq_move_42 := equiv_sq_move_42.
Notation sq_move_13 := equiv_sq_move_13.
Notation sq_move_31 := equiv_sq_move_31.

(* Dependent path product definition of [PathSquare] CoqDoc *)
Definition equiv_sq_dp_prod {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  : DPath (fun xy => fst xy = snd xy) (path_prod' p0x p1x) px0 px1
    <~> PathSquare px0 px1 p0x p1x.
Proof.
  refine (_ oE (dp_paths_FlFr _ _ _)^-1).
  refine (_ oE (equiv_concat_l (concat_pp_p _ _ _) _)^-1).
  refine (_ oE equiv_moveL_Mp _ _ _).
  refine (_ oE sq_path).
  exact (sq_ccGG (ap_fst_path_prod _ _) (ap_snd_path_prod _ _)).
Defined.

Notation sq_dp_prod := equiv_sq_dp_prod.

(* Concatenation of squares *)
Section PathSquareConcat.

  Context {A : Type} {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}.

  (* Horizontal concatenation of squares *)
  Definition sq_concat_h  {a02 a12 : A}
    {p0y : a01 = a02} {p1y : a11 = a12} {px2 : a02 = a12}
    : PathSquare px0 px1 p0x p1x -> PathSquare px1 px2 p0y p1y
      -> PathSquare px0 px2 (p0x @ p0y) (p1x @ p1y).
  Proof.
    intros a b.
    destruct b.
    refine (sq_ccGG _ _ a).
    1,2: apply inverse, concat_p1.
  Defined.

  Infix "@@h" := sq_concat_h : square_scope.

  (* Vertical concatenation of squares *)
  Definition sq_concat_v {a20 a21 : A}
    {py0 : a10 = a20} {py1 : a11 = a21} {p2x : a20 = a21}
    : PathSquare px0 px1 p0x p1x -> PathSquare py0 py1 p1x p2x
      -> PathSquare (px0 @ py0) (px1 @ py1) p0x p2x.
  Proof.
    intros a b.
    destruct b.
    refine (sq_GGcc _ _ a).
    1,2: apply inverse, concat_p1.
  Defined.

  Infix "@@v" := sq_concat_v : square_scope.

End PathSquareConcat.

(* Horizontal groupoid laws for concatenation *)
Section GroupoidLawsH.

  (* There are many more laws to write, but it seems we don't really need them *)

  Context
    {A : Type}
    {a00 a10 a01 a11 a02 a12 a20 a21 a03 a13 : A} {px0 : a00 = a10}
    {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
    {px2 : a02 = a12} {p0y : a01 = a02} {p1y : a11 = a12}
    {px3 : a03 = a13} {p0z : a02 = a03} {p1z : a12 = a13}
    (s : PathSquare px0 px1 p0x p1x).

  Local Open Scope square_scope.
  Notation hr := (sq_refl_h _).

  Definition sq_concat_h_s1 : sq_concat_h s hr = sq_ccGG (concat_p1 _)^ (concat_p1 _)^ s.
  Proof.
    by destruct s.
  Defined.

  Definition sq_concat_h_1s : sq_concat_h hr s = sq_ccGG (concat_1p _)^ (concat_1p _)^ s.
  Proof.
    by destruct s.
  Defined.

  Context (t : PathSquare px1 px2 p0y p1y) (u : PathSquare px2 px3 p0z p1z).

  Definition sq_concat_h_ss_s : sq_concat_h (sq_concat_h s t) u
    = sq_ccGG (concat_p_pp _ _ _) (concat_p_pp _ _ _) (sq_concat_h s (sq_concat_h t u)).
  Proof.
    by destruct s, u, (sq_1G^-1 t), p0y.
  Defined.

End GroupoidLawsH.

(** [PathSquare] Kan fillers ~ Every open box has a lid *)

Section Kan.

  (* These can be used to prove groupoid laws about paths *)
  Context {A : Type} {a00 a10 a01 a11 : A}.

  Definition sq_fill_l (px1 : a01 = a11) (p0x : a00 = a01) (p1x : a10 = a11)
    : {px0 : a00 = a10 & PathSquare px0 px1 p0x p1x}.
  Proof.
    exists (p0x @ px1 @ p1x^).
    by destruct px1, p0x, p1x.
  Defined.

  Definition sq_fill_l_uniq
             {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
             {px0 : a00 = a10} (s : PathSquare px0 px1 p0x p1x)
             {px0' : a00 = a10} (s' : PathSquare px0' px1 p0x p1x)
    : px0 = px0'.
  Proof.
    destruct s.
    apply sq_path^-1 in s'.
    exact (s'^ @ concat_p1 _).
  Defined.

  Definition sq_fill_r (px0 : a00 = a10) (p0x : a00 = a01) (p1x : a10 = a11)
    : {px1 : a01 = a11 & PathSquare px0 px1 p0x p1x}.
  Proof.
    exists (p0x^ @ px0 @ p1x).
    by destruct px0, p0x, p1x.
  Defined.

  Definition sq_fill_r_uniq
             {px0 : a00 = a10} {p0x : a00 = a01} {p1x : a10 = a11}
             {px1 : a01 = a11} (s : PathSquare px0 px1 p0x p1x)
             {px1' : a01 = a11} (s' : PathSquare px0 px1' p0x p1x)
    : px1 = px1'.
  Proof.
    destruct s.
    apply sq_path^-1 in s'.
    exact (s' @ concat_1p _).
  Defined.

  Definition equiv_sq_fill_lr (p0x : a00 = a01) (p1x : a10 = a11)
    : (a00 = a10) <~> (a01 = a11).
  Proof.
    srapply equiv_adjointify.
    - intros px0; exact (sq_fill_r px0 p0x p1x).1.
    - intros px1; exact (sq_fill_l px1 p0x p1x).1.
    - intros px1.
      exact (sq_fill_r_uniq (sq_fill_r _ p0x p1x).2
                            (sq_fill_l px1 p0x p1x).2).
    - intros px0.
      exact (sq_fill_l_uniq (sq_fill_l _ p0x p1x).2
                            (sq_fill_r px0 p0x p1x).2).
  Defined.

  Definition sq_fill_t (px0 : a00 = a10) (px1 : a01 = a11) (p1x : a10 = a11)
    : {p0x : a00 = a01 & PathSquare px0 px1 p0x p1x}.
  Proof.
    exists (px0 @ p1x @ px1^).
    by destruct px0, px1, p1x.
  Defined.

  Definition sq_fill_b (px0 : a00 = a10) (px1 : a01 = a11) (p0x : a00 = a01)
    : {p1x : a10 = a11 & PathSquare px0 px1 p0x p1x}.
  Proof.
    exists (px0^ @ p0x @ px1).
    by destruct px0, px1, p0x.
  Defined.

End Kan.

(* Apply a function to the sides of square *)
Definition sq_ap {A B : Type} {a00 a10 a01 a11 : A} (f : A -> B)
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  : PathSquare px0 px1 p0x p1x -> PathSquare (ap f px0) (ap f px1) (ap f p0x) (ap f p1x).
Proof.
  by intros [].
Defined.

(** This preserves reflexivity *)
Definition sq_ap_refl_h {A B} (f : A -> B) {a0 a1 : A} (p : a0 = a1)
  : sq_ap f (sq_refl_h p) = sq_refl_h (ap f p).
Proof.
  by destruct p.
Defined.

Definition sq_ap_refl_v {A B} (f : A -> B) {a0 a1 : A} (p : a0 = a1)
  : sq_ap f (sq_refl_v p) = sq_refl_v (ap f p).
Proof.
  by destruct p.
Defined.

(** [PathSquare]s respect products *)
Definition equiv_sq_prod {A B : Type} {a00 a10 a01 a11 : A} {px0 : a00 = a10}
  {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11} {b00 b10 b01 b11 : B}
  {qx0 : b00 = b10} {qx1 : b01 = b11} {q0x : b00 = b01} {q1x : b10 = b11}
  : (PathSquare px0 px1 p0x p1x) * (PathSquare qx0 qx1 q0x q1x)
    <~> PathSquare (path_prod' px0 qx0) (path_prod' px1 qx1)
        (path_prod' p0x q0x) (path_prod' p1x q1x).
Proof.
  refine (_ oE (equiv_functor_prod' sq_path sq_path)^-1%equiv).
  refine (_ oE equiv_path_prod (_,_) (_,_)).
  srefine (_ oE equiv_ap' _ _ _).
  3: exact (equiv_path_prod (_,_) (_,_)).
  refine (_ oE equiv_concat_l _^ _).
  2: apply (path_prod_pp (_,_) (_,_) (_,_)).
  refine (_ oE equiv_concat_r _ _).
  2: apply (path_prod_pp (_,_) (_,_) (_,_)).
  exact sq_path.
Defined.

Notation sq_prod := equiv_sq_prod.

(** The natural square from an [ap] *)
Definition ap_nat {A B} {f f' : A -> B} (h : f == f') {x y : A} (p : x = y)
  : PathSquare (ap f p) (ap f' p) (h x) (h y).
Proof.
  by destruct p; apply sq_1G.
Defined.

(** The transpose of the natural square *)
Definition ap_nat' {A B} {f f' : A -> B} (h : f == f') {x y : A} (p : x = y)
  : PathSquare (h x) (h y) (ap f p) (ap f' p).
Proof.
  by destruct p; apply sq_G1.
Defined.

(** [ap_compose] fits naturally into a square *)
Definition ap_compose_sq {A B C} (f : A -> B) (g : B -> C) {x y : A} (p : x = y)
  : PathSquare (ap (g o f) p) (ap g (ap f p)) 1 1 := sq_G1 (ap_compose f g p).

Definition ap_idmap_sq {A} {x y : A} (p : x = y) : PathSquare (ap idmap p) p 1 1
  := sq_G1 (ap_idmap p).

(** A [DPath] of a certain form can be turned into a square *)
Definition equiv_sq_dp {A B : Type} {f g : A -> B} {a1 a2 : A} {p : a1 = a2}
  {q1 : f a1 = g a1} {q2 : f a2 = g a2}
  : DPath (fun x => f x = g x) p q1 q2 <~> PathSquare q1 q2 (ap f p) (ap g p).
Proof.
  destruct p.
  exact sq_G1.
Defined.

Notation sq_dp := equiv_sq_dp.

(** [ap011] fits into a square *)
Definition sq_ap011 {A B C} (f : A -> B -> C)
  {a a' : A} (p : a = a') {b b' : B} (q : b = b')
  : PathSquare (ap (fun x => f x b) p) (ap (fun x => f x b') p)
    (ap (f a) q) (ap (f a') q).
Proof.
  apply sq_dp.
  exact (apD (fun y => ap (fun x => f x y) p) q).
Defined.

