Require Import Basics.
Require Import Types.
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

(* Contents:

  * Definition of PathSquare 
  * Degnerate PathSquares as paths between paths
  * Flipping squares horizontally and vertically
  * PathSquare transpose
  * PathSquare inverse
  * PathSquare rotations
  * Edge rewriting
  * Concatenation
  * Kan fillers
  * natural squares from ap

*)


(* Definition of PathSquare *)
(* PathSquare left right up down *)
Cumulative Inductive PathSquare {A} : forall a00 {a10 a01 a11 : A},
  a00 = a10 -> a01 = a11 -> a00 = a01 -> a10 = a11 -> Type
  := sq_id : forall {x : A},
    PathSquare x 1 1 1 1.

Arguments sq_id {A x}.
Arguments PathSquare {A _ _ _ _}.
Notation "1" := sq_id : square_scope.

(* It seems coq has difficulty actually using these, but destruct seems
   to work fine. TODO: Work out if these are correct. *)
Scheme PathSquare_ind := Induction for PathSquare Sort Type.
Arguments PathSquare_ind {A} P f {_ _ _ _ _ _ _ _} _.
Scheme PathSquare_rec := Minimality for PathSquare Sort Type.
Arguments PathSquare_rec {A} P f {_ _ _ _ _ _ _ _} _.

(* PathSquare_ind is an equivalence, similar to how paths_ind is *)
Global Instance isequiv_PathSquare_ind `{Funext} {A}
  (P : forall (a00 a10 a01 a11 : A) (p : a00 = a10) (p0 : a01 = a11)
    (p1 : a00 = a01) (p2 : a10 = a11),
    PathSquare p p0 p1 p2 -> Type) : IsEquiv (PathSquare_ind P).
Proof.
  serapply isequiv_adjointify.
  1: intros X ?; apply X.
  2: intro; reflexivity.
  intro.
  do 8 (apply path_forall; intro).
  apply path_forall.
  by intros [].
Defined.

(* PathSquares can be given by 2-dimensional paths *)
Definition sq_path {A} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11}
  {p0x : a00 = a01} {p1x : a10 = a11}
  : px0 @ p1x = p0x @ px1 -> PathSquare px0 px1 p0x p1x.
Proof.
  intro q.
  by destruct px0, p0x, (cancelL 1 _ _ q), p1x.
Defined.

Global Instance isequiv_sq_path {A} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
: IsEquiv (@sq_path _ _ _ _ _ px0 px1 p0x p1x).
Proof.
  serapply isequiv_adjointify; try by intros [].
  intro X.
  destruct px0, p0x.
  destruct (eissect (equiv_cancelL 1 _ _) X).
  cbn; set (p := cancelL 1 _ _ X).
  clearbody p; clear X.
  by destruct p, p1x.
Defined.

(** Squares in (n+2)-truncated types are n-truncated *)
Global Instance istrunc_sq n
  {A} `{!IsTrunc n.+2 A} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11}
  {p0x : a00 = a01} {p1x : a10 = a11}
  : IsTrunc n (PathSquare px0 px1 p0x p1x).
Proof.
  serapply (trunc_equiv _ sq_path).
Defined.

(* We can give degenerate squares *)
Section PathSquaresFromPaths.

  (* NOTE: These are much easier to prove but stringing them along with
    equivalences is how we get them to be equivalences *)

  Context
    {A : Type} {a00 a10 a01 : A}
    {p p' : a00 = a10} {q q' : a00 = a01}.

  Definition sq_G1  : p = p' -> PathSquare p p' 1 1.
  Proof.
    intro.
    by apply sq_path, (equiv_concat_lr (concat_p1 _)^ (concat_1p _))^-1.
  Defined.

  Global Instance isequiv_sq_G1 : IsEquiv sq_G1 := _.

  Definition sq_1G : q = q' -> PathSquare 1 1 q q'.
  Proof.
    intro.
    by apply sq_path, (equiv_concat_lr (concat_1p _)^ (concat_p1 _))^-1.
  Defined.

  Global Instance isequiv_sq_1G : IsEquiv sq_G1 := _.

End PathSquaresFromPaths.

(* PathSquare horizontal reflexivity *)
Definition sq_refl_h {A} {a0 a1 : A} (p : a0 = a1)
  : PathSquare p p 1 1 := sq_G1 1.

(* PathSquare vertical reflexivity *)
Definition sq_refl_v {A} {a0 a1 : A} (p : a0 = a1)
  : PathSquare 1 1 p p := sq_1G 1.

(* Horizontal flip *)
Definition sq_flip_h {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  : PathSquare px0 px1 p0x p1x -> PathSquare px1 px0 p0x^ p1x^.
Proof.
  destruct p0x, p1x.
  intro.
  by apply sq_G1, inverse, sq_G1^-1.
Defined.

Global Instance isequiv_sq_flip_h {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  : IsEquiv (sq_flip_h (px0:=px0) (px1:=px1) (p0x:=p0x) (p1x:=p1x)).
Proof.
  destruct p0x, p1x; exact _.
Defined.

(* Vertical flip *)
Definition sq_flip_v {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  : PathSquare px0 px1 p0x p1x -> PathSquare px0^ px1^ p1x p0x.
Proof.
  destruct px0, px1.
  intro.
  by apply sq_1G, inverse, sq_1G^-1.
Defined.

Global Instance isequiv_sq_flip_v {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  : IsEquiv (sq_flip_v (px0:=px0) (px1:=px1) (p0x:=p0x) (p1x:=p1x)).
Proof.
  destruct px0, px1; exact _.
Defined.

(* Transpose of a square *)
Definition sq_tr {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
: PathSquare px0 px1 p0x p1x -> PathSquare p0x p1x px0 px1.
Proof.
  by intros [].
Defined.

(** [sq_tr] is "involutive" *)
Definition sq_tr_sq_tr {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  (s : PathSquare px0 px1 p0x p1x) : sq_tr (sq_tr s) = s.
Proof. 
  destruct s. reflexivity. 
Defined.

(* NOTE: sq_tr ought to be some sort of involution but it obviously isn't
   since it is not of the form A -> A. Perhaps there is a more general
   "involution" but between equivalent types? But then that very equivalence
   is given by sq_tr so it seems a bit circular... *)

Section sq_tr_args.
Local Arguments sq_tr {_ _ _ _ _} _ _ _ _.
Global Instance isequiv_sq_tr {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  : IsEquiv (sq_tr px0 px1 p0x p1x).
Proof.
  serapply isequiv_adjointify.
  1: apply sq_tr.
  1,2: exact sq_tr_sq_tr.
Defined.
End sq_tr_args.

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
  Definition sq_V : PathSquare px0 px1 p0x p1x -> PathSquare px1^ px0^ p1x^ p0x^.
  Proof.
    intro.
    by apply sq_path, (equiv_concat_lr (inv_pp _ _ )^ (inv_pp _ _)),
      inverse2, sq_path^-1, sq_tr.
  Defined.

  Global Instance isequiv_sq_V : IsEquiv sq_V := _.

  (* Left rotation : left right top bottom  ->  top bottom right left *)
  Definition sq_rot_l : PathSquare px0 px1 p0x p1x -> PathSquare p0x^ p1x^ px1 px0.
  Proof.
    intro.
    by apply sq_path, moveR_Vp, (equiv_concat_r (concat_pp_p _ _ _)),
      moveL_pV, sq_path^-1.
  Defined.

  Global Instance isequiv_sq_rot_l : IsEquiv sq_rot_l := _.

  (* Right rotation : left right top bottom -> bottom top left right *)
  Definition sq_rot_r : PathSquare px0 px1 p0x p1x -> PathSquare p1x p0x px0^ px1^.
  Proof.
    intro.
    by apply sq_path, moveL_Vp, (equiv_concat_l (concat_p_pp _ _ _)),
      moveR_pV, sq_path^-1.
  Defined.

  Global Instance isequiv_sq_rot_r : IsEquiv sq_rot_r := _.

End PathSquareOps.

(* Lemmas for rewriting sides of squares *)
Section PathSquareRewriting.

  Context {A : Type}
    {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}.

  (* These are all special cases of the following "rewrite all sides"
     lemma which we prove is an equivalence giving us all special cases
     as equivalences too *)

  Definition sq_GGGG {px0' px1' p0x' p1x'} (qx0 : px0 = px0')
    (qx1 : px1 = px1') (q0x : p0x = p0x') (q1x : p1x = p1x')
    : PathSquare px0 px1 p0x p1x -> PathSquare px0' px1' p0x' p1x'.
  Proof.
    by destruct qx0, qx1, q0x, q1x.
  Defined.

  Global Instance isequiv_sq_GGGG {px0' px1' p0x' p1x'} (qx0 : px0 = px0')
    (qx1 : px1 = px1') (q0x : p0x = p0x') (q1x : p1x = p1x')
    : IsEquiv (sq_GGGG qx0 qx1 q0x q1x).
  Proof.
    destruct qx0, qx1, q0x, q1x; exact _.
  Defined.

  Context {px0' px1' p0x' p1x'}
    (qx0 : px0 = px0') (qx1 : px1 = px1')
    (q0x : p0x = p0x') (q1x : p1x = p1x').

  Definition sq_Gccc := sq_GGGG qx0 1 1 1.
  Definition sq_cGcc := sq_GGGG 1 qx1 1 1.
  Definition sq_ccGc := sq_GGGG 1 1 q0x 1.
  Definition sq_cccG := sq_GGGG 1 1 1 q1x.
  Definition sq_GGcc := sq_GGGG qx0 qx1 1 1.
  Definition sq_GcGc := sq_GGGG qx0 1 q0x 1.
  Definition sq_GccG := sq_GGGG qx0 1 1 q1x.
  Definition sq_cGGc := sq_GGGG 1 qx1 q0x 1.
  Definition sq_cGcG := sq_GGGG 1 qx1 1 q1x.
  Definition sq_ccGG := sq_GGGG 1 1 q0x q1x.
  Definition sq_GGGc := sq_GGGG qx0 qx1 q0x 1.
  Definition sq_cGGG := sq_GGGG 1 qx1 q0x q1x.

End PathSquareRewriting.

Section MovePaths.
  Context {A : Type} {x x00 x20 x02 x22 : A}
  {f10 : x00 = x20} {f12 : x02 = x22} {f01 : x00 = x02} {f21 : x20 = x22}.
  (** Operations to move paths around a square. We define all these operations
    immediately as equvialences. 
    The naming first number indicates in which argument the path that moves is 
    on the left of the equivalence, and the second number where it is on the right.
    The equivalences are all set up so that on the right, there is no path inversion.
    For the [24] and [13] equivalences there is a path inverse on the left.
    The corresponding equivalences [42] and [31] are the symmetric versions of these,
    but the path inverse is in another place. *)

  Definition sq_move_23 {f12'' : x02 = x} {f12' : x = x22} 
    : PathSquare f10 (f12'' @ f12') f01 f21 <~> PathSquare f10 f12' (f01 @ f12'') f21.
  Proof.
    clear f12. destruct f12''. 
    serapply Build_Equiv. 
    + refine (fun s => sq_ccGc (concat_p1 _)^ (sq_cGcc (concat_1p _) s)).
    + exact _.
  Defined.

  Definition sq_move_14 {f10'' : x00 = x} {f10' : x = x20} 
    : PathSquare (f10'' @ f10') f12 f01 f21 <~> PathSquare f10'' f12 f01 (f10' @ f21).
  Proof.
    clear f10. destruct f10'. 
    serapply Build_Equiv. 
    + refine (fun s => sq_cccG (concat_1p _)^ (sq_Gccc (concat_p1 _) s)).
    + exact _.
  Defined.

  Definition sq_move_24 {f12'' : x02 = x} {f12' : x22 = x} 
    : PathSquare f10 (f12'' @ f12'^) f01 f21 <~> PathSquare f10 f12'' f01 (f21 @ f12').
  Proof.
    clear f12. destruct f12'. 
    serapply Build_Equiv. 
    + refine (fun s => sq_cccG (concat_p1 _)^ (sq_cGcc (concat_p1 _) s)).
    + exact _.
  Defined.

  Definition sq_move_42 {f12'' : x02 = x} {f12' : x = x22} 
    : PathSquare f10 f12'' f01 (f21 @ f12'^) <~> PathSquare f10 (f12'' @ f12') f01 f21.
  Proof.
    clear f12. destruct f12'. 
    symmetry.
    serapply Build_Equiv. 
    + refine (fun s => sq_cccG (concat_p1 _)^ (sq_cGcc (concat_p1 _) s)).
    + exact _.
  Defined.

  Definition sq_move_13 {f10'' : x = x00} {f10' : x = x20} 
    : PathSquare (f10''^ @ f10') f12 f01 f21 <~> PathSquare f10' f12 (f10'' @ f01) f21.
  Proof.
    clear f10. destruct f10''. 
    serapply Build_Equiv. 
    + refine (fun s => sq_ccGc (concat_1p _)^ (sq_Gccc (concat_1p _) s)).
    + exact _.
  Defined.

  Definition sq_move_31 {f10'' : x00 = x} {f10' : x = x20} 
    : PathSquare f10' f12 (f10''^ @ f01) f21 <~> PathSquare (f10'' @ f10') f12 f01 f21.
  Proof.
    clear f10. destruct f10''. 
    symmetry.
    refine (Build_Equiv _ _ (fun s => sq_ccGc (concat_1p _)^ (sq_Gccc (concat_1p _) s)) _).
  Defined.

End MovePaths.

Section DPathPathSquare.

  (* An alternative equivalent definition for PathSquares in terms of
     DPaths. This is the original one Mike had written. *)

  Context {A} {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}.

  (* Depdent path product definition of PathSquare *)
  Definition sq_dp_prod : DPath (fun xy => fst xy = snd xy)
    (path_prod' p0x p1x) px0 px1 -> PathSquare px0 px1 p0x p1x.
  Proof.
    intro.
    set (p := (dp_paths_FlFr _ _ _)^-1 X).
    apply (equiv_concat_l (concat_pp_p _ _ _) _)^-1,
      moveL_Mp, sq_path in p.
    exact (sq_ccGG (ap_fst_path_prod _ _) (ap_snd_path_prod _ _) p).
  Defined.

  Global Instance isequiv_sq_dpath_prod : IsEquiv sq_dp_prod := _.

End DPathPathSquare.

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

End PathSquareConcat.

(* Notations for horizontal and vertical concatenation *)
Infix "@h" := sq_concat_h (at level 10) : square_scope.
Infix "@v" := sq_concat_v (at level 10) : square_scope.

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

  Definition sq_concat_h_s1 : s @h hr = sq_ccGG (concat_p1 _)^ (concat_p1 _)^ s.
  Proof.
    by destruct s.
  Defined.

  Definition sq_concat_h_1s : hr @h s = sq_ccGG (concat_1p _)^ (concat_1p _)^ s.
  Proof.
    by destruct s.
  Defined.

  Context (t : PathSquare px1 px2 p0y p1y) (u : PathSquare px2 px3 p0z p1z).

  Definition sq_concat_h_ss_s : (s @h t) @h u
    = sq_ccGG (concat_p_pp _ _ _) (concat_p_pp _ _ _) (s @h (t @h u)).
  Proof.
    by destruct s, u, (sq_1G^-1 t), p0y.
  Defined.

End GroupoidLawsH.

(* PathSquare Kan fillers ~ Every open box has a lid *)

Section Kan.

  (* These can be used to prove groupoid laws about paths *)
  Context {A : Type} {a00 a10 a01 a11 : A}.

  Definition sq_fill_l (px1 : a01 = a11) (p0x : a00 = a01) (p1x : a10 = a11)
    : {px0 : a00 = a10 & PathSquare px0 px1 p0x p1x}.
  Proof.
    exists (p0x @ px1 @ p1x^).
    by destruct px1, p0x, p1x.
  Defined.

  Definition sq_fill_r (px0 : a00 = a10) (p0x : a00 = a01) (p1x : a10 = a11)
    : {px1 : a01 = a11 & PathSquare px0 px1 p0x p1x}.
  Proof.
    exists (p0x^ @ px0 @ p1x).
    by destruct px0, p0x, p1x.
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

(* Curried version of the following equivalence *)
Definition sq_prod {A B : Type} {a00 a10 a01 a11 : A} {px0 : a00 = a10}
  {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11} {b00 b10 b01 b11 : B}
  {qx0 : b00 = b10} {qx1 : b01 = b11} {q0x : b00 = b01} {q1x : b10 = b11}
  : PathSquare px0 px1 p0x p1x -> PathSquare qx0 qx1 q0x q1x
    -> PathSquare (path_prod' px0 qx0) (path_prod' px1 qx1)
        (path_prod' p0x q0x) (path_prod' p1x q1x).
Proof.
  by intros [] [].
Defined.

(*
(* PathSquares respect products *)
(* TODO: Finish this: we ought to have some sort of eta for sq_prod
   that might help *)
Definition equiv_sq_prod {A B : Type} {a00 a10 a01 a11 : A} {px0 : a00 = a10}
  {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11} {b00 b10 b01 b11 : B}
  {qx0 : b00 = b10} {qx1 : b01 = b11} {q0x : b00 = b01} {q1x : b10 = b11}
  : (PathSquare px0 px1 p0x p1x) * (PathSquare qx0 qx1 q0x q1x)
    <~> PathSquare (path_prod' px0 qx0) (path_prod' px1 qx1)
        (path_prod' p0x q0x) (path_prod' p1x q1x).
Proof.
  serapply equiv_adjointify.
  1: apply uncurry, sq_prod.
  { intro c.
    destruct p1x, q1x, p0x, q0x.
    apply sq_G1^-1 in c.
    set (f := ap (ap fst) c); clearbody f.
    set (s := ap (ap snd) c); clearbody s.
    destruct ((ap_fst_path_prod _ _)^ @ ap (ap fst) c @ ap_fst_path_prod _ _).
    destruct ((ap_snd_path_prod _ _)^ @ ap (ap snd) c @ ap_snd_path_prod _ _).
    split.
    1,2: apply sq_refl_h. }
  { intro c.
    set (s1 := sq_GGGG (ap_fst_path_prod _ _) (ap_fst_path_prod _ _)
      (ap_fst_path_prod _ _) (ap_fst_path_prod _ _) (sq_ap fst c)).
    set (s2 := sq_GGGG (ap_snd_path_prod _ _) (ap_snd_path_prod _ _)
      (ap_snd_path_prod _ _) (ap_snd_path_prod _ _) (sq_ap snd c)).
    admit. }
  by intros [[] []].
Admitted. *)

(* The natural square from an ap *)
Definition ap_nat {A B} {f f' : A -> B} (h : f == f') {x y : A} (p : x = y)
  : PathSquare (ap f p) (ap f' p) (h x) (h y).
Proof.
  by destruct p; apply sq_1G.
Defined.

(* The transpose of the natural square *)
Definition ap_nat' {A B} {f f' : A -> B} (h : f == f') {x y : A} (p : x = y)
  : PathSquare (h x) (h y) (ap f p) (ap f' p).
Proof.
  by destruct p; apply sq_G1.
Defined.

(* ap_compose fits naturally into a square *)
Definition ap_compose_sq {A B C} (f : A -> B) (g : B -> C) {x y : A} (p : x = y)
  : PathSquare (ap (g o f) p) (ap g (ap f p)) 1 1 := sq_G1 (ap_compose f g p).

Definition ap_idmap_sq {A} {x y : A} (p : x = y) : PathSquare (ap idmap p) p 1 1
  := sq_G1 (ap_idmap p).

(* A DPath of a certain form can be turned into a square *)
Definition sq_dp {A B : Type} {f g : A -> B} {a1 a2 : A} {p : a1 = a2}
  {q1 : f a1 = g a1} {q2 : f a2 = g a2}
  : DPath (fun x => f x = g x) p q1 q2 -> PathSquare q1 q2 (ap f p) (ap g p).
Proof.
  destruct p.
  exact sq_G1.
Defined.

Global Instance isequiv_sq_dp {A B : Type} {f g : A -> B} {a1 a2 : A}
  {p : a1 = a2} {q1 : f a1 = g a1} {q2 : f a2 = g a2}
  : IsEquiv (sq_dp (p:=p) (q1:=q1) (q2:=q2)).
Proof.
  destruct p; exact _.
Defined.

(* ap2 fits into a square *)
Definition sq_ap2 {A B C} (f : A -> B -> C)
  {a a' : A} (p : a = a') {b b' : B} (q : b = b')
  : PathSquare (ap (fun x => f x b) p) (ap (fun x => f x b') p)
    (ap (f a) q) (ap (f a') q)
  := sq_dp (dp_apD (fun y => ap (fun x => f x y) _) _).

(* The function in ap2 can be uncurried *)
Definition ap_uncurry {A B C} (f : A -> B -> C) {a a' : A} (p : a = a')
  {b b' : B} (q : b = b')
  : PathSquare (ap (uncurry f) (path_prod' p q)) (ap2 f p q) 1 1.
Proof.
  by destruct p, q.
Defined.


