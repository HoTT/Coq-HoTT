Require Import Basics.
Require Import Cubical.DPath.
Require Import Cubical.PathSquare.
Require Import Cubical.DPathSquare.
Require Import Types.Paths Types.Prod.

Declare Scope cube_scope.
Delimit Scope cube_scope with cube.
Local Unset Elimination Schemes.
Generalizable All Variables.

Local Open Scope square_scope.

(*
x001----pi01----x101              x001----pi01----x101
 |  \               \              |               |  \
 |  p00i  ==si0i=>  p10i           |               |  p10i
p0i1  \               \           p0i1 ==sii1=>   p1i1  \
 |    x000----pi00----x100         |               |    x100
 |s0ii |               |    ===>   |               | s1ii|
x011   |               |          x011----pi11----x111   |
  \   p0i0  ==sii0=>  p1i0          \               \   p1i0
 p01i  |               |           p01i  ==si1i=>  p11i  |
     \ |               |               \               \ |
      x010----pi10----x110              x010----pi10----x110
 *)

(** Contents:
  * Definition of [PathCube]
  * [PathCube] reflexivity
  * [PathCube] face rewriting
  * [PathCube]s from paths between squares
  * [PathCube]s from squares
  * [PathCube] flipping
  * Kan fillers
  * [PathCube] concatenation
  * natural cubes from [ap]
*)


(** Homogeneous cubes *)
(** PathCube left right top bottom front back *)
Cumulative Inductive PathCube {A}
  : forall x000 {x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  (s0ii : PathSquare p0i0 p0i1 p00i p01i) (s1ii : PathSquare p1i0 p1i1 p10i p11i)
  (sii0 : PathSquare p0i0 p1i0 pi00 pi10) (sii1 : PathSquare p0i1 p1i1 pi01 pi11)
  (si0i : PathSquare p00i p10i pi00 pi01) (si1i : PathSquare p01i p11i pi10 pi11), Type
  := idcube : forall x, PathCube x 1 1 1 1 1 1.

Arguments PathCube {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

(* TODO: ": rename" is needed because the default names changed in Rocq 9.2.0.  When the minimum supported version is >= 9.2.0, the ": rename" can be removed. *)
Scheme PathCube_ind := Induction for PathCube Sort Type.
Arguments PathCube_ind {A} P f
  {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} : rename.

(* TODO: ": rename" is needed because the default names changed in Rocq 9.2.0.  When the minimum supported version is >= 9.2.0, the ": rename" can be removed. *)
Scheme PathCube_rec := Minimality for PathCube Sort Type.
Arguments PathCube_rec {A} P f
  {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} : rename.

(* These notations make it easier to write our lemmas *)
Local Notation hr := (sq_refl_h _).
Local Notation vr := (sq_refl_v _).
Local Notation tr := sq_tr.
Local Notation fv := sq_flip_v.

(** [PathCube]s form a path of squares up to retyping *)
Definition equiv_cu_path {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : PathSquare p0i0 p0i1 p00i p01i} {s1ii : PathSquare p1i0 p1i1 p10i p11i}
  {sii0 : PathSquare p0i0 p1i0 pi00 pi10} {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
  {si0i : PathSquare p00i p10i pi00 pi01} {si1i : PathSquare p01i p11i pi10 pi11}
  : sq_concat_h (tr (fv s0ii)) (sq_concat_h si0i (tr s1ii)) =
      sq_ccGG
        (moveL_Vp _ _ _ (sq_path^-1 sii0))
        (moveL_Vp _ _ _ (sq_path^-1 sii1)) si1i
      <~> PathCube s0ii s1ii sii0 sii1 si0i si1i.
Proof.
  srapply equiv_adjointify.
  { destruct sii0, sii1; cbn.
    rewrite (eisretr sq_G1 si0i)^,
      (eisretr sq_1G s0ii)^,
      (eisretr sq_1G s1ii)^.
    intro X.
    by destruct (sq_G1^-1 si0i), (sq_1G^-1 s0ii),
      (sq_1G^-1 s1ii), X, p00i. }
  1,2: by intros [].
  destruct sii0, sii1.
  cbn.
  rewrite <- (eisretr sq_G1 si0i).
  rewrite <- (eisretr sq_1G s0ii).
  rewrite <- (eisretr sq_1G s1ii).
  destruct (@equiv_inv _ _ sq_G1 _ si0i).
  destruct (@equiv_inv _ _ sq_1G _ s0ii).
  destruct (@equiv_inv _ _ sq_1G _ s1ii).
  destruct p00i.
  intro X.
  by destruct X.
Defined.

Notation cu_path := equiv_cu_path.

Section Reflexivity.

  (** [PathCube] reflexivity *)

  Context {A} {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}.

  (* Left right reflexivity *)
  Definition cu_refl_lr (s : PathSquare px0 px1 p0x p1x) : PathCube s s hr hr hr hr.
  Proof.
    by destruct s.
  Defined.

  (* Top bottom reflexivity *)
  Definition cu_refl_tb (s : PathSquare px0 px1 p0x p1x) : PathCube hr hr s s vr vr.
  Proof.
    by destruct s.
  Defined.

  (* Front back reflexivity *)
  Definition cu_refl_fb (s : PathSquare px0 px1 p0x p1x) : PathCube vr vr vr vr s s.
  Proof.
    by destruct s.
  Defined.

End Reflexivity.

(* Lemmas for rewriting faces of cubes *)
Section PathCubeRewriting.

  Context {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
    {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
    {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
    {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
    {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
    {s0ii : PathSquare p0i0 p0i1 p00i p01i} {s1ii : PathSquare p1i0 p1i1 p10i p11i}
    {sii0 : PathSquare p0i0 p1i0 pi00 pi10} {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
    {si0i : PathSquare p00i p10i pi00 pi01} {si1i : PathSquare p01i p11i pi10 pi11}.

  (* We write the most general version and derive special cases from this *)
  Definition equiv_cu_GGGGGG {s0ii' s1ii' sii0' sii1' si0i' si1i'}
    (t0ii : s0ii = s0ii') (t1ii : s1ii = s1ii') (tii0 : sii0 = sii0')
    (tii1 : sii1 = sii1') (ti0i : si0i = si0i') (ti1i : si1i = si1i')
    : PathCube s0ii s1ii sii0 sii1 si0i si1i
    <~> PathCube s0ii' s1ii' sii0' sii1' si0i' si1i'.
  Proof.
    by destruct t0ii, t1ii, tii0, tii1, ti0i, ti1i.
  Defined.

  Context {s0ii' s1ii' sii0' sii1' si0i' si1i'}
    (t0ii : s0ii = s0ii') (t1ii : s1ii = s1ii') (tii0 : sii0 = sii0')
    (tii1 : sii1 = sii1') (ti0i : si0i = si0i') (ti1i : si1i = si1i').

  Definition equiv_cu_Gccccc := equiv_cu_GGGGGG t0ii 1 1 1 1 1.
  Definition equiv_cu_cGcccc := equiv_cu_GGGGGG 1 t1ii 1 1 1 1.
  Definition equiv_cu_ccGccc := equiv_cu_GGGGGG 1 1 tii0 1 1 1.
  Definition equiv_cu_cccGcc := equiv_cu_GGGGGG 1 1 1 tii1 1 1.
  Definition equiv_cu_ccccGc := equiv_cu_GGGGGG 1 1 1 1 ti0i 1.
  Definition equiv_cu_cccccG := equiv_cu_GGGGGG 1 1 1 1 1 ti1i.
  Definition equiv_cu_ccGGGG := equiv_cu_GGGGGG 1 1 tii0 tii1 ti0i ti1i.
  Definition equiv_cu_GGGGcc := equiv_cu_GGGGGG t0ii t1ii tii0 tii1 1 1.
  Definition equiv_cu_GGcccc := equiv_cu_GGGGGG t0ii t1ii 1 1 1 1.
  Definition equiv_cu_ccGGcc := equiv_cu_GGGGGG 1 1 tii0 tii1 1 1.
  Definition equiv_cu_ccccGG := equiv_cu_GGGGGG 1 1 1 1 ti0i ti1i.

End PathCubeRewriting.

Notation cu_GGGGGG := equiv_cu_GGGGGG.
Notation cu_Gccccc := equiv_cu_Gccccc.
Notation cu_cGcccc := equiv_cu_cGcccc.
Notation cu_ccGccc := equiv_cu_ccGccc.
Notation cu_cccGcc := equiv_cu_cccGcc.
Notation cu_ccccGc := equiv_cu_ccccGc.
Notation cu_cccccG := equiv_cu_cccccG.
Notation cu_ccGGGG := equiv_cu_ccGGGG.
Notation cu_GGGGcc := equiv_cu_GGGGcc.
Notation cu_GGcccc := equiv_cu_GGcccc.
Notation cu_ccGGcc := equiv_cu_ccGGcc.
Notation cu_ccccGG := equiv_cu_ccccGG.

(* Rotating top and bottom to front and back *)
Definition equiv_cu_rot_tb_fb {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : PathSquare p0i0 p0i1 p00i p01i} {s1ii : PathSquare p1i0 p1i1 p10i p11i}
  {sii0 : PathSquare p0i0 p1i0 pi00 pi10} {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
  {si0i : PathSquare p00i p10i pi00 pi01} {si1i : PathSquare p01i p11i pi10 pi11}
  : PathCube si0i si1i (sq_tr s0ii) (sq_tr s1ii) (sq_tr sii0) (sq_tr sii1)
    <~> PathCube s0ii s1ii sii0 sii1 si0i si1i.
Proof.
  srapply equiv_adjointify.
  { intro cube.
    refine (cu_GGGGcc _ _ _ _ _).
    1,2,3,4: exact (eissect tr _).
    revert cube.
    set (a := tr s0ii).
    set (b := tr s1ii).
    set (c := tr sii0).
    set (d := tr sii1).
    clearbody a b c d; clear s0ii s1ii sii0 sii1.
    intro cube.
    by destruct cube. }
  1,2 : by intros [].
  rewrite <- (eissect tr s0ii).
  rewrite <- (eissect tr s1ii).
  rewrite <- (eissect tr sii0).
  rewrite <- (eissect tr sii1).
  set (a := tr s0ii).
  set (b := tr s1ii).
  set (c := tr sii0).
  set (d := tr sii1).
  clearbody a b c d; clear s0ii s1ii sii0 sii1.
  intro X.
  rewrite <- (eissect (cu_ccGGGG (eisretr tr _)
    (eisretr tr _) (eisretr tr _) (eisretr tr _)) X).
  set (e := cu_ccGGGG (eisretr tr _) (eisretr tr _)
    (eisretr tr _) (eisretr tr _) X).
  clearbody e; clear X.
  by destruct e.
Defined.

Notation cu_rot_tb_fb := equiv_cu_rot_tb_fb.

(** Degenerate cubes formed from paths between squares *)

(** The first case is easiest to prove and can be written as equivalences *)
Definition equiv_cu_G11 {A} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11}
  {p0x : a00 = a01} {p1x : a10 = a11}
  {s s' : PathSquare px0 px1 p0x p1x}
  : s = s' <~> PathCube s s' hr hr hr hr.
Proof.
  destruct s.
  refine (cu_path oE _).
  refine (equiv_concat_l (sq_concat_h_1s (sq_concat_h 1%square (tr s'))
    (p0y:=1) (p1y:=1)) _ oE _).
  refine (equiv_concat_l (sq_concat_h_1s (tr s')
    (p0y:=1) (p1y:=1)) _ oE _).
  refine (equiv_moveR_equiv_M (f:=tr) _ _ oE _).
  apply equiv_path_inverse.
Defined.

(** This case can be reduced to the first by rotating the cube
    and rewriting some faces *)
Definition equiv_cu_1G1 {A} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11}
  {p0x : a00 = a01} {p1x : a10 = a11}
  {s s' : PathSquare px0 px1 p0x p1x}
: s = s' <~> PathCube hr hr s s' vr vr.
Proof.
  refine (cu_rot_tb_fb oE _).
  refine (cu_rot_tb_fb oE _).
  refine (cu_ccGGGG _ _ _ _ oE _).
  1,2: exact sq_tr_refl_v^.
  1,2: exact (eisretr tr _)^.
  refine (_ oE equiv_ap' tr _ _).
  exact equiv_cu_G11.
Defined.

(** Finally this is an even simpler rotation *)
Definition equiv_cu_11G {A} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11}
  {p0x : a00 = a01} {p1x : a10 = a11}
  {s s' : PathSquare px0 px1 p0x p1x}
  : s = s' <~> PathCube vr vr vr vr s s'.
Proof.
  refine (cu_rot_tb_fb oE _).
  refine (cu_ccGGGG _ _ _ _ oE _).
  1-4: exact sq_tr_refl_v^.
  by exact equiv_cu_G11.
Defined.

Notation cu_G11 := equiv_cu_G11.
Notation cu_1G1 := equiv_cu_1G1.
Notation cu_11G := equiv_cu_11G.

(** Degenerate cubes given by squares *)
Section PathPathSquares.

  Context {A} {x y : A} {a00 a10 a01 a11 : x = y}
    (px0 : a00 = a10) (px1 : a01 = a11)
    (p0x : a00 = a01) (p1x : a10 = a11).

  Definition equiv_cu_GG1
    : PathSquare px0 px1 p0x p1x
      <~> PathCube (sq_G1 px0) (sq_G1 px1) (sq_G1 p0x) (sq_G1 p1x) 1 1.
  Proof.
    destruct p0x, p1x, a00.
    refine (_ oE sq_G1^-1).
    refine (_ oE equiv_ap' sq_G1 _ _).
    exact cu_G11.
  Defined.

  Definition equiv_cu_1GG
    : PathSquare px0 px1 p0x p1x
    <~> PathCube 1 1 (sq_1G px0) (sq_1G px1) (sq_1G p0x) (sq_1G p1x).
  Proof.
    destruct px0, px1, a01.
    refine(_ oE sq_1G^-1).
    refine (_ oE equiv_ap' sq_1G _ _).
    exact cu_11G.
  Defined.

  Definition equiv_cu_G1G : PathSquare px0 px1 p0x p1x
    <~> PathCube (sq_1G px0) (sq_1G px1) 1 1 (sq_G1 p0x) (sq_G1 p1x).
  Proof.
    destruct p0x, p1x, a10.
    refine(_ oE sq_G1^-1).
    refine (_ oE equiv_ap' sq_1G _ _).
    exact cu_G11.
  Defined.

End PathPathSquares.

Notation cu_GG1 := equiv_cu_GG1.
Notation cu_G1G := equiv_cu_G1G.
Notation cu_1GG := equiv_cu_1GG.
Arguments cu_GG1 {_ _ _ _ _ _ _ _ _ _ _}.
Arguments cu_G1G {_ _ _ _ _ _ _ _ _ _ _}.
Arguments cu_1GG {_ _ _ _ _ _ _ _ _ _ _}.

(** [PathCube]s can be given by [DPathSquare]s over paths *)
Definition equiv_cu_ds
  {A B} {f g : A -> B} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11}
  {p0x : a00 = a01} {p1x : a10 = a11}
  {s : PathSquare px0 px1 p0x p1x}
  {b00 : f a00 = g a00} {b01 : f a01 = g a01}
  {b10 : f a10 = g a10} {b11 : f a11 = g a11}
  {qx0 : DPath (fun x => f x = g x) px0 b00 b10}
  {qx1 : DPath (fun x => f x = g x) px1 b01 b11}
  {q0x : DPath (fun x => f x = g x) p0x b00 b01}
  {q1x : DPath (fun x => f x = g x) p1x b10 b11}
  : DPathSquare (fun x => f x = g x) s qx0 qx1 q0x q1x
    <~> PathCube (sq_dp qx0) (sq_dp qx1) (sq_dp q0x) (sq_dp q1x)
      (sq_ap f s) (sq_ap g s).
Proof.
  destruct s.
  exact cu_GG1.
Defined.

Notation cu_ds := equiv_cu_ds.

(** [PathCube]s can be given by [DPath]s over [PathSquare]s *)
Definition equiv_dp_cu {A B : Type} {x1 x2 : A} {a00 a01 a10 a11 : A -> B}
  {px0 : a00 == a10} {px1 : a01 == a11} {p0x : a00 == a01} {p1x : a10 == a11}
  {f1 : PathSquare (px0 x1) (px1 x1) (p0x x1) (p1x x1)}
  {f2 : PathSquare (px0 x2) (px1 x2) (p0x x2) (p1x x2)}
  {p : x1 = x2}
  : PathCube f1 f2 (sq_dp (apD px0 p)) (sq_dp (apD px1 p))
     (sq_dp (apD p0x p)) (sq_dp (apD p1x p))
  <~> DPath (fun x => PathSquare (px0 x) (px1 x) (p0x x) (p1x x)) p f1 f2.
Proof.
  destruct p; symmetry; exact cu_G11.
Defined.

Notation dp_cu := equiv_dp_cu.

(** Flipping a cube along the left right direction *)
Definition equiv_cu_flip_lr {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : PathSquare p0i0 p0i1 p00i p01i} {s1ii : PathSquare p1i0 p1i1 p10i p11i}
  {sii0 : PathSquare p0i0 p1i0 pi00 pi10} {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
  {si0i : PathSquare p00i p10i pi00 pi01} {si1i : PathSquare p01i p11i pi10 pi11}
  : PathCube s0ii s1ii sii0 sii1 si0i si1i
    <~> PathCube s1ii s0ii (sq_flip_h sii0) (sq_flip_h sii1)
        (sq_flip_h si0i) (sq_flip_h si1i).
Proof.
  destruct si1i, si0i.
  refine (cu_GGcccc _ _ oE _).
  1,2: exact (eisretr sq_G1 _).
  refine (cu_GG1 oE _).
  refine (sq_flip_h oE _).
  refine (cu_GG1^-1 oE _).
  refine (cu_GGGGcc _ _ _ _).
  all: exact (eisretr sq_G1 _)^.
Defined.

Notation cu_flip_lr := equiv_cu_flip_lr.

(** [PathCube] Kan fillers ~ Every open crate has a lid *)

Definition cu_fill_left {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
                                          (s1ii : PathSquare p1i0 p1i1 p10i p11i)
  (sii0 : PathSquare p0i0 p1i0 pi00 pi10) (sii1 : PathSquare p0i1 p1i1 pi01 pi11)
  (si0i : PathSquare p00i p10i pi00 pi01) (si1i : PathSquare p01i p11i pi10 pi11)
  : {s0ii : PathSquare p0i0 p0i1 p00i p01i & PathCube s0ii s1ii sii0 sii1 si0i si1i}.
Proof.
  destruct si0i, si1i.
  set (a := sq_G1^-1 s1ii).
  set (b := sq_G1^-1 sii0).
  set (c := sq_G1^-1 sii1).
  rewrite <- (eisretr sq_G1 s1ii).
  rewrite <- (eisretr sq_G1 sii0).
  rewrite <- (eisretr sq_G1 sii1).
  change (sq_G1^-1 s1ii) with a.
  change (sq_G1^-1 sii0) with b.
  change (sq_G1^-1 sii1) with c.
  clearbody a b c.
  clear s1ii sii0 sii1.
  refine (sq_G1 (b @ a @ c^); _).
  by destruct a, b, c, p0i1.
Defined.

Definition cu_fill_right {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  (s0ii : PathSquare p0i0 p0i1 p00i p01i)
  (sii0 : PathSquare p0i0 p1i0 pi00 pi10) (sii1 : PathSquare p0i1 p1i1 pi01 pi11)
  (si0i : PathSquare p00i p10i pi00 pi01) (si1i : PathSquare p01i p11i pi10 pi11)
  : {s1ii : PathSquare p1i0 p1i1 p10i p11i & PathCube s0ii s1ii sii0 sii1 si0i si1i}.
Proof.
  refine (_;_).
  apply cu_flip_lr^-1.
  apply cu_fill_left.
Defined.

Definition cu_fill_top {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  (s0ii : PathSquare p0i0 p0i1 p00i p01i) (s1ii : PathSquare p1i0 p1i1 p10i p11i)
                                          (sii1 : PathSquare p0i1 p1i1 pi01 pi11)
  (si0i : PathSquare p00i p10i pi00 pi01) (si1i : PathSquare p01i p11i pi10 pi11)
  : {sii0 : PathSquare p0i0 p1i0 pi00 pi10 & PathCube s0ii s1ii sii0 sii1 si0i si1i}.
Proof.
  refine (_;_).
  apply cu_rot_tb_fb.
  apply cu_rot_tb_fb.
  refine (cu_Gccccc (eisretr tr _)^ _).
  apply cu_fill_left.
Defined.

Definition cu_fill_bottom {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  (s0ii : PathSquare p0i0 p0i1 p00i p01i) (s1ii : PathSquare p1i0 p1i1 p10i p11i)
  (sii0 : PathSquare p0i0 p1i0 pi00 pi10)
  (si0i : PathSquare p00i p10i pi00 pi01) (si1i : PathSquare p01i p11i pi10 pi11)
  : {sii1 : PathSquare p0i1 p1i1 pi01 pi11 & PathCube s0ii s1ii sii0 sii1 si0i si1i}.
Proof.
  refine (_;_).
  apply cu_rot_tb_fb.
  apply cu_rot_tb_fb.
  refine (cu_cGcccc (eisretr tr _)^ _).
  apply cu_fill_right.
Defined.

Definition cu_fill_front {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  (s0ii : PathSquare p0i0 p0i1 p00i p01i) (s1ii : PathSquare p1i0 p1i1 p10i p11i)
  (sii0 : PathSquare p0i0 p1i0 pi00 pi10) (sii1 : PathSquare p0i1 p1i1 pi01 pi11)
                                          (si1i : PathSquare p01i p11i pi10 pi11)
  : {si0i : PathSquare p00i p10i pi00 pi01 & PathCube s0ii s1ii sii0 sii1 si0i si1i}.
Proof.
  refine (_;_).
  apply cu_rot_tb_fb.
  apply cu_fill_left.
Defined.

Definition cu_fill_back {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  (s0ii : PathSquare p0i0 p0i1 p00i p01i) (s1ii : PathSquare p1i0 p1i1 p10i p11i)
  (sii0 : PathSquare p0i0 p1i0 pi00 pi10) (sii1 : PathSquare p0i1 p1i1 pi01 pi11)
  (si0i : PathSquare p00i p10i pi00 pi01)
  : {si1i : PathSquare p01i p11i pi10 pi11 & PathCube s0ii s1ii sii0 sii1 si0i si1i}.
Proof.
  refine (_;_).
  apply cu_rot_tb_fb.
  apply cu_fill_right.
Defined.

(** [PathCube] concatenation *)

Section Concat.

  Context {A : Type}
    (* Main Cube *)
    {x000 x010 x100 x110 x001 x011 x101 x111 : A}
    {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
    {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
    {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
    {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
    {s0ii : PathSquare p0i0 p0i1 p00i p01i} {s1ii : PathSquare p1i0 p1i1 p10i p11i}
    {sii0 : PathSquare p0i0 p1i0 pi00 pi10} {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
    {si0i : PathSquare p00i p10i pi00 pi01} {si1i : PathSquare p01i p11i pi10 pi11}
    (ciii : PathCube s0ii s1ii sii0 sii1 si0i si1i).

  Definition cu_concat_lr
    {x201 x200 x210 x211 : A}
    {pj01 : x101 = x201} {pj11 : x111 = x211} {pj10 : x110 = x210}
    {pj00 : x100 = x200} {p2i1 : x201 = x211} {p2i0 : x200 = x210}
    {p20i : x200 = x201} {p21i : x210 = x211}
    {sji0 : PathSquare p1i0 p2i0 pj00 pj10} {sji1 : PathSquare p1i1 p2i1 pj01 pj11}
    {sj0i : PathSquare p10i p20i pj00 pj01} {sj1i : PathSquare p11i p21i pj10 pj11}
    {s2ii : PathSquare p2i0 p2i1 p20i p21i}
    (cjii : PathCube s1ii s2ii sji0 sji1 sj0i sj1i)
    : PathCube s0ii s2ii (sq_concat_h sii0 sji0) (sq_concat_h sii1 sji1)
        (sq_concat_h si0i sj0i) (sq_concat_h si1i sj1i).
  Proof.
    destruct cjii, pi00, pi01, pi10, pi11.
    exact ciii.
  Defined.

  Definition cu_concat_tb
    {x020 x021 x120 x121 : A}
    {p0j0 : x010 = x020} {p1j0 : x110 = x120} {p0j1 : x011 = x021}
    {p1j1 : x111 = x121} {p02i : x020 = x021} {p12i : x120 = x121}
    {pi20 : x020 = x120} {pi21 : x021 = x121}
    {s0ji : PathSquare p0j0 p0j1 p01i p02i} {s1ji : PathSquare p1j0 p1j1 p11i p12i}
    {sij0 : PathSquare p0j0 p1j0 pi10 pi20} {sij1 : PathSquare p0j1 p1j1 pi11 pi21}
    {si2i : PathSquare p02i p12i pi20 pi21}
    (ciji : PathCube s0ji s1ji sij0 sij1 si1i si2i)
    : PathCube (sq_concat_v s0ii s0ji) (sq_concat_v s1ii s1ji)
        (sq_concat_v sii0 sij0) (sq_concat_v sii1 sij1) si0i si2i.
  Proof.
    destruct ciji, p0i0, p1i0, p0i1, p1i1.
    exact ciii.
  Defined.

  Definition cu_concat_fb
    {x002 x012 x102 x112 : A}
    {p0i2 : x002 = x012} {p00j : x001 = x002} {p01j : x011 = x012}
    {p1i2 : x102 = x112} {p10j : x101 = x102} {p11j : x111 = x112}
    {pi02 : x002 = x102} {pi12 : x012 = x112}
    {s0ij : PathSquare p0i1 p0i2 p00j p01j} {s1ij : PathSquare p1i1 p1i2 p10j p11j}
    {si0j : PathSquare p00j p10j pi01 pi02} {si1j : PathSquare p01j p11j pi11 pi12}
    {sii2 : PathSquare p0i2 p1i2 pi02 pi12}
    (ciij : PathCube s0ij s1ij sii1 sii2 si0j si1j)
    : PathCube (sq_concat_h s0ii s0ij) (sq_concat_h s1ii s1ij)
        sii0 sii2 (sq_concat_v si0i si0j) (sq_concat_v si1i si1j).
  Proof.
    destruct ciij, p00i, p10i, p11i, p01i.
    exact ciii.
  Defined.

End Concat.

(* Notation for left right concatenation *)
Notation "x '@lr' y" := (cu_concat_lr x y) : cube_scope.

Local Notation apc := (ap_compose_sq _ _ _).

(** [sq_ap] analogue for [ap_compose] *)
Definition sq_ap_compose {A B C : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  (f : A -> B) (g : B -> C) (s : PathSquare px0 px1 p0x p1x)
  : PathCube (sq_ap (g o f) s) (sq_ap g (sq_ap f s)) apc apc apc apc.
Proof.
  by destruct s.
Defined.

Local Notation api := (ap_idmap_sq _).

(** [sq_ap] analogue for [ap_idmap] *)
Definition sq_ap_idmap {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  (s : PathSquare px0 px1 p0x p1x)
  : PathCube (sq_ap idmap s) s api api api api.
Proof.
  by destruct s.
Defined.

Local Notation apn := (ap_nat _ _).

(** [sq_ap] analogue for [ap_nat] *)
Definition sq_ap_nat
  {A B : Type} {a00 a10 a01 a11 : A} (f f' : A -> B) (h : f == f')
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  (s : PathSquare px0 px1 p0x p1x)
  : PathCube (sq_ap f s) (sq_ap f' s) (ap_nat h _) apn apn apn.
Proof.
  destruct s as [x]; cbn; by destruct (h x).
Defined.

(** Uncurry a function in [sq_ap2] *)
Definition sq_ap_uncurry {A B C} (f : A -> B -> C)
  {a a' : A} (p : a = a') {b b' : B} (q : b = b')
  : PathCube (sq_ap (uncurry f) (sq_prod (hr, vr))) (sq_ap011 f p q)
    (sq_G1 (ap_uncurry _ _ _)) (sq_G1 (ap_uncurry _ _ _))
    (sq_G1 (ap_uncurry _ _ _)) (sq_G1 (ap_uncurry _ _ _)).
Proof.
  by destruct p, q.
Defined.

(** [ap] for cubes *)
Definition cu_ap {A B} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : PathSquare p0i0 p0i1 p00i p01i} {s1ii : PathSquare p1i0 p1i1 p10i p11i}
  {sii0 : PathSquare p0i0 p1i0 pi00 pi10} {sii1 : PathSquare p0i1 p1i1 pi01 pi11}
  {si0i : PathSquare p00i p10i pi00 pi01} {si1i : PathSquare p01i p11i pi10 pi11}
  (f : A -> B) (c : PathCube s0ii s1ii sii0 sii1 si0i si1i)
  : PathCube (sq_ap f s0ii) (sq_ap f s1ii) (sq_ap f sii0)
     (sq_ap f sii1) (sq_ap f si0i) (sq_ap f si1i).
Proof.
  by destruct c.
Defined.
