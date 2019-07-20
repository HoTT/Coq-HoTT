Require Import Basics.
Require Import DPath.
Require Import Square.
Require Import DSquare.
Require Import Types.Paths.

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

(* Homogeneous cubes *)
(* Cube left right top bottom front back *)
Cumulative Inductive Cube {A}
  : forall x000 {x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  (s0ii : Square p0i0 p0i1 p00i p01i) (s1ii : Square p1i0 p1i1 p10i p11i)
  (sii0 : Square p0i0 p1i0 pi00 pi10) (sii1 : Square p0i1 p1i1 pi01 pi11)
  (si0i : Square p00i p10i pi00 pi01) (si1i : Square p01i p11i pi10 pi11), Type
  := idcube : forall x, Cube x 1 1 1 1 1 1.

Arguments Cube {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

Scheme Cube_ind := Induction for Cube Sort Type.
Arguments Cube_ind {A} P f
  {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

Scheme Cube_rec := Minimality for Cube Sort Type.
Arguments Cube_rec {A} P f
  {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

(* These notations make it easier to write our lemmas *)
Local Notation hr := (sq_refl_h _).
Local Notation vr := (sq_refl_v _).
Local Notation tr := sq_tr.
Local Notation fv := sq_flip_v.

(* Cubes form a path of squares up to retyping *)
Definition cu_path {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  (s0ii : Square p0i0 p0i1 p00i p01i) (s1ii : Square p1i0 p1i1 p10i p11i)
  (sii0 : Square p0i0 p1i0 pi00 pi10) (sii1 : Square p0i1 p1i1 pi01 pi11)
  (si0i : Square p00i p10i pi00 pi01) (si1i : Square p01i p11i pi10 pi11)
  : (tr (fv s0ii)) @h (si0i @h (tr s1ii)) =
      sq_ccGG
        (moveL_Vp _ _ _ (sq_path^-1 sii0))
        (moveL_Vp _ _ _ (sq_path^-1 sii1)) si1i
      -> Cube s0ii s1ii sii0 sii1 si0i si1i.
Proof.
  destruct sii0, sii1.
  cbn.
  rewrite (eisretr sq_G1 si0i)^,
    (eisretr sq_1G s0ii)^,
    (eisretr sq_1G s1ii)^.
  intro X.
  by destruct (sq_G1^-1 si0i), (sq_1G^-1 s0ii),
    (sq_1G^-1 s1ii), X, p00i.
Defined.

(* This is an equivalence, albeit a slow one *)
(* TODO: speed this up *)
Global Instance isequiv_cu_path {A}
  {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : Square p0i0 p0i1 p00i p01i} {s1ii : Square p1i0 p1i1 p10i p11i}
  {sii0 : Square p0i0 p1i0 pi00 pi10} {sii1 : Square p0i1 p1i1 pi01 pi11}
  {si0i : Square p00i p10i pi00 pi01} {si1i : Square p01i p11i pi10 pi11}
  : IsEquiv (cu_path s0ii s1ii sii0 sii1 si0i si1i).
Proof.
  serapply isequiv_adjointify.
  1,2: by intros [].
  destruct sii0, sii1.
  cbn.
  rewrite (eisretr sq_G1 si0i)^,
    (eisretr sq_1G s0ii)^,
    (eisretr sq_1G s1ii)^.
  intro X.
  by destruct (sq_G1^-1 si0i), (sq_1G^-1 s0ii),
    (sq_1G^-1 s1ii), X, p00i.
Defined.

Arguments cu_path {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

Section Reflexivity.

  (* Cube reflexivity *)

  Context {A} {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}.

  (* Left right reflexivity *)
  Definition cu_refl_lr (s : Square px0 px1 p0x p1x) : Cube s s hr hr hr hr.
  Proof.
    by destruct s.
  Defined.

  (* Top bottom reflexivity *)
  Definition cu_refl_tb (s : Square px0 px1 p0x p1x) : Cube hr hr s s vr vr.
  Proof.
    by destruct s.
  Defined.

  (* Front back reflexivity *)
  Definition cu_refl_fb (s : Square px0 px1 p0x p1x) : Cube vr vr vr vr s s.
  Proof.
    by destruct s.
  Defined.

End Reflexivity.

(* Lemmas for rewriting faces of cubes *)
Section CubeRewriting.

  Context {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
    {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
    {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
    {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
    {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
    {s0ii : Square p0i0 p0i1 p00i p01i} {s1ii : Square p1i0 p1i1 p10i p11i}
    {sii0 : Square p0i0 p1i0 pi00 pi10} {sii1 : Square p0i1 p1i1 pi01 pi11}
    {si0i : Square p00i p10i pi00 pi01} {si1i : Square p01i p11i pi10 pi11}.

  (* We write the most general version and derive special cases from this *)
  Definition cu_GGGGGG {s0ii' s1ii' sii0' sii1' si0i' si1i'}
    (t0ii : s0ii = s0ii') (t1ii : s1ii = s1ii') (tii0 : sii0 = sii0')
    (tii1 : sii1 = sii1') (ti0i : si0i = si0i') (ti1i : si1i = si1i')
    : Cube s0ii s1ii sii0 sii1 si0i si1i
    -> Cube s0ii' s1ii' sii0' sii1' si0i' si1i'.
  Proof.
    by destruct t0ii, t1ii, tii0, tii1, ti0i, ti1i.
  Defined.

  Global Instance isequiv_cu_GGGGGG {s0ii' s1ii' sii0' sii1' si0i' si1i'}
    (t0ii : s0ii = s0ii') (t1ii : s1ii = s1ii') (tii0 : sii0 = sii0')
    (tii1 : sii1 = sii1') (ti0i : si0i = si0i') (ti1i : si1i = si1i')
    : IsEquiv (cu_GGGGGG t0ii t1ii tii0 tii1 ti0i ti1i).
  Proof.
    destruct t0ii, t1ii, tii0, tii1, ti0i, ti1i; exact _.
  Defined.

  Context {s0ii' s1ii' sii0' sii1' si0i' si1i'}
    (t0ii : s0ii = s0ii') (t1ii : s1ii = s1ii') (tii0 : sii0 = sii0')
    (tii1 : sii1 = sii1') (ti0i : si0i = si0i') (ti1i : si1i = si1i').

  Definition cu_Gccccc := cu_GGGGGG t0ii 1 1 1 1 1.
  Definition cu_cGcccc := cu_GGGGGG 1 t1ii 1 1 1 1.
  Definition cu_ccGccc := cu_GGGGGG 1 1 tii0 1 1 1.
  Definition cu_cccGcc := cu_GGGGGG 1 1 1 tii1 1 1.
  Definition cu_ccccGc := cu_GGGGGG 1 1 1 1 ti0i 1.
  Definition cu_cccccG := cu_GGGGGG 1 1 1 1 1 ti1i.
  Definition cu_ccGGGG := cu_GGGGGG 1 1 tii0 tii1 ti0i ti1i.
  Definition cu_GGGGcc := cu_GGGGGG t0ii t1ii tii0 tii1 1 1.
  Definition cu_GGcccc := cu_GGGGGG t0ii t1ii 1 1 1 1.
  Definition cu_ccGGcc := cu_GGGGGG 1 1 tii0 tii1 1 1.
  Definition cu_ccccGG := cu_GGGGGG 1 1 1 1 ti0i ti1i.

End CubeRewriting.

(* Rotating top and bottom to front and back *)
Definition cu_rot_tb_fb {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  (s0ii : Square p0i0 p0i1 p00i p01i) (s1ii : Square p1i0 p1i1 p10i p11i)
  (sii0 : Square p0i0 p1i0 pi00 pi10) (sii1 : Square p0i1 p1i1 pi01 pi11)
  (si0i : Square p00i p10i pi00 pi01) (si1i : Square p01i p11i pi10 pi11)
  : Cube si0i si1i (sq_tr s0ii) (sq_tr s1ii) (sq_tr sii0) (sq_tr sii1)
   -> Cube s0ii s1ii sii0 sii1 si0i si1i.
Proof.
  intro cube.
  refine (cu_GGGGcc _ _ _ _ _).
  1,2,3,4: exact (eissect tr _).
  revert cube.
  set (a := tr s0ii).
  set (b := tr s1ii).
  set (c := tr sii0).
  set (d := tr sii1).
  clearbody a b c d; clear s0ii s1ii sii0 sii1.
  intro cube.
  by destruct cube.
Defined.

Global Instance isequiv_cu_rot_tb_fb
  {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : Square p0i0 p0i1 p00i p01i} {s1ii : Square p1i0 p1i1 p10i p11i}
  {sii0 : Square p0i0 p1i0 pi00 pi10} {sii1 : Square p0i1 p1i1 pi01 pi11}
  {si0i : Square p00i p10i pi00 pi01} {si1i : Square p01i p11i pi10 pi11}
  : IsEquiv (cu_rot_tb_fb s0ii s1ii sii0 sii1 si0i si1i).
Proof.
  serapply isequiv_adjointify.
  1,2 : by intros [].
  unfold Sect.
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

Arguments cu_rot_tb_fb {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

Section CubesFromPaths.

  (* Degnerate cubes formed from paths between squares *)

  (* The first case is easiest to prove and can be written as equivalences *)
  Definition cu_G11 {A} {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}
    (s s' : Square px0 px1 p0x p1x)
    : s = s' -> Cube s s' hr hr hr hr.
  Proof.
    destruct s; intro.
    apply cu_path.
    refine (equiv_concat_l (sq_concat_h_1s (1%square @h (tr s'))
      (p0y:=1) (p1y:=1)) _ _).
    refine (equiv_concat_l (sq_concat_h_1s (tr s')
      (p0y:=1) (p1y:=1)) _ _).
    cbn; apply equiv_moveR_equiv_M.
    by symmetry.
  Defined.

  (* This makes proving it is an equivalence very easy *)
  Global Instance isequiv_cu_G11 {A} {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}
    {s s' : Square px0 px1 p0x p1x}
  : IsEquiv (cu_G11 s s').
  Proof.
    destruct s; exact _.
  Defined.

  (* This case can be reduced to the first by rotating the cube
     and rewriting some faces *)
  Definition cu_1G1 {A} {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}
    (s s' : Square px0 px1 p0x p1x)
  : s = s' -> Cube hr hr s s' vr vr.
  Proof.
    intro p.
    apply cu_rot_tb_fb.
    apply cu_rot_tb_fb.
    apply (ap tr) in p.
    refine (cu_ccGGGG _ _ _ _ _).
    1,2: exact sq_tr_refl_v^.
    1,2: exact (eisretr tr _)^.
    by apply cu_G11.
  Defined.

  (* This is automatically an equivalence *)
  Global Instance isequiv_cu_1G1 {A} {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}
    (s s' : Square px0 px1 p0x p1x)
  : IsEquiv (cu_1G1 s s') := _.

  (* Finally this is an even simpler rotation *)
  Definition cu_11G {A} {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}
    (s s' : Square px0 px1 p0x p1x)
    : s = s' -> Cube vr vr vr vr s s'.
  Proof.
    intro p.
    apply cu_rot_tb_fb.
    refine (cu_ccGGGG _ _ _ _ _).
    1,2,3,4: exact sq_tr_refl_v^.
    by apply cu_G11.
  Defined.

  (* Which is also automatically an equivalence *)
  Global Instance isequiv_cu_11G {A} {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}
    (s s' : Square px0 px1 p0x p1x)
  : IsEquiv (cu_11G s s') := _.

End CubesFromPaths.

Arguments cu_G11 {_ _ _ _ _ _ _ _ _ _ _}.
Arguments cu_1G1 {_ _ _ _ _ _ _ _ _ _ _}.
Arguments cu_11G {_ _ _ _ _ _ _ _ _ _ _}.

(* Degnerate cubes given by squares *)
Section PathSquares.

  Section PathSquaresMaps.

    Context {A} {x y : A} {a00 a10 a01 a11 : x = y}
      (px0 : a00 = a10) (px1 : a01 = a11)
      (p0x : a00 = a01) (p1x : a10 = a11).

    Definition cu_GG1 : Square px0 px1 p0x p1x
      -> Cube (sq_G1 px0) (sq_G1 px1) (sq_G1 p0x) (sq_G1 p1x) 1 1.
    Proof.
      destruct p0x, p1x, a10.
      intro.
      refine (cu_G11 _).
      refine (equiv_ap _ _ _ _).
      by apply sq_G1^-1.
    Defined.

    Definition cu_1GG : Square px0 px1 p0x p1x
      -> Cube 1 1 (sq_1G px0) (sq_1G px1) (sq_1G p0x) (sq_1G p1x).
    Proof.
      destruct px0, px1, a01.
      intro.
      refine (cu_11G _).
      refine (equiv_ap _ _ _ _).
      by apply sq_1G^-1.
    Defined.

    Definition cu_G1G : Square px0 px1 p0x p1x
      -> Cube (sq_1G px0) (sq_1G px1) 1 1 (sq_G1 p0x) (sq_G1 p1x).
    Proof.
      destruct p0x, p1x, a10.
      intro.
      refine (cu_G11 _).
      refine (equiv_ap _ _ _ _).
      by apply sq_G1^-1.
    Defined.

  End PathSquaresMaps.

  Context {A} {x y : A} {a00 a10 a01 a11 : x = y}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}.

  Global Instance isequiv_cu_GG1
    : IsEquiv (cu_GG1 px0 px1 p0x p1x).
  Proof.
    destruct p0x, p1x, a10; exact _.
  Defined.

  Global Instance isequiv_cu_1GG
    : IsEquiv (cu_1GG px0 px1 p0x p1x).
  Proof.
    destruct px0, px1, a01; exact _.
  Defined.

  Global Instance isequiv_cu_G1G
    : IsEquiv (cu_GG1 px0 px1 p0x p1x).
  Proof.
    destruct p0x, p1x, a10; exact _.
  Defined.

End PathSquares.

Arguments cu_GG1 {_ _ _ _ _ _ _ _ _ _ _}.
Arguments cu_G1G {_ _ _ _ _ _ _ _ _ _ _}.
Arguments cu_1GG {_ _ _ _ _ _ _ _ _ _ _}.

Section CubeDSquare.

  Context {A B} {f g : A -> B} {a00 a10 a01 a11 : A}
    {px0 : a00 = a10} {px1 : a01 = a11}
    {p0x : a00 = a01} {p1x : a10 = a11}.

  (* Cubes can be given by DSquares over Paths*)
  Definition cu_ds (s : Square px0 px1 p0x p1x)
    {b00 : f a00 = g a00} {b01 : f a01 = g a01}
    {b10 : f a10 = g a10} {b11 : f a11 = g a11}
    (qx0 : DPath (fun x => f x = g x) px0 b00 b10)
    (qx1 : DPath (fun x => f x = g x) px1 b01 b11)
    (q0x : DPath (fun x => f x = g x) p0x b00 b01)
    (q1x : DPath (fun x => f x = g x) p1x b10 b11)
    : DSquare (fun x => f x = g x) s qx0 qx1 q0x q1x
    -> Cube (sq_dp qx0) (sq_dp qx1) (sq_dp q0x) (sq_dp q1x)
        (sq_ap f s) (sq_ap g s).
  Proof.
    destruct s.
    apply cu_GG1.
  Defined.

  Global Instance isequiv_cu_ds {s : Square px0 px1 p0x p1x}
    {b00 : f a00 = g a00} {b01 : f a01 = g a01}
    {b10 : f a10 = g a10} {b11 : f a11 = g a11}
    {qx0 : DPath (fun x => f x = g x) px0 b00 b10}
    {qx1 : DPath (fun x => f x = g x) px1 b01 b11}
    {q0x : DPath (fun x => f x = g x) p0x b00 b01}
    {q1x : DPath (fun x => f x = g x) p1x b10 b11}
    : IsEquiv (cu_ds s qx0 qx1 q0x q1x).
  Proof.
    unfold cu_ds; destruct s; exact _.
  Defined.

End CubeDSquare.

Arguments cu_ds {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

Section CubeDPath.

  Context {A B : Type} {x1 x2 : A} {a00 a01 a10 a11 : A -> B}
    {px0 : a00 == a10} {px1 : a01 == a11} {p0x : a00 == a01} {p1x : a10 == a11}
    {f1 : Square (px0 x1) (px1 x1) (p0x x1) (p1x x1)}
    {f2 : Square (px0 x2) (px1 x2) (p0x x2) (p1x x2)}.

  (* Cubes can be given by DPaths over Squares *)
  Definition cu_dp {p : x1 = x2} 
    : Cube f1 f2 (sq_dp (dp_apD px0 p)) (sq_dp (dp_apD px1 p))
       (sq_dp (dp_apD p0x p)) (sq_dp (dp_apD p1x p))
    -> DPath (fun x => Square (px0 x) (px1 x) (p0x x) (p1x x)) p f1 f2.
  Proof.
    destruct p; apply cu_G11^-1.
  Defined.

  Global Instance isequiv_cu_dp {p : x1 = x2} : IsEquiv (cu_dp (p:=p)).
  Proof.
    unfold cu_dp.
    destruct p.
    exact _.
  Defined.

End CubeDPath.

(* Flipping a cube along the left right direction *)
Definition cu_flip_lr {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  (s0ii : Square p0i0 p0i1 p00i p01i) (s1ii : Square p1i0 p1i1 p10i p11i)
  (sii0 : Square p0i0 p1i0 pi00 pi10) (sii1 : Square p0i1 p1i1 pi01 pi11)
  (si0i : Square p00i p10i pi00 pi01) (si1i : Square p01i p11i pi10 pi11)
  : Cube s0ii s1ii sii0 sii1 si0i si1i
  -> Cube s1ii s0ii (sq_flip_h sii0) (sq_flip_h sii1)
        (sq_flip_h si0i) (sq_flip_h si1i).
Proof.
  destruct si1i, si0i.
  intro.
  refine (cu_GGGGcc _ _ _ _ _).
  1,2,3,4: exact (eisretr sq_G1 _).
  apply cu_GG1.
  apply sq_flip_h^-1.
  apply cu_GG1^-1.
  refine (cu_GGGGcc _ _ _ _ _).
  1,2: exact (eisretr sq_G1 _)^.
  1,2: by apply moveL_equiv_M, moveL_equiv_M, moveL_equiv_V.
  exact X.
Defined.

Global Instance isequiv_cu_flip_lr {A}
  {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : Square p0i0 p0i1 p00i p01i} {s1ii : Square p1i0 p1i1 p10i p11i}
  {sii0 : Square p0i0 p1i0 pi00 pi10} {sii1 : Square p0i1 p1i1 pi01 pi11}
  {si0i : Square p00i p10i pi00 pi01} {si1i : Square p01i p11i pi10 pi11}
  : IsEquiv (cu_flip_lr s0ii s1ii sii0 sii1 si0i si1i).
Proof.
  destruct si1i, si0i.
  exact _.
Defined.

Arguments cu_flip_lr {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _}.

(* Cube Kan fillers ~ Every open crate has a lid *)


Definition cu_fill_left {A} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
                                      (s1ii : Square p1i0 p1i1 p10i p11i)
  (sii0 : Square p0i0 p1i0 pi00 pi10) (sii1 : Square p0i1 p1i1 pi01 pi11)
  (si0i : Square p00i p10i pi00 pi01) (si1i : Square p01i p11i pi10 pi11)
  : {s0ii : Square p0i0 p0i1 p00i p01i & Cube s0ii s1ii sii0 sii1 si0i si1i}.
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
  (s0ii : Square p0i0 p0i1 p00i p01i)
  (sii0 : Square p0i0 p1i0 pi00 pi10) (sii1 : Square p0i1 p1i1 pi01 pi11)
  (si0i : Square p00i p10i pi00 pi01) (si1i : Square p01i p11i pi10 pi11)
  : {s1ii : Square p1i0 p1i1 p10i p11i & Cube s0ii s1ii sii0 sii1 si0i si1i}.
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
  (s0ii : Square p0i0 p0i1 p00i p01i) (s1ii : Square p1i0 p1i1 p10i p11i)
                                      (sii1 : Square p0i1 p1i1 pi01 pi11)
  (si0i : Square p00i p10i pi00 pi01) (si1i : Square p01i p11i pi10 pi11)
  : {sii0 : Square p0i0 p1i0 pi00 pi10 & Cube s0ii s1ii sii0 sii1 si0i si1i}.
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
  (s0ii : Square p0i0 p0i1 p00i p01i) (s1ii : Square p1i0 p1i1 p10i p11i)
  (sii0 : Square p0i0 p1i0 pi00 pi10)
  (si0i : Square p00i p10i pi00 pi01) (si1i : Square p01i p11i pi10 pi11)
  : {sii1 : Square p0i1 p1i1 pi01 pi11 & Cube s0ii s1ii sii0 sii1 si0i si1i}.
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
  (s0ii : Square p0i0 p0i1 p00i p01i) (s1ii : Square p1i0 p1i1 p10i p11i)
  (sii0 : Square p0i0 p1i0 pi00 pi10) (sii1 : Square p0i1 p1i1 pi01 pi11)
                                      (si1i : Square p01i p11i pi10 pi11)
  : {si0i : Square p00i p10i pi00 pi01 & Cube s0ii s1ii sii0 sii1 si0i si1i}.
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
  (s0ii : Square p0i0 p0i1 p00i p01i) (s1ii : Square p1i0 p1i1 p10i p11i)
  (sii0 : Square p0i0 p1i0 pi00 pi10) (sii1 : Square p0i1 p1i1 pi01 pi11)
  (si0i : Square p00i p10i pi00 pi01)
  : {si1i : Square p01i p11i pi10 pi11 & Cube s0ii s1ii sii0 sii1 si0i si1i}.
Proof.
  refine (_;_).
  apply cu_rot_tb_fb.
  apply cu_fill_right.
Defined.

(* Cube concatenation *)
Section CubeConcat.

  Context {A} {x000 x010 x100 x110 x001 x011 x101 x111 x201 x200 x210 x211 : A}
    {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
    {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
    {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
    {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
    {pj01 : x101 = x201} {pj11 : x111 = x211} {pj10 : x110 = x210}
    {pj00 : x100 = x200} {p2i1 : x201 = x211} {p2i0 : x200 = x210}
    {p20i : x200 = x201} {p21i : x210 = x211}
    {s0ii : Square p0i0 p0i1 p00i p01i} {s1ii : Square p1i0 p1i1 p10i p11i}
    {sii0 : Square p0i0 p1i0 pi00 pi10} {sii1 : Square p0i1 p1i1 pi01 pi11}
    {si0i : Square p00i p10i pi00 pi01} {si1i : Square p01i p11i pi10 pi11}
    {sji0 : Square p1i0 p2i0 pj00 pj10} {sji1 : Square p1i1 p2i1 pj01 pj11}
    {sj0i : Square p10i p20i pj00 pj01} {sj1i : Square p11i p21i pj10 pj11}
    {s2ii : Square p2i0 p2i1 p20i p21i}.

  (* We only define left right concatenation for now since that is what we
     need. The other concatenations will not be as nice however, due to the
     orientation of the faces of the cubes. *)

  (* TODO: Work out why this is so slow *)
  (* Left right concatenation *)
  Definition cu_concat_lr : Cube s0ii s1ii sii0 sii1 si0i si1i
    -> Cube s1ii s2ii sji0 sji1 sj0i sj1i
    -> Cube s0ii s2ii (sq_concat_h sii0 sji0) (sq_concat_h sii1 sji1)
         (sq_concat_h si0i sj0i) (sq_concat_h si1i sj1i).
  Proof.
    intros a b.
    destruct b.
    unfold sq_concat_h.
    by destruct a.
  Defined.

End CubeConcat.

(* Notation for left right concatenation *)
Notation "x '@lr' y" := (cu_concat_lr x y) (at level 10) : cube_scope.

Local Notation apc := (ap_compose_sq _ _ _).

(* sq_ap analogue for ap_compse *)
Definition sq_ap_compose {A B C : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  (f : A -> B) (g : B -> C) (s : Square px0 px1 p0x p1x)
  : Cube (sq_ap (g o f) s) (sq_ap g (sq_ap f s)) apc apc apc apc.
Proof.
  by destruct s.
Defined.

Local Notation api := (ap_idmap_sq _).

(* sq_ap analogue for ap_idmap *)
Definition sq_ap_idmap {A : Type} {a00 a10 a01 a11 : A}
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  (s : Square px0 px1 p0x p1x)
  : Cube (sq_ap idmap s) s api api api api.
Proof.
  by destruct s.
Defined.

Local Notation apn := (ap_nat _ _).

(* sq_ap analogue for ap_nat *)
Definition sq_ap_nat
  {A B : Type} {a00 a10 a01 a11 : A} (f f' : A -> B) (h : f == f')
  {px0 : a00 = a10} {px1 : a01 = a11} {p0x : a00 = a01} {p1x : a10 = a11}
  (s : Square px0 px1 p0x p1x)
  : Cube (sq_ap f s) (sq_ap f' s) (ap_nat h _) apn apn apn.
Proof.
  destruct s as [x]; cbn; by destruct (h x).
Defined.

(* Uncurry a function in sq_ap2 *)
Definition sq_ap_uncurry {A B C} (f : A -> B -> C)
  {a a' : A} (p : a = a') {b b' : B} (q : b = b')
  : Cube (sq_ap (uncurry f) (sq_prod hr vr)) (sq_ap2 f p q)
  (ap_uncurry _ _ _) (ap_uncurry _ _ _) (ap_uncurry _ _ _) (ap_uncurry _ _ _).
Proof.
  by destruct p, q.
Defined.

(* ap for cubes *)
Definition cu_ap {A B} {x000 x010 x100 x110 x001 x011 x101 x111 : A}
  {p0i0 : x000 = x010} {p1i0 : x100 = x110} {pi00 : x000 = x100}
  {pi10 : x010 = x110} {p0i1 : x001 = x011} {p1i1 : x101 = x111}
  {pi01 : x001 = x101} {pi11 : x011 = x111} {p00i : x000 = x001}
  {p01i : x010 = x011} {p10i : x100 = x101} {p11i : x110 = x111}
  {s0ii : Square p0i0 p0i1 p00i p01i} {s1ii : Square p1i0 p1i1 p10i p11i}
  {sii0 : Square p0i0 p1i0 pi00 pi10} {sii1 : Square p0i1 p1i1 pi01 pi11}
  {si0i : Square p00i p10i pi00 pi01} {si1i : Square p01i p11i pi10 pi11}
  (f : A -> B) (c : Cube s0ii s1ii sii0 sii1 si0i si1i)
  : Cube (sq_ap f s0ii) (sq_ap f s1ii) (sq_ap f sii0)
     (sq_ap f sii1) (sq_ap f si0i) (sq_ap f si1i).
Proof.
  by destruct c.
Defined.
