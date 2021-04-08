Require Import HoTT.Basics HoTT.Types.
Require Import HoTT.Cubical.
Require Import HoTT.Spaces.Circle HoTT.Spaces.Torus.Torus.

(* In this file we:
    - Prove that the Torus is equivalent to the product of two circles
 *)
Section TorusEquivCircle.

  (* We use function extensionality when defining the
     map from circles to torus *)
  Context `{Funext}.

  (* Here is a cube filler for help with circle recursion into the torus *)
  Definition c2t_square_and_cube
    : {s : PathSquare loop_a loop_a
        (ap (Circle_rec _ tbase loop_b) loop)
        (ap (Circle_rec _ tbase loop_b) loop)
      &  PathCube s surf hr hr
         (sq_G1 (Circle_rec_beta_loop _ _ _))
         (sq_G1 (Circle_rec_beta_loop _ _ _))}.
  Proof.
    apply cu_fill_left.
  Defined.

  (* We define the map from the Torus to the Circles *)
  Definition t2c : Torus -> Circle * Circle.
  Proof.
    srapply Torus_rec.
    + exact (base, base). (* The point of the torus is taken to (base, base *)
    + exact (path_prod' loop 1). (* loop_a is taken to loop in the first *)
    + exact (path_prod' 1 loop). (* loop_b is taken to loop in the second *)
    + exact (sq_prod (hr, vr)). (* The square is the obvious product of squares *)
  Defined.

  (* We now define the curried function from the circles to the torus *)
  Definition c2t' : Circle -> Circle -> Torus.
  Proof.
    srapply Circle_rec.
    + srapply Circle_rec.     (* Double circle recursion *)
      - exact tbase.      (* The basepoint is sent to the point of the torus *)
      - exact loop_b.     (* The second loop is sent to loop_b *)
    + apply path_forall.  (* We use function extensionality here to induct *)
      srapply Circle_ind_dp.  (* Circle induction as a DPath *)
      - exact loop_a.     (* The first loop is sent to loop_a *)
      - srapply sq_dp^-1. (* This DPath is actually a square *)
        apply (pr1 c2t_square_and_cube). (* We apply the cap we found above *)
  Defined.

  (* Here is the uncurried version *)
  Definition c2t : Circle * Circle -> Torus.
  Proof.
    apply uncurry, c2t'.
  Defined.

  (* Computation rules for c2t' as a cube filler *)
  Definition c2t'_beta :
    {bl1 : PathSquare (ap (fun y => c2t' base y) loop) loop_b 1 1 &
    {bl2 : PathSquare (ap (fun x => c2t' x base) loop) loop_a 1 1 &
    PathCube (sq_ap011 c2t' loop loop) surf bl2 bl2 bl1 bl1}}.
  Proof.
    refine (_;_;_).
    unfold sq_ap011.
    (* 1. Unfusing ap *)
    refine (cu_concat_lr (cu_ds (dp_apD_nat
      (fun y => ap_compose _ (fun f => f y) _) _)) _
      (sji0:=?[X1]) (sji1:=?X1) (sj0i:=?[Y1]) (sj1i:=?Y1) (pj11:=1)).
    (* 2. Reducing c2t' on loop *)
    refine (cu_concat_lr (cu_ds (dp_apD_nat
      (fun x => ap_apply_l _ _ @ apD10 (ap _(Circle_rec_beta_loop _ _ _)) x) _)) _
      (sji0:=?[X2]) (sji1:=?X2) (sj0i:=?[Y2]) (sj1i:=?Y2) (pj11:=1)).
    (* 3. Reducing ap10 on function extensionality *)
    refine (cu_concat_lr (cu_ds (dp_apD_nat (ap10_path_forall _ _ _) _)) _
      (sji0:=?[X3]) (sji1:=?X3) (sj0i:=?[Y3]) (sj1i:=?Y3) (pj11:=1)).
    (* 4. Reducing Circle_ind_dp on loop *)
    refine (cu_concat_lr (cu_G11 (ap _ (Circle_ind_dp_beta_loop _ _ _))) _
      (sji0:=?[X4]) (sji1:=?X4) (sj0i:=?[Y4]) (sj1i:=?Y4) (pj11:=1)).
    (* 5. collapsing equivalence *)
    refine (cu_concat_lr (cu_G11 (eisretr _ _)) _
      (sji0:=?[X5]) (sji1:=?X5) (sj0i:=?[Y5]) (sj1i:=?Y5) (pj11:=1)).
    (* 6. filling the cube *)
    apply c2t_square_and_cube.2.
  Defined.

  Local Open Scope path_scope.
  Local Open Scope cube_scope.

  (* We now prove that t2c is a section of c2t *)
  Definition t2c2t : c2t o t2c == idmap.
  Proof.
    (* We start with Torus induction *)
    refine (Torus_ind _ 1 _ _ _).
    (* Our DPathSquare is really just a cube *)
    apply cu_ds^-1.
    (* We pretend that our sides have sq_dpath o sq_dpath^-1
      and get rid of them *)
    refine (cu_GGGGcc (eisretr _ _)^ (eisretr _ _)^
      (eisretr _ _)^ (eisretr _ _)^ _).
    (* Apply a symmetry to get the faces on the right side *)
    apply cu_rot_tb_fb.
    (* Clean up other faces *)
    refine (cu_ccGGGG (eisretr _ _)^ (eisretr _ _)^
      (eisretr _ _)^ (eisretr _ _)^ _).
    (* Now we finish the proof with the following composition of cubes *)
    refine ((sq_ap_compose t2c c2t surf)
      @lr (cu_ap c2t (Torus_rec_beta_surf _ _ _ _ _ ))
      @lr (sq_ap_uncurry _ _ _)
      @lr (pr2 (pr2 c2t'_beta))
      @lr (cu_flip_lr (sq_ap_idmap _))).
  Defined.

  (* NOTE: The last step in the previous proof can be done as a sequence of
     refines however coq really struggles to unify this. Below is the original
     way we proved the last statement before making it short and sweet. As can
     be seen, we need to give refine hints using existential variables which is
     tedious to write out, and perhaps motivates why we wrote it as one big
     concatenation. Ideally the way below should be as smooth as the way above,
     since above is difficult to write directly without having tried below.

    (* Now we decompose the cube with middle sq_ap_compose *)
    (* Note: coq sucks at unifying this so we have to explicitly give paths *)
    refine (cu_concat_lr (sq_ap_compose t2c c2t surf) _
      (sji0:=?[X1]) (sji1:=?X1) (sj0i:=?[Y1]) (sj1i:=?Y1) (pj11:=1)).
    (* Now we reduce (sq_ap t2c surf) *)
    refine (cu_concat_lr (cu_ap c2t (Torus_rec_beta_surf _ _ _ _ _ )) _
      (sji0:=?[X2]) (sji1:=?X2) (sj0i:=?[Y2]) (sj1i:=?Y2) (pj11:=1)).
    (* We now uncurry c2t inside sq_ap *)
    refine (cu_concat_lr (sq_ap_uncurry _ _ _) _
      (sji0:=?[X3]) (sji1:=?X3) (sj0i:=?[Y3]) (sj1i:=?Y3) (pj11:=1)).
    (* Reduce sq_ap2 c2t' loop loop *)
    refine (cu_concat_lr (pr2 (pr2 c2t'_beta)) _
      (sji0:=?[X4]) (sji1:=?X4) (sj0i:=?[Y4]) (sj1i:=?Y4) (pj11:=1)).
    (* Finally flip and sq_ap idmap *)
    refine (cu_flip_lr (sq_ap_idmap _)).

  *)

  Local Notation apcs := (ap_compose_sq _ _ _).

  Definition sq_ap011_compose {A B C D : Type} (f : A -> B -> C) (g : C -> D)
    {a a' : A} (p : a = a') {b b' : B} (q : b = b')
    : PathCube (sq_ap011 (fun x y => g (f x y)) p q) (sq_ap g (sq_ap011 f p q))
        apcs apcs apcs apcs.
  Proof.
    by destruct p, q.
  Defined.

  (* We now prove t2c is a retraction of c2t *)
  Definition c2t2c : t2c o c2t == idmap.
  Proof.
    rapply prod_ind.
    (* Start with double circle induction *)
    srefine (Circle_ind_dp _ (Circle_ind_dp _ 1 _) _).
    (* Change the second loop case into a square and shelve *)
    1: apply sq_dp^-1, sq_tr^-1; shelve.
    (* Take the forall out of the DPath *)
    apply dp_forall_domain.
    intro x; apply sq_dp^-1; revert x.
    srefine (Circle_ind_dp _ _ _).
    1: apply sq_tr^-1; shelve.
    apply dp_cu.
    refine (cu_ccGGcc _ _ _).
    1,2: refine (ap sq_dp (Circle_ind_dp_beta_loop _ _ _)
      @ eisretr _ _)^.
    apply cu_rot_tb_fb.
    refine (cu_ccGGGG _ _ _ _ _).
    1,2,3,4: exact (eisretr _ _)^.
    refine((sq_ap011_compose c2t' t2c loop loop)
      @lr (cu_ap t2c (c2t'_beta.2.2))
      @lr (Torus_rec_beta_surf _ _ _ _ _)
      @lr (cu_flip_lr (sq_ap_idmap _))
      @lr (sq_ap_uncurry _ _ _)).
  Defined.

(* refine (cu_concat_lr (sq_ap2_compose c2t' t2c loop loop) _
      (sji0:=?[X1]) (sji1:=?X1) (sj0i:=?[Y1]) (sj1i:=?Y1) (pj11:=1)).
    refine (cu_concat_lr (cu_ap t2c (c2t'_beta.2.2)) _
      (sji0:=?[X2]) (sji1:=?X2) (sj0i:=?[Y2]) (sj1i:=?Y2) (pj11:=1)).
    refine (cu_concat_lr (Torus_rec_beta_surf _ _ _ _ _) _
      (sji0:=?[X3]) (sji1:=?X3) (sj0i:=?[Y3]) (sj1i:=?Y3) (pj11:=1)).
    refine (cu_concat_lr (cu_flip_lr (sq_ap_idmap _)) _
      (sji0:=?[X4]) (sji1:=?X4) (sj0i:=?[Y4]) (sj1i:=?Y4) (pj11:=1)).
    apply sq_ap_uncurry. *)

  Definition equiv_torus_prod_Circle : Torus <~> Circle * Circle
    := equiv_adjointify t2c c2t c2t2c t2c2t.

End TorusEquivCircle.
