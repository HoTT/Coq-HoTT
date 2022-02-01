Require Import Basics Types.
Require Import Homotopy.Syllepsis.

(* In this file, we prove a coherence law relating [eh_V p (q @ r)] to [eh_V p q] and [eh_V p q].  This is kept separate from Syllepsis.v because it is slow.  Improvements to the speed are welcome!  *)

(* We need this equivalence twice below. *)
Local Lemma equiv_helper {X} {a b : X} {p q r : a = b} (s : p = q) (t : q @ 1 = r) (u : p @ 1 = r)
  : whiskerR s 1 @ t = u
      <~> ((concat_p1 p)^ @ (u @ t^)) @ (concat_p1 q) = s.
Proof.
  pose (H := moveL_Mp _ _ _ (moveL_pV _ _ _ (whiskerR_p1 s))).
  snrapply (_ oE (equiv_moveL_pV _ _ _)).
  snrapply (_ oE (equiv_concat_l H _)^-1%equiv).
  snrapply (_ oE (equiv_moveL_Vp _ _ _)).
  snrapply (_ oE (equiv_moveL_pM _ _ _)).
  snrapply (equiv_path_inverse _ _).
Defined.

(* Coherence #2: We now prove that "eh_V p (q @ r)" suitably relates to "eh_V p q" and "eh_V p q". *)
Section eh_V_p_pp.

  Context {X : Type}.

  (* 0-paths *)
  Context {a b c d e f : X}.

  (* 1-paths *)
  Context {wlx0 x0 wrx0 : a = b}.
  Context {wlx1 x1 wrx1 : c = d}.
  Context {wlx2 x2 wrx2 : e = f}.

  Context {wly0 y0 wry0 : b = d}.
  Context {wly1 y1 wry1 : a = c}.

  Context {wlz0 z0 wrz0 : d = f}.
  Context {wlz1 z1 wrz1 : c = e}.

  Context {wlyz0 wryz0 : b = f}.
  Context {wlyz1 wryz1 : a = e}.

  (* 2-paths *)
  Context {ulnat_x0 : wlx0 @ 1 = 1 @ x0}.
  Context {urnat_x0 : wrx0 @ 1 = 1 @ x0}.
  Context {ulnat_x1 : wlx1 @ 1 = 1 @ x1}.
  Context {urnat_x1 : wrx1 @ 1 = 1 @ x1}.
  Context {ulnat_x2 : wlx2 @ 1 = 1 @ x2}.
  Context {urnat_x2 : wrx2 @ 1 = 1 @ x2}.

  Context {ulnat_y0 : wly0 @ 1 = 1 @ y0}.
  Context {urnat_y0 : wry0 @ 1 = 1 @ y0}.
  Context {ulnat_y1 : wly1 @ 1 = 1 @ y1}.
  Context {urnat_y1 : wry1 @ 1 = 1 @ y1}.

  Context {ulnat_z0 : wlz0 @ 1 = 1 @ z0}.
  Context {urnat_z0 : wrz0 @ 1 = 1 @ z0}.
  Context {ulnat_z1 : wlz1 @ 1 = 1 @ z1}.
  Context {urnat_z1 : wrz1 @ 1 = 1 @ z1}.

  Context {ulnat_yz0 : wlyz0 @ 1 = 1 @ (y0 @ z0)}.
  Context {urnat_yz0 : wryz0 @ 1 = 1 @ (y0 @ z0)}.
  Context {ulnat_yz1 : wlyz1 @ 1 = 1 @ (y1 @ z1)}.
  Context {urnat_yz1 : wryz1 @ 1 = 1 @ (y1 @ z1)}.

  Context {ehlnat_x0 : wlx0 @ 1 = 1 @ wrx0}.
  Context {ehlnat_x1 : wlx1 @ 1 = 1 @ wrx1}.
  Context {ehlnat_x2 : wlx2 @ 1 = 1 @ wrx2}.

  Context {ehrnat_y0 : wry0 @ 1 = 1 @ wly0}.
  Context {ehrnat_y1 : wry1 @ 1 = 1 @ wly1}.

  Context {ehrnat_z0 : wrz0 @ 1 = 1 @ wlz0}.
  Context {ehrnat_z1 : wrz1 @ 1 = 1 @ wlz1}.

  Context {ehrnat_yz0 : wryz0 @ 1 = 1 @ wlyz0}.
  Context {ehrnat_yz1 : wryz1 @ 1 = 1 @ wlyz1}.

  Context {wlrnat_x_y : wlx0 @ wry0 = wry1 @ wlx1}.
  Context {wlrnat_y_x : wly1 @ wrx1 = wrx0 @ wly0}.

  Context {wlrnat_x_z : wlx1 @ wrz0 = wrz1 @ wlx2}.
  Context {wlrnat_z_x : wlz1 @ wrx2 = wrx1 @ wlz0}.

  Context {wlrnat_x_yz : wlx0 @ wryz0 = wryz1 @ wlx2}.
  Context {wlrnat_yz_x : wlyz1 @ wrx2 = wrx0 @ wlyz0}.

  Context {wrpp_yz0 : wry0 @ wrz0 = wryz0}.
  Context {wlpp_yz0 : wly0 @ wlz0 = wlyz0}.
  Context {wrpp_yz1 : wry1 @ wrz1 = wryz1}.
  Context {wlpp_yz1 : wly1 @ wlz1 = wlyz1}.

  (* 3-paths *)
  Context {H_ulnat_yz0 :
    (ulnat_y0 [-] ulnat_z0) = whiskerR wlpp_yz0 _ @ ulnat_yz0}.

  Context {H_urnat_yz0 :
    (urnat_y0 [-] urnat_z0) = whiskerR wrpp_yz0 _ @ urnat_yz0}.

  Context {H_ulnat_yz1 :
    (ulnat_y1 [-] ulnat_z1) = whiskerR wlpp_yz1 _ @ ulnat_yz1}.

  Context {H_urnat_yz1 :
    (urnat_y1 [-] urnat_z1) = whiskerR wrpp_yz1 _ @ urnat_yz1}.

  Context {H_ehrnat_yz0 :
    (ehrnat_y0 [-] ehrnat_z0) @ whiskerL _ wlpp_yz0 =
    whiskerR wrpp_yz0 _ @ ehrnat_yz0}.

  Context {H_ehrnat_yz1 :
    (ehrnat_y1 [-] ehrnat_z1) @ whiskerL _ wlpp_yz1 =
    whiskerR wrpp_yz1 _ @ ehrnat_yz1}.

  Context {H_wlrnat_x_yz :
    (wlrnat_x_y [I] wlrnat_x_z) @ whiskerR wrpp_yz1 _ =
    whiskerL _ wrpp_yz0 @ wlrnat_x_yz}.

  Context {H_wlrnat_yz_x :
    (wlrnat_y_x [-] wlrnat_z_x) @ whiskerL _ wlpp_yz0 =
    whiskerR wlpp_yz1 _ @ wlrnat_yz_x}.

  Hypothesis ehlnat_1p_x0 :
    (ehlnat_x0 [I] urnat_x0) @ 1 = 1 @ ulnat_x0.

  Hypothesis ehlnat_1p_x1 :
    (ehlnat_x1 [I] urnat_x1) @ 1 = 1 @ ulnat_x1.

  Hypothesis ehlnat_1p_x2 :
    (ehlnat_x2 [I] urnat_x2) @ 1 = 1 @ ulnat_x2.

  Context {ehrnat_p1_y0 :
    (ehrnat_y0 [I] ulnat_y0) @ 1 = 1 @ urnat_y0}.

  Context {ehrnat_p1_y1 :
    (ehrnat_y1 [I] ulnat_y1) @ 1 = 1 @ urnat_y1}.

  Context {ehrnat_p1_z0 :
    (ehrnat_z0 [I] ulnat_z0) @ 1 = 1 @ urnat_z0}.

  Context {ehrnat_p1_z1 :
    (ehrnat_z1 [I] ulnat_z1) @ 1 = 1 @ urnat_z1}.

  Context {ehrnat_p1_yz0 :
    (ehrnat_yz0 [I] ulnat_yz0) @ 1 = 1 @ urnat_yz0}.

  Context {ehrnat_p1_yz1 :
    (ehrnat_yz1 [I] ulnat_yz1) @ 1 = 1 @ urnat_yz1}.

  Context {wlrnat_V_x_y :
    whiskerR wlrnat_x_y _ @ (ehrnat_y1 [-] ehlnat_x1) =
    (ehlnat_x0 [-] ehrnat_y0) @ whiskerL _ wlrnat_y_x^}.

  Context {wlrnat_V_x_z :
    whiskerR wlrnat_x_z _ @ (ehrnat_z1 [-] ehlnat_x2) =
    (ehlnat_x1 [-] ehrnat_z0) @ whiskerL _ wlrnat_z_x^}.

  Context {wlrnat_V_x_yz :
    whiskerR wlrnat_x_yz _ @ (ehrnat_yz1 [-] ehlnat_x2) =
    (ehlnat_x0 [-] ehrnat_yz0) @ whiskerL _ wlrnat_yz_x^}.

  (* 4-paths *)
  Hypothesis H_ehrnat_p1_yz0 :
    Ehrnat_p1_pp 1 1 H_ehrnat_yz0 H_ulnat_yz0 H_urnat_yz0
      ehrnat_p1_y0 ehrnat_p1_z0 =
    ehrnat_p1_yz0.

  Hypothesis H_ehrnat_p1_yz1 :
    Ehrnat_p1_pp 1 1 H_ehrnat_yz1 H_ulnat_yz1 H_urnat_yz1
      ehrnat_p1_y1 ehrnat_p1_z1 =
    ehrnat_p1_yz1.

  Hypothesis H_wlrnat_V_x_yz :
    Wlrnat_V_p_pp H_ehrnat_yz0 H_ehrnat_yz1 H_wlrnat_x_yz H_wlrnat_yz_x
      wlrnat_V_x_y wlrnat_V_x_z =
    wlrnat_V_x_yz.

  (* the coherence *)
  Definition eh_V_p_pp_gen :
    let eh_V_x_y := eh_V_gen (ehlnat_1p_x0) (ehlnat_1p_x1)
      (ehrnat_p1_y0) (ehrnat_p1_y1) (wlrnat_V_x_y) in
    let eh_V_x_z := eh_V_gen (ehlnat_1p_x1) (ehlnat_1p_x2)
      (ehrnat_p1_z0) (ehrnat_p1_z1) (wlrnat_V_x_z) in
    let eh_V_x_yz := eh_V_gen (ehlnat_1p_x0) (ehlnat_1p_x2)
      (ehrnat_p1_yz0) (ehrnat_p1_yz1) (wlrnat_V_x_yz) in
    whiskerR (concat_p1 _ @@ concat_p1 _) _ @ whiskerR eh_V_x_yz _ @ lrucancel 1 @
    whiskerL _ (Syllepsis.concat_pp_p_p_pp _ _ _)^ @ whiskerL _ (concat_p1 _ @@ concat_p1 _)^ =
    (eh_p_pp_gen H_urnat_yz0 H_urnat_yz1 H_wlrnat_x_yz [-]
     lrucancel (whiskerL _ (ap (fun p => whiskerL y1 p) (moveL_V1 _ _ eh_V_x_z)))) [-]
    (eh_pp_p_gen H_ulnat_yz1 H_ulnat_yz0 H_wlrnat_yz_x [-]
     lrucancel (whiskerL _ (ap (fun p => whiskerR p z0) (moveL_1V _ _ eh_V_x_y)))).
  Proof.
    destruct H_ehrnat_p1_yz0, H_ehrnat_p1_yz1, H_wlrnat_V_x_yz.
    clear H_ehrnat_p1_yz0 H_ehrnat_p1_yz1 H_wlrnat_V_x_yz.

    revert H_wlrnat_x_yz H_ulnat_yz0 H_ulnat_yz1 H_urnat_yz0 H_urnat_yz1.
    revert wlrnat_x_y wlrnat_V_x_y.
    snrapply (equiv_path_ind _ _ _ (fun _ => (equiv_helper _ _ _)^-1%equiv)).
    revert wlrnat_x_z wlrnat_V_x_z.
    snrapply (equiv_path_ind _ _ _ (fun _ => (equiv_helper _ _ _)^-1%equiv)).

    revert ulnat_x0 ehlnat_1p_x0.
    snrapply equiv_path_ind_rlucancel.
    revert ulnat_x1 ehlnat_1p_x1.
    snrapply equiv_path_ind_rlucancel.
    revert ulnat_x2 ehlnat_1p_x2.
    snrapply equiv_path_ind_rlucancel.

    revert urnat_y0 ehrnat_p1_y0.
    snrapply equiv_path_ind_rlucancel.
    revert urnat_y1 ehrnat_p1_y1.
    snrapply equiv_path_ind_rlucancel.
    revert urnat_z0 ehrnat_p1_z0.
    snrapply equiv_path_ind_rlucancel.
    revert urnat_z1 ehrnat_p1_z1.
    snrapply equiv_path_ind_rlucancel.
    revert wlrnat_x_yz.
    snrapply equiv_path_ind_moveR_Vp_inv.
    revert wlrnat_yz_x H_wlrnat_yz_x.
    snrapply equiv_path_ind_moveR_Vp_inv.
    revert ehrnat_yz0 H_ehrnat_yz0.
    snrapply equiv_path_ind_moveR_Vp_inv.
    revert ehrnat_yz1 H_ehrnat_yz1.
    snrapply equiv_path_ind_moveR_Vp_inv.

    revert ulnat_yz0.
    snrapply equiv_path_ind_moveR_Vp_inv.
    revert ulnat_yz1.
    snrapply equiv_path_ind_moveR_Vp_inv.
    revert urnat_yz0.
    snrapply equiv_path_ind_moveR_Vp_inv.
    revert urnat_yz1.
    snrapply equiv_path_ind_moveR_Vp_inv.

    destruct wrpp_yz0, wlpp_yz0, wrpp_yz1, wlpp_yz1.
    clear wrpp_yz0 wlpp_yz0 wrpp_yz1 wlpp_yz1.

    revert x0 urnat_x0.
    snrapply equiv_path_ind_rlucancel.
    revert x1 urnat_x1.
    snrapply equiv_path_ind_rlucancel.
    revert x2 urnat_x2.
    snrapply equiv_path_ind_rlucancel.
    revert y0 ulnat_y0.
    snrapply equiv_path_ind_rlucancel.
    revert y1 ulnat_y1.
    snrapply equiv_path_ind_rlucancel.
    revert z0 ulnat_z0.
    snrapply equiv_path_ind_rlucancel.
    revert z1 ulnat_z1.
    snrapply equiv_path_ind_rlucancel.

    revert wlrnat_y_x wlrnat_z_x.

    revert wrx0 ehlnat_x0.
    snrapply equiv_path_ind_rlucancel.
    revert wrx1 ehlnat_x1.
    snrapply equiv_path_ind_rlucancel.
    revert wrx2 ehlnat_x2.
    snrapply equiv_path_ind_rlucancel.
    revert wly0 ehrnat_y0.
    snrapply equiv_path_ind_rlucancel.
    revert wly1 ehrnat_y1.
    snrapply equiv_path_ind_rlucancel.
    revert wlz0 ehrnat_z0.
    snrapply equiv_path_ind_rlucancel.
    revert wlz1 ehrnat_z1.
    snrapply equiv_path_ind_rlucancel.

    destruct wry0, wry1, wrz0, wrz1.
    clear wry0 wry1 wrz0 wrz1.
    revert wlx0.
    snrapply equiv_path_ind_lrucancel.
    revert wlx1.
    snrapply equiv_path_ind_lrucancel.
    destruct wlx2.
    clear wlx2.
    reflexivity.
  Qed.

End eh_V_p_pp.

Definition eh_V_p_pp {X} {a : X} (p q r : idpath (idpath a) = idpath (idpath a)) :
  whiskerR (concat_p1 _ @@ concat_p1 _) _ @ whiskerR (eh_V p (q @ r)) _ @ lrucancel 1 @
  whiskerL _ (Syllepsis.concat_pp_p_p_pp _ _ _)^ @ whiskerL _ (concat_p1 _ @@ concat_p1 _)^ =
  (eh_p_pp_gen (urnat_pp q r) (urnat_pp q r) (wlrnat_p_pp p q r) [-]
   lrucancel (whiskerL _ (ap (fun p => whiskerL q p) (moveL_V1 _ _ (eh_V p r))))) [-]
  (eh_pp_p_gen (ulnat_pp q r) (ulnat_pp q r) (wlrnat_pp_p q r p) [-]
   lrucancel (whiskerL _ (ap (fun p => whiskerR p r) (moveL_1V _ _ (eh_V p q))))).
Proof.
  rapply eh_V_p_pp_gen.
  - exact (ehrnat_p1_pp q r).
  - exact (ehrnat_p1_pp q r).
  - exact (wlrnat_V_p_pp p q r).
Defined.

