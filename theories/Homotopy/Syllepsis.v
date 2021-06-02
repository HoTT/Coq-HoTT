From HoTT Require Import Basics Types.

(* vertical composition of squares *)
Section concat_square_vert.

  Context {X : Type}.

  (* 0-paths *)
  Context {a0 b0 c0 : X}.
  Context {a1 b1 c1 : X}.

  (* 1-paths *)
  Context {a01 : a0 = a1}.
  Context {b01 : b0 = b1}.
  Context {c01 : c0 = c1}.

  Context {ab0 : a0 = b0}.
  Context {ab1 : a1 = b1}.

  Context {bc0 : b0 = c0}.
  Context {bc1 : b1 = c1}.

  (* 2-paths *)
  Context (p : ab0 @ b01 = a01 @ ab1).
  Context (q : bc0 @ c01 = b01 @ bc1).

  Local Definition concat_square_vert :
    (ab0 @ bc0) @ c01 = a01 @ (ab1 @ bc1).
  Proof.
    refine (concat_pp_p _ _ _ @ _).
    refine (whiskerL _ q @ _).
    refine (concat_p_pp _ _ _ @ _).
    refine (whiskerR p _ @ _).
    apply concat_pp_p.
  Defined.

End concat_square_vert.

Infix "[-]" := (concat_square_vert) (at level 60).

(* horizontal composition of squares *)
Section concat_square_hor.

  Context {X : Type}.

  (* 0-paths *)
  Context {a0 b0 c0 : X}.
  Context {a1 b1 c1 : X}.

  (* 1-paths *)
  Context {a01 : a0 = a1}.
  Context {b01 : b0 = b1}.
  Context {c01 : c0 = c1}.

  Context {ab0 : a0 = b0}.
  Context {ab1 : a1 = b1}.

  Context {bc0 : b0 = c0}.
  Context {bc1 : b1 = c1}.

  (* 2-paths *)
  Context (p : a01 @ ab1 = ab0 @ b01).
  Context (q : b01 @ bc1 = bc0 @ c01).

  Local Definition concat_square_hor :
    a01 @ (ab1 @ bc1) = (ab0 @ bc0) @ c01.
  Proof.
    refine (concat_p_pp _ _ _ @ _).
    refine (whiskerR p _ @ _).
    refine (concat_pp_p _ _ _ @ _).
    refine (whiskerL _ q @ _).
    apply concat_p_pp.
  Defined.

End concat_square_hor.

Infix "[I]" := (concat_square_hor) (at level 60).

(* We will frequently use the following equivalences. *)
Definition rlucancel {X} {a b : X} {p q : a = b} :
  (p @ 1 = 1 @ q) <~> (p = q).
Proof.
  refine (equiv_compose' _ _).
  - exact (equiv_concat_r (concat_1p _) _).
  - exact (equiv_concat_l (concat_p1 _)^ _).
Defined.

Definition lrucancel {X} {a b : X} {p q : a = b} :
  (1 @ p = q @ 1) <~> (p = q).
Proof.
  refine (equiv_compose' _ _).
  - exact (equiv_concat_r (concat_p1 _) _).
  - exact (equiv_concat_l (concat_1p _)^ _).
Defined.

(* Interaction of the above equivalences with square composition. *)
Definition rlucancel_sVs_1_pp {X} {a b c : X} {p : a = b} {q : b = c} {r} (theta : p @ q = r) :
  (rlucancel^-1 1 [-] rlucancel^-1 1) @ whiskerL _ theta = whiskerR theta _ @ (rlucancel^-1 1).
Proof.
  by induction theta, p, q.
Defined.

Definition lrucancel_sHs_1_pp {X} {a b c : X} {p : a = b} {q : b = c} {r} (theta : p @ q = r) :
  (lrucancel^-1 1 [I] lrucancel^-1 1) @ whiskerR theta _ = whiskerL _ theta @ (lrucancel^-1 1).
Proof.
  by induction theta, p, q.
Defined.

Definition rlucancel_sHs_1 {X} {a b : X} (p : a = b) :
  (rlucancel^-1 1 [I] rlucancel^-1 1) = rlucancel^-1 (idpath p).
Proof.
  by induction p.
Defined.

Definition lrucancel_sVs_1 {X} {a b : X} (p : a = b) :
  (lrucancel^-1 1 [-] lrucancel^-1 1) = lrucancel^-1 (idpath p).
Proof.
  by induction p.
Defined.

(* Naturality of composition with 1. *)
Definition ulnat {X} {a b : X} {u v : a = b} (p : u = v) :
  whiskerL 1 p @ concat_1p v = concat_1p u @ p.
Proof.
  induction p.
  exact (lrucancel^-1 1).
Defined. 

Definition urnat {X} {a b : X} {u v : a = b} (p : u = v) :
  whiskerR p 1 @ concat_p1 v = concat_p1 u @ p.
Proof.
  induction p.
  exact (lrucancel^-1 1).
Defined.

(* Exchange law for whiskering on the left and on the right. *)
Definition wlrnat {X} {a b c : X} {u v : a = b} {x y : b = c} p q :
  whiskerL u p @ whiskerR q y = whiskerR q x @ whiskerL v p.
Proof.
  by induction p, q.
Defined.

(* Eckmann-Hilton *)
Theorem eh {X} {a : X} (p q : idpath a = idpath a) :
  p @ q = q @ p.
Proof.
  refine (_ @ rlucancel (urnat q [-] ulnat p)).
  refine ((rlucancel (ulnat p [-] urnat q))^ @ _).
  exact (wlrnat p q).
Defined.

(* Eckmann-Hilton on reflexivity. *)
Local Definition eh_1p_gen {X} {a b : X} {u v : a = b} (p : u = v) {q} (theta : whiskerR p 1 @ 1 = 1 @ q) :
  (rlucancel (1 [-] theta))^ @ wlrnat 1 p @ rlucancel (theta [-] 1) @ concat_p1 q = concat_1p q.
Proof.
  revert theta.
  srapply (equiv_ind rlucancel^-1).
  intro theta.
  by induction theta, p.
Defined.

Definition eh_1p {X} {a : X} (p : idpath a = idpath a) :
  eh 1 p @ concat_p1 p = concat_1p p.
Proof.
  exact (eh_1p_gen p (urnat p)).
Defined.

Local Definition eh_p1_gen {X} {a b : X} {u v : a = b} (p : u = v) {q} (theta : whiskerL 1 p @ 1 = 1 @ q) :
  (rlucancel (theta [-] 1))^ @ wlrnat p 1 @ rlucancel (1 [-] theta) @ concat_1p q = concat_p1 q.
Proof.
  revert theta.
  srapply (equiv_ind rlucancel^-1).
  intro theta.
  by induction theta, p.
Defined.

Definition eh_p1 {X} {a : X} (p : idpath a = idpath a) :
  eh p 1 @ concat_1p p = concat_p1 p.
Proof.
  exact (eh_p1_gen p (ulnat p)).
Defined.

(* Naturality of Eckmann-Hilton. *)
Definition ehlnat {X} {a : X} (u : idpath a = idpath a) {x y} (p : x = y) :
  whiskerL u p @ eh u y = eh u x @ whiskerR p u.
Proof.
  induction p.
  exact (lrucancel^-1 1).
Defined.

Definition ehrnat {X} {a : X} {u v} (p : u = v) (x : idpath a = idpath a) :
  whiskerR p x @ eh v x = eh u x @ whiskerL x p.
Proof.
  induction p.
  exact (lrucancel^-1 1).
Defined.

(* Naturality of Eckmann-Hilton when the fixed path is 1. *)
Definition ehlnat_1p {X} {a : X} {u v : idpath a = idpath a} (p : u = v) :
  (ehlnat 1 p [I] urnat p) @ whiskerR (eh_1p u) _ = whiskerL _ (eh_1p v) @ ulnat p.
Proof.
  induction p.
  apply lrucancel_sHs_1_pp.
Defined.

Definition ehrnat_p1 {X} {a : X} {u v : idpath a = idpath a} (p : u = v) :
  (ehrnat p 1 [I] ulnat p) @ whiskerR (eh_p1 u) _ = whiskerL _ (eh_p1 v) @ urnat p.
Proof.
  induction p.
  apply lrucancel_sHs_1_pp.
Defined.

(* These lemmas should probably be in the library in some form. *)
Local Definition concat_p_pp_pp_p {A} {u v x y : A} (p : u = v) (q : v = x) (r : x = y) :
  concat_p_pp p q r @ concat_pp_p p q r = 1.
Proof.
  by induction p, q, r.
Defined.

Local Definition concat_pp_p_p_pp {A} {u v x y : A} (p : u = v) (q : v = x) (r : x = y) :
  concat_pp_p p q r @ concat_p_pp p q r = 1.
Proof.
  by induction p, q, r.
Defined.

(* These lemmas are in the library but with worse computational behavior. *)
Local Definition whiskerL_pp {A} {a b c : A} (u : a = b) {v w z : b = c} (p : v = w) (q : w = z) :
  whiskerL u (p @ q) = whiskerL u p @ whiskerL u q.
Proof.
  by destruct p, q.
Defined.

Local Definition whiskerR_pp {A} {a b c : A} {u v w : a = b} (z : b = c) (p : u = v) (q : v = w) :
  whiskerR (p @ q) z = whiskerR p z @ whiskerR q z.
Proof.
  by destruct p, q.
Defined.

(* We now prove that "ulnat (p @ q)" suitably relates to "ulnat p" and "ulnat q". *)
Definition ulnat_pp {X} {a b : X} {u v w : a = b} (p : u = v) (q : v = w) :
  ulnat p [-] ulnat q = whiskerR (whiskerL_pp _ p q)^ _ @ ulnat (p @ q).
Proof.
  by induction p, q, u.
Defined.

(* We now prove that "urnat (p @ q)" suitably relates to "urnat p" and "urnat q". *)
Definition urnat_pp {X} {a b : X} {u v w : a = b} (p : u = v) (q : v = w) :
  urnat p [-] urnat q = whiskerR (whiskerR_pp _ p q)^ _ @ urnat (p @ q).
Proof.
  by induction p, q, u.
Defined.

(* We now prove that "ehlnat u (p @ q)" suitably relates to "ehlnat u p" and "ehlnat u q". *)
Definition ehlnat_pp {X} {a : X} (u : idpath a = idpath a) {v w : idpath a = idpath a} (p : v = 1) (q : 1 = w) :
  (ehlnat u p [-] ehlnat u q) @ whiskerL _ (whiskerR_pp _ p q)^ =
  (whiskerR (whiskerL_pp _ p q)^ _) @ ehlnat u (p @ q).
Proof.
  revert p.
  srapply (equiv_ind (equiv_path_inverse _ _)).
  intro p.
  induction p, q.
  cbn.
  apply rlucancel^-1, lrucancel_sVs_1.
Defined.

(* We now prove that "ehrnat (p @ q) w" suitably relates to "ehrnat p w" and "ehrnat q w". *)
Definition ehrnat_pp {X} {a : X} {u v : idpath a = idpath a} (p : u = 1) (q : 1 = v) (w : idpath a = idpath a) :
  (ehrnat p w [-] ehrnat q w) @ whiskerL _ (whiskerL_pp _ p q)^ =
  (whiskerR (whiskerR_pp _ p q)^ _) @ ehrnat (p @ q) w.
Proof.
  revert p.
  srapply (equiv_ind (equiv_path_inverse _ _)).
  intro p.
  induction p, q.
  cbn.
  apply rlucancel^-1, lrucancel_sVs_1.
Defined.

(* We now prove that "wlrnat p (q @ r)" suitably relates to "wlrnat p q" and "wlrnat q p". *)
Definition wlrnat_p_pp {X} {a b c : X} {u v w : a = b} {x y : b = c} (p : x = y) (q : u = v) (r : v = w) :
  (wlrnat p q [I] wlrnat p r) @ whiskerR (whiskerR_pp _ q r)^ _ =
  whiskerL _ (whiskerR_pp _ q r)^ @ wlrnat p (q @ r).
Proof.
  by induction p, q, r.
Defined.

(* We now prove that "wlrnat (p @ q) r" suitably relates to "wlrnat p r" and "wlrnat q r". *)
Definition wlrnat_pp_p {X} {a b c : X} {u v : a = b} {x y z : b = c} (p : x = y) (q : y = z) (r : u = v) :
  (wlrnat p r [-] wlrnat q r) @ whiskerL _ (whiskerL_pp _ p q)^ =
  whiskerR (whiskerL_pp _ p q)^ _ @ wlrnat (p @ q) r.
Proof.
  by induction p, q, r.
Defined.

(* We now prove that "wlrnat p q" suitably relates to "wlrnat q p". *)
Definition wlrnat_V {X} {a : X} {u v x y : idpath a = idpath a} p q :
  whiskerR (wlrnat p q) (eh v y) @ (ehrnat q x [-] ehlnat v p) =
  (ehlnat u p [-] ehrnat q y) @ whiskerL (eh u x) (wlrnat q p)^.
Proof.
  induction p, q.
  exact (lrucancel^-1 1).
Defined.

(* Coherence #1: We now prove that "eh p (q @ r)" suitably relates to "eh p q" and "eh p r". *)
Section eh_p_pp.

  Context {X : Type}.

  (* 0-paths *)
  Context {a b c d e f : X}.

  (* 1-paths *)
  Context {wlx0 x0 : a = b}.
  Context {wlx1 x1 : c = d}.
  Context {wlx2 x2 : e = f}.

  Context {wry0 y0 : b = d}.
  Context {wry1 y1 : a = c}.

  Context {wrz0 z0 : d = f}.
  Context {wrz1 z1 : c = e}.

  Context {wryz0 : b = f}.
  Context {wryz1 : a = e}.

  (* 2-paths *)
  Context {ulnat_x0 : wlx0 @ 1 = 1 @ x0}.
  Context {ulnat_x1 : wlx1 @ 1 = 1 @ x1}.
  Context {ulnat_x2 : wlx2 @ 1 = 1 @ x2}.

  Context {urnat_y0 : wry0 @ 1 = 1 @ y0}.
  Context {urnat_y1 : wry1 @ 1 = 1 @ y1}.

  Context {urnat_z0 : wrz0 @ 1 = 1 @ z0}.
  Context {urnat_z1 : wrz1 @ 1 = 1 @ z1}.

  Context {urnat_yz0 : wryz0 @ 1 = 1 @ (y0 @ z0)}.
  Context {urnat_yz1 : wryz1 @ 1 = 1 @ (y1 @ z1)}.

  Context {wlrnat_x_y : wlx0 @ wry0 = wry1 @ wlx1}.
  Context {wlrnat_x_z : wlx1 @ wrz0 = wrz1 @ wlx2}.
  Context {wlrnat_x_yz : wlx0 @ wryz0 = wryz1 @ wlx2}.

  Context {wrpp_yz0 : wry0 @ wrz0 = wryz0}.
  Context {wrpp_yz1 : wry1 @ wrz1 = wryz1}.

  (* 3-paths *)
  Hypothesis H_urnat_yz0 :
    (urnat_y0 [-] urnat_z0) = whiskerR wrpp_yz0 _ @ urnat_yz0.

  Hypothesis H_urnat_yz1 :
    (urnat_y1 [-] urnat_z1) = whiskerR wrpp_yz1 _ @ urnat_yz1.

  Hypothesis H_wlrnat_x_yz :
    (wlrnat_x_y [I] wlrnat_x_z) @ whiskerR wrpp_yz1 _ =
    whiskerL _ wrpp_yz0 @ wlrnat_x_yz.

  (* the coherence *)
  Definition eh_p_pp_gen :
    let EH_x_y := (rlucancel (ulnat_x0 [-] urnat_y0))^ @
      wlrnat_x_y @ rlucancel (urnat_y1 [-] ulnat_x1) in
    let EH_x_z := (rlucancel (ulnat_x1 [-] urnat_z0))^ @
      wlrnat_x_z @ rlucancel (urnat_z1 [-] ulnat_x2) in
    let EH_x_yz := (rlucancel (ulnat_x0 [-] urnat_yz0))^ @
      wlrnat_x_yz @ rlucancel (urnat_yz1 [-] ulnat_x2) in
    EH_x_yz @ (concat_pp_p _ _ _ @ whiskerL _ EH_x_z^) =
    concat_p_pp _ _ _ @ whiskerR EH_x_y _ @ concat_pp_p _ _ _.
  Proof.
    apply moveR_Vp in H_urnat_yz0, H_urnat_yz1, H_wlrnat_x_yz.
    induction H_urnat_yz0, H_urnat_yz1, H_wlrnat_x_yz.
    clear H_urnat_yz0 H_urnat_yz1 H_wlrnat_x_yz.
    induction wrpp_yz0, wrpp_yz1.
    clear wrpp_yz0 wrpp_yz1.
    revert ulnat_x0.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_x0.
    induction ulnat_x0.
    clear ulnat_x0.
    revert ulnat_x1.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_x1.
    induction ulnat_x1.
    clear ulnat_x1.
    revert ulnat_x2.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_x2.
    induction ulnat_x2.
    clear ulnat_x2.
    revert urnat_y0.
    srapply (equiv_ind rlucancel^-1).
    intro urnat_y0.
    induction urnat_y0.
    clear urnat_y0.
    revert urnat_y1.
    srapply (equiv_ind rlucancel^-1).
    intro urnat_y1.
    induction urnat_y1.
    clear urnat_y1.
    revert urnat_z0.
    srapply (equiv_ind rlucancel^-1).
    intro urnat_z0.
    induction urnat_z0.
    clear urnat_z0.
    revert urnat_z1.
    srapply (equiv_ind rlucancel^-1).
    intro urnat_z1.
    induction urnat_z1.
    clear urnat_z1.
    induction wry0, wry1, wrz0, wrz1.
    clear wry0 wry1 wrz0 wrz1.
    revert wlrnat_x_y.
    srapply (equiv_ind rlucancel^-1).
    intro wlrnat_x_y.
    induction wlrnat_x_y.
    clear wlrnat_x_y.
    revert wlrnat_x_z.
    srapply (equiv_ind rlucancel^-1).
    intro wlrnat_x_z.
    induction wlrnat_x_z.
    clear wlrnat_x_z.
    induction wlx0.
    clear wlx0.
    reflexivity.
  Defined.

End eh_p_pp.

Theorem eh_p_pp {X} {a : X} (p q r : idpath a = idpath a) :
  eh p (q @ r) @ (concat_pp_p _ _ _ @ whiskerL _ (eh p r)^) =
  concat_p_pp _ _ _ @ whiskerR (eh p q) _ @ concat_pp_p _ _ _.
Proof.
  rapply eh_p_pp_gen.
  - exact (urnat_pp q r).
  - exact (urnat_pp q r).
  - exact (wlrnat_p_pp p q r).
Defined.

(* Coherence #1: We now prove that "eh (p @ q) r" suitably relates to "eh p r" and "eh q r". *)
Section eh_pp_p.

  Context {X : Type}.

  (* 0-paths *)
  Context {a b c d e f : X}.

  (* 1-paths *)
  Context {wlx0 x0 : a = b}.
  Context {wlx1 x1 : d = e}.

  Context {wly0 y0 : b = c}.
  Context {wly1 y1 : e = f}.

  Context {wrz0 z0 : c = f}.
  Context {wrz1 z1 : b = e}.
  Context {wrz2 z2 : a = d}.

  Context {wlxy0 : a = c}.
  Context {wlxy1 : d = f}.

  (* 2-paths *)
  Context {ulnat_x0 : wlx0 @ 1 = 1 @ x0}.
  Context {ulnat_x1 : wlx1 @ 1 = 1 @ x1}.

  Context {ulnat_y0 : wly0 @ 1 = 1 @ y0}.
  Context {ulnat_y1 : wly1 @ 1 = 1 @ y1}.

  Context {urnat_z0 : wrz0 @ 1 = 1 @ z0}.
  Context {urnat_z1 : wrz1 @ 1 = 1 @ z1}.
  Context {urnat_z2 : wrz2 @ 1 = 1 @ z2}.

  Context {ulnat_xy0 : wlxy0 @ 1 = 1 @ (x0 @ y0)}.
  Context {ulnat_xy1 : wlxy1 @ 1 = 1 @ (x1 @ y1)}.

  Context {wlrnat_x_z : wlx0 @ wrz1 = wrz2 @ wlx1}.
  Context {wlrnat_y_z : wly0 @ wrz0 = wrz1 @ wly1}.
  Context {wlrnat_xy_z : wlxy0 @ wrz0 = wrz2 @ wlxy1}.

  Context {wlpp_xy0 : wlx0 @ wly0 = wlxy0}.
  Context {wlpp_xy1 : wlx1 @ wly1 = wlxy1}.

  (* 3-paths *)
  Hypothesis H_ulnat_xy0 :
    (ulnat_x0 [-] ulnat_y0) = whiskerR wlpp_xy0 _ @ ulnat_xy0.

  Hypothesis H_ulnat_xy1 :
    (ulnat_x1 [-] ulnat_y1) = whiskerR wlpp_xy1 _ @ ulnat_xy1.

  Hypothesis H_wlrnat_xy_z :
    (wlrnat_x_z [-] wlrnat_y_z) @ whiskerL _ wlpp_xy1 =
    whiskerR wlpp_xy0 _ @ wlrnat_xy_z.

  (* the coherence *)
  Definition eh_pp_p_gen :
    let EH_x_z := (rlucancel (ulnat_x0 [-] urnat_z1))^ @
      wlrnat_x_z @ rlucancel (urnat_z2 [-] ulnat_x1) in
    let EH_y_z := (rlucancel (ulnat_y0 [-] urnat_z0))^ @
      wlrnat_y_z @ rlucancel (urnat_z1 [-] ulnat_y1) in
    let EH_xy_z := (rlucancel (ulnat_xy0 [-] urnat_z0))^ @
      wlrnat_xy_z @ rlucancel (urnat_z2 [-] ulnat_xy1) in
    EH_xy_z @ (concat_p_pp _ _ _ @ whiskerR EH_x_z^ _) =
    concat_pp_p _ _ _ @ whiskerL _ EH_y_z @ concat_p_pp _ _ _.
  Proof.
    apply moveR_Vp in H_ulnat_xy0, H_ulnat_xy1, H_wlrnat_xy_z.
    induction H_ulnat_xy0, H_ulnat_xy1, H_wlrnat_xy_z.
    clear H_ulnat_xy0 H_ulnat_xy1 H_wlrnat_xy_z.
    induction wlpp_xy0, wlpp_xy1.
    clear wlpp_xy0 wlpp_xy1.
    revert ulnat_x0.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_x0.
    induction ulnat_x0.
    clear ulnat_x0.
    revert ulnat_x1.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_x1.
    induction ulnat_x1.
    clear ulnat_x1.
    revert ulnat_y0.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_y0.
    induction ulnat_y0.
    clear ulnat_y0.
    revert ulnat_y1.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_y1.
    induction ulnat_y1.
    clear ulnat_y1.
    revert urnat_z0.
    srapply (equiv_ind rlucancel^-1).
    intro urnat_z0.
    induction urnat_z0.
    clear urnat_z0.
    revert urnat_z1.
    srapply (equiv_ind rlucancel^-1).
    intro urnat_z1.
    induction urnat_z1.
    clear urnat_z1.
    revert urnat_z2.
    srapply (equiv_ind rlucancel^-1).
    intro urnat_z2.
    induction urnat_z2.
    clear urnat_z2.
    induction wlx0, wlx1, wly0, wly1.
    clear wlx0 wlx1 wly0 wly1.
    revert wlrnat_x_z.
    srapply (equiv_ind lrucancel^-1).
    intro wlrnat_x_z.
    induction wlrnat_x_z.
    clear wlrnat_x_z.
    revert wlrnat_y_z.
    srapply (equiv_ind lrucancel^-1).
    intro wlrnat_y_z.
    induction wlrnat_y_z.
    clear wlrnat_y_z.
    induction wrz0.
    clear wrz0.
    reflexivity.
  Defined.

End eh_pp_p.

Theorem eh_pp_p {X} {a : X} (p q r : idpath a = idpath a) :
  eh (p @ q) r @ (concat_p_pp _ _ _ @ whiskerR (eh p r)^ _) =
  concat_pp_p _ _ _ @ whiskerL _ (eh q r) @ concat_p_pp _ _ _.
Proof.
  rapply eh_pp_p_gen.
  - exact (ulnat_pp p q).
  - exact (ulnat_pp p q).
  - exact (wlrnat_pp_p p q r).
Defined.

(* Syllepsis: We now prove that "eh p q" is suitably related to "eh q p". *)
Section eh_V.

  Context {X : Type}.

  (* 0-paths *)
  Context {a b c d : X}.

  (* 1-paths *)
  Context {wlx0 x0 wrx0 : a = b}.
  Context {wlx1 x1 wrx1 : c = d}.
  
  Context {wly0 y0 wry0 : b = d}.
  Context {wly1 y1 wry1 : a = c}.

  (* 2-paths *)
  Context {ulnat_x0 : wlx0 @ 1 = 1 @ x0}.
  Context {urnat_x0 : wrx0 @ 1 = 1 @ x0}.
  Context {ulnat_x1 : wlx1 @ 1 = 1 @ x1}.
  Context {urnat_x1 : wrx1 @ 1 = 1 @ x1}.

  Context {ulnat_y0 : wly0 @ 1 = 1 @ y0}.
  Context {urnat_y0 : wry0 @ 1 = 1 @ y0}.
  Context {ulnat_y1 : wly1 @ 1 = 1 @ y1}.
  Context {urnat_y1 : wry1 @ 1 = 1 @ y1}.

  Context {ehlnat_x0 : wlx0 @ 1 = 1 @ wrx0}.
  Context {ehlnat_x1 : wlx1 @ 1 = 1 @ wrx1}.

  Context {ehrnat_y0 : wry0 @ 1 = 1 @ wly0}.
  Context {ehrnat_y1 : wry1 @ 1 = 1 @ wly1}.

  Context {wlrnat_x_y : wlx0 @ wry0 = wry1 @ wlx1}.
  Context {wlrnat_y_x : wly1 @ wrx1 = wrx0 @ wly0}.

  (* 3-paths *)
  Hypothesis ehlnat_1p_x0 :
    (ehlnat_x0 [I] urnat_x0) @ 1  = 1 @ ulnat_x0.

  Hypothesis ehlnat_1p_x1 :
    (ehlnat_x1 [I] urnat_x1) @ 1 = 1 @ ulnat_x1.

  Hypothesis ehrnat_p1_y0 :
    (ehrnat_y0 [I] ulnat_y0) @ 1 = 1 @ urnat_y0.

  Hypothesis ehrnat_p1_y1 :
    (ehrnat_y1 [I] ulnat_y1) @ 1 = 1 @ urnat_y1.

  Hypothesis wlrnat_V_x_y :
    whiskerR wlrnat_x_y _ @ (ehrnat_y1 [-] ehlnat_x1) =
    (ehlnat_x0 [-] ehrnat_y0) @ whiskerL _ wlrnat_y_x^.

  (* the syllepsis *)
  Definition eh_V_gen :
    let EH_x_y := (rlucancel (ulnat_x0 [-] urnat_y0))^ @
      wlrnat_x_y @ rlucancel (urnat_y1 [-] ulnat_x1) in
    let EH_y_x := (rlucancel (ulnat_y1 [-] urnat_x1))^ @
      wlrnat_y_x @ rlucancel (urnat_x0 [-] ulnat_y0) in
    EH_x_y @ EH_y_x = 1.
  Proof.
    pose (H_whiskerR_wlrnat_x_y := moveL_Mp _ _ _ (moveL_pV _ _ _ (whiskerR_p1 wlrnat_x_y))).
    apply moveL_pV in wlrnat_V_x_y.
    apply (concat H_whiskerR_wlrnat_x_y^) in wlrnat_V_x_y.
    apply moveL_Vp, moveL_pV in wlrnat_V_x_y.
    apply symmetry in wlrnat_V_x_y.
    induction wlrnat_V_x_y.
    clear wlrnat_V_x_y.
    clear H_whiskerR_wlrnat_x_y.
    revert ehlnat_1p_x0.
    srapply (equiv_ind rlucancel^-1).
    intro ehlnat_1p_x0.
    induction ehlnat_1p_x0.
    clear ehlnat_1p_x0.
    revert ehlnat_1p_x1.
    srapply (equiv_ind rlucancel^-1).
    intro ehlnat_1p_x1.
    induction ehlnat_1p_x1.
    clear ehlnat_1p_x1.
    revert ehrnat_p1_y0.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_p1_y0.
    induction ehrnat_p1_y0.
    clear ehrnat_p1_y0.
    revert ehrnat_p1_y1.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_p1_y1.
    induction ehrnat_p1_y1.
    clear ehrnat_p1_y1.
    revert ehlnat_x0.
    srapply (equiv_ind rlucancel^-1).
    intro ehlnat_x0.
    induction ehlnat_x0.
    clear ehlnat_x0.
    revert ehlnat_x1.
    srapply (equiv_ind rlucancel^-1).
    intro ehlnat_x1.
    induction ehlnat_x1.
    clear ehlnat_x1.
    revert ehrnat_y0.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_y0.
    induction ehrnat_y0.
    clear ehrnat_y0.
    revert ehrnat_y1.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_y1.
    induction ehrnat_y1.
    clear ehrnat_y1.
    revert urnat_x0.
    srapply (equiv_ind rlucancel^-1).
    intro urnat_x0.
    induction urnat_x0.
    clear urnat_x0.
    revert urnat_x1.
    srapply (equiv_ind rlucancel^-1).
    intro urnat_x1.
    induction urnat_x1.
    clear urnat_x1.
    revert ulnat_y0.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_y0.
    induction ulnat_y0.
    clear ulnat_y0.
    revert ulnat_y1.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_y1.
    induction ulnat_y1.
    clear ulnat_y1.
    induction wry0, wry1.
    clear wry0 wry1.
    revert wlrnat_y_x.
    srapply (equiv_ind lrucancel^-1).
    intro wlrnat_y_x.
    induction wlrnat_y_x.
    clear wlrnat_y_x.
    induction wlx1.
    clear wlx1.
    reflexivity.
  Defined.

End eh_V.

Theorem eh_V {X} {a : X} (p q : idpath (idpath a) = idpath (idpath a)) :
  eh p q @ eh q p = 1.
Proof.
  rapply eh_V_gen.
  - exact (ehlnat_1p p).
  - exact (ehlnat_1p p).
  - exact (ehrnat_p1 q).
  - exact (ehrnat_p1 q).
  - exact (wlrnat_V p q).
Defined.

(* Given "ehrnat_p1 y" and "ehrnat_p1 z", we can explicitly construct "ehrnat_p1 (y @ z)". *)
Section Ehrnat_p1_pp.

  Context {X : Type}.

  (* 0-paths *)
  Context {a0 a1 a2 : X}.
  Context {b0 b1 b2 : X}.
  Context {c0 c1 c2 : X}.

  (* 1-paths *)
  Context {wry : a0 = b0}.
  Context {wrz : b0 = c0}.

  Context {wly : a1 = b1}.
  Context {wlz : b1 = c1}.

  Context {y : a2 = b2}.
  Context {z : b2 = c2}.

  Context {wryz : a0 = c0}.
  Context {wlyz : a1 = c1}.

  Context {a01 : a0 = a1}.
  Context {a12 : a1 = a2}.

  Context {b01 : b0 = b1}.
  Context {b12 : b1 = b2}.

  Context {c01 : c0 = c1}.
  Context {c12 : c1 = c2}.

  Context {a02 : a0 = a2}.
  Context {c02 : c0 = c2}.
  
  (* 2-paths *)
  Context {ehrnat_y : wry @ b01 = a01 @ wly}.
  Context {ehrnat_z : wrz @ c01 = b01 @ wlz}.
  Context {ehrnat_yz : wryz @ c01 = a01 @ wlyz}.

  Context {ulnat_y : wly @ b12 = a12 @ y}.
  Context {ulnat_z : wlz @ c12 = b12 @ z}.
  Context {ulnat_yz : wlyz @ c12 = a12 @ (y @ z)}.

  Context {urnat_y : wry @ (b01 @ b12) = a02 @ y}.
  Context {urnat_z : wrz @ c02 = (b01 @ b12) @ z}.
  Context {urnat_yz : wryz @ c02 = a02 @ (y @ z)}.

  Context {wrpp_yz : wry @ wrz = wryz}.
  Context {wlpp_yz : wly @ wlz = wlyz}.

  Context (H_a02 : a01 @ a12 = a02).
  Context (H_c02 : c01 @ c12 = c02).

  (* 3-paths *)
  Hypothesis H_ehrnat_yz :
    (ehrnat_y [-] ehrnat_z) @ whiskerL _ wlpp_yz =
    whiskerR wrpp_yz _ @ ehrnat_yz.

  Hypothesis H_ulnat_yz :
    (ulnat_y [-] ulnat_z) = whiskerR wlpp_yz _ @ ulnat_yz.

  Hypothesis H_urnat_yz :
    (urnat_y [-] urnat_z) = whiskerR wrpp_yz _ @ urnat_yz.

  Variable ehrnat_p1_y :
    (ehrnat_y [I] ulnat_y) @ whiskerR H_a02 _ = 1 @ urnat_y.

  Variable ehrnat_p1_z :
    (ehrnat_z [I] ulnat_z) @ 1 = whiskerL _ H_c02 @ urnat_z.

  (* the composite iso *)
  Definition Ehrnat_p1_pp :
    (ehrnat_yz [I] ulnat_yz) @ whiskerR H_a02 _ =
    whiskerL _ H_c02 @ urnat_yz.
  Proof.
    apply moveR_Vp in H_urnat_yz, H_ulnat_yz, H_ehrnat_yz.
    induction H_urnat_yz, H_ulnat_yz, H_ehrnat_yz.
    clear H_urnat_yz H_ulnat_yz H_ehrnat_yz.
    apply moveR_Vp in ehrnat_p1_y, ehrnat_p1_z.
    induction ehrnat_p1_y, ehrnat_p1_z.
    clear ehrnat_p1_y ehrnat_p1_z.
    induction H_a02, H_c02.
    clear H_a02 H_c02.
    induction wrpp_yz, wlpp_yz.
    clear wrpp_yz wlpp_yz.
    induction a01, a12, b01, b12, c01, c12.
    clear a01 a12 b01 b12 c01 c12.
    revert ulnat_y.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_y.
    induction ulnat_y.
    clear ulnat_y.
    revert ulnat_z.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_z.
    induction ulnat_z.
    clear ulnat_z.
    revert ehrnat_y.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_y.
    induction ehrnat_y.
    clear ehrnat_y.
    revert ehrnat_z.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_z.
    induction ehrnat_z.
    clear ehrnat_z.
    induction wry, wrz.
    clear wry wrz.
    reflexivity.
  Defined.

End Ehrnat_p1_pp.

Definition ehrnat_p1_pp {X} {a : X} {u v : idpath a = idpath a} (q : u = 1) (r : 1 = v) :
  Ehrnat_p1_pp (eh_p1 u) (eh_p1 v) (ehrnat_pp q r 1) (ulnat_pp q r) (urnat_pp q r)
    (ehrnat_p1 q) (ehrnat_p1 r) =
  ehrnat_p1 (q @ r).
Proof.
  revert q.
  srapply (equiv_ind (equiv_path_inverse _ _)).
  intro q.
  by induction q, r.
Defined.

(* Given "wlrnat_V x y" and "wlrnat_V x z", we can explicitly construct "wlrnat_V x (y @ z)". *)
Section wlrnat_V_p_pp.

  Context {X : Type}.

  (* 0-paths *)
  Context {a0 b0 c0 d0 e0 f0 : X}.
  Context {a1 b1 c1 d1 e1 f1 : X}.

  (* 1-paths *)
  Context {wlx0 : a0 = b0}.
  Context {wlx1 : c0 = d0}.
  Context {wlx2 : e0 = f0}.

  Context {wrx0 : a1 = b1}.
  Context {wrx1 : c1 = d1}.
  Context {wrx2 : e1 = f1}.

  Context {wry0 : b0 = d0}.
  Context {wly0 : b1 = d1}.
  Context {wry1 : a0 = c0}.
  Context {wly1 : a1 = c1}.

  Context {wrz0 : d0 = f0}.
  Context {wlz0 : d1 = f1}.
  Context {wrz1 : c0 = e0}.
  Context {wlz1 : c1 = e1}.

  Context {a01 : a0 = a1}.
  Context {b01 : b0 = b1}.
  Context {c01 : c0 = c1}.
  Context {d01 : d0 = d1}.
  Context {e01 : e0 = e1}.
  Context {f01 : f0 = f1}.

  Context {wryz0 : b0 = f0}.
  Context {wlyz0 : b1 = f1}.
  Context {wryz1 : a0 = e0}.
  Context {wlyz1 : a1 = e1}.

  (* 2-paths *)
  Context {ehlnat_x0 : wlx0 @ b01 = a01 @ wrx0}.
  Context {ehlnat_x1 : wlx1 @ d01 = c01 @ wrx1}.
  Context {ehlnat_x2 : wlx2 @ f01 = e01 @ wrx2}.

  Context {ehrnat_y0 : wry0 @ d01 = b01 @ wly0}.
  Context {ehrnat_y1 : wry1 @ c01 = a01 @ wly1}.

  Context {ehrnat_z0 : wrz0 @ f01 = d01 @ wlz0}.
  Context {ehrnat_z1 : wrz1 @ e01 = c01 @ wlz1}.

  Context {ehrnat_yz0 : wryz0 @ f01 = b01 @ wlyz0}.
  Context {ehrnat_yz1 : wryz1 @ e01 = a01 @ wlyz1}.

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
  Hypothesis H_ehrnat_yz0 :
    (ehrnat_y0 [-] ehrnat_z0) @ whiskerL _ wlpp_yz0 =
    whiskerR wrpp_yz0 _ @ ehrnat_yz0.

  Hypothesis H_ehrnat_yz1 :
    (ehrnat_y1 [-] ehrnat_z1) @ whiskerL _ wlpp_yz1 =
    whiskerR wrpp_yz1 _ @ ehrnat_yz1.

  Hypothesis H_wlrnat_x_yz :
    (wlrnat_x_y [I] wlrnat_x_z) @ whiskerR wrpp_yz1 _ =
    whiskerL _ wrpp_yz0 @ wlrnat_x_yz.

  Hypothesis H_wlrnat_yz_x :
    (wlrnat_y_x [-] wlrnat_z_x) @ whiskerL _ wlpp_yz0 =
    whiskerR wlpp_yz1 _ @ wlrnat_yz_x.

  Variable wlrnat_V_x_y :
    whiskerR wlrnat_x_y _ @ (ehrnat_y1 [-] ehlnat_x1) =
    (ehlnat_x0 [-] ehrnat_y0) @ whiskerL _ wlrnat_y_x^.

  Variable wlrnat_V_x_z :
    whiskerR wlrnat_x_z _ @ (ehrnat_z1 [-] ehlnat_x2) =
    (ehlnat_x1 [-] ehrnat_z0) @ whiskerL _ wlrnat_z_x^.

  (* the composite square *)
  Definition Wlrnat_V_p_pp :
    whiskerR wlrnat_x_yz _ @ (ehrnat_yz1 [-] ehlnat_x2) =
    (ehlnat_x0 [-] ehrnat_yz0) @ whiskerL _ wlrnat_yz_x^.
  Proof.
    apply moveR_Vp in H_ehrnat_yz0, H_ehrnat_yz1.
    induction H_ehrnat_yz0, H_ehrnat_yz1.
    clear H_ehrnat_yz0 H_ehrnat_yz1.
    apply moveR_Vp in H_wlrnat_x_yz, H_wlrnat_yz_x.
    induction H_wlrnat_x_yz, H_wlrnat_yz_x.
    clear H_wlrnat_x_yz H_wlrnat_yz_x.
    induction a01, b01, c01, d01, e01, f01.
    clear a01 b01 c01 d01 e01 f01.
    pose (H_whiskerR_wlrnat_x_y := moveL_Mp _ _ _ (moveL_pV _ _ _ (whiskerR_p1 wlrnat_x_y))).
    pose (H_whiskerR_wlrnat_x_z := moveL_Mp _ _ _ (moveL_pV _ _ _ (whiskerR_p1 wlrnat_x_z))).
    apply moveL_pV in wlrnat_V_x_y.
    apply (concat H_whiskerR_wlrnat_x_y^) in wlrnat_V_x_y.
    apply moveL_Vp, moveL_pV in wlrnat_V_x_y.
    apply symmetry in wlrnat_V_x_y.
    induction wlrnat_V_x_y.
    clear wlrnat_V_x_y.
    apply moveL_pV in wlrnat_V_x_z.
    apply (concat H_whiskerR_wlrnat_x_z^) in wlrnat_V_x_z.
    apply moveL_Vp, moveL_pV in wlrnat_V_x_z.
    apply symmetry in wlrnat_V_x_z.
    induction wlrnat_V_x_z.
    clear wlrnat_V_x_z.
    clear H_whiskerR_wlrnat_x_y H_whiskerR_wlrnat_x_z.
    induction wrpp_yz0, wlpp_yz0, wrpp_yz1, wlpp_yz1.
    clear wrpp_yz0 wlpp_yz0 wrpp_yz1 wlpp_yz1.
    revert ehlnat_x0.
    srapply (equiv_ind rlucancel^-1).
    intro ehlnat_x0.
    induction ehlnat_x0.
    clear ehlnat_x0.
    revert ehlnat_x1.
    srapply (equiv_ind rlucancel^-1).
    intro ehlnat_x1.
    induction ehlnat_x1.
    clear ehlnat_x1.
    revert ehlnat_x2.
    srapply (equiv_ind rlucancel^-1).
    intro ehlnat_x2.
    induction ehlnat_x2.
    clear ehlnat_x2.
    revert ehrnat_y0.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_y0.
    induction ehrnat_y0.
    clear ehrnat_y0.
    revert ehrnat_y1.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_y1.
    induction ehrnat_y1.
    clear ehrnat_y1.
    revert ehrnat_z0.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_z0.
    induction ehrnat_z0.
    clear ehrnat_z0.
    revert ehrnat_z1.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_z1.
    induction ehrnat_z1.
    clear ehrnat_z1.
    induction wry0, wry1, wrz0, wrz1.
    clear wry0 wry1 wrz0 wrz1.
    revert wlrnat_y_x.
    srapply (equiv_ind lrucancel^-1).
    intro wlrnat_y_x.
    induction wlrnat_y_x.
    clear wlrnat_y_x.
    revert wlrnat_z_x.
    srapply (equiv_ind lrucancel^-1).
    intro wlrnat_z_x.
    induction wlrnat_z_x.
    clear wlrnat_z_x.
    induction wlx2.
    clear wlx2.
    reflexivity.
  Defined.

End wlrnat_V_p_pp.

Definition wlrnat_V_p_pp {X} {a : X} {u v w : idpath a = idpath a} (p : 1 = w) (q : u = 1) (r : 1 = v) :
  Wlrnat_V_p_pp (ehrnat_pp q r _) (ehrnat_pp q r _) (wlrnat_p_pp p q r) (wlrnat_pp_p q r p)
    (wlrnat_V p q) (wlrnat_V p r) =
  wlrnat_V p (q @ r).
Proof.
  revert q.
  srapply (equiv_ind (equiv_path_inverse _ _)).
  intro q.
  by induction p, q, r.
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
    whiskerR (concat_p1 _ @@ concat_p1 _) _ @ whiskerR eh_V_x_yz _ @ lrucancel^-1 1 @
    whiskerL _ (concat_pp_p_p_pp _ _ _)^ @ whiskerL _ (concat_p1 _ @@ concat_p1 _)^ =
    (eh_p_pp_gen H_urnat_yz0 H_urnat_yz1 H_wlrnat_x_yz [-]
     lrucancel^-1 (whiskerL _ (ap (fun p => whiskerL y1 p) (moveL_V1 _ _ eh_V_x_z)))) [-]
    (eh_pp_p_gen H_ulnat_yz1 H_ulnat_yz0 H_wlrnat_yz_x [-]
     lrucancel^-1 (whiskerL _ (ap (fun p => whiskerR p z0) (moveL_1V _ _ eh_V_x_y)))).
  Proof.
    induction H_ehrnat_p1_yz0, H_ehrnat_p1_yz1, H_wlrnat_V_x_yz.
    clear H_ehrnat_p1_yz0 H_ehrnat_p1_yz1 H_wlrnat_V_x_yz.
    pose (H_whiskerR_wlrnat_x_y := moveL_Mp _ _ _ (moveL_pV _ _ _ (whiskerR_p1 wlrnat_x_y))).
    pose (H_whiskerR_wlrnat_x_z := moveL_Mp _ _ _ (moveL_pV _ _ _ (whiskerR_p1 wlrnat_x_z))).
    revert wlrnat_V_x_y.
    srapply (equiv_ind (moveL_pV _ _ _)^-1).
    srapply (equiv_ind (equiv_concat_l H_whiskerR_wlrnat_x_y _)).
    srapply (equiv_ind (moveL_Vp _ _ _)^-1).
    srapply (equiv_ind (moveL_pV _ _ _)^-1).
    srapply (equiv_ind (equiv_path_inverse _ _)).
    intro wlrnat_V_x_y.
    induction wlrnat_V_x_y.
    clear wlrnat_V_x_y.
    revert wlrnat_V_x_z.
    srapply (equiv_ind (moveL_pV _ _ _)^-1).
    srapply (equiv_ind (equiv_concat_l H_whiskerR_wlrnat_x_z _)).
    srapply (equiv_ind (moveL_Vp _ _ _)^-1).
    srapply (equiv_ind (moveL_pV _ _ _)^-1).
    srapply (equiv_ind (equiv_path_inverse _ _)).
    intro wlrnat_V_x_z.
    induction wlrnat_V_x_z.
    clear wlrnat_V_x_z.
    revert H_whiskerR_wlrnat_x_y H_whiskerR_wlrnat_x_z.
    revert ehlnat_1p_x0.
    srapply (equiv_ind rlucancel^-1).
    intro ehlnat_1p_x0.
    induction ehlnat_1p_x0.
    clear ehlnat_1p_x0.
    revert ehlnat_1p_x1.
    srapply (equiv_ind rlucancel^-1).
    intro ehlnat_1p_x1.
    induction ehlnat_1p_x1.
    clear ehlnat_1p_x1.
    revert ehlnat_1p_x2.
    srapply (equiv_ind rlucancel^-1).
    intro ehlnat_1p_x2.
    induction ehlnat_1p_x2.
    clear ehlnat_1p_x2.
    revert ehrnat_p1_y0.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_p1_y0.
    induction ehrnat_p1_y0.
    clear ehrnat_p1_y0.
    revert ehrnat_p1_y1.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_p1_y1.
    induction ehrnat_p1_y1.
    clear ehrnat_p1_y1.
    revert ehrnat_p1_z0.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_p1_z0.
    induction ehrnat_p1_z0.
    clear ehrnat_p1_z0.
    revert ehrnat_p1_z1.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_p1_z1.
    induction ehrnat_p1_z1.
    clear ehrnat_p1_z1.
    revert H_wlrnat_x_yz.
    srapply (equiv_ind (moveR_Vp _ _ _)^-1).
    intro H_wlrnat_x_yz.
    induction H_wlrnat_x_yz.
    clear H_wlrnat_x_yz.
    revert H_wlrnat_yz_x.
    srapply (equiv_ind (moveR_Vp _ _ _)^-1).
    intro H_wlrnat_yz_x.
    induction H_wlrnat_yz_x.
    clear H_wlrnat_yz_x.
    revert H_ehrnat_yz0.
    srapply (equiv_ind (moveR_Vp _ _ _)^-1).
    intro H_ehrnat_yz0.
    induction H_ehrnat_yz0.
    clear H_ehrnat_yz0.
    revert H_ehrnat_yz1.
    srapply (equiv_ind (moveR_Vp _ _ _)^-1).
    intro H_ehrnat_yz1.
    induction H_ehrnat_yz1.
    clear H_ehrnat_yz1.
    revert H_ulnat_yz0.
    srapply (equiv_ind (moveR_Vp _ _ _)^-1).
    intro H_ulnat_yz0.
    induction H_ulnat_yz0.
    clear H_ulnat_yz0.
    revert H_ulnat_yz1.
    srapply (equiv_ind (moveR_Vp _ _ _)^-1).
    intro H_ulnat_yz1.
    induction H_ulnat_yz1.
    clear H_ulnat_yz1.
    revert H_urnat_yz0.
    srapply (equiv_ind (moveR_Vp _ _ _)^-1).
    intro H_urnat_yz0.
    induction H_urnat_yz0.
    clear H_urnat_yz0.
    revert H_urnat_yz1.
    srapply (equiv_ind (moveR_Vp _ _ _)^-1).
    intro H_urnat_yz1.
    induction H_urnat_yz1.
    clear H_urnat_yz1.
    induction wrpp_yz0, wlpp_yz0, wrpp_yz1, wlpp_yz1.
    clear wrpp_yz0 wlpp_yz0 wrpp_yz1 wlpp_yz1.
    revert ehlnat_x0.
    srapply (equiv_ind rlucancel^-1).
    intro ehlnat_x0.
    induction ehlnat_x0.
    clear ehlnat_x0.
    revert ehlnat_x1.
    srapply (equiv_ind rlucancel^-1).
    intro ehlnat_x1.
    induction ehlnat_x1.
    clear ehlnat_x1.
    revert ehlnat_x2.
    srapply (equiv_ind rlucancel^-1).
    intro ehlnat_x2.
    induction ehlnat_x2.
    clear ehlnat_x2.
    revert ehrnat_y0.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_y0.
    induction ehrnat_y0.
    clear ehrnat_y0.
    revert ehrnat_y1.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_y1.
    induction ehrnat_y1.
    clear ehrnat_y1.
    revert ehrnat_z0.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_z0.
    induction ehrnat_z0.
    clear ehrnat_z0.
    revert ehrnat_z1.
    srapply (equiv_ind rlucancel^-1).
    intro ehrnat_z1.
    induction ehrnat_z1.
    clear ehrnat_z1.
    revert urnat_x0.
    srapply (equiv_ind rlucancel^-1).
    intro urnat_x0.
    induction urnat_x0.
    clear urnat_x0.
    revert urnat_x1.
    srapply (equiv_ind rlucancel^-1).
    intro urnat_x1.
    induction urnat_x1.
    clear urnat_x1.
    revert urnat_x2.
    srapply (equiv_ind rlucancel^-1).
    intro urnat_x2.
    induction urnat_x2.
    clear urnat_x2.
    revert ulnat_y0.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_y0.
    induction ulnat_y0.
    clear ulnat_y0.
    revert ulnat_y1.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_y1.
    induction ulnat_y1.
    clear ulnat_y1.
    revert ulnat_z0.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_z0.
    induction ulnat_z0.
    clear ulnat_z0.
    revert ulnat_z1.
    srapply (equiv_ind rlucancel^-1).
    intro ulnat_z1.
    induction ulnat_z1.
    clear ulnat_z1.
    induction wry0, wry1, wrz0, wrz1.
    clear wry0 wry1 wrz0 wrz1.
    revert wlrnat_y_x.
    srapply (equiv_ind lrucancel^-1).
    intro wlrnat_y_x.
    induction wlrnat_y_x.
    clear wlrnat_y_x.
    revert wlrnat_z_x.
    srapply (equiv_ind lrucancel^-1).
    intro wlrnat_z_x.
    induction wlrnat_z_x.
    clear wlrnat_z_x.
    induction wlx2.
    clear wlx2.
    reflexivity.
  Defined.

End eh_V_p_pp.

Definition eh_V_p_pp {X} {a : X} (p q r : idpath (idpath a) = idpath (idpath a)) :
  whiskerR (concat_p1 _ @@ concat_p1 _) _ @ whiskerR (eh_V p (q @ r)) _ @ lrucancel^-1 1 @
  whiskerL _ (concat_pp_p_p_pp _ _ _)^ @ whiskerL _ (concat_p1 _ @@ concat_p1 _)^ =
  (eh_p_pp_gen (urnat_pp q r) (urnat_pp q r) (wlrnat_p_pp p q r) [-]
   lrucancel^-1 (whiskerL _ (ap (fun p => whiskerL q p) (moveL_V1 _ _ (eh_V p r))))) [-]
  (eh_pp_p_gen (ulnat_pp q r) (ulnat_pp q r) (wlrnat_pp_p q r p) [-]
   lrucancel^-1 (whiskerL _ (ap (fun p => whiskerR p r) (moveL_1V _ _ (eh_V p q))))).
Proof.
  rapply eh_V_p_pp_gen.
  - exact (ehrnat_p1_pp q r).
  - exact (ehrnat_p1_pp q r).
  - exact (wlrnat_V_p_pp p q r).
Defined.

