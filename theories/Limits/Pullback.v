Require Import HoTT.Basics HoTT.Types.
Require Import HFiber Homotopy.IdentitySystems Cubical.PathSquare.
Require Import Diagrams.CommutativeSquares.

Local Open Scope path_scope.

(** * Pullbacks *)

(** The pullback as an object *)
Definition Pullback {A B C} (f : B -> A) (g : C -> A)
  := { b : B & { c : C & f b = g c }}.

Global Arguments Pullback {A B C}%_type_scope (f g)%_function_scope.

(** The universal commutative square *)
Definition pullback_pr1 {A B C} {f : B -> A} {g : C -> A}
: Pullback f g -> B := (fun z => z.1).
Definition pullback_pr2 {A B C} {f : B -> A} {g : C -> A}
: Pullback f g -> C := (fun z => z.2.1).
Definition pullback_commsq {A B C} (f : B -> A) (g : C -> A)
: f o pullback_pr1 == g o pullback_pr2
:= (fun z => z.2.2).

(** The universally induced map into it by any commutative square *)
Definition pullback_corec {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h)
: A -> Pullback k g
:= fun a => (f a ; h a ; p a).

Definition pullback_corec_uncurried {A B C D} (k : B -> D) (g : C -> D)
  : { f : A -> B & { h : A -> C & k o f == g o h }} -> (A -> Pullback k g).
Proof.
  intros [f [h p]].
  exact (pullback_corec p).
Defined.

Global Instance isequiv_pullback_corec {A B C D} (k : B -> D) (g : C -> D)
  : IsEquiv (@pullback_corec_uncurried A B C D k g).
Proof.
  snrapply isequiv_adjointify.
  - intro m.
    exact (pullback_pr1 o m ; pullback_pr2 o m ; (pullback_commsq k g) o m).
  - reflexivity.
  - reflexivity.
Defined.

Definition equiv_pullback_corec {A B C D} (k : B -> D) (g : C -> D)
  : { f : A -> B & { h : A -> C & k o f == g o h }} <~> (A -> Pullback k g)
  := Build_Equiv _ _ _ (isequiv_pullback_corec k g).

(** A homotopy commutative square is equivalent to a pullback of arrow types *)
Definition equiv_ispullback_commsq `{Funext} {A B C D} (k : B -> D) (g : C -> D)
  : { f : A -> B & { h : A -> C & k o f == g o h }}
    <~> @Pullback (A -> D) (A -> B) (A -> C) (fun f => k o f) (fun h => g o h).
Proof.
  apply equiv_functor_sigma_id; intro f.
  apply equiv_functor_sigma_id; intro h.
  apply equiv_path_forall.
Defined.

(** The diagonal of a map *)
Definition diagonal {X Y : Type} (f : X -> Y) : X -> Pullback f f
  := fun x => (x;x;idpath).

(** The fiber of the diagonal is a path-space in the fiber. *)
Definition hfiber_diagonal {X Y : Type} (f : X -> Y) (p : Pullback f f)
  : hfiber (diagonal f) p <~>  ((p.1 ; p.2.2) = (p.2.1 ; idpath) :> hfiber f (f p.2.1)).
Proof.
  destruct p as [x1 [x2 p]]; cbn.
  refine (_ oE equiv_functor_sigma_id (fun x => (equiv_path_sigma _ _ _)^-1)); cbn.
  refine (_ oE equiv_sigma_assoc' _ _).
  refine (_ oE equiv_contr_sigma _); cbn.
  refine (equiv_path_sigma _ _ _ oE _ oE (equiv_path_sigma _ _ _)^-1); cbn.
  apply equiv_functor_sigma_id; intros q.
  destruct q; cbn.
  apply equiv_path_inverse.
Defined.

(** Symmetry of the pullback *)
Definition equiv_pullback_symm {A B C} (f : B -> A) (g : C -> A)
: Pullback f g <~> Pullback g f.
Proof.
  refine (_ oE equiv_sigma_symm (fun b c => f b = g c)).
  apply equiv_functor_sigma_id; intros c.
  apply equiv_functor_sigma_id; intros b.
  apply equiv_path_inverse.
Defined.

(** Pullback over [Unit] is equivalent to a product. *)
Definition equiv_pullback_unit_prod (A B : Type)
: Pullback (const_tt A) (const_tt B) <~> A * B.
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  - intros [a [b _]]; exact (a , b).
  - intros [a b]; exact (a ; b ; 1).
  - intros [a b]; exact 1.
  - intros [a [b p]]; simpl.
    apply (path_sigma' _ 1); simpl.
    apply (path_sigma' _ 1); simpl.
    apply path_contr.
Defined.

(** The property of a given commutative square being a pullback *)
Definition IsPullback {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h)
  := IsEquiv (pullback_corec p).

Definition equiv_ispullback {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h) (ip : IsPullback p)
  : A <~> Pullback k g
  := Build_Equiv _ _ (pullback_corec p) ip.

(** This is equivalent to the transposed square being a pullback. *)
Definition ispullback_symm {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : g o h == k o f) (pb : IsPullback (fun a => (p a)^))
  : IsPullback p.
Proof.
  rapply (cancelL_isequiv (equiv_pullback_symm g k)).
  apply pb.
Defined.

(** The pullback of the projections [{d:D & P d} -> D <- {d:D & Q d}] is equivalent to [{d:D & P d * Q d}]. *)
Definition ispullback_sigprod {D : Type} (P Q : D -> Type)
  : IsPullback (fun z:{d:D & P d * Q d} => 1%path : (z.1;fst z.2).1 = (z.1;snd z.2).1).
Proof.
  srapply isequiv_adjointify.
  - intros [[d1 p] [[d2 q] e]]; cbn in e.
    exists d1. exact (p, e^ # q).
  - intros [[d1 p] [[d2 q] e]]; unfold pullback_corec; cbn in *.
    destruct e; reflexivity.
  - intros [d [p q]]; reflexivity.
Defined.

Definition equiv_sigprod_pullback {D : Type} (P Q : D -> Type)
  : {d:D & P d * Q d} <~> Pullback (@pr1 D P) (@pr1 D Q)
  := Build_Equiv _ _ _ (ispullback_sigprod P Q).

(** For any commutative square, the fiber of the fibers is equivalent to the fiber of the "gap map" [pullback_corec]. *)
Definition hfiber_pullback_corec {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h) (b : B) (c : C) (q : k b = g c)
  : hfiber (pullback_corec p) (b; c; q) <~> hfiber (functor_hfiber p b) (c; q^).
Proof.
  unfold hfiber, functor_hfiber, functor_sigma.
  refine (equiv_sigma_assoc _ _ oE _).
  apply equiv_functor_sigma_id; intros a; cbn.
  refine (_ oE (equiv_path_sigma _ _ _)^-1); cbn.
  apply equiv_functor_sigma_id; intro p0; cbn.
  rewrite transport_sigma'; cbn.
  refine ((equiv_path_sigma _ _ _) oE _ oE (equiv_path_sigma _ _ _)^-1); cbn.
  apply equiv_functor_sigma_id; intro p1; cbn.
  rewrite !transport_paths_Fr, !transport_paths_Fl.
  refine (_ oE (equiv_ap (equiv_path_inverse _ _) _ _)); cbn.
  apply equiv_concat_l.
  refine (_ @ (inv_pp _ _)^).  apply whiskerL.
  refine (_ @ (inv_pp _ _)^).  apply whiskerL.
  symmetry; apply inv_V.
Defined.

(** If the induced maps on fibers are equivalences, then a square is a pullback. *)
Definition ispullback_isequiv_functor_hfiber {A B C D : Type}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h)
           (e : forall b:B, IsEquiv (functor_hfiber p b))
  : IsPullback p.
Proof.
  unfold IsPullback.
  apply isequiv_contr_map; intro x.
  rapply contr_equiv'.
  - symmetry; apply hfiber_pullback_corec.
  - exact _.
Defined.

(** Conversely, if the square is a pullback then the induced maps on fibers are equivalences. *)
Definition isequiv_functor_hfiber_ispullback {A B C D : Type}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h)
           (e : IsPullback p)
  : forall b:B, IsEquiv (functor_hfiber p b).
Proof.
  apply isequiv_from_functor_sigma.
  unfold IsPullback in e.
  snrapply isequiv_commsq'.
  4: exact (equiv_fibration_replacement f)^-1%equiv.
  1: exact (Pullback k g).
  1: exact (pullback_corec p).
  { apply (functor_sigma idmap); intro b.
    apply (functor_sigma idmap); intro c.
    apply inverse. }
  { intros [x [y q]].
    destruct q.
    apply (path_sigma' _ idpath).
    apply (path_sigma' _ idpath).
    simpl.
    refine (_^ @ (inv_Vp _ _)^).
    apply concat_1p. }
  all: exact _.
Defined.

(** The pullback of a map along another one *)
Definition pullback_along {A B C} (f : B -> A) (g : C -> A)
: Pullback f g -> B
  := pr1.

Notation "f ^*" := (pullback_along f) : function_scope.

Definition hfiber_pullback_along {A B C} (f : B -> A) (g : C -> A) (b:B)
: hfiber (f ^* g) b <~> hfiber g (f b).
Proof.
  refine (equiv_functor_sigma_id (fun c => equiv_path_inverse _ _) oE _).
  make_equiv_contr_basedpaths.
Defined.

(** And the dual sort of pullback *)
Definition pullback_along' {A B C} (g : C -> A) (f : B -> A)
: Pullback f g -> C
  := fun z => z.2.1.

Arguments pullback_along' / .

Notation "g ^*'" := (pullback_along' g) : function_scope.

Definition hfiber_pullback_along' {A B C} (g : C -> A) (f : B -> A) (c:C)
: hfiber (g ^*' f) c <~> hfiber f (g c).
Proof.
  make_equiv_contr_basedpaths.
Defined.

(** A version where [g] is pointed, but we unbundle the pointed condition to avoid importing pointed types. *)
Definition hfiber_pullback_along_pointed {A B C} {c : C} {a : A}
           (g : C -> A) (f : B -> A) (p : g c = a)
  : hfiber (g ^*' f) c <~> hfiber f a.
Proof.
  refine (_ oE hfiber_pullback_along' _ _ _); cbn.
  srapply (equiv_functor_hfiber2 (h:=equiv_idmap) (k:=equiv_idmap)).
  - reflexivity.
  - assumption.
Defined.

Section Functor_Pullback.

  Context {A1 B1 C1 A2 B2 C2}
          (f1 : B1 -> A1) (g1 : C1 -> A1)
          (f2 : B2 -> A2) (g2 : C2 -> A2)
          (h : A1 -> A2) (k : B1 -> B2) (l : C1 -> C2)
          (p : f2 o k == h o f1) (q : g2 o l == h o g1).

  Definition functor_pullback : Pullback f1 g1 -> Pullback f2 g2
    := functor_sigma k
        (fun b1 => (functor_sigma l
                     (fun c1 e1 => p b1 @ ap h e1 @ (q c1)^))).

  Definition hfiber_functor_pullback (z : Pullback f2 g2)
  : hfiber functor_pullback z
    <~> Pullback (transport (hfiber h) z.2.2 o functor_hfiber (k := f2) p z.1)
                 (functor_hfiber q z.2.1).
  Proof.
    destruct z as [b2 [c2 e2]].
    refine (_ oE hfiber_functor_sigma _ _ _ _ _ _).
    apply equiv_functor_sigma_id.
    intros [b1 e1]; simpl.
    refine (_ oE (equiv_transport _ (transport_sigma' e1^ (c2; e2)))).
    refine (_ oE hfiber_functor_sigma _ _ _ _ _ _); simpl.
    apply equiv_functor_sigma_id.
    intros [c1 e3]; simpl.
    refine (_ oE (equiv_transport _
                   (ap (fun e => e3^ # e) (transport_paths_Fl e1^ e2)))).
    refine (_ oE (equiv_transport _ (transport_paths_Fr e3^ _))).
    unfold functor_hfiber; simpl.
    refine (equiv_concat_l (transport_sigma' e2 _) _ oE _); simpl.
    refine (equiv_path_sigma _ _ _ oE _); simpl.
    apply equiv_functor_sigma_id; intros e0; simpl.
    refine (equiv_concat_l (transport_paths_Fl e0 _) _ oE _).
    refine (equiv_concat_l (whiskerL (ap h e0)^ (transport_paths_r e2 _)) _ oE _).
    refine (equiv_moveR_Vp _ _ _ oE _).
    refine (equiv_concat_l (concat_pp_p _ _ _) _ oE _).
    refine (equiv_moveR_Vp _ _ _ oE _).
    do 2 refine (equiv_concat_r (concat_pp_p _ _ _) _ oE _).
    refine (equiv_moveL_pM _ _ _ oE _).
    abstract (rewrite !ap_V, inv_V; refine (equiv_path_inverse _ _)).
  Defined.

End Functor_Pullback.

Section EquivPullback.
  Context {A B C f g A' B' C' f' g'}
          (eA : A <~> A') (eB : B <~> B') (eC : C <~> C')
          (p : f' o eB == eA o f) (q :  g' o eC == eA o g).

  Lemma equiv_pullback
    : Pullback f g <~> Pullback f' g'.
  Proof.
    unfold Pullback.
    apply (equiv_functor_sigma' eB); intro b.
    apply (equiv_functor_sigma' eC); intro c.
    refine (equiv_concat_l (p _) _ oE _).
    refine (equiv_concat_r (q _)^ _ oE _).
    refine (equiv_ap' eA _ _).
  Defined.

End EquivPullback.


(** Pullbacks commute with sigmas *)
Section PullbackSigma.

  Context
    {X Y Z : Type}
    {A : X -> Type} {B : Y -> Type} {C : Z -> Type}
    (f : Y -> X) (g : Z -> X)
    (r : forall x, B x -> A (f x))
    (s : forall x, C x -> A (g x)).

  Definition equiv_sigma_pullback
    : {p : Pullback f g & Pullback (transport A p.2.2 o r p.1) (s p.2.1)}
      <~> Pullback (functor_sigma f r) (functor_sigma g s).
  Proof.
    refine (equiv_functor_sigma_id (fun _ => equiv_functor_sigma_id _) oE _).
    - intros; rapply equiv_path_sigma.
    - make_equiv.
  Defined.

End PullbackSigma.

(** ** Paths in pullbacks *)

Definition equiv_path_pullback {A B C} (f : B -> A) (g : C -> A)
           (x y : Pullback f g)
  : { p : x.1 = y.1 & { q : x.2.1 = y.2.1 & PathSquare (ap f p) (ap g q) x.2.2 y.2.2 } }
      <~> (x = y).
Proof.
  revert y; rapply equiv_path_from_contr.
  { exists idpath. exists idpath.
    cbn. apply sq_refl_v. }
  destruct x as [b [c p]]; unfold Pullback; cbn.
  contr_sigsig b (idpath b).
  contr_sigsig c (idpath c).
  cbn.
  rapply (contr_equiv' {p' : f b = g c & p = p'}).
  apply equiv_functor_sigma_id; intros p'.
  apply sq_1G.
Defined.

(** Maps into pullbacks are determined by their composites with the projections, and a coherence.  This can also be proved directly.  With [Funext], we could also prove an equivalence analogous to [equiv_path_pullback_rec_hset] below.  Not sure of the best name for this version. *)
Definition pullback_homotopic {A B C D} {g : C -> D} {k : B -> D}
           (f h : A -> Pullback k g)
           (p1 : pullback_pr1 o f == pullback_pr1 o h)
           (p2 : pullback_pr2 o f == pullback_pr2 o h)
           (q : forall a, (ap k) (p1 a) @ (h a).2.2 = (f a).2.2 @ (ap g) (p2 a))
  : f == h.
Proof.
  intro a.
  apply equiv_path_pullback.
  exists (p1 a).  exists (p2 a).
  apply sq_path, q.
Defined.

(** When [A] is a set, the [PathSquare] becomes trivial. *)
Definition equiv_path_pullback_hset {A B C} `{IsHSet A} (f : B -> A) (g : C -> A)
           (x y : Pullback f g)
  : (x.1 = y.1) * (x.2.1 = y.2.1) <~> (x = y).
Proof.
  refine (equiv_path_pullback f g x y oE _^-1%equiv).
  refine (_ oE equiv_sigma_prod (fun pq => PathSquare (ap f (fst pq)) (ap g (snd pq)) (x.2).2 (y.2).2)).
  rapply equiv_sigma_contr. (* Uses [istrunc_sq]. *)
Defined.

Lemma equiv_path_pullback_rec_hset `{Funext} {A X Y Z : Type} `{IsHSet Z}
      (f : X -> Z) (g : Y -> Z) (phi psi : A -> Pullback f g)
  : ((pullback_pr1 o phi == pullback_pr1 o psi) * (pullback_pr2 o phi == pullback_pr2 o psi))
      <~> (phi == psi).
Proof.
  refine (_ oE equiv_prod_coind _ _).
  srapply equiv_functor_forall_id; intro a; cbn.
  apply equiv_path_pullback_hset.
Defined.

(** The 3x3 Lemma *)

Section Pullback3x3.

  Context
    (A00 A02 A04 A20 A22 A24 A40 A42 A44 : Type)
    (f01 : A00 -> A02) (f03 : A04 -> A02)
    (f10 : A00 -> A20) (f12 : A02 -> A22) (f14 : A04 -> A24)
    (f21 : A20 -> A22) (f23 : A24 -> A22)
    (f30 : A40 -> A20) (f32 : A42 -> A22) (f34 : A44 -> A24)
    (f41 : A40 -> A42) (f43 : A44 -> A42)
    (H11 : f12 o f01 == f21 o f10) (H13 : f12 o f03 == f23 o f14)
    (H31 : f32 o f41 == f21 o f30) (H33 : f32 o f43 == f23 o f34).

  Let fX1 := functor_pullback f10 f30 f12 f32 f21 f01 f41 H11 H31.
  Let fX3 := functor_pullback f14 f34 f12 f32 f23 f03 f43 H13 H33.
  Let f1X := functor_pullback f01 f03 f21 f23 f12 f10 f14 (symmetry _ _ H11) (symmetry _ _ H13).
  Let f3X := functor_pullback f41 f43 f21 f23 f32 f30 f34 (symmetry _ _ H31) (symmetry _ _ H33).

  Theorem pullback3x3 : Pullback fX1 fX3 <~> Pullback f1X f3X.
  Proof.
    refine (_ oE _ oE _).
    1,3:do 2 (rapply equiv_functor_sigma_id; intro).
    1:apply equiv_path_pullback.
    1:symmetry; apply equiv_path_pullback.
    refine (_ oE _).
    { do 4 (rapply equiv_functor_sigma_id; intro).
      refine (sq_tr oE _).
      refine (sq_move_14^-1 oE _).
      refine (sq_move_31 oE _).
      refine (sq_move_24^-1 oE _).
      refine (sq_move_23^-1 oE _).
      rewrite 2 inv_V.
      reflexivity. }
    make_equiv.
  Defined.

End Pullback3x3.

(** Pasting for pullbacks (or 2-pullbacks lemma) *)

Section Pasting.

  (** Given the following diagram where the right square is a pullback square, then the outer square is a pullback square if and only if the left square is a pullback. *)
  (* A --k--> B --l--> C
     |    //  |    //  |
     f  comm  g  comm  h
     |  //    |  //    |
     V //     V //     V
     X --i--> Y --j--> Z *)
  Context
    {A B C X Y Z : Type}
    {k : A -> B} {l : B -> C}
    {f : A -> X} {g : B -> Y} {h : C -> Z}
    {i : X -> Y} {j : Y -> Z}
    (H : i o f == g o k) (K : j o g == h o l) {e1 : IsPullback K}.

  Definition ispullback_pasting_left
    : IsPullback (comm_square_comp' H K) -> IsPullback H.
  Proof.
    intro e2.
    apply ispullback_isequiv_functor_hfiber.
    intro b.
    pose (e1' := isequiv_functor_hfiber_ispullback _ e1 (i b)).
    pose (e2' := isequiv_functor_hfiber_ispullback _ e2 b).
    snrapply isequiv_commsq'.
    7: apply isequiv_idmap.
    4: apply (functor_hfiber_compose H K b).
    1,2: exact _.
  Defined.

  Definition ispullback_pasting_outer
    : IsPullback H -> IsPullback (comm_square_comp' H K).
  Proof.
    intro e2.
    apply ispullback_isequiv_functor_hfiber.
    intro b.
    pose (e1' := isequiv_functor_hfiber_ispullback _ e1 (i b)).
    pose (e2' := isequiv_functor_hfiber_ispullback _ e2 b).
    snrapply isequiv_commsq'.
    9: apply isequiv_idmap.
    4: symmetry; apply (functor_hfiber_compose H K b).
    1,2: exact _.
  Defined.

End Pasting.
