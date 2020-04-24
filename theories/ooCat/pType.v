(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import ooCat.Cat1 ooCat.Paths ooCat.Forall ooCat.Sigma ooCat.Type.

Generalizable Variables m n p A B C.

(** ** Pointed families over pointed types *)

Class IsDPointed {A : Type} `{IsPointed A} (B : A -> Type)
  := dpoint : B (point A).

Global Instance isdpointed_const `{IsPointed A, IsPointed B}
  : IsDPointed (@const A Type B)
  := point B.

Arguments dpoint {A _} B {_}.

(** ** pType *)

(** Let's define [pType] as a sigma here, since then we can apply the general theorems about sigmas of displayed categories. *)

Definition pType := sig IsPointed.


(** ** [pType] is displayed globular over [Type] *)

CoFixpoint isdglob_pforall `{IsDPointed A B}
           (Bg := fun a => isglob_withpaths (B a))
  : IsDGlob 0 (fun (f : forall a:A, B a) => f (point A) = dpoint B).
Proof.
  unshelve econstructor.
  - intros f g p fp gp.
    exact (p (point A) = fp @ gp^).
  - intros f g fp gp; cbn.
    rapply isdglob_pforall.
Defined.

Global Existing Instance isdglob_pforall.

Global Instance isdglob_ispointed
  : IsDGlob 1 IsPointed.
Proof.
  unshelve econstructor.
  - intros X Y f ? ?.
    exact (f (point X) = point Y).
  - intros X Y ? ?. cbn.
    exact (@isdglob_pforall _ _ (@const X Type Y) _).
Defined.

Global Instance isglob_ptype : IsGlob 1 pType.
Proof.
  unfold pType.
  (** What's up with the universes? *)
  Fail exact (@isglob_sigma 1 Type IsPointed _ _).
Abort.


(** ** [pType] is a displayed 0-coherent category over [Type] *)

CoFixpoint isdfunctor0_postcomp_pforall
           `{IsDPointed A B} {C : A -> Type} `{!IsDPointed C}
           (F : forall a, B a -> C a) (Fp : F (point A) (dpoint B) = dpoint C)
           (** We expand [ap (F (point A)) p @ Fp] into a singleton here because it makes the applications easier. *)
           (G : forall (f : forall a:A, B a) (p : f (point A) = dpoint B),
               F (point A) (f (point A)) = dpoint C)
           (Gp : forall (f : forall a:A, B a) (p : f (point A) = dpoint B),
               G f p = ap (F (point A)) p @ Fp)
           (Bg := fun a => isglob_withpaths (B a))
           (Cg := fun a => isglob_withpaths (C a))
           (Fg := fun a => isfunctor0_withpaths (F a))
  : IsDFunctor0 (fun (f : forall a:A, B a) => fun a => F a (f a))
                (fun (f : forall a:A, B a) (p : f (point A) = dpoint B) => G f p).
Proof.
  unshelve econstructor.
  - cbn; intros f g fp gp p u.
    refine (ap (ap (F (point A))) u @ _).
    refine (_ @ ((Gp f fp)^ @@ (inverse2 (Gp g gp)^))).
    refine (ap_pp _ _ _ @ _ @ (idpath @@ (inv_pp _ _)^)).
    refine (_ @ concat_p_pp _ _ _).
    refine (idpath @@ _).
    refine (ap_V _ _ @ _).
    symmetry; apply concat_p_Vp.
  - intros f g fp gp.
    rapply isdfunctor0_postcomp_pforall.
    intros; reflexivity.
Defined.

(*
CoFixpoint isdfunctor0_precomp_pforall
           `{IsDPointed A B} `{!IsPointed C} (h : C -> A) (hp : h (point C) = point A)
           (Bg := fun a => isglob_withpaths (B a))
           (Bhp := hp^ # (dpoint B) : IsDPointed (B o h))
           (Bhg := @isdglob_pforall C _ (B o h) _)
  : IsDFunctor0 (fun (g : forall a:A, B a) => fun c => g (h c))
                (fun (g : forall a:A, B a) (p : g (point A) = dpoint B)
                 => moveL_transport_V B hp (g (h (point C))) (dpoint B) (apD g hp @ p)).
Proof.
  unshelve econstructor.
  - cbn; intros g1 g2 gp1 gp2 p pp.
*)

CoFixpoint isdcat0_pforall `{IsDPointed A B}
           (Bg := fun a => isglob_withpaths (B a))
           (Bc0 := fun a => iscat0_withpaths (B a))
  : IsDCat0 0 (fun (f : forall a:A, B a) => f (point A) = dpoint B).
Proof.
  unshelve econstructor; cbn in *.
  - intros f g h fp gp hp q p r s.
    refine ((whiskerR s _ @ whiskerL _ r) @ _).
    refine (concat_pp_p _ _ _ @ _).
    refine (idpath @@ _).
    apply concat_V_pp.
  - intros f fp.
    symmetry; apply concat_pV.
  - intros f g h fp gp hp q qp; cbn.
    refine (@isdfunctor0_postcomp_pforall
              A _ (fun a => f a = g a) (fp @ gp^) (fun a => f a = h a)
              _ (fun (a:A) (t:f a = g a) => t @ q a) _ _ _).
    intros k kp; cbn.
    refine (concat_pp_p _ _ _ @ whiskerR _ _).
    symmetry; apply ap_concat_r.
  - intros f g h fp gp hp p pp; cbn.
    refine (@isdfunctor0_postcomp_pforall
              A _ (fun a => g a = h a) (gp @ hp^) (fun a => f a = h a)
              _ (fun (a:A) (t:g a = h a) => p a @ t) _ _ _).
    intros k kp; cbn.
    refine (((concat_whisker _ _ _ _ _ _) @@ idpath) @ _).
    refine (concat_pp_p _ _ _ @ whiskerR _ _).
    symmetry; apply ap_concat_l.
  - intros _ f g fp gp p pe pp.
    apply (cancelR _ _ (p (point A))).
    pose (isqiso_from_forall _ p (point A)).
    refine (qiso_isretr (p (point A)) @ _).
    refine (_ @ (idpath @@ pp^)).
    refine (_ @ concat_pp_p _ _ _).
    refine (_ @ ((concat_pV_p _ _)^ @@ idpath)).
    symmetry; cbn; apply concat_pV.
  - intros f g fp gp; cbn.
    rapply isdcat0_pforall.
Defined.

Global Existing Instance isdcat0_pforall.

Global Instance isdcat0_ispointed
  : IsDCat0 1 IsPointed.
Proof.
  unshelve econstructor.
  - cbn; intros X Y Z ? ? ? g f gp fp.
    exact (ap g fp @ gp).
  - cbn; intros X ?; reflexivity.
  - cbn; intros X Y Z ? ? ? g gp.
    rapply isdfunctor0_postcomp_pforall; cbn.
    intros; reflexivity.
  - cbn; intros X Y Z ? ? ? f fp.
    admit. (** I think this requires some precomposition lemma *)
  - intros [].
  - intros X Y ? ?; cbn.
    exact (@isdcat0_pforall X _ (@const X Type Y) _).
Admitted.

(*
Global Instance iscat0_ptype : IsCat0 1 pType.
 *)
