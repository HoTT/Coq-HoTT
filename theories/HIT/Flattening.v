(* -*- mode: coq; mode: visual-line -*- *)

(** * The flattening lemma. *)

Require Import HoTT.Basics UnivalenceImpliesFunext.
Require Import Types.Paths Types.Forall Types.Sigma Types.Arrow Types.Universe.
Local Open Scope path_scope.
Require Import HoTT.HIT.Coeq.

(** The base HIT [W] is just a homotopy coequalizer [Coeq]. *)

(** TODO: Make the names in this file more usable, move it into [Coeq.v], and use it to derive corresponding flattening lemmas for [pushout], etc. *)

(** Now we define the flattened HIT which will be equivalent to the total space of a fibration over [W]. *)

Module Export FlattenedHIT.

Private Inductive Wtil (A B : Type) (f g : B -> A)
  (C : A -> Type) (D : forall b, C (f b) <~> C (g b))
  : Type :=
| cct : forall a, C a -> Wtil A B f g C D.

Arguments cct {A B f g C D} a c.

Axiom ppt : forall {A B f g C D} (b:B) (y:C (f b)),
  @cct A B f g C D (f b) y = cct (g b) (D b y).

Definition Wtil_ind {A B f g C D} (Q : Wtil A B f g C D -> Type)
  (cct' : forall a x, Q (cct a x))
  (ppt' : forall b y, (ppt b y) # (cct' (f b) y) = cct' (g b) (D b y))
  : forall w, Q w
  := fun w => match w with cct a x => cct' a x end.

Axiom Wtil_ind_beta_ppt
  : forall {A B f g C D} (Q : Wtil A B f g C D -> Type)
    (cct' : forall a x, Q (cct a x))
    (ppt' : forall b y, (ppt b y) # (cct' (f b) y) = cct' (g b) (D b y))
    (b:B) (y : C (f b)),
    apD (Wtil_ind Q cct' ppt') (ppt b y) = ppt' b y.

End FlattenedHIT.

Definition Wtil_rec {A B f g C} {D : forall b, C (f b) <~> C (g b)}
  (Q : Type) (cct' : forall a (x : C a), Q)
  (ppt' : forall b (y : C (f b)), cct' (f b) y = cct' (g b) (D b y))
  : Wtil A B f g C D -> Q
  := Wtil_ind (fun _ => Q) cct' (fun b y => transport_const _ _ @ ppt' b y).

Definition Wtil_rec_beta_ppt
  {A B f g C} {D : forall b, C (f b) <~> C (g b)}
  (Q : Type) (cct' : forall a (x : C a), Q)
  (ppt' : forall (b:B) (y : C (f b)), cct' (f b) y = cct' (g b) (D b y))
  (b:B) (y: C (f b))
  : ap (@Wtil_rec A B f g C D Q cct' ppt') (ppt b y) = ppt' b y.
Proof.
  unfold Wtil_rec.
  eapply (cancelL (transport_const (ppt (C:=C) b y) _)).
  refine ((apD_const
    (@Wtil_ind A B f g C D (fun _ => Q) cct' _) (ppt b y))^ @ _).
  refine (Wtil_ind_beta_ppt (fun _ => Q) _ _ _ _).
Defined.



(** Now we define the fibration over it that we will be considering the total space of. *)

Section AssumeAxioms.
Context `{Univalence}.

Context {B A : Type} {f g : B -> A}.
Context {C : A -> Type} {D : forall b, C (f b) <~> C (g b)}.

Let W' := Coeq f g.

Let P : W' -> Type
  := Coeq_rec Type C (fun b => path_universe (D b)).



(** Now we give the total space the same structure as [Wtil]. *)

Let sWtil := { w:W' & P w }.

Let scct (a:A) (x:C a) : sWtil := (existT P (coeq a) x).

Let sppt (b:B) (y:C (f b)) : scct (f b) y = scct (g b) (D b y)
  := path_sigma' P (cglue b)
       (transport_path_universe' P (cglue b) (D b)
         (Coeq_rec_beta_cglue Type C (fun b0 => path_universe (D b0)) b) y).

(** Here is the dependent eliminator *)
Definition sWtil_ind (Q : sWtil -> Type)
  (scct' : forall a x, Q (scct a x))
  (sppt' : forall b y, (sppt b y) # (scct' (f b) y) = scct' (g b) (D b y))
  : forall w, Q w.
Proof.
  apply sigT_ind.
  refine (Coeq_ind (fun w => forall x:P w, Q (w;x))
    (fun a x => scct' a x) _).
  intros b.
  apply (dpath_forall P (fun a b => Q (a;b)) _ _ (cglue b)
    (scct' (f b)) (scct' (g b))).
  intros y.
  set (q := transport_path_universe' P (cglue b) (D b)
    (Coeq_rec_beta_cglue Type C (fun b0 : B => path_universe (D b0)) b) y).
  rewrite transportD_is_transport.
  refine (_ @ apD (scct' (g b)) q^).
  refine (moveL_transport_V (fun x => Q (scct (g b) x)) q _ _ _).
  rewrite transport_compose, <- transport_pp.
  refine (_ @ sppt' b y).
  apply ap10, ap.
  refine (whiskerL _ (ap_existT P (coeq (g b)) _ _ q) @ _).
  exact ((path_sigma_p1_1p' _ _ _)^).
Defined.

(** The eliminator computes on the point constructor. *)
Definition sWtil_ind_beta_cct (Q : sWtil -> Type)
  (scct' : forall a x, Q (scct a x))
  (sppt' : forall b y, (sppt b y) # (scct' (f b) y) = scct' (g b) (D b y))
  (a:A) (x:C a)
  : sWtil_ind Q scct' sppt' (scct a x) = scct' a x
  := 1.

(** This would be its propositional computation rule on the path constructor... *)
(**
<<
Definition sWtil_ind_beta_ppt (Q : sWtil -> Type)
  (scct' : forall a x, Q (scct a x))
  (sppt' : forall b y, (sppt b y) # (scct' (f b) y) = scct' (g b) (D b y))
  (b:B) (y:C (f b))
  : apD (sWtil_ind Q scct' sppt') (sppt b y) = sppt' b y.
Proof.
  unfold sWtil_ind.
  (** ... but it's a doozy! *)
Abort.
>> *)

(** Fortunately, it turns out to be enough to have the computation rule for the *non-dependent* eliminator! *)

(** We could define that in terms of the dependent one, as usual...
<<
Definition sWtil_rec (P : Type)
  (scct' : forall a (x : C a), P)
  (sppt' : forall b (y : C (f b)), scct' (f b) y = scct' (g b) (D b y))
  : sWtil -> P
  := sWtil_ind (fun _ => P) scct' (fun b y => transport_const _ _ @ sppt' b y).
>> *)

(** ...but if we define it diindly, then it's easier to reason about. *)
Definition sWtil_rec (Q : Type)
  (scct' : forall a (x : C a), Q)
  (sppt' : forall b (y : C (f b)), scct' (f b) y = scct' (g b) (D b y))
  : sWtil -> Q.
Proof.
  apply sigT_ind.
  refine (Coeq_ind (fun w => P w -> Q) (fun a x => scct' a x) _).
  intros b.
  refine (dpath_arrow P (fun _ => Q) _ _ _ _).
  intros y.
  refine (transport_const _ _ @ _).
  refine (sppt' b _ @ ap _ _).
  refine ((transport_path_universe' P (cglue b) (D b) _ _)^).
  exact (Coeq_rec_beta_cglue _ _ _ _).
Defined.

Open Scope long_path_scope.

Definition sWtil_rec_beta_ppt (Q : Type)
  (scct' : forall a (x : C a), Q)
  (sppt' : forall b (y : C (f b)), scct' (f b) y = scct' (g b) (D b y))
  (b:B) (y: C (f b))
  : ap (sWtil_rec Q scct' sppt') (sppt b y) = sppt' b y.
Proof.
  unfold sWtil_rec, sppt.
  refine (@ap_sigT_rec_path_sigma W' P Q _ _ (cglue b) _ _ _ _ @ _); simpl.
  rewrite (@Coeq_ind_beta_cglue B A f g).
  rewrite (ap10_dpath_arrow P (fun _ => Q) (cglue b) _ _ _ y).
  repeat rewrite concat_p_pp.
  (** Now everything cancels! *)
  rewrite ap_V, concat_pV_p, concat_pV_p, concat_pV_p, concat_Vp.
  by apply concat_1p.
Qed.

Close Scope long_path_scope.

(** Woot! *)
Definition equiv_flattening : Wtil A B f g C D <~> sWtil.
Proof.
  (** The maps back and forth are obtained easily from the non-dependent eliminators. *)
  refine (equiv_adjointify
    (Wtil_rec _ scct sppt)
    (sWtil_rec _ cct ppt)
    _ _).
  (** The two homotopies are completely symmetrical, using the *dependent* eliminators, but only the computation rules for the non-dependent ones. *)
  - refine (sWtil_ind _ (fun a x => 1) _). intros b y.
    apply dpath_path_FFlr.
    rewrite concat_1p, concat_p1.
    rewrite sWtil_rec_beta_ppt.
      by symmetry; apply (@Wtil_rec_beta_ppt A B f g C D).
  - refine (Wtil_ind _ (fun a x => 1) _). intros b y.
    apply dpath_path_FFlr.
    rewrite concat_1p, concat_p1.
    rewrite Wtil_rec_beta_ppt.
      by symmetry; apply sWtil_rec_beta_ppt.
Defined.

End AssumeAxioms.
