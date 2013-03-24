(* -*- mode: coq; mode: visual-line -*- *)

(** * The flattening lemma. *)

Require Import Overture PathGroupoids Equivalences.
Require Import Paths Forall Sigma Arrow Universe.
Local Open Scope path_scope.
Local Open Scope equiv_scope.


(* Some lemmas that ought to go elsewhere. *)

Definition transport_path_sigma {A:Type} (B:A->Type) (C:sigT B -> Type)
  (x1 x2:A) (p:x1=x2) (y1:B x1) (y2:B x2) (q:p # y1 = y2) (z:C (x1;y1))
  : transport C (path_sigma' B p q) z
  = transport C (ap (existT B x2) q)
      (transportD B (fun a b => C (a;b)) p y1 z).
Proof.
  destruct p. destruct q. reflexivity.
Defined.

Definition ap_sigT_rect_path_sigma {A : Type} (P : A -> Type) {Q : Type}
  (x1 x2:A) (p:x1=x2) (y1:P x1) (y2:P x2) (q:p # y1 = y2)
  (d : forall a, P a -> Q)
  : ap (sigT_rect (fun _ => Q) d) (path_sigma' P p q)
  = (ap (d x1) (transport_Vp _ p y1))^
  @ (transport_const p _)^
  @ (transport_arrow p _ _)^
  @ apD10 (apD d p) (p # y1)
  @ ap (d x2) q.
Proof.
  destruct p. destruct q. reflexivity.
Defined.


(* First we define the general non-recursive HIT. *)

Module Export BaseHIT.

Local Inductive W (A B : Type) (f g : B -> A) : Type :=
| cc : A -> W A B f g.

Arguments cc {A B f g} a.

Axiom pp : forall {A B f g} (b:B), @cc A B f g (f b) = cc (g b).

Definition W_rect {A B f g} (P : W A B f g -> Type)
  (cc' : forall a, P (cc a))
  (pp' : forall b, (pp b) # (cc' (f b)) = cc' (g b))
  : forall w, P w
  := fun w => match w with cc a => cc' a end.

Axiom W_rect_beta_pp
  : forall {A B f g} (P : W A B f g -> Type) (cc' : forall a, P (cc a))
  (pp' : forall b, (pp b) # (cc' (f b)) = cc' (g b)) (b:B),
  apD (W_rect P cc' pp') (pp b) = pp' b.

End BaseHIT.

Definition W_rectnd {A B f g} (P : Type) (cc' : A -> P)
  (pp' : forall b, cc' (f b) = cc' (g b))
  : W A B f g -> P
  := W_rect (fun _ => P) cc' (fun b => transport_const _ _ @ pp' b).

Definition W_rectnd_beta_pp {A B f g} (P : Type) (cc' : A -> P)
  (pp' : forall b:B, cc' (f b) = cc' (g b)) (b:B)
  : ap (W_rectnd P cc' pp') (pp b) = pp' b.
Proof.
  unfold W_rectnd.
  refine (cancelL (transport_const (pp b) _) _ _ _).
  refine ((apD_const (@W_rect A B f g (fun _ => P) cc' _) (pp b))^ @ _).
  refine (W_rect_beta_pp (fun _ => P) _ _ _).
Defined.



(* Now we define the flattened HIT which will be equivalent to the total space of a fibration over [W]. *)

Module Export FlattenedHIT.

Local Inductive Wtil (A B : Type) (f g : B -> A)
  (C : A -> Type) (D : forall b, C (f b) <~> C (g b))
  : Type :=
| cct : forall a, C a -> Wtil A B f g C D.

Arguments cct {A B f g C D} a c.

Axiom ppt : forall {A B f g C D} (b:B) (y:C (f b)),
  @cct A B f g C D (f b) y = cct (g b) (D b y).

Definition Wtil_rect {A B f g C D} (Q : Wtil A B f g C D -> Type)
  (cct' : forall a x, Q (cct a x))
  (ppt' : forall b y, (ppt b y) # (cct' (f b) y) = cct' (g b) (D b y))
  : forall w, Q w
  := fun w => match w with cct a x => cct' a x end.

Axiom Wtil_rect_beta_ppt
  : forall {A B f g C D} (Q : Wtil A B f g C D -> Type)
    (cct' : forall a x, Q (cct a x))
    (ppt' : forall b y, (ppt b y) # (cct' (f b) y) = cct' (g b) (D b y))
    (b:B) (y : C (f b)),
    apD (Wtil_rect Q cct' ppt') (ppt b y) = ppt' b y.

End FlattenedHIT.

Definition Wtil_rectnd {A B f g C} {D : forall b, C (f b) <~> C (g b)}
  (Q : Type) (cct' : forall a (x : C a), Q)
  (ppt' : forall b (y : C (f b)), cct' (f b) y = cct' (g b) (D b y))
  : Wtil A B f g C D -> Q
  := Wtil_rect (fun _ => Q) cct' (fun b y => transport_const _ _ @ ppt' b y).

Definition Wtil_rectnd_beta_ppt
  {A B f g C} {D : forall b, C (f b) <~> C (g b)}
  (Q : Type) (cct' : forall a (x : C a), Q)
  (ppt' : forall (b:B) (y : C (f b)), cct' (f b) y = cct' (g b) (D b y))
  (b:B) (y: C (f b))
  : ap (@Wtil_rectnd A B f g C D Q cct' ppt') (ppt b y) = ppt' b y.
Proof.
  unfold Wtil_rectnd.
  refine (cancelL (transport_const (ppt b y) _) _ _ _).
  refine ((apD_const
    (@Wtil_rect A B f g C D (fun _ => Q) cct' _) (ppt b y))^ @ _).
  refine (Wtil_rect_beta_ppt (fun _ => Q) _ _ _ _).
Defined.



(* Now we define the fibration over it that we will be considering the total space of. *)

Section AssumeAxioms.
Context `{Funext} `{Univalence}.

Context {A B : Type} {f g : B -> A}.
Context {C : A -> Type} {D : forall b, C (f b) <~> C (g b)}.

Let W' := W A B f g.

Let P : W' -> Type
  := W_rectnd Type C (fun b => path_universe (D b)).



(* Now we give the total space the same structure as [Wtil]. *)

Let sWtil := { w:W' & P w }.

Let scct (a:A) (x:C a) : sWtil := (existT P (cc a) x).

Let sppt (b:B) (y:C (f b)) : scct (f b) y = scct (g b) (D b y).
Proof.
  refine (path_sigma' P (pp b) _).
  refine (transport_path_universe' P (pp b) (D b) _ _).
  refine (W_rectnd_beta_pp _ _ _ _).
Defined.

(* Here is the dependent eliminator *)
Definition sWtil_rect (Q : sWtil -> Type)
  (scct' : forall a x, Q (scct a x))
  (sppt' : forall b y, (sppt b y) # (scct' (f b) y) = scct' (g b) (D b y))
  : forall w, Q w.
Proof.
  apply sigT_rect.
  refine (W_rect (fun w => forall x:P w, Q (w;x))
    (fun a x => scct' a x) _).
  intros b.
  apply (dpath_forall P (fun a b => Q (a;b)) _ _ (pp b)
    (scct' (f b)) (scct' (g b))).
  intros y.
  set (q := transport_path_universe' P (pp b) (D b)
    (W_rectnd_beta_pp Type C (fun b0 : B => path_universe (D b0)) b) y).
  refine ((ap (transport Q (ap (existT P (cc (g b))) q)))^-1 _).
  refine ((transport_path_sigma P Q _ _ (pp b) _ _ q _)^ @ _).
  refine (sppt' b y @ _).
  refine ((apD (scct' (g b)) q)^ @ _).
  exact (transport_compose Q (existT P (cc (g b))) q _).
Defined.

(* The eliminator computes on the point constructor. *)
Definition sWtil_rect_beta_cct (Q : sWtil -> Type)
  (scct' : forall a x, Q (scct a x))
  (sppt' : forall b y, (sppt b y) # (scct' (f b) y) = scct' (g b) (D b y))
  (a:A) (x:C a)
  : sWtil_rect Q scct' sppt' (scct a x) = scct' a x
  := 1.

(* This would be its propositional computation rule on the path constructor... *)
Definition sWtil_rect_beta_ppt (Q : sWtil -> Type)
  (scct' : forall a x, Q (scct a x))
  (sppt' : forall b y, (sppt b y) # (scct' (f b) y) = scct' (g b) (D b y))
  (b:B) (y:C (f b))
  : apD (sWtil_rect Q scct' sppt') (sppt b y) = sppt' b y.
Proof.
  unfold sWtil_rect.
  (* ... but it's a doozy! *)
Abort.

(* Fortunately, it turns out to be enough to have the computation rule for the *non-dependent* eliminator! *)

(* We could define that in terms of the dependent one, as usual...
Definition sWtil_rectnd (P : Type) 
  (scct' : forall a (x : C a), P)
  (sppt' : forall b (y : C (f b)), scct' (f b) y = scct' (g b) (D b y))
  : sWtil -> P
  := sWtil_rect (fun _ => P) scct' (fun b y => transport_const _ _ @ sppt' b y).
*)

(* ...but if we define it directly, then it's easier to reason about. *)
Definition sWtil_rectnd (Q : Type) 
  (scct' : forall a (x : C a), Q)
  (sppt' : forall b (y : C (f b)), scct' (f b) y = scct' (g b) (D b y))
  : sWtil -> Q.
Proof.
  apply sigT_rect.
  refine (W_rect (fun w => P w -> Q) (fun a x => scct' a x) _).
  intros b.
  apply path_forall; intros x.
  refine (@transport_arrow W' P (fun _ => Q) _ _ _ _ _ @ _).
  refine (transport_const _ _ @ _).
  refine (sppt' b _ @ _).
  apply ap.
  refine ((transport_path_universe' P (pp b) (D b) _ _)^ @ _).
  exact (W_rectnd_beta_pp _ _ _ _).
  by apply transport_pV.
Defined.

(* Buckle your seat belts. *)
Open Scope long_path_scope.

Definition sWtil_rectnd_beta_ppt (Q : Type) 
  (scct' : forall a (x : C a), Q)
  (sppt' : forall b (y : C (f b)), scct' (f b) y = scct' (g b) (D b y))
  (b:B) (y: C (f b))
  : ap (sWtil_rectnd Q scct' sppt') (sppt b y) = sppt' b y.
Proof.
  unfold sWtil_rectnd, sppt.
  refine (@ap_sigT_rect_path_sigma W' P Q _ _ (pp b) _ _ _ _ @ _); simpl.
  rewrite (@W_rect_beta_pp A B f g).
  rewrite apD10_path_forall.
  (* This equality is everywhere *)
  set (q := transport_path_universe' P (pp b) (D b)
    (W_rectnd_beta_pp Type C (fun b0 : B => path_universe (D b0)) b)).
  repeat rewrite concat_p_pp.
  (* And now things cancel like magic! *)
  repeat rewrite concat_pV_p.
  (* Now we can apply naturality *)
  rewrite transport_pVp.
  refine (whiskerR (whiskerL _ (ap02 (scct' (g b))
    (concat_Ap (fun u => (q u)^) (transport_Vp P (pp b) y))^)) _ @ _).
  rewrite concat_pp_p, <- ap_pp, concat_pV_p, <- ap_compose, concat_pp_p.
  (* More naturality *)
  refine (whiskerL _ (concat_Ap (sppt' b) (transport_Vp P (pp b) y))^ @ _).
  by apply concat_V_pp. 
Qed.

Close Scope long_path_scope.

(* Woot! *)
Definition equiv_flattening : Wtil A B f g C D <~> sWtil.
Proof.
  (* The maps back and forth are obtained easily from the non-dependent eliminators. *)
  refine (equiv_adjointify
    (Wtil_rectnd _ scct sppt)
    (sWtil_rectnd _ cct ppt)
    _ _).
  (* The two homotopies are completely symmetrical, using the *dependent* eliminators, but only the computation rules for the non-dependent ones. *)
  refine (sWtil_rect _ (fun a x => 1) _). intros b y.
  apply dpath_path_FFlr.
  rewrite concat_1p, concat_p1.
  rewrite sWtil_rectnd_beta_ppt.
  by apply symmetry, (@Wtil_rectnd_beta_ppt A B f g C D).
  refine (Wtil_rect _ (fun a x => 1) _). intros b y.
  apply dpath_path_FFlr.
  rewrite concat_1p, concat_p1.
  rewrite Wtil_rectnd_beta_ppt.
  by apply symmetry, sWtil_rectnd_beta_ppt.
Defined.

End AssumeAxioms.
