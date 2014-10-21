(* -*- mode: coq; mode: visual-line -*- *)
(** * Comparing definitions of equivalence *)

Require Import HoTT.Basics.
Require Import Types.Sigma Types.Forall Types.Record Types.Paths Types.Prod Types.Arrow HProp.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables A B f.

Section AssumeFunext.
Context `{Funext}.

(** In this file we show that several different definitions of "equivalence" are all equivalent to the one we have chosen.  This also yields alternative proofs that [IsEquiv f] is an hprop. *)

(** ** Contractible maps *)

(** We say a map is "contractible" if all of its homotopy fibers are contractible.  (More generally, a map is n-truncated if all of its homotopy fibers are n-truncated.)  This was Voevodsky's first definition of equivalences in homotopy type theory.

   It is fairly straightforward to show that this definition is *logically* equivalent to the one we have given.
*)

Definition fcontr_isequiv `(f : A -> B)
  : IsEquiv f -> (forall b:B, Contr {a : A & f a = b}).
Proof.
  intros ? b.  exists (f^-1 b ; eisretr f b).  intros [a p].
  refine (path_sigma' _ ((ap f^-1 p)^ @ eissect f a) _).
  rewrite (transport_compose (fun y => y = b) f _ _), transport_paths_l.
  rewrite ap_pp, ap_V, <- ap_compose, inv_Vp, concat_pp_p.
  unfold compose; rewrite (concat_A1p (eisretr f) p).
  rewrite eisadj.  by apply concat_V_pp.
Defined.

Definition isequiv_fcontr `(f : A -> B)
  : (forall b:B, Contr {a : A & f a = b}) -> IsEquiv f.
Proof.
  intros ?. refine (BuildIsEquiv _ _ _
    (fun b => (center {a : A & f a = b}).1)
    (fun b => (center {a : A & f a = b}).2)
    (fun a => (@contr {x : A & f x = f a} _ (a;1))..1)
    _).
  intros a. apply moveL_M1.
  rewrite <- transport_paths_l, <- transport_compose.
  exact ((@contr {x : A & f x = f a} _ (a;1))..2).
Defined.

(** Therefore, since both are hprops, they are equivalent by [equiv_iff_hprop].  However, we can also use this to *prove* that [IsEquiv] is an hprop.  We begin by showing that if [f] is an equivalence, then the type of sections of [f] and the type of retractions of [f] are both contractible. *)

Definition contr_sect_equiv `(f : A -> B) `{IsEquiv A B f}
  : Contr {g : B -> A & Sect g f}.
Proof.
  (* First we turn homotopies into paths. *)
  refine (contr_equiv' { g : B -> A & f o g = idmap } _).
  symmetry.
  refine (equiv_functor_sigma' (equiv_idmap _) _); intros g.
  exact (equiv_path_forall (f o g) idmap).
  (* Now this is just the fiber over [idmap] of postcomposition with [f], and the latter is an equivalence since [f] is. *)
  apply fcontr_isequiv; exact _.
Defined.

Definition contr_retr_equiv `(f : A -> B) `{IsEquiv A B f}
  : Contr {g : B -> A & Sect f g}.
Proof.
  (* This proof is just like the previous one. *)
  refine (contr_equiv' { g : B -> A & g o f = idmap } _).
  symmetry.
  refine (equiv_functor_sigma' (equiv_idmap _) _); intros g.
  exact (equiv_path_forall (g o f) idmap).
  apply fcontr_isequiv; exact _.
Defined.

(** Using this, we can prove that [IsEquiv f] is an h-proposition.  We make this a [Local Instance] since we already have a [Global Instance] of it available in [types/Universe].  *)

Local Instance hprop_isequiv `(f : A -> B) : IsHProp (IsEquiv f).
Proof.
  apply hprop_inhabited_contr; intros ?.
  (* Get rid of that pesky record. *)
  refine (contr_equiv _ (issig_isequiv f)).
  (* Now we claim that the top two elements, [s] and the coherence relation, taken together are contractible, so we can peel them off. *)
  refine (contr_equiv' {g : B -> A & Sect g f}
    (equiv_inverse (equiv_functor_sigma' (equiv_idmap (B -> A))
      (fun g => (@equiv_sigma_contr (Sect g f)
        (fun r => {s : Sect f g & forall x, r (f x) = ap f (s x) })
        _))))).
  (* What remains afterwards is just the type of sections of [f]. *)
  2:apply contr_sect_equiv; assumption.
  intros r.
  (* Now we claim this is equivalent to a certain space of paths. *)
  refine (contr_equiv'
    (forall x, (existT (fun a => f a = f x) x 1) = (g (f x); r (f x)))
    (equiv_inverse _)).
  (* The proof of this equivalence is basically just rearranging quantifiers and paths. *)
  refine (equiv_compose' _ (equiv_sigT_coind (fun x => g (f x) = x)
      (fun x p => r (f x) = ap f p))).
  refine (equiv_functor_forall' (equiv_idmap A) _); intros a; simpl.
  refine (equiv_compose' (equiv_path_inverse _ _) _).
  refine (equiv_compose' (equiv_path_sigma (fun x => f x = f a)
    (g (f a) ; r (f a)) (a ; 1)) _); simpl.
  refine (equiv_functor_sigma' (equiv_idmap _) _); intros p; simpl.
  rewrite (transport_compose (fun y => y = f a) f), transport_paths_l.
  refine (equiv_compose' (equiv_moveR_Vp _ _ _) _).
  by rewrite concat_p1; apply equiv_idmap.
  (* Finally, this is a space of paths in a fiber of [f]. *)
  refine (@contr_forall _ _ _ _); intros a.
  refine (@contr_paths_contr _ _ _ _).
  by refine (fcontr_isequiv f _ _).
Qed.

(** Now since [IsEquiv f] and the assertion that its fibers are contractible are both HProps, logical equivalence implies equivalence. *)

Definition equiv_fcontr_isequiv `(f : A -> B)
  : (forall b:B, Contr {a : A & f a = b}) <~> IsEquiv f.
Proof.
  apply equiv_iff_hprop.
  by apply isequiv_fcontr.
  by apply fcontr_isequiv.
Defined.

(** Alternatively, we could also construct this equivalence directly, and derive the fact that [IsEquiv f] is an HProp from that.  *)

Local Definition equiv_fcontr_isequiv' `(f : A -> B)
  : (forall b:B, Contr {a : A & f a = b}) <~> IsEquiv f.
Proof.
  (* First we get rid of those pesky records. *)
  refine (equiv_compose' _ (equiv_functor_forall idmap
    (fun b => equiv_inverse (issig_contr {a : A & f a = b})))).
  refine (equiv_compose' (issig_isequiv f) _).
  (* Now we can really get to work.
     First we peel off the inverse function and the [eisretr]. *)
  refine (equiv_compose' _ (equiv_inverse (equiv_sigT_coind _ _))).
  refine (equiv_compose' _ (equiv_inverse
    (@equiv_functor_sigma' _ _ _ (fun f0 => forall x y, f0 x = y)
      (equiv_sigT_coind _ _)
      (fun fg => equiv_idmap (forall x y,
        (equiv_sigT_coind _ (fun b a => f a = b) fg x = y)))))).
  refine (equiv_compose' _ (equiv_inverse (equiv_sigma_assoc
    (fun g => forall x, f (g x) = x)
    (fun gh => forall x y,
      (fun b => (gh.1 b; gh.2 b)) x = y)))).
  refine (equiv_functor_sigma' (equiv_idmap _) _). intros g.
  refine (equiv_functor_sigma' (equiv_idmap _) _). intros r. simpl.
  (* Now we use the fact that Paulin-Mohring J is an equivalence. *)
  refine (equiv_compose' _ (equiv_inverse (@equiv_functor_forall' _ _
    (fun x => forall a (y : f a = x),
      (existT (fun a => f a = x) (g x) (r x)) = (a;y))
    _ _ (equiv_idmap _)
    (fun x:B => equiv_sigT_ind
      (fun y:exists a:A, f a = x => (g x;r x) = y))))).
  refine (equiv_compose' _ (equiv_flip _)).
  refine (equiv_compose' _ (equiv_inverse (@equiv_functor_forall' _ _
    (fun a => existT (fun a' => f a' = f a) (g (f a)) (r (f a)) = (a;1))
    _ _ (equiv_idmap A)
    (fun a => equiv_paths_ind (f a)
      (fun b y => (existT (fun a => f a = b) (g b) (r b)) = (a;y)))))).
  (* We identify the paths in a Sigma-type. *)
  refine (equiv_compose' _ (equiv_inverse (@equiv_functor_forall' _ _
    (fun a =>
      exists p, transport (fun a' : A => f a' = f a) p (r (f a)) = 1)
    _ _ (equiv_idmap A)
    (fun a => equiv_path_sigma (fun a' => f a' = f a)
      (g (f a);r (f a)) (a;1))))).
  (* Now we can peel off the [eissect]. *)
  refine (equiv_compose' _ (equiv_inverse (equiv_sigT_coind
    (fun a => g (f a) = a)
    (fun a p => transport (fun a' => f a' = f a) p (r (f a)) = 1)))).
  refine (equiv_functor_sigma' (equiv_idmap _) _). intros s.
  (* And what's left is the [eisadj]. *)
  refine (equiv_functor_forall' (equiv_idmap _) _). intros a; simpl.
  refine (equiv_compose' _ (equiv_concat_l
             (transport_compose (fun b => b = f a) f (s a) (r (f a))
              @ transport_paths_l (ap f (s a)) (r (f a)))^ 1)).
  exact (equiv_compose'
    (equiv_concat_r (concat_p1 _) _)
    (equiv_inverse (equiv_moveR_Vp (r (f a)) 1 (ap f (s a))))).
Defined.

(** ** Bi-invertible maps *)

(** A map is "bi-invertible" if it has both a section and a retraction, not necessarily the same.  This definition of equivalence was proposed by Andre Joyal. *)

Definition BiInv `(f : A -> B) : Type
  := {g : B -> A & Sect f g} * {h : B -> A & Sect h f}.

(** It seems that the easiest way to show that bi-invertibility is equivalent to being an equivalence is also to show that both are h-props and that they are logically equivalent. *)

Definition equiv_biinv `(f : A -> B)
  : BiInv f -> IsEquiv f.
Proof.
  intros [[g s] [h r]].
  exact (isequiv_adjointify f g
    (fun x => ap f (ap g (r x)^ @ s (h x))  @ r x)
    s).
Defined.

Global Instance isprop_biinv `(f : A -> B) : IsHProp (BiInv f) | 0.
Proof.
  apply hprop_inhabited_contr.
  intros bif; pose (fe := equiv_biinv f bif).
  apply @contr_prod.
  (* For this, we've done all the work already. *)
  by apply contr_retr_equiv.
  by apply contr_sect_equiv.
Defined.

Definition equiv_biinv_equiv `(f : A -> B)
  : BiInv f <~> IsEquiv f.
Proof.
  apply equiv_iff_hprop.
  by apply equiv_biinv.
  intros ?.  split.
  by exists (f^-1); apply eissect.
  by exists (f^-1); apply eisretr.
Defined.

End AssumeFunext.
