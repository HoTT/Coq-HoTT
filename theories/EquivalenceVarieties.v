(* -*- mode: coq; mode: visual-line -*- *)
(** * Comparing definitions of equivalence *)

Require Import Overture PathGroupoids Equivalences Trunc HProp.
Require Import Sigma Forall Record Paths Prod.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables A B f.

Section AssumeFunext.
Context `{Funext}.

(** In this file we show that several different definitions of "equivalence" are all equivalent to the one we have chosen. *)

(** ** Contractible maps *)

(** We say a map is "contractible" if all of its homotopy fibers are contractible.  (More generally, a map is n-truncated if all of its homotopy fibers are n-truncated.)  This was Voevodsky's first definition of equivalences in homotopy type theory.  The most conceptual way to show that this notion is equivalent to our definition of [IsEquiv] is by "rearranging sigmas and pis" and using the universal property of Paulin-Mohring J.

   TODO: There is a lot of bookkeeping in this proof.  Can we set things up so that Coq can do more inference for us? *)

Definition equiv_fcontr_isequiv `(f : A -> B)
  : (forall b:B, Contr {a : A & f a = b}) <~> IsEquiv f.
Proof.
  (* First we get rid of those pesky records. *)
  refine (equiv_compose' _ (equiv_functor_forall idmap
    (fun b => equiv_inverse (issig_contr {a : A & f a = b})))).
  refine (equiv_compose' (issig_isequiv f) _).
  (* Now we can really get to work.
     First we peel off the inverse function and the [eisretr]. *)
  refine (equiv_compose' _ (equiv_inverse (equiv_sigT_corect _ _))).
  refine (equiv_compose' _ (equiv_inverse
    (@equiv_functor_sigma' _ _ _ (fun f0 => forall x y, f0 x = y)
      (equiv_sigT_corect _ _)
      (fun fg => equiv_idmap (forall x y,
        (equiv_sigT_corect _ (fun b a => f a = b) fg x = y)))))).
  refine (equiv_compose' _ (equiv_inverse (equiv_sigma_assoc
    (fun g => forall x, f (g x) = x)
    (fun gh => forall x y,
      (let (g, h) return (forall b, exists a, (f a) = b)
        := gh in fun b => (g b; h b)) x = y)))).
  refine (equiv_functor_sigma' (equiv_idmap _) _). intros g.
  refine (equiv_functor_sigma' (equiv_idmap _) _). intros r. simpl.
  (* Now we use the fact that Paulin-Mohring J is an equivalence. *)
  refine (equiv_compose' _ (equiv_inverse (@equiv_functor_forall' _ _
    (fun x => forall a (y : f a = x),
      (existT (fun a => f a = x) (g x) (r x)) = (a;y))
    _ _ (equiv_idmap _)
    (fun x:B => equiv_sigT_rect
      (fun y:exists a:A, f a = x => (g x;r x) = y))))).
  refine (equiv_compose' _ (equiv_flip _)).
  refine (equiv_compose' _ (equiv_inverse (@equiv_functor_forall' _ _
    (fun a => existT (fun a' => f a' = f a) (g (f a)) (r (f a)) = (a;1))
    _ _ (equiv_idmap A)
    (fun a => equiv_paths_rect (f a)
      (fun b y => (existT (fun a => f a = b) (g b) (r b)) = (a;y)))))).
  (* We identify the paths in a Sigma-type. *)
  refine (equiv_compose' _ (equiv_inverse (@equiv_functor_forall' _ _
    (fun a =>
      exists p, transport (fun a' : A => f a' = f a) p (r (f a)) = 1)
    _ _ (equiv_idmap A)
    (fun a => equiv_path_sigma (fun a' => f a' = f a)
      (g (f a);r (f a)) (a;1))))).
  (* Now we can peel off the [eissect]. *)
  refine (equiv_compose' _ (equiv_inverse (equiv_sigT_corect
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

Definition isequiv_fcontr `(f : A -> B)
  : (forall b:B, Contr {a : A & f a = b}) -> IsEquiv f
  := equiv_fcontr_isequiv f.

Definition fcontr_equiv `(f : A -> B) `{IsEquiv A B f}
  : forall b:B, Contr {a : A & f a = b}
  := (equiv_fcontr_isequiv f)^-1 _.

(** Since contractibility is an HProp, it follows that so is [IsEquiv f].  This might be the easiest way to prove that our definition of [IsEquiv f] is an HProp. *)

Instance hprop_isequiv `(f : A -> B) : IsHProp (IsEquiv f).
Proof.
  refine (trunc_equiv (equiv_fcontr_isequiv f)).
Defined.


(** ** Bi-invertible maps *)

(** A map is "bi-invertible" if it has both a section and a retraction, not necessarily the same.  This definition of equivalence was proposed by Andre Joyal. *)

Definition BiInv `(f : A -> B) : Type
  := {g : B -> A & Sect f g} * {h : B -> A & Sect h f}.

(** It seems that the easiest way to show that bi-invertibility is equivalent to being an equivalence is to show that both are h-props and that they are logically equivalent. *)

Definition equiv_biinv `(f : A -> B)
  : BiInv f -> IsEquiv f.
Proof.
  intros [[g s] [h r]].
  apply isequiv_adjointify with g.
  - intros x.
    path_via (f (h x)). apply ap.
    path_via (g (f (h x))).
    exact (ap g (r x)^).
  - assumption.
Defined.

Instance isprop_biinv `(f : A -> B) : IsHProp (BiInv f).
Proof.
  (* We may as well assume [f] to be an equivalence. *)
  apply hprop_inhabited_contr.
  intros bif; pose (fe := equiv_biinv f bif).
  (* Now we can split into the two halves. *)
  apply @contr_prod.
  (* For the first half, we change homotopies into paths. *)
  - refine (@contr_equiv' { g : B -> A & g o f = idmap } _ _ _).
    + apply symmetry.
      (* Then we use the fact that precomposing with an equivalence is an equivalence. *)
      refine (equiv_functor_sigma' (equiv_idmap _) _); intros g.
      exact (equiv_path_forall (g o f) idmap).
    + apply equiv_fcontr_isequiv; exact _.
  (* The other half is similar. *)
  - refine (@contr_equiv' { h : B -> A & f o h = idmap } _ _ _).
    + apply symmetry.
      refine (equiv_functor_sigma' (equiv_idmap _) _); intros h.
      exact (equiv_path_forall (f o h) idmap).
    + apply equiv_fcontr_isequiv; exact _.
Defined.

Definition equiv_biinv_equiv `(f : A -> B)
  : BiInv f <~> IsEquiv f.
Proof.
  apply equiv_iff_hprop.
  - apply equiv_biinv.
  - intros ?.  split.
    + exists (f^-1). apply eissect.
    + exists (f^-1). apply eisretr.
Defined.

End AssumeFunext.
