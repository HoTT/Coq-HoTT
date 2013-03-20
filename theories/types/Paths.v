(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about path spaces *)

Require Import Overture PathGroupoids Equivalences.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

Generalizable Variables A B f x y z.

(** ** Path spaces *)

(** The path spaces of a path space are not, of course, determined; they are just the higher-dimensional structure of the original space. *)

(** ** Transporting in path spaces.

   There are potentially a lot of these lemmas, so we adopt a uniform naming scheme.  The letter `l` means the left endpoint varies, while `r` means the right endpoint varies.  A letter `F` means application of a function to that (varying) endpoint. *)

Definition transport_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y)
  : transport (fun x => x = y) p q = p^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  : transport (fun y => x = y) p q = q @ p.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_lr {A : Type} {x1 x2 : A} (p : x1 = x2) (q : x1 = x1)
  : transport (fun x => x = x) p q = p^ @ q @ p.
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y)
  : transport (fun x => f x = y) p q = (ap f p)^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_Fr {A B : Type} {g : A -> B} {y1 y2 : A} {x : B}
  (p : y1 = y2) (q : x = g y1)
  : transport (fun y => x = g y) p q = q @ (ap g p).
Proof.
  destruct p. apply symmetry, concat_p1.
Defined.

Definition transport_paths_FlFr {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1)
  : transport (fun x => f x = g x) p q = (ap f p)^ @ q @ (ap g p).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FFlr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = x1)
  : transport (fun x => g (f x) = x) p q = (ap g (ap f p))^ @ q @ p.
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_lFFr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = g (f x1))
  : transport (fun x => x = g (f x)) p q = p^ @ q @ (ap g (ap f p)).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.


(** ** Functorial action *)

(** 'functor_path' is called [ap]. *)

(** ** Equivalences between path spaces *)

(** If [f] is an equivalence, then so is [ap f].  We are lazy and use [adjointify]. *)
Instance isequiv_ap `{IsEquiv A B f} (x y : A)
  : IsEquiv (@ap A B f x y)
  := isequiv_adjointify (ap f)
  (fun q => (eissect f x)^  @  ap f^-1 q  @  eissect f y)
  (fun q =>
    ap_pp f _ _
    @ whiskerR (ap_pp f _ _) _
    @ ((ap_V f _ @ inverse2 (eisadj f _)^)
      @@ (ap_compose f^-1 f _)^
      @@ (eisadj f _)^)
    @ concat_pA1_p (eisretr f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _)
  (fun p =>
    whiskerR (whiskerL _ (ap_compose f f^-1 _)^) _
    @ concat_pA1_p (eissect f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _).

Definition equiv_ap `(f : A -> B) `{IsEquiv A B f} (x y : A)
  : (x = y) <~> (f x = f y)
  := BuildEquiv _ _ (ap f) _.

(* TODO: Is this really necessary? *)
Definition equiv_inj `{IsEquiv A B f} {x y : A}
  : (f x = f y) -> (x = y)
  := (ap f)^-1.

(** ** Path operations are equivalences *)

Instance isequiv_path_inverse {A : Type} (x y : A)
  : IsEquiv (@inverse A x y)
  := BuildIsEquiv _ _ _ (@inverse A y x) (@inv_V A y x) (@inv_V A x y) _.
Proof.
  intros p; destruct p; reflexivity.
Defined.

Definition equiv_path_inverse {A : Type} (x y : A)
  : (x = y) <~> (y = x)
  := BuildEquiv _ _ (@inverse A x y) _.

Instance isequiv_concat_l {A : Type} `(p : x = y) (z : A)
  : IsEquiv (@concat A x y z p)
  := BuildIsEquiv _ _ _ (@concat A y x z p^)
     (concat_p_Vp p) (concat_V_pp p) _.
Proof.
  intros q; destruct p; destruct q; reflexivity.
Defined.

Definition equiv_concat_l {A : Type} `(p : x = y) (z : A)
  : (y = z) <~> (x = z)
  := BuildEquiv _ _ (concat p) _.

Instance isequiv_concat_r {A : Type} `(p : y = z) (x : A)
  : IsEquiv (fun q:x=y => q @ p)
  := BuildIsEquiv _ _ (fun q => q @ p) (fun q => q @ p^)
     (fun q => concat_pV_p q p) (fun q => concat_pp_V q p) _.
Proof.
  intros q; destruct p; destruct q; reflexivity.
Defined.

Definition equiv_concat_r {A : Type} `(p : y = z) (x : A)
  : (x = y) <~> (x = z)
  := BuildEquiv _ _ (fun q => q @ p) _.

(* We can use these to build up more complicated equivalences.  Here's an example. *)
Definition equiv_moveR_Vp {A : Type} {x y z : A}
  (p : x = z) (q : y = z) (r : x = y)
  : (p = r @ q) <~> (r^ @ p = q)
  := equiv_compose'
       (equiv_concat_r (concat_V_pp r q) (r^ @ p))
       (equiv_ap (equiv_concat_l r^ z) p (r @ q)).


(** *** Dependent paths *)

(** Usually, a dependent path over [p:x1=x2] in [P:A->Type] between [y1:P x1] and [y2:P x2] is a path [transport P p y1 = y2] in [P x2].  However, when [P] is a path space, these dependent paths have a more convenient description: rather than transporting the left side both forwards and backwards, we transport both sides of the equation forwards, forming a sort of "naturality square".

   We use the same naming scheme as for the transport lemmas. *)

Definition dpath_path_l {A : Type} {x1 x2 y : A}
  (p : x1 = x2) (q : x1 = y) (r : x2 = y)
  : q = p @ r
  <~>
  transport (fun x => x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_r (concat_1p r) q).
Defined.

Definition dpath_path_r {A : Type} {x y1 y2 : A}
  (p : y1 = y2) (q : x = y1) (r : x = y2)
  : q @ p = r
  <~>
  transport (fun y => x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_lr {A : Type} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = x1) (r : x2 = x2)
  : q @ p = p @ r
  <~>
  transport (fun x => x = x) p q = r.
Proof.
  destruct p; simpl.
  refine (equiv_compose' (B := (q @ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)^ r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
Defined.

Definition dpath_path_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y) (r : f x2 = y)
  : q = ap f p @ r
  <~>
  transport (fun x => f x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_r (concat_1p r) q).
Defined.

Definition dpath_path_Fr {A B : Type} {g : A -> B} {x : B} {y1 y2 : A}
  (p : y1 = y2) (q : x = g y1) (r : x = g y2)
  : q @ ap g p = r
  <~>
  transport (fun y => x = g y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_FlFr {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1) (r : f x2 = g x2)
  : q @ ap g p = ap f p @ r
  <~>
  transport (fun x => f x = g x) p q = r.
Proof.
  destruct p; simpl.
  refine (equiv_compose' (B := (q @ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)^ r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
Defined.

Definition dpath_path_FFlr {A B : Type} {f : A -> B} {g : B -> A}
  {x1 x2 : A} (p : x1 = x2) (q : g (f x1) = x1) (r : g (f x2) = x2)
  : q @ p = ap g (ap f p) @ r
  <~>
  transport (fun x => g (f x) = x) p q = r.
Proof.
  destruct p; simpl.
  refine (equiv_compose' (B := (q @ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)^ r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
Defined.

Definition dpath_path_lFFr {A B : Type} {f : A -> B} {g : B -> A}
  {x1 x2 : A} (p : x1 = x2) (q : x1 = g (f x1)) (r : x2 = g (f x2))
  : q @ ap g (ap f p) = p @ r
  <~>
  transport (fun x => x = g (f x)) p q = r.
Proof.
  destruct p; simpl.
  refine (equiv_compose' (B := (q @ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)^ r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
Defined.


(** ** Universal mapping property *)

Instance isequiv_paths_rect `{Funext} {A : Type} (a : A)
  (P : forall x, (a = x) -> Type)
  : IsEquiv (paths_rect a P)
  := isequiv_adjointify (paths_rect a P) (fun f => f a 1) _ _.
Proof.
  - intros f.
    apply path_forall; intros x.
    apply path_forall; intros p.
    destruct p; reflexivity.
  - intros u. reflexivity.
Defined.

Definition equiv_paths_rect `{Funext} {A : Type} (a : A)
  (P : forall x, (a = x) -> Type)
  : P a 1 <~> forall x p, P x p
  := BuildEquiv _ _ (paths_rect a P) _.

(** ** Truncation *)

(** Paths reduce truncation level by one.  This is essentially the definition of [IsTrunc_internal]. *)
