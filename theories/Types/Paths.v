(** * Theorems about path spaces *)

Require Import Basics.Overture Basics.Equivalences Basics.PathGroupoids Basics.Tactics.

Local Open Scope path_scope.

Generalizable Variables A B f x y z.

(** ** Path spaces *)

(** The path spaces of a path space are not, of course, determined; they are just the
    higher-dimensional structure of the original space. *)

(** ** Transporting in path spaces.

   There are potentially a lot of these lemmas, so we adopt a uniform naming scheme:

   - `l` means the left endpoint varies
   - `r` means the right endpoint varies
   - `F` means application of a function to that (varying) endpoint.
*)

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
  destruct p. symmetry; apply concat_p1.
Defined.

Definition transport_paths_FFl {A B C : Type} {f : A -> B} {g : B -> C}
  {x1 x2 : A} {y : C} (p : x1 = x2) (q : g (f x1) = y)
  : transport (fun x => g (f x) = y) p q = (ap g (ap f p))^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_FlFr {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1)
  : transport (fun x => f x = g x) p q = (ap f p)^ @ q @ (ap g p).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FlFr_D {A : Type} {B : A -> Type}
  {f g : forall a, B a} {x1 x2 : A} (p : x1 = x2) (q : f x1 = g x1)
: transport (fun x => f x = g x) p q
  = (apD f p)^ @ ap (transport B p) q @ (apD g p).
Proof.
  destruct p; simpl.
  exact ((ap_idmap _)^ @ (concat_1p _)^ @ (concat_p1 _)^).
Defined.

Definition transport_paths_Flr {A : Type} {f : A -> A} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = x1)
  : transport (fun x => f x = x) p q = (ap f p)^ @ q @ p.
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

Definition transport_paths_FFlFr {A B C : Type}
  {f : A -> B} {g : B -> C} {h : A -> C} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = h x1)
  : transport (fun x => g (f x) = h x) p q = (ap g (ap f p))^ @ q @ (ap h p).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FlFFr {A B C : Type}
  {f : A -> C} {g : B -> C} {h : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g (h x1))
  : transport (fun x => f x = g (h x)) p q = (ap f p)^ @ q @ (ap g (ap h p)).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FFlFFr {A B B' C : Type}
  {f : A -> B} {f' : A -> B'} {g : B -> C} {g' : B' -> C} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = g' (f' x1))
  : transport (fun x => g (f x) = g' (f' x)) p q = (ap g (ap f p))^ @ q @ (ap g' (ap f' p)).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

(** Variants of the above that do the most common rearranging. We could add similar variants for the others as needed. *)
Definition transport_paths_Flr' {A : Type} {f : A -> A} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = x1) (r : f x2 = x2)
  (h : (ap f p) @ r = q @ p)
  : transport (fun x => f x = x) p q = r.
Proof.
  refine (transport_paths_Flr _ _ @ _).
  refine (concat_pp_p _ _ _ @ _).
  apply moveR_Vp.
  exact h^.
Defined.

Definition transport_paths_FlFr' {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1) (r : (f x2) = (g x2))
  (h : (ap f p) @ r = q @ (ap g p))
  : transport (fun x => f x = g x) p q = r.
Proof.
  refine (transport_paths_FlFr _ _ @ _).
  refine (concat_pp_p _ _ _ @ _).
  apply moveR_Vp.
  exact h^.
Defined.

Definition transport_paths_FFlr' {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = x1) (r : g (f x2) = x2)
  (h : (ap g (ap f p)) @ r = q @ p)
  : transport (fun x => g (f x) = x) p q = r.
Proof.
  refine (transport_paths_FFlr _ _ @ _).
  refine (concat_pp_p _ _ _ @ _).
  apply moveR_Vp.
  exact h^.
Defined.

Definition transport_paths_FFlFr' {A B C : Type}
  {f : A -> B} {g : B -> C} {h : A -> C} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = h x1) (r : g (f x2) = h x2)
  (h' : (ap g (ap f p)) @ r = q @ (ap h p))
  : transport (fun x => g (f x) = h x) p q = r.
Proof.
  lhs nrapply (transport_paths_FFlFr p q).
  lhs nrapply concat_pp_p.
  apply moveR_Vp.
  exact h'^.
Defined.

Definition transport_paths_FlFFr' {A B C : Type}
  {f : A -> C} {g : B -> C} {h : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g (h x1)) (r : f x2 = g (h x2))
  (h' : (ap f p) @ r = q @ (ap g (ap h p)))
  : transport (fun x => f x = g (h x)) p q = r.
Proof.
  lhs nrapply (transport_paths_FlFFr p q).
  lhs nrapply concat_pp_p.
  apply moveR_Vp.
  exact h'^.
Defined.

Definition transport_paths_FFlFFr' {A B B' C : Type}
  {f : A -> B} {f' : A -> B'} {g : B -> C} {g' : B' -> C} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = g' (f' x1)) (r : g (f x2) = g' (f' x2))
  (h : ap g (ap f p) @ r = q @ ap g' (ap f' p))
  : transport (fun x => g (f x) = g' (f' x)) p q = r.
Proof.
  lhs nrapply (transport_paths_FFlFFr p q).
  lhs nrapply concat_pp_p.
  apply moveR_Vp.
  exact h^.
Defined.

Definition transport011_paths {A B X} (f : A -> X) (g : B -> X)
  {a1 a2 : A} {b1 b2 : B} (p : a1 = a2) (q : b1 = b2)
  (r : f a1 = g b1)
  : transport011 (fun a b => f a = g b) p q r = (ap f p)^ @ r @ ap g q.
Proof.
  destruct p, q; cbn.
  symmetry.
  lhs nrapply concat_p1.
  apply concat_1p.
Defined.

(** ** Transporting in 2-path types *)

Definition transport_paths2 {A : Type} {x y : A}
           (p : x = y) (q : idpath x = idpath x)
: transport (fun a => idpath a = idpath a) p q
  =  (concat_Vp p)^
    @ whiskerL p^ ((concat_1p p)^ @ whiskerR q p @ concat_1p p)
    @ concat_Vp p.
Proof.
  destruct p. simpl.
  refine (_ @ (concat_p1 _)^).
  refine (_ @ (concat_1p _)^).
  (** The tricky thing here is getting a sufficiently general statement that we can prove it by path induction. *)
  assert (H : forall (p : x = x) (q : 1 = p),
                (q @ (concat_p1 p)^) @ (concat_1p (p @ 1))^
                = whiskerL (idpath x) (idpath 1 @ whiskerR q 1 @ idpath (p @ 1))).
  { intros p' q'. destruct q'. reflexivity. }
  transitivity (q @ (concat_p1 1)^ @ (concat_1p 1)^).
  { simpl; exact ((concat_p1 _)^ @ (concat_p1 _)^). }
  refine (H 1 q).
Defined.

(** ** Functorial action *)

(** 'functor_path' is called [ap]. *)

(** ** Equivalences between path spaces *)

(** [isequiv_ap] and [equiv_ap] are in Equivalences.v  *)

(** ** Path operations are equivalences *)

Global Instance isequiv_path_inverse {A : Type} (x y : A)
  : IsEquiv (@inverse A x y) | 0.
Proof.
  refine (Build_IsEquiv _ _ _ (@inverse A y x)
                       (@inv_V A y x) (@inv_V A x y) _).
  intros p; destruct p; reflexivity.
Defined.

Definition equiv_path_inverse {A : Type} (x y : A)
  : (x = y) <~> (y = x)
  := Build_Equiv _ _ (@inverse A x y) _.

Global Instance isequiv_concat_l {A : Type} `(p : x = y:>A) (z : A)
  : IsEquiv (@transitivity A _ _ x y z p) | 0.
Proof.
  refine (Build_IsEquiv _ _ _ (concat p^)
                       (concat_p_Vp p) (concat_V_pp p) _).
  intros q; destruct p; destruct q; reflexivity.
Defined.

Definition equiv_concat_l {A : Type} `(p : x = y) (z : A)
  : (y = z) <~> (x = z)
  := Build_Equiv _ _ (concat p) _.

Global Instance isequiv_concat_r {A : Type} `(p : y = z) (x : A)
  : IsEquiv (fun q:x=y => q @ p) | 0.
Proof.
  refine (Build_IsEquiv _ _ (fun q => q @ p) (fun q => q @ p^)
           (fun q => concat_pV_p q p) (fun q => concat_pp_V q p) _).
  intros q; destruct p; destruct q; reflexivity.
Defined.

Definition equiv_concat_r {A : Type} `(p : y = z) (x : A)
  : (x = y) <~> (x = z)
  := Build_Equiv _ _ (fun q => q @ p) _.

Global Instance isequiv_concat_lr {A : Type} {x x' y y' : A} (p : x' = x) (q : y = y')
  : IsEquiv (fun r:x=y => p @ r @ q) | 0
  := @isequiv_compose _ _ (fun r => p @ r) _ _ (fun r => r @ q) _.

Definition equiv_concat_lr {A : Type} {x x' y y' : A} (p : x' = x) (q : y = y')
  : (x = y) <~> (x' = y')
  := Build_Equiv _ _ (fun r:x=y => p @ r @ q) _.

Definition equiv_p1_1q {A : Type} {x y : A} {p q : x = y}
  : p = q <~> p @ 1 = 1 @ q
  := equiv_concat_lr (concat_p1 p) (concat_1p q)^.

Definition equiv_1p_q1 {A : Type} {x y : A} {p q : x = y}
  : p = q <~> 1 @ p = q @ 1
  := equiv_concat_lr (concat_1p p) (concat_p1 q)^.

Global Instance isequiv_whiskerL {A} {x y z : A} (p : x = y) {q r : y = z}
: IsEquiv (@whiskerL A x y z p q r).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - apply cancelL.
  - intros k. unfold cancelL.
    rewrite !whiskerL_pp.
    refine ((_ @@ 1 @@ _) @ whiskerL_pVL p k).
    + destruct p, q; reflexivity.
    + destruct p, r; reflexivity.
  - intros k. unfold cancelL.
    refine ((_ @@ 1 @@ _) @ whiskerL_VpL p k).
    + destruct p, q; reflexivity.
    + destruct p, r; reflexivity.
Defined.

Definition equiv_whiskerL {A} {x y z : A} (p : x = y) (q r : y = z)
: (q = r) <~> (p @ q = p @ r)
  := Build_Equiv _ _ (whiskerL p) _.

Definition equiv_cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
: (p @ q = p @ r) <~> (q = r)
  := equiv_inverse (equiv_whiskerL p q r).

Definition isequiv_cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
  : IsEquiv (cancelL p q r).
Proof.
  change (IsEquiv (equiv_cancelL p q r)); exact _.
Defined.

Global Instance isequiv_whiskerR {A} {x y z : A} {p q : x = y} (r : y = z)
: IsEquiv (fun h => @whiskerR A x y z p q h r).
Proof.
  simple refine (isequiv_adjointify _ _ _ _).
  - apply cancelR.
  - intros k. unfold cancelR.
    rewrite !whiskerR_pp.
    refine ((_ @@ 1 @@ _) @ whiskerR_VpR k r).
    + destruct p, r; reflexivity.
    + destruct q, r; reflexivity.
  - intros k. unfold cancelR.
    refine ((_ @@ 1 @@ _) @ whiskerR_pVR k r).
    + destruct p, r; reflexivity.
    + destruct q, r; reflexivity.
Defined.

Definition equiv_whiskerR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p = q) <~> (p @ r = q @ r)
  := Build_Equiv _ _ (fun h => whiskerR h r) _.

Definition equiv_cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p @ r = q @ r) <~> (p = q)
  := equiv_inverse (equiv_whiskerR p q r).

Definition isequiv_cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
  : IsEquiv (cancelR p q r).
Proof.
  change (IsEquiv (equiv_cancelR p q r)); exact _.
Defined.

(** We can use these to build up more complicated equivalences.

In particular, all of the [move] family are equivalences.

(Note: currently, some but not all of these [isequiv_] lemmas have corresponding [equiv_] lemmas.  Also, they do *not* currently contain the computational content that e.g. the inverse of [moveR_Mp] is [moveL_Vp]; perhaps it would be useful if they did? *)

Global Instance isequiv_moveR_Mp
 {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveR_Mp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveR_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (p = r^ @ q) <~> (r @ p = q)
:= Build_Equiv _ _ (moveR_Mp p q r) _.

Global Instance isequiv_moveR_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveR_pM p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveR_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (r = q @ p^) <~> (r @ p = q)
:= Build_Equiv _ _ (moveR_pM p q r) _.

Global Instance isequiv_moveR_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: IsEquiv (moveR_Vp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveR_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: (p = r @ q) <~> (r^ @ p = q)
:= Build_Equiv _ _ (moveR_Vp p q r) _.

Global Instance isequiv_moveR_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: IsEquiv (moveR_pV p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveR_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: (r = q @ p) <~> (r @ p^ = q)
:= Build_Equiv _ _ (moveR_pV p q r) _.

Global Instance isequiv_moveL_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveL_Mp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveL_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (r^ @ q = p) <~> (q = r @ p)
:= Build_Equiv _ _ (moveL_Mp p q r) _.

Definition isequiv_moveL_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveL_pM p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveL_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  q @ p^ = r <~> q = r @ p
  := Build_Equiv _ _ _ (isequiv_moveL_pM p q r).

Global Instance isequiv_moveL_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: IsEquiv (moveL_Vp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveL_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: r @ q = p <~> q = r^ @ p
:= Build_Equiv _ _ (moveL_Vp p q r) _.

Global Instance isequiv_moveL_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: IsEquiv (moveL_pV p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.

Definition equiv_moveL_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: q @ p = r <~> q = r @ p^
:= Build_Equiv _ _ (moveL_pV p q r) _.

Definition isequiv_moveL_1M {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveL_1M p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_M1 {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveL_M1 p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveL_1V p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveL_V1 p q).
Proof.
  destruct q. apply isequiv_concat_l.
Defined.

Definition isequiv_moveR_M1 {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveR_M1 p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Global Instance isequiv_moveR_1M {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveR_1M p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Definition equiv_moveR_1M {A : Type} {x y : A} (p q : x = y)
  : (1 = q @ p^) <~> (p = q)
  := Build_Equiv _ _ (moveR_1M p q) _.

Definition isequiv_moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveR_1V p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.

Definition isequiv_moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveR_V1 p q).
Proof.
  destruct p. apply isequiv_concat_r.
Defined.


Definition moveR_moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (q : transport P p u = v)
  : moveR_transport_p P p u v (moveL_transport_V P p u v q) = q.
Proof.
  destruct p; reflexivity.
Defined.

Definition moveL_moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
           (p : x = y) (u : P x) (v : P y) (q : u = transport P p^ v)
  : moveL_transport_V P p u v (moveR_transport_p P p u v q) = q.
Proof.
  destruct p; reflexivity.
Defined.

Global Instance isequiv_moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: IsEquiv (moveR_transport_p P p u v).
Proof.
  srapply isequiv_adjointify.
  - apply moveL_transport_V.
  - intro q; apply moveR_moveL_transport_V.
  - intro q; apply moveL_moveR_transport_p.
Defined.

Definition equiv_moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: u = transport P p^ v <~> transport P p u = v
:= Build_Equiv _ _ (moveR_transport_p P p u v) _.


Definition moveR_moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
           (p : y = x) (u : P x) (v : P y) (q : transport P p^ u = v)
  : moveR_transport_V P p u v (moveL_transport_p P p u v q) = q.
Proof.
  destruct p; reflexivity.
Defined.

Definition moveL_moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
           (p : y = x) (u : P x) (v : P y) (q : u = transport P p v)
  : moveL_transport_p P p u v (moveR_transport_V P p u v q) = q.
Proof.
  destruct p; reflexivity.
Defined.

Global Instance isequiv_moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: IsEquiv (moveR_transport_V P p u v).
Proof.
  srapply isequiv_adjointify.
  - apply moveL_transport_p.
  - intro q; apply moveR_moveL_transport_p.
  - intro q; apply moveL_moveR_transport_V.
Defined.

Definition equiv_moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: u = transport P p v <~> transport P p^ u = v
:= Build_Equiv _ _ (moveR_transport_V P p u v) _.

Global Instance isequiv_moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: IsEquiv (moveL_transport_V P p u v).
Proof.
  srapply isequiv_adjointify.
  - apply moveR_transport_p.
  - intro q; apply moveL_moveR_transport_p.
  - intro q; apply moveR_moveL_transport_V.
Defined.

Definition equiv_moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: transport P p u = v <~> u = transport P p^ v
:= Build_Equiv _ _ (moveL_transport_V P p u v) _.

Global Instance isequiv_moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: IsEquiv (moveL_transport_p P p u v).
Proof.
  srapply isequiv_adjointify.
  - apply moveR_transport_V.
  - intro q; apply moveL_moveR_transport_V.
  - intro q; apply moveR_moveL_transport_p.
Defined.

Definition equiv_moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: transport P p^ u = v <~> u = transport P p v
:= Build_Equiv _ _ (moveL_transport_p P p u v) _.

Global Instance isequiv_moveR_equiv_M `{IsEquiv A B f} (x : A) (y : B)
: IsEquiv (@moveR_equiv_M A B f _ x y).
Proof.
  unfold moveR_equiv_M.
  refine (@isequiv_compose _ _ (ap f) _ _ (fun q => q @ eisretr f y) _).
Defined.

Definition equiv_moveR_equiv_M `{IsEquiv A B f} (x : A) (y : B)
  : (x = f^-1 y) <~> (f x = y)
  := Build_Equiv _ _ (@moveR_equiv_M A B f _ x y) _.

Global Instance isequiv_moveR_equiv_V `{IsEquiv A B f} (x : B) (y : A)
: IsEquiv (@moveR_equiv_V A B f _ x y).
Proof.
  unfold moveR_equiv_V.
  refine (@isequiv_compose _ _ (ap f^-1) _ _ (fun q => q @ eissect f y) _).
Defined.

Definition equiv_moveR_equiv_V `{IsEquiv A B f} (x : B) (y : A)
  : (x = f y) <~> (f^-1 x = y)
  := Build_Equiv _ _ (@moveR_equiv_V A B f _ x y) _.

Global Instance isequiv_moveL_equiv_M `{IsEquiv A B f} (x : A) (y : B)
: IsEquiv (@moveL_equiv_M A B f _ x y).
Proof.
  unfold moveL_equiv_M.
  refine (@isequiv_compose _ _ (ap f) _ _ (fun q => (eisretr f y)^ @ q) _).
Defined.

Definition equiv_moveL_equiv_M `{IsEquiv A B f} (x : A) (y : B)
  : (f^-1 y = x) <~> (y = f x)
  := Build_Equiv _ _ (@moveL_equiv_M A B f _ x y) _.

Global Instance isequiv_moveL_equiv_V `{IsEquiv A B f} (x : B) (y : A)
: IsEquiv (@moveL_equiv_V A B f _ x y).
Proof.
  unfold moveL_equiv_V.
  refine (@isequiv_compose _ _ (ap f^-1) _ _ (fun q => (eissect f y)^ @ q) _).
Defined.

Definition equiv_moveL_equiv_V `{IsEquiv A B f} (x : B) (y : A)
  : (f y = x) <~> (y = f^-1 x)
  := Build_Equiv _ _ (@moveL_equiv_V A B f _ x y) _.

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
  transitivity (q @ 1 = r).
  - exact (equiv_concat_r (concat_1p r) (q @ 1)).
  - exact (equiv_concat_l (concat_p1 q)^ r).
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
  transitivity (q @ 1 = r).
  - exact (equiv_concat_r (concat_1p r) (q @ 1)).
  - exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_FFlr {A B : Type} {f : A -> B} {g : B -> A}
  {x1 x2 : A} (p : x1 = x2) (q : g (f x1) = x1) (r : g (f x2) = x2)
  : q @ p = ap g (ap f p) @ r
  <~>
  transport (fun x => g (f x) = x) p q = r.
Proof.
  destruct p; simpl.
  transitivity (q @ 1 = r).
  - exact (equiv_concat_r (concat_1p r) (q @ 1)).
  - exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_lFFr {A B : Type} {f : A -> B} {g : B -> A}
  {x1 x2 : A} (p : x1 = x2) (q : x1 = g (f x1)) (r : x2 = g (f x2))
  : q @ ap g (ap f p) = p @ r
  <~>
  transport (fun x => x = g (f x)) p q = r.
Proof.
  destruct p; simpl.
  transitivity (q @ 1 = r).
  - exact (equiv_concat_r (concat_1p r) (q @ 1)).
  - exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_paths2 {A : Type} {x y : A}
           (p : x = y) (q : idpath x = idpath x)
           (r : idpath y = idpath y)
: (concat_1p p)^ @ whiskerR q p @ concat_1p p
  = (concat_p1 p)^ @ whiskerL p r @ concat_p1 p
  <~>
  transport (fun a => idpath a = idpath a) p q = r.
Proof.
  destruct p. simpl.
  refine (_ oE (equiv_whiskerR _ _ 1)^-1).
  refine (_ oE (equiv_whiskerL 1 _ _)^-1).
  refine (equiv_concat_lr _ _).
  - symmetry; apply whiskerR_p1_1.
  - apply whiskerL_1p_1.
Defined.

(** ** Universal mapping property *)

Global Instance isequiv_paths_ind `{Funext} {A : Type} (a : A)
  (P : forall x, (a = x) -> Type)
  : IsEquiv (paths_ind a P) | 0.
Proof.
  refine (isequiv_adjointify (paths_ind a P) (fun f => f a 1) _ _).
  - intros f.
    apply path_forall; intros x.
    apply path_forall; intros p.
    destruct p; reflexivity.
  - intros u. reflexivity.
Defined.

Definition equiv_paths_ind `{Funext} {A : Type} (a : A)
  (P : forall x, (a = x) -> Type)
  : P a 1 <~> forall x p, P x p
  := Build_Equiv _ _ (paths_ind a P) _.

Global Instance isequiv_paths_ind_r `{Funext} {A : Type} (a : A)
  (P : forall x, (x = a) -> Type)
  : IsEquiv (paths_ind_r a P) | 0.
Proof.
  refine (isequiv_adjointify (paths_ind_r a P) (fun f => f a 1) _ _).
  - intros f.
    apply path_forall; intros x.
    apply path_forall; intros p.
    destruct p; reflexivity.
  - intros u. reflexivity.
Defined.

Definition equiv_paths_ind_r `{Funext} {A : Type} (a : A)
  (P : forall x, (x = a) -> Type)
  : P a 1 <~> forall x p, P x p
  := Build_Equiv _ _ (paths_ind_r a P) _.

(** ** Truncation *)

(** Paths reduce truncation level by one.  This is essentially the definition of [IsTrunc_internal]. *)
