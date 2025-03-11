From HoTT Require Import Basics.Overture Basics.Tactics Types.Paths.


(** Here we test the [transport_paths FlFr] style tactics. *)

(** *** 0 functions *)

(** Transporting the left *)
Definition transport_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y)
  (r : x2 = y)
  (expected : p^ @ q = r)
  : transport (fun x => x = y) p q = r.
Proof.
  by transport_paths l.
Defined.

(** Transporting both *)
Definition transport_paths_lr {A : Type} {x1 x2 : A} (p : x1 = x2) (q : x1 = x1)
  (r : x2 = x2)
  (expected : p @ r = q @ p)
  : transport (fun x => x = x) p q = r.
Proof.
  by transport_paths lr.
Defined.

(** Transporting the right *)
Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  (r : x = y2)
  (expected : q @ p = r)
  : transport (fun y => x = y) p q = r.
Proof.
  by transport_paths r.
Defined.

(** *** 1 function *)

Definition transport_paths_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y)
  (r : f x2 = y)
  (expected : q = ap f p @ r)
  : transport (fun x => f x = y) p q = r.
Proof.
  by transport_paths Fl.
Defined.

Definition transport_paths_Flr {A : Type} {f : A -> A} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = x1)
  (r : f x2 = x2)
  (expected : ap f p @ r = q @ p) 
  : transport (fun x => f x = x) p q = r.
Proof.
  by transport_paths Flr.
Defined.

Definition transport_paths_lFr {A : Type} {f : A -> A} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = f x1)
  (r : x2 = f x2)
  (expected : p @ r = q @ ap f p)
  : transport (fun x => x = f x) p q = r.
Proof.
  by transport_paths lFr.
Defined.

Definition transport_paths_Fr {A B : Type} {g : A -> B} {y1 y2 : A} {x : B}
  (p : y1 = y2) (q : x = g y1)
  (r : x = g y2)
  (expected : q @ ap g p = r)
  : transport (fun y => x = g y) p q = r.
Proof.
  by transport_paths Fr.
Defined.

(** *** 2 functions *)

Definition transport_paths_FFl {A B C : Type} {f : A -> B} {g : B -> C}
  {x1 x2 : A} {y : C} (p : x1 = x2) (q : g (f x1) = y)
  (r : g (f x2) = y)
  (expected : q = ap g (ap f p) @ r)
  : transport (fun x => g (f x) = y) p q = r.
Proof.
  by transport_paths FFl.
Defined.

Definition transport_paths_FFlr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = x1)
  (r : g (f x2) = x2)
  (expected : ap g (ap f p) @ r = q @ p)
  : transport (fun x => g (f x) = x) p q = r.
Proof.
  by transport_paths FFlr.
Defined.

Definition transport_paths_FlFr {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1)
  (r : f x2 = g x2)
  (expected : ap f p @ r = q @ ap g p)
  : transport (fun x => f x = g x) p q = r.
Proof.
  by transport_paths FlFr.
Defined.

Definition transport_paths_lFFr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = g (f x1))
  (r : x2 = g (f x2))
  (expected : p @ r = q @ ap g (ap f p))
  : transport (fun x => x = g (f x)) p q = r.
Proof.
  by transport_paths lFFr.
Defined.

Definition transport_paths_FFr {A B C : Type} {f : A -> B} {g : B -> C}
  {x1 x2 : A} {y : C} (p : x1 = x2) (q : y = g (f x1))
  (r : y = g (f x2))
  (expected : q @ ap g (ap f p) = r)
  : transport (fun x => y = g (f x)) p q = r.
Proof.
  by transport_paths FFr.
Defined.

(** *** 3 functions *)

Definition transport_paths_FFFl {A B C D : Type}
  {f : A -> B} {g : B -> C} {h : C -> D} {x1 x2 : A} {y : D}
  (p : x1 = x2) (q : h (g (f x1)) = y)
  (r : h (g (f x2)) = y)
  (expected : q = ap h (ap g (ap f p)) @ r)
  : transport (fun x => h (g (f x)) = y) p q = r.
Proof.
  by transport_paths FFFl.
Defined.

Definition transport_paths_FFFlr {A B C : Type}
  {f : A -> B} {g : B -> C} {h : C -> A} {x1 x2 : A}
  (p : x1 = x2) (q : h (g (f x1)) = x1)
  (r : h (g (f x2)) = x2)
  (expected : ap h (ap g (ap f p)) @ r = q @ p)
  : transport (fun x => h (g (f x)) = x) p q = r.
Proof.
  by transport_paths FFFlr.
Defined.

Definition transport_paths_FFlFr {A B C : Type}
  {f : A -> B} {g : B -> C} {h : A -> C} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = h x1)
  (r : g (f x2) = h x2)
  (expected : ap g (ap f p) @ r = q @ ap h p)
  : transport (fun x => g (f x) = h x) p q = r.
Proof.
  by transport_paths FFlFr.
Defined.

Definition transport_paths_FlFFr {A B C : Type}
  {f : A -> C} {g : B -> C} {h : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g (h x1))
  (r : f x2 = g (h x2))
  (expected : ap f p @ r = q @ ap g (ap h p))
  : transport (fun x => f x = g (h x)) p q = r.
Proof.
  by transport_paths FlFFr.
Defined.

Definition transport_paths_lFFFr {A B C : Type}
  {f : A -> B} {g : B -> C} {h : C -> A} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = h (g (f x1)))
  (r : x2 = h (g (f x2)))
  (expected : p @ r = q @ ap h (ap g (ap f p)))
  : transport (fun x => x = h (g (f x))) p q = r.
Proof.
  by transport_paths lFFFr.
Defined.

Definition transport_paths_FFFr {A B C D : Type}
  {f : A -> B} {g : B -> C} {h : C -> D} {x1 x2 : A} {y : D}
  (p : x1 = x2) (q : y = h (g (f x1)))
  (r : y = h (g (f x2)))
  (expected : q @ ap h (ap g (ap f p)) = r)
  : transport (fun x => y = h (g (f x))) p q = r.
Proof.
  (** TODO: Coq is unable to unify, work out why *)
  Fail transport_paths FFFr.
  lhs napply (transport_paths_FFFr (g:=g)).
  assumption.
Defined.

(** *** 4 functions *)

Definition transport_paths_FFFlFr {A B C D : Type}
  {f : A -> B} {g : B -> C} {h : C -> D} {k : A -> D} {x1 x2 : A}
  (p : x1 = x2) (q : h (g (f x1)) = k x1)
  (r : h (g (f x2)) = k x2)
  (expected : ap h (ap g (ap f p)) @ r = q @ ap k p)
  : transport (fun x => h (g (f x)) = k x) p q = r.
Proof.
  by transport_paths FFFlFr.
Defined.

Definition transport_paths_FFlFFr {A B B' C : Type}
  {f : A -> B} {f' : A -> B'} {g : B -> C} {g' : B' -> C} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = g' (f' x1))
  (r : g (f x2) = g' (f' x2))
  (expected : ap g (ap f p) @ r = q @ ap g' (ap f' p))
  : transport (fun x => g (f x) = g' (f' x)) p q = r.
Proof.
  by transport_paths FFlFFr.
Defined.
