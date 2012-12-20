(** * Theorems about cartesian products *)

Require Import Common Paths Contractible.

Open Scope path_scope.

(** *** Paths *)

Definition prod_unpack {A B : Type} {P : A * B -> Type} (u : A * B) :
  P (fst u, snd u) -> P u
  :=
  let (x, y) as u return (P (fst u, snd u) -> P u) := u in idmap.

Definition prod_path {A B : Type} {x x' : A} {y y' : B} :
  x = x' -> y = y' -> (x, y) = (x', y')
  :=
  fun p q => match p, q with idpath, idpath => 1 end.

Definition ap_fst_prod_path {A B : Type} {x y : A} {x' y' : B} (p : x = y) (q : x' = y') :
  ap fst (prod_path p q) = p
  :=
  match p as i return (ap fst (prod_path i q) = i) with
    idpath =>
    match q as j return (ap fst (prod_path 1 j) = 1) with
      idpath => 1
    end
  end.

Definition ap_snd_prod_path {A B : Type} {x y : A} {x' y' : B} (p : x = y) (q : x' = y') :
  ap snd (prod_path p q) = q
  :=
  match q as j return (ap snd (prod_path p j) = j) with
    idpath =>
    match p as i return (ap snd (prod_path i 1) = 1) with
      idpath => 1
    end
  end.

Definition prod_path_fst_snd {A B : Type} {x x' : A} {y y' : B} (p : (x,y) = (x',y')) :
  prod_path (ap fst p) (ap snd p) = p.


(** *** Transport *)

(** *** HLevel *)

Definition prod_contr (A : Contr) (B : Contr) : Contr :=
  BuildContr
  (prod A B)
  (contr_center A, contr_center B)
  (fun y : prod A B =>
    let (a, b) as p return ((contr_center A, contr_center B) = p) := y in
      pair_path (contr a) (contr b)).

Canonical Structure prod_contr.


(** *** Equivalences *)
