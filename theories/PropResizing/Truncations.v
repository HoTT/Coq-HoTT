(* -*- mode: coq; mode: visual-line -*-  *)
(** * Impredicative truncations. *)

Require Import HoTT.Basics HoTT.Types UnivalenceImpliesFunext HProp.
Require Import PropResizing.PropResizing.
Local Open Scope path_scope.

(* Be careful about [Import]ing this file!  It defines truncations
with the same name as those constructed with HITs.  Probably you want
to use those instead, if you are using HITs. *)

Section AssumePropResizing.
  Context `{PropResizing}.

  Definition merely@{i j} (A : Type@{i}) : Type@{i}
    := forall P:Type@{j}, IsHProp P -> (A -> P) -> P.   (* requires j < i *)

  Definition trm {A} : A -> merely A
    := fun a P HP f => f a.

  Global Instance ishprop_merely `{Funext} (A : Type) : IsHProp (merely A).
  Proof.
    exact _.
  Defined.

  Definition merely_rec {A : Type@{i}} {P : Type@{j}} `{IsHProp P} (f : A -> P)
    : merely A -> P
    := fun ma => (equiv_resize_hprop P)^-1
                 (ma (resize_hprop P) _ (equiv_resize_hprop P o f)).

  Definition functor_merely `{Funext} {A B : Type} (f : A -> B)
    : merely A -> merely B.
  Proof.
    srefine (merely_rec (trm o f)).
  Defined.

(* show what is gained by propositional resizing, without mentioning universe levels *)
  Local Definition typeofid (A : Type) := A -> A.
   
  Local Definition functor_merely_sameargs `{Funext} {A : Type} (f : typeofid A)
    : typeofid (merely A) := functor_merely f.

(* a more informative version using universe levels *)
  Local Definition functor_merely_sameuniv `{Funext} {A B: Type@{i}} (f : A -> B)
    : merely@{j k} A -> merely@{j k} B:= functor_merely f.    (* requires i <= j & k < j *)


End AssumePropResizing.

(* Here, we show what goes wrong without propositional resizing. We do not use what we imported with Require Import PropResizing.PropResizing. *)

(* a more explicit definition of being a prop *)
Local Definition IsHProp_expl (A : Type@{i}) : Type@{i} :=
  forall x y : A, Contr_internal (x = y).

Local Definition ishprop_expl_merely `{Funext} (A : Type@{i})
  : IsHProp_expl@{i} (merely@{i j} A).
Proof.
  exact (@trunc_forall H Type (fun P : Type => IsHProp_expl P -> (A -> P) -> P)
  (-1)
  (fun P : Type =>
   @trunc_forall H (IsHProp_expl P) (fun _ : IsHProp_expl P => (A -> P) -> P)
     (-1) (fun p : IsHProp_expl P => @trunc_arrow H (A -> P) P (-1) p))).
Defined.

(* the naive definition *)
Local Definition merely_rec_naive {A : Type@{i}} {P : Type@{j}} {p:IsHProp_expl@{j} P} (f : A -> P)
  : merely@{i j} A -> P
  := fun ma => ma P p f.

(* the too weak definition *)
Local Definition functor_merely_weak `{Funext} {A B : Type@{k}} (f : A -> B)
  : merely@{j k} A -> merely@{k l} B. (* evidently, this requires k<j and l<k *)
Proof.
  srefine (merely_rec_naive (trm o f)).
  apply ishprop_expl_merely.
Defined.

(* impossible due to universe inconsistency:
Local Definition functor_merely_weak_sameargs `{Funext} {A : Type} (f : typeofid A)
  : typeofid(merely A) := functor_merely_weak f.
The following much weaker definition is possible:
*)

Local Definition functor_merely_weak_sameargs_weak `{Funext} {A : Type} (f : typeofid A)
  : merely A -> merely A := functor_merely_weak f.

(* a more informative version using universe levels *)
Local Definition functor_merely_weak_sameuniv_weak `{Funext} {A B: Type@{i}} (f : A -> B)
  : merely@{j k} A -> merely@{k l} B:= functor_merely_weak f.
(* requires i <= j & l < k < j *)
