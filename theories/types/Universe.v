(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the universe, including univalence as a typeclass. *)

Require Import Common Paths Contractible Equivalences.
Open Scope path_scope.
Open Scope equiv_scope.

(** *** Paths *)

Generalizable Variables A B f.

Instance isequiv_path {A B : Type} (p : A = B)
  : IsEquiv (transport (fun X:Type => X) p)
  := BuildIsEquiv _ _ _ (transport (fun X:Type => X) p^)
  (fun b => ((transport_pp idmap p^ p b)^ @ transport2 idmap (concat_Vp p) b))
  (fun a => ((transport_pp idmap p p^ a)^ @ transport2 idmap (concat_pV p) a))
  (fun a => match p with idpath => 1 end).

Definition equiv_path (A B : Type) (p : A = B) : A <~> B
  := BuildEquiv _ _ (transport (fun X:Type => X) p) _.

Class Univalence := {
  isequiv_equiv_path :> forall (A B : Type), IsEquiv (equiv_path A B)
}.

Section Univalence.
Context `{Univalence}.

Definition path_universe_uncurried {A B : Type} (f : A <~> B) : A = B
  := (equiv_path A B)^-1 f.

Definition path_universe {A B : Type} (f : A -> B) {feq : IsEquiv f} : (A = B)
  := path_universe_uncurried (BuildEquiv _ _ f feq).

Definition transport_path_universe {A B : Type} (f : A -> B) {feq : IsEquiv f}
  : transport (fun X:Type => X) (path_universe f) = f
  := ap (equiv_fun A B) (eisretr (equiv_path A B) (BuildEquiv _ _ f feq)).

Definition eta_path_universe {A B : Type} (p : A = B)
  : path_universe (equiv_path A B p) = p
  := eissect (equiv_path A B) p.

Definition isequiv_path_universe {A B : Type}
  : IsEquiv (@path_universe_uncurried A B)
  := isequiv_inverse.

Definition equiv_path_universe {A B : Type} : (A <~> B) <~> (A = B)
  := BuildEquiv _ _ (@path_universe_uncurried A B) isequiv_path_universe.

End Univalence.
