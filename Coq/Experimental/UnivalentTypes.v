(** Call a type constructor [P : forall (A B : Type), (A <~> B) -> Type] univalent if it
   satisfies the equivalence indunction principle, as in [Univalence.equiv_induction].
   We would like to show that all definable [P] have this property.
*)

Add LoadPath "..".

Require Import Paths Fibrations Contractible Funext HLevel
  Equivalences FiberEquivalences FunextEquivalences Univalence.
Require Import ExtensionalityAxiom.

Section PathEquiv.
  (* We first recall a fact about paths that we're going to mimic. *)

  Variable A : Type.
  Variable P : forall (x y : A), x ~~> y -> Type.

  Let path_diag : (forall x y (p : x ~~> y), P x y p) -> (forall x, P x x (idpath x)) :=
    fun s x => s x x (idpath x).

  Let path_undiag : (forall x, P x x (idpath x)) -> (forall x y (p : x ~~> y), P x y p).
  Proof.
    intros s x y p.
    induction p.
    apply s.
  Defined.

  Lemma path_rect_equiv :
     (forall x y (p : x ~~> y), P x y p) <~> (forall x, P x x (idpath x)).
  Proof.
    apply (equiv_from_hequiv path_diag path_undiag).
    intro.
    apply funext_dep; intro.
    now apply idpath.
    intro s.
    apply funext_dep; intro x.
    apply funext_dep; intro y.
    apply funext_dep; intro p.
    induction p.
    now apply idpath.
  Defined.

  Lemma diag_is_section (s : forall x y (p : x ~~> y), P x y p) :
    forall x y (p : x ~~> y), path_undiag (path_diag s) x y p ~~> s x y p.
  Proof.
    path_induction.
  Defined.

  Lemma diag_is_retraction (t : forall x, P x x (idpath x)) :
    forall x, path_diag (path_undiag t) x ~~> t x.
  Proof.
    intro x.
    apply idpath.
  Defined.

End PathEquiv.

Definition EquivSection (P : forall (U V : Type), (U <~> V) -> Type) :=
  forall U V (e : U <~> V), P U V e.

Definition diag {P : forall (U V : Type), (U <~> V) -> Type} :=
  fun (s : forall U V (e : U <~> V), P U V e) (T : Type) => s T T (idequiv T).

Structure Univalent := {
  uni_ty :> forall (U V : Type), (U <~> V) -> Type ;
  uni_j : (forall (T : Type), uni_ty T T (idequiv T)) -> (forall (U V : Type) (e : U <~> V), uni_ty U V e) ;
  uni_comp : forall (s : forall T, uni_ty T T (idequiv T)) T, (s T) ~~> (s T)
}.



Implicit Arguments uni_ty [U V].

(** To treat dependent types we need a notion of a family over a univalent type. *)

(* Structure UnivalentFamily (P : Univalent) := { *)
(*   fam_ty :> forall (U V : Type) (e : U <~> V), P U V e -> Type ; *)
(*   fam_rect : (forall (T : Type) x, fam_ty T T (idequiv T) x) <~> forall (U V : Type) (e : U <~> V) x, fam_ty U V e x *)
(* }. *)

(* Implicit Arguments fam_ty [P U V]. *)
(* Implicit Arguments fam_rect [P]. *)

Section CartesianProduct.
  (* Closure of univalence under cartesian products. *)

  Variable (P Q : Univalent).

  Definition prod_rect (s : forall (T : Type), P T T (idequiv T) * Q T T (idequiv T)) U V (e : U <~> V) :=
    (uni_rect P (fun T => fst (s T)) U V e, uni_rect Q (fun T => snd (s T)) U V e).

  Axiom large_ext : forall (R : fibration Type) (s t : section R), (forall X, s X ~~> t X) -> s ~~> t.

  Definition UnivalentCartesianProduct : Univalent.
  Proof.
    refine
      {| uni_ty := fun (U V : Type) (e : U <~> V) => (P U V e * Q U V e)%type |}.
    apply (equiv_from_hequiv
      prod_rect
      (fun s T => s T T (idequiv T))).
    intro s.
    apply large_ext; intro X.
    apply large_ext; intro Y.
    apply funext_dep; intro e.
    apply prod_path_equiv; split.
    unfold prod_rect; simpl.



    
    apply section_equiv.

  Defined.

End CartesianProduct.

Section DependentSum.
  (* Closure of univalence under dependent sums. *)
  
  Variable (P : Univalent).
  Variable (Q : UnivalentFamily P).

  Definition UnivalentSum : Univalent.
  Proof.
    refine {| uni_ty := fun U V (e : U <~> V) => total (Q U V e) |}.
    intros d U V e.
    exists (uni_rect P (fun T => pr1 (d T)) U V e).
    apply fam_rect.
    intros T x.
    apply (pr2 (d T)).
    

