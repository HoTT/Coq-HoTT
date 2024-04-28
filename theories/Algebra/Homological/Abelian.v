Require Import Basics.Overture Basics.Tactics Basics.Equivalences.
Require Import WildCat.Core WildCat.Equiv WildCat.PointedCat WildCat.Opposite.
Require Import Algebra.AbGroups.AbelianGroup Algebra.Rings.Ring.
Require Import Algebra.Homological.Additive.
Require Import canonical_names.

(** * Abelian Categories *)

Local Open Scope mc_scope.
Local Open Scope mc_add_scope.

(** ** Kernels and cokernels *)

(** *** Kernels *)

Class Kernel {A : Type} `{IsPointedCat A} {a b : A} (f : a $-> b) := {
  cat_ker_obj : A;
  cat_ker : cat_ker_obj $-> a;

  cat_ker_zero : f $o cat_ker $== zero_morphism;

  cat_ker_corec {x} (g : x $-> a) : f $o g $== zero_morphism -> x $-> cat_ker_obj;

  cat_ker_corec_beta {x} (g : x $-> a) (p : f $o g $== zero_morphism)
    : cat_ker $o cat_ker_corec g p $== g;
    
  monic_cat_ker : Monic cat_ker;
}.

Arguments cat_ker_obj {A _ _ _ _ _ a b} f {_}.
Arguments cat_ker_corec {A _ _ _ _ _ a b f _ x} g p.
Arguments cat_ker {A _ _ _ _ _ a b} f {_}.
Arguments cat_ker_zero {A _ _ _ _ _ a b} f {_}.
Arguments monic_cat_ker {A _ _ _ _ _ a b} f {_}.

(** Kernels of monomorphisms are zero. *)
Definition ker_zero_monic {A : Type} `{IsPointedCat A}
  {a b : A} (f : a $-> b) `{!Kernel f}
  : Monic f -> cat_ker f $== zero_morphism.
Proof.
  intros monic.
  apply monic.
  refine (cat_ker_zero f $@ _^$).
  apply cat_zero_r.
Defined.

(** Maps with zero kernel are monic. *)
Definition monic_ker_zero {A : Type} `{IsAdditive A}
  {a b : A} (f : a $-> b) `{!Kernel f}
  : cat_ker f $== zero_morphism -> Monic f.
Proof.
  intros ker_zero c g h p.
  apply GpdHom_path.
  apply path_hom in p.
  change (@paths (AbHom c a) g h).
  change (@paths (AbHom c b) (f $o g) (f $o h)) in p.
  apply grp_moveL_1M.
  apply grp_moveL_1M in p.
  apply GpdHom_path in p.
  apply path_hom.
  refine ((cat_ker_corec_beta (g + (-h)) _)^$ $@ (ker_zero $@R _) $@ cat_zero_l _).
  refine (addcat_dist_l _ _ _ $@ _ $@ p).
  apply GpdHom_path.
  f_ap.
  apply path_hom.
  symmetry.
  apply addcat_comp_negate_r.
Defined.

(** *** Cokernels *)

Class Cokernel {A : Type} `{IsPointedCat A} {a b : A} (f : a $-> b)
  := cokernel_kernel_op :: Kernel (A := A^op) (f : Hom (A:= A^op) b a).

Arguments Cokernel {A _ _ _ _ _ a b} f.

Definition cat_coker_obj {A : Type} `{IsPointedCat A} {a b : A} (f : a $-> b)
  `{!Cokernel f} : A
  := cat_ker_obj (A:=A^op) (a:=b) f.

Definition cat_coker {A : Type} `{IsPointedCat A} {a b : A} (f : a $-> b)
  `{!Cokernel f} : b $-> cat_coker_obj f
  := cat_ker (A:=A^op) (a:=b) (b:=a) f.

Definition cat_coker_zero {A : Type} `{IsPointedCat A} {a b : A} (f : a $-> b)
  `{!Cokernel f} : cat_coker f $o f $== zero_morphism
  := cat_ker_zero (A:=A^op) (a:=b) f.

Definition cat_coker_rec {A : Type} `{IsPointedCat A} {a b : A} {f : a $-> b}
  `{!Cokernel f} {x} (g : b $-> x)
  : g $o f $== zero_morphism -> cat_coker_obj f $-> x
  := cat_ker_corec (A:=A^op) (a:=b) (b:=a) g.

Definition cat_coker_rec_beta {A : Type} `{IsPointedCat A} {a b : A} (f : a $-> b)
  `{!Cokernel f} {x} (g : b $-> x) (p : g $o f $== zero_morphism)
  : cat_coker_rec g p $o cat_coker f $== g
  := cat_ker_corec_beta (A:=A^op) (a:=b) (b:=a) g p.

Definition epic_cat_coker {A : Type} `{IsPointedCat A}
  {a b : A} (f : a $-> b) `{!Cokernel f}
  : Epic (cat_coker f)
  := monic_cat_ker (A:=A^op) (a:=b) (b:=a) f.

Definition coker_zero_epic {A : Type} `{IsPointedCat A}
  {a b : A} (f : a $-> b) `{!Cokernel f}
  : Epic f -> cat_coker f $== zero_morphism
  := ker_zero_monic (A:=A^op) (a:=b) f.

Definition epic_coker_zero {A : Type} `{IsAdditive A}
  {a b : A} (f : a $-> b) {k : Cokernel f}
  : cat_coker f $== zero_morphism -> Epic f
  := monic_ker_zero (A:=A^op) (a:=b) (b:=a) f.

(** ** Preabelian categories *)

Class IsPreAbelian {A : Type} `{IsAdditive A} := {
  preabelian_has_kernels :: forall {a b : A} (f : a $-> b), Kernel f;
  preabelian_has_cokernels :: forall {a b : A} (f : a $-> b), Cokernel f;
}.

Definition cat_coker_ker_ker_coker {A : Type} `{IsPreAbelian A}
  {a b : A} (f : a $-> b)
  : cat_coker_obj (cat_ker f) $-> cat_ker_obj (cat_coker f).
Proof.
  snrapply cat_coker_rec.
  - snrapply cat_ker_corec.
    + exact f.
    + apply cat_coker_zero.
  - snrapply monic_cat_ker.
    refine ((cat_assoc _ _ _)^$ $@ _).
    refine ((_ $@R _) $@ _).
    1: apply cat_ker_corec_beta.
    refine (_ $@ (cat_zero_r _)^$).
    apply cat_ker_zero.
Defined.

(** ** Abelian categories *)

Class IsAbelian {A : Type} `{IsPreAbelian A} := {
  catie_preabelian_canonical_map : forall a b (f : a $-> b),
    CatIsEquiv (cat_coker_ker_ker_coker f);
}.

