Require Export Basics.
Require Export WildCat.Core.
Require Export WildCat.Equiv.

(** ** The category of types *)

Global Instance is01cat_type : Is01Cat Type
  := Build_Is01Cat Type (fun a b => a -> b)
                      (fun a => idmap) (fun a b c g f => g o f).

Global Instance is01cat_arrow {A B : Type}: Is01Cat (A $-> B)
  := Build_Is01Cat _ (fun f g => f == g) (fun f a => idpath)
                      (fun f g h p q a => q a @ p a).

Global Instance is0gpd_arrow {A B : Type}: Is0Gpd (A $-> B).
Proof.
  apply Build_Is0Gpd.
  intros f g p a ; exact (p a)^.
Defined.

Global Instance is0functor_type_postcomp {A B C : Type} (h : B $-> C):
  Is0Functor (cat_postcomp A h).
Proof.
  apply Build_Is0Functor.
  intros f g p a; exact (ap h (p a)).
Defined.

Global Instance is0functor_type_precomp {A B C : Type} (h : A $-> B):
  Is0Functor (cat_precomp C h).
Proof.
  apply Build_Is0Functor.
  intros f g p a; exact (p (h a)).
Defined.

Global Instance is1cat_strong_type : Is1Cat_Strong Type.
Proof.
  srapply Build_Is1Cat_Strong; cbn; intros; reflexivity.
Defined.

Global Instance hasmorext_type `{Funext} : HasMorExt Type.
Proof.
  srapply Build_HasMorExt.
  intros A B f g; cbn in *.
  refine (isequiv_homotopic (@apD10 A (fun _ => B) f g) _).
  intros p.
  destruct p; reflexivity.
Defined.

Global Instance hasequivs_type : HasEquivs Type.
Proof.
  srefine (Build_HasEquivs Type _ _ Equiv (@IsEquiv) _ _ _ _ _ _ _ _); intros A B.
  all:intros f.
  - exact f.
  - exact _.
  - apply Build_Equiv.
  - intros; reflexivity.
  - intros; exact (f^-1).
  - cbn. intros ? x; apply eissect.
  - cbn. intros ? x; apply eisretr.
  - intros g r s; refine (isequiv_adjointify f g r s).
Defined.

Definition catie_isequiv {A B : Type} {f : A $-> B}
       `{IsEquiv A B f} : CatIsEquiv f.
Proof.
  assumption.
Defined.

Hint Immediate catie_isequiv : typeclass_instances.
