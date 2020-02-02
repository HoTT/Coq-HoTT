Require Export Basics.
Require Export WildCat.Core.

(** * Path groupoids as wild categories *)

(** Not global instances for now *)
Local Instance is01cat_paths (A : Type) : Is01Cat A.
Proof.
  unshelve econstructor.
  - constructor; intros x y; exact (x = y).
  - intros a; reflexivity.
  - intros a b c q p; exact (p @ q).
Defined.

Local Instance is0gpd_paths (A : Type) : Is0Gpd A.
Proof.
  constructor.
  intros x y p; exact (p^).
Defined.