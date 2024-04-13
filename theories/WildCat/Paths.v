Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids.
Require Import WildCat.Core WildCat.TwoOneCat.

(** * Path groupoids as wild categories *)

(** Not global instances for now *)
Local Instance isgraph_paths (A : Type) : IsGraph A.
Proof.
  constructor.
  intros x y; exact (x = y).
Defined.

Local Instance is01cat_paths (A : Type) : Is01Cat A.
Proof.
  unshelve econstructor.
  - intros a; reflexivity.
  - intros a b c q p; exact (p @ q).
Defined.

Local Instance is0gpd_paths (A : Type) : Is0Gpd A.
Proof.
  constructor.
  intros x y p; exact (p^).
Defined.

Local Instance is2graph_paths (A : Type) : Is2Graph A := fun _ _ => _.
Local Instance is3graph_paths (A : Type) : Is3Graph A := fun _ _ => _.

Local Instance is1cat_paths {A : Type} : Is1Cat A.
Proof.
  snrapply Build_Is1Cat.
  - exact _.
  - exact _.
  - intros x y z p.
    snrapply Build_Is0Functor.
    intros q r h.
    exact (whiskerR h p).
  - intros x y z p.
    snrapply Build_Is0Functor.
    intros q r h.
    exact (whiskerL p h).
  - intros w x y z p q r.
    exact (concat_p_pp p q r). 
  - intros x y p.
    exact (concat_p1 p).
  - intros x y p.
    exact (concat_1p p).
Defined.

Local Instance is1gpd_paths {A : Type} : Is1Gpd A.
Proof.
  snrapply Build_Is1Gpd.
  - intros x y p.
    exact (concat_pV p).
  - intros x y p.
    exact (concat_Vp p).
Defined.

Local Instance is21cat_paths {A : Type} : Is21Cat A.
Proof.
  snrapply Build_Is21Cat.
  - exact _.
  - exact _.
  - intros x y z p.
    snrapply Build_Is1Functor.
    + intros a b q r h.
      exact (ap (fun x => whiskerR x _) h).
    + reflexivity.
    + intros a b c q r.
      exact (whiskerR_pp p q r).
  - intros x y z p.
    snrapply Build_Is1Functor.
    + intros a b q r h.
      exact (ap (whiskerL p) h).
    + reflexivity.
    + intros a b c q r.
      exact (whiskerL_pp p q r).
  - intros a b c q r s t h g.
    exact (concat_whisker q r s t h g)^.
  - intros a b c d q r s t h.
    apply concat_p_pp_nat_r.
  - intros a b c d q r s t h.
    apply concat_p_pp_nat_m.
  - intros a b c d q r s t h.
    apply concat_p_pp_nat_l.
  - intros a b p q h; cbn.
    apply moveL_Mp.
    lhs nrapply concat_p_pp.
    exact (whiskerR_p1 h).
  - intros a b p q h.
    apply moveL_Mp.
    lhs rapply concat_p_pp.
    exact (whiskerL_1p h).
  - intros a b c d e p q r s.
    lhs nrapply concat_p_pp.
    exact (pentagon p q r s).
  - intros a b c p q.
    exact (triangulator p q).
Defined.
