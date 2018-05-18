(** * Constant functor *)
Require Import Categories.Category.
Require Import Category.Core Functor.Core.

Definition const_functor
           {C D : PreCategory}
           (X : D)
  : Functor C D
  := Build_Functor C
                   D
                   (fun _ => X)
                   (fun _ _ _ => Category.identity X)
                   (fun _ _ _ _ _ => (left_identity _ _ _ _)^)
                   (fun _ => idpath).