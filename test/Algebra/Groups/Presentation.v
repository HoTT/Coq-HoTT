From HoTT Require Import Basics Spaces.Finite.Fin Spaces.Finite.FinSeq.
From HoTT.Algebra.Groups Require Import Group Presentation FreeGroup.

(** Treat parsing warnings as errors so these tests cannot rely on Rocq's deprecated level tolerance. *)
Local Set Warnings "+parsing".

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

Check ⟨ x | x * x * x , x^ ⟩.
Check ⟨ x , y | x * y ,  x * y * x , x * y^ * x * x * x⟩.
Check ⟨ x , y , z | x * y * z , x * z^ , x * y⟩.

(** Presentations can be passed as unparenthesized function arguments, with one or several relators. *)
Succeed Definition test : gp_generators ⟨ x | x ⟩ = Fin 1 := 1.
Succeed Definition test : gp_generators ⟨ x , y | x * y ⟩ = Fin 2 := 1.
Succeed Definition test
  : gp_generators ⟨ x , y , z | x * y * z ⟩ = Fin 3 := 1.
Succeed Definition test : gp_rel_index ⟨ x | x , x^ ⟩ = Fin 2 := 1.
Succeed Definition test
  : gp_rel_index ⟨ x , y | x * y , y * x , x^ ⟩ = Fin 3 := 1.
Succeed Definition test
  : gp_rel_index ⟨ x , y , z | x * y , y * z , z * x ⟩ = Fin 3 := 1.

(** Check binder substitution and the order of relators. *)
Succeed Definition test
  : gp_relators ⟨ x | x , x^ ⟩ (fin_nat 1)
    = (freegroup_in (fin_nat 0))^ := 1.
Succeed Definition test
  : gp_relators ⟨ x , y | x * y ⟩ (fin_nat 0)
    = freegroup_in (fin_nat 0) * freegroup_in (fin_nat 1) := 1.
Succeed Definition test
  : gp_relators ⟨ x , y , z | x * y , z^ , x * z ⟩ (fin_nat 1)
    = (freegroup_in (fin_nat 2))^ := 1.

(** Relators still admit full terms, including binders, at level 200. *)
Succeed Definition test
  : gp_relators ⟨ x | let y := x in y * x ⟩ (fin_nat 0)
    = freegroup_in (fin_nat 0) * freegroup_in (fin_nat 0) := 1.
Succeed Definition test
  : gp_relators ⟨ x , y | (fun z => z * y) x ⟩ (fin_nat 0)
    = freegroup_in (fin_nat 0) * freegroup_in (fin_nat 1) := 1.
Succeed Definition test
  : gp_relators ⟨ x , y , z | x , let w := z in w * y ⟩ (fin_nat 1)
    = freegroup_in (fin_nat 2) * freegroup_in (fin_nat 1) := 1.
