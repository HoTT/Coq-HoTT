From HoTT Require Import Basics Spaces.Finite.Fin Spaces.Finite.FinSeq.
From HoTT.Algebra.Groups Require Import Group Presentation FreeGroup.

(** Treat parsing warnings as errors so these tests cannot rely on Rocq's deprecated level tolerance. *)
Local Set Warnings "+parsing".

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

(** Check the full expansions, including binder substitution and the order of relators. *)
Succeed Definition test
  : ⟨ x | x , x^ ⟩
    = Build_Finite_GroupPresentation 1 2
        (fscons (freegroup_in (fin_nat 0))
          (fscons ((freegroup_in (fin_nat 0))^) fsnil)) := 1.
Succeed Definition test
  : ⟨ x , y | y , x ⟩
    = Build_Finite_GroupPresentation 2 2
        (fscons (freegroup_in (fin_nat 1))
          (fscons (freegroup_in (fin_nat 0)) fsnil)) := 1.
Succeed Definition test
  : ⟨ x , y , z | z , x , y ⟩
    = Build_Finite_GroupPresentation 3 3
        (fscons (freegroup_in (fin_nat 2))
          (fscons (freegroup_in (fin_nat 0))
            (fscons (freegroup_in (fin_nat 1)) fsnil))) := 1.

(** Each notation also works as an unparenthesized function argument with a single relator. *)
Succeed Definition test : gp_generators ⟨ x | x ⟩ = Fin 1 := 1.
Succeed Definition test : gp_generators ⟨ x , y | x * y ⟩ = Fin 2 := 1.
Succeed Definition test
  : gp_generators ⟨ x , y , z | x * y * z ⟩ = Fin 3 := 1.

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
