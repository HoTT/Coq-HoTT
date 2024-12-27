From HoTT Require Import Basics Spaces.Finite.Fin Spaces.Finite.FinSeq.
From HoTT.Algebra.Groups Require Import Group Presentation FreeGroup.

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

Check ⟨ x | x * x * x , x^ ⟩.
Check ⟨ x , y | x * y ,  x * y * x , x * y^ * x * x * x⟩.
Check ⟨ x , y , z | x * y * z , x * z^ , x * y⟩.
