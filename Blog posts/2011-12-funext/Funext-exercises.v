Add LoadPath "../../Coq".
Require Export Paths Equivalences Funext.


Definition funext_correction_exercise
  : funext_dep_statement -> funext_dep_statement.
Proof.  
Admitted.

Lemma funext_correction_comp1_exercise :
  forall (funext : funext_dep_statement),
  funext_comp1_statement (funext_correction_exercise funext).
Proof.
Admitted.


Definition funext_comp1_to_left_inverse_exercise funext :
    (funext_comp1_statement funext)
  ->
    (forall A P (f g : forall x:A, P x) (p : f == g),
      funext A P f g (happly_dep p) == p).

