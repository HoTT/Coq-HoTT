Require Import HoTT.Basics HoTT.Types.Bool HoTT.Types.Paths.
Require Import Colimits.Diagram Colimits.Colimit.
Local Open Scope path.


Definition mappingtelescope_graph : graph.
  simple refine (Build_graph _ _).
  - exact nat.
  - intros n m; exact (S n = m).
Defined.


Definition sequence := diagram mappingtelescope_graph.


Definition Build_sequence (X : nat -> Type) (f : forall n, X n -> X n.+1)
  : sequence.
  unshelve econstructor.
  exact X. intros i j p; destruct p. apply f.
Defined.


Definition equiv_sequence (D1 D2: sequence)
           (H0: (D1 0) <~> (D2 0))
           (Hn: forall n (e: (D1 n) <~> (D2 n)),
               {e' : (D1 n.+1) <~> (D2 n.+1)
                     & (D2 _f 1) o e == e' o (D1 _f 1)})
  : D1 ≃ D2.
Proof.
  simple refine (Build_diagram_equiv (Build_diagram_map _ _) _).
  - intros n. apply equiv_fun. induction n. apply H0. exact (Hn n IHn).1.
  - intros n m q; destruct q. induction n; simpl. exact (Hn 0 H0).2.
    simple refine (Hn n.+1 _).2.
  - intros n; simpl. induction n; simpl. apply H0. apply (Hn n _ ).1.
Defined.
