(** * Building blocks for a globally nameless style of tactic reasoning *)

(** ** [hyp] returns any hypothesis, with subsequent failures backtracking through all hypotheses *)
Ltac hyp := multimatch goal with H : _ |- _ => constr:H end.

(** ** [enforce foo] ensures that [foo] is well-typed *)
Tactic Notation "enforce" open_constr(term) := idtac.

(** ** [syntax_enforce [ H := body ]] ensures that [H] has a body which is syntactically equal to [body] *)
Tactic Notation "syntax_enforce" "[" constr(H) ":=" open_constr(body) "]" := let H' := (eval unfold H in H) in constr_eq H' body.

(** ** [enforce [ x = y ]] ensures that two terms, possibly containing holes, are judgmentally equal *)
Tactic Notation "enforce" "[" open_constr(x) "=" open_constr(y) "]" := unify x y.

(** An example *)
Goal False -> let X0 := I in False -> True.
Proof.
  intros.
  let H := hyp in
  enforce (H : Logic.True);
    syntax_enforce [ H := I ];
    enforce [ H = _ ];
    enforce [ _ = H ];
    enforce [ H = I ].
Abort.
