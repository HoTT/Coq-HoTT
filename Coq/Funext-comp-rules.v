Require Export Fibrations Contractible Equivalences FiberEquivalences Funext.

(** * Relationship between computation rules

The above, incidentally, appears to answer some questions which Richard Garner discusses and leaves open in “On the strength of dependent products…”.  

There are two computation rules one could consider for a term [funext : funext_dep_statement].  Essentially, one (call it [funext_comp1]) says that [funext] is left inverse to [happly]; the other ([funext_comp2]) says that it is right inverse.

The above arguments show that these two are equivalent, since in the presence of any term of type [funext_statement], [happly] is an equivalence.

In “On the strength…”, RG considers [funext_comp1] as the rule ‘Π-ext-comp’ (section 5.1), and says of the combination [funext] + [funext_comp1] :

“However, when it comes to function extensionality, there are a number of statements which intuitively should be true but which seem to be impossible to prove. Here are two typical examples.”

The first of these examples is [funext_comp2]!

Indeed, all the other strong principles he considers later in the paper are also derivable without much difficulty from [strong_funext] as considered here, and hence from [funext]/[funext_comp1].

Formalising this: *)

Definition funext_comp1_statement (funext : funext_dep_statement)
  := (forall X P f, funext X P f f (fun x => idpath (f x)) == idpath f).
(** ‘Π-ext-comp’ in Garner. *)

Definition funext_comp2_statement (funext : funext_dep_statement)
  := (forall X P f g p x,
      happly_dep (funext X P f g p) x == p x).
(** ‘Π-ext-app’ in Garner; and [strong_funext_dep_compute] above. *)

(** Given [funext : funext_dep_statement], the first computation rule may not hold for [funext] itself; but we can always find a better witness for which it does hold: *)
Definition funext_correction : funext_dep_statement -> funext_dep_statement
  :=
(fun funext =>
  fun X P f g h => 
      (funext X P f g h)
    @ 
      ! (funext X P g g (fun x => idpath (g x)))
).

Lemma funext_correction_comp1 :
  forall (funext : funext_dep_statement),
  funext_comp1_statement (funext_correction funext).
Proof.
  unfold funext_comp1_statement.
  unfold funext_correction.
  auto with path_hints.
Defined.

(** Given [funext] satisfying *both* computation rules, it’s easy to prove [strong_funext_statement]: *)
Lemma funext_comp_to_strong
  (funext : funext_dep_statement)
  (funext_comp1 : funext_comp1_statement funext)
  (funext_comp2 : funext_comp2_statement funext)
: strong_funext_statement.
Proof.
  intros.  unfold strong_funext_statement.
  intros.  
  (* [funext] gives a two-sided inverse to [happly]: *)  
  apply (hequiv_is_equiv happly (funext _ _ f g)).
  (* First, show it’s a right inverse: *)
  intro h_fg.  apply funext.  
  intro x.  apply (funext_comp2 X (fun _ => Y)).
  (* Now, show it’s a left inverse: *)
  intro p.  destruct p.  apply funext_comp1.
Defined.

(** Now, we know from the theorems above that [funext_statement] implies [strong_funext_statement].

But given [strong_funext_statement], [happly] is an equivalence, so any [funext] is left inverse to it iff it’s right inverse to it.

So in fact for any given [funext], the two computation rules are equivalent! 

Question: can we give a more direct proof of [funext_comp2_statement] than using the above argument??  Hopefully unwinding that argument a bit should be possible… *)

(** Warmup: chasing around [funext_dep_statement -> strong_funext_statement -> funext_dep_statement] should essentially give [funext_correction].  If we simply put together this roundabout proof, will it β-reduce to something comprehensible?  *)

Theorem naive_to_strong_funext_dep
  : funext_dep_statement -> strong_funext_dep_statement.
Proof.
  intro funext.
  apply weak_to_strong_funext_dep.
  apply funext_dep_to_eta_dep.  assumption.
  apply funext_dep_to_weak.  assumption.
Defined.

Theorem naive_to_naive_funext_dep
  : funext_dep_statement -> funext_dep_statement.
Proof.
  intro funext.
  apply strong_to_naive_funext_dep.
  apply naive_to_strong_funext_dep.
  assumption.
Defined.

(* [Eval compute in naive_to_naive_funext_dep.] *)
(* …crashes Coq, after ten minutes and 3.5 GB of virtual memory. *)

(** So, let’s review the proof of the two computation rules from [strong_funext_dep]: *)
Theorem strong_funext_dep_comp2
  (strong_funext_dep : strong_funext_dep_statement)
: funext_comp2_statement (strong_to_naive_funext_dep strong_funext_dep).
Proof.
  unfold funext_comp2_statement.
  intros.
  unfold strong_to_naive_funext_dep.
  unfold inverse.
  simpl.
  exact (happly_dep (pr2 (pr1 (strong_funext_dep X P f g p))) x).
Defined.

Theorem strong_funext_dep_comp1
  (strong_funext_dep : strong_funext_dep_statement)
: funext_comp1_statement (strong_to_naive_funext_dep strong_funext_dep).
Proof.
  unfold funext_comp1_statement.
  intros.
  unfold strong_to_naive_funext_dep.
  unfold inverse.
  simpl.
  unfold strong_funext_dep_statement in *.
  (* To show the desired equality, we first lift the points to the homotopy fiber, and then show them equal there, which is easy since it’s contractible.  *)
  apply (@base_path _ _ (pr1 (strong_funext_dep X P f f (fun x : X => idpath (f x)))) (idpath f; idpath _)).
  symmetry.
  apply (pr2 (strong_funext_dep X P f f (fun x : X => idpath (f x)))).
Defined.