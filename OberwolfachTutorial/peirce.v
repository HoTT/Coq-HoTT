(** This simple example shows how to prove theorems in the propositional fragment. We show
   that Peirce's law is equivalent to the Law of Excluded Middle (LEM). *)

(** First we define both laws. In Coq a definition is stated with the [Definition]
   keyword. An exception to this rule are inductive, coinductive, fixpoint and cofixpoint
   definitions. *)

Definition peirce := forall p q : Prop, ((p -> q) -> p) -> p.

(** Let us explain the notation. Universal quantification is written as [forall]. the kind
   of propositions as [Prop], while [->] means implication or a function space (there is
   actually no difference in Coq). And here is LEM. *)

Definition lem := forall r, r \/ ~ r.

(** Notation: disjunction is [\/], conjunction is [/\] and negation is [~]. *)

(** Notice how in the definition of [lem] we did not have to explain to Coq that [r] is a
   proposition. Whenever it is possible to infer types by unification, Coq does so. In the
   definition of [lem] it is clear that [r] is a proposition because disjunction expects
   propositions as arguments. *)

(** A beginner's mistake which may take a long time to discover is to write a colon [:]
   instead of [:=] in the definition, e.g.,

   [Definition lem : forall r, r \/ ~r.]

   Coq happily accepts this line and enters "definition mode" in which the user is
   supposed to define an element of type [forall r, r \/ ~r], in other words a
   proof of [forall r, r \/ ~r]. There is of course a huge difference between
   defining [lem] to be the statement [forall r, r \/ ~r] or defining it to be
   the proof of this statement.

   To illustrate how the "definition mode" works, we show two definitions of
   the composition operation. One is direct, the other is by construction in
   the definition mode. Which one gets used mainly depends on how complicated
   the constructed object is. If you can just write it down straight from your
   head, you will probably opt for the direct mode.
*)

Definition composition_direct (A B C : Type) (f : A -> B) (g : B -> C) : A -> C :=
  fun (x : A) => g (f x).

Definition composition_indirect (A B C : Type) (f : A -> B) (g : B -> C) : A -> C.
Proof.
  intro x.
  apply g.
  apply f.
  exact x.
Defined.

(** Note that we ended the definition with [Defined], whereas proofs are ended with [Qed].
   (Actually, you can can end both with either, the difference is in whether the constructed
   object is "transparent" or "opaque". *)

(** Let us insepect both definitions. *)
Print composition_direct.
Print composition_indirect.
(** They are the same. *)

(** Let us now proceed with our main objective, the equivalence of [peirce] and [coq].

   First we will show to do proofs by hand in excruciating detail by proving that [peirce]
   implies [lem] "by hand". Then we will use Coq tactics to prove the equivalence in a far
   less painful way.

   A theorem is stated with the [Theorem] keyword or one of its synonyms ([Lemma],
   [Proposition], [Corollary], [Example], [Remark], etc.). A theorem must have a name so
   that we can refer to it later on. *)

Theorem peirce_implies_lem_by_hand: peirce -> lem.
Proof.
  (* First we unfold the definitions. *)
  unfold peirce, lem.
  (* The proof of an implication almost always starts with the application of
     [intro] tactic, which places the antecedent into the context. *)
  intro.
  (* Similarly, the proof of a universal statement usually starts with the
     application of the introduction rule for universal quantifiers. *)
  intro.
  (* By the way, we could have performed both applications of [intro] with a single
     [intros]. 

     At this point we have to use the hypothesis [H] somehow. If we say [apply H] then Coq
     will figure out that it should take [p := r \/ ~r] in [H], otherwise [H] won't be
     applicable. But it cannot guess what to take for [q], so we tell it. *)
  apply H with (p := r \/ ~r) (q := ~(r \/ ~r)).
  (* Again, we have an implication, so do [intro], except this time we write [intro G]
     to give the newly created hypothesis the name [G] (otherwise Coq calls it [H0]).
     As a rule of thumb, you should always name hyptheses explicitly if you intend to
     refer to them explicitly. *)
  intro G.
  (* Now the proof requires a bit of thought. The hypothesis [G] looks strange, as it is
     of the form "if [P] then not [P]". So in fact we can derive a contradiction from [G].
     Then our goal follows from the derived contradiction.

     The Coq tactic which means "I am going to finish the proof by deriving a statement
     [P] and its negation" is [absurd P]. But what should [P] be in our case? Let us try
     [~r]. *)
  absurd (~ r).
  (* We get two subgoals to be proved, [~~r] and [~r]. Since negation [~P] is defined in
     Coq as the implication [P -> False], we can start proving [~~r] with [intro]. *)
  intro K.
  (* How are we going to prove [False]? By using the fishy hypothesis [G], whose conclusion
     is in fact [False], once we unfold [~(r \/ ~r)] to [r \/ ~r -> False]. *)
  apply G.
  (* A direct proof of a disjunction proceeds either by [left] or [right] tactic, depending
     on which disjunct we want to prove. *)
  right.
  (* What we need to prove now is actually an assumption. So we use the [assumption] tactic. *)
  assumption.
  (* We now repeat the exercise for the other case. *)
  right.
  assumption.
  (* We are also supposed to prove [~r]. The proof is very similar to the proof of [~~r]. *)
  intro L.
  apply G.
  (* At this point we can guess the next two steps. They will be [left] and [assumption].
     We can tell Coq to perform them both in a single step by writing a semicolon between them.
     Seasoned Coq users write long and complicated sequences with semicolons that nobody can
     understand. *)
  left; assumption.
  left; assumption.
Qed.

Print peirce_implies_lem_by_hand.

(** The proof above is very detailed. In practice we would use more powerful Coq tactics. *)

Theorem peirce_iff_lem_better: peirce <-> lem.
Proof.
  (* As before, we unfold the definitions. *)
  unfold peirce, lem.
  (* We are now proving an equivalence, which is defined to be a conjunction
     of implications. So we first split the proof into two subproofs of both
     conjuncts with the [split] tactic. The tactic works on anyhting that
     looks like a finite product or a conjunction. *)
  split.
  (* From now on we won't comment on the uses of [intro] tactic. *)
  intros.
  (* We are still following the strategy from the earlier proof that
     [peirce] implies [lem]. At this point we use [H]. *)
  apply H with (q := ~(r \/ ~r)).
  intro G.
  (* In the proof above we used [absurd (~r)] and ended up doing very fine-grained
     intuitionistic propositional reasoning. Coq has a tactic which is sound and complete
     for intuitionistic propositional calculus. It is called [tauto]. *)
  tauto.
  (* Viola, one implication is done. Now the other one. *)
  intros H p q G.
  (* To prove Peirce's law from LEM we need to use a well-chosen instance of
     LEM. The [tauto] tactic cannot guess it, we have to tell Coq what to use.
     
     Suppose you are thinking "well, since [p] or [~p] holds by [H], we could consider
     the two cases [p] and [~p]". In the language of Coq tactics this means that you
     want to use the assertion [H p]. There are several ways to do that. A useful
     one to know is [destruct], which eliminates a statement. *)
  destruct (H p).
  (* Coq destructed [H p], which is the disjunction [p \/ ~p] by splitting the
     proof into two parts. In one part we get the assumption [p] and in the other
     [~p]. *)
  assumption.
  (* Presumably [tauto] is smart enough to figure this out. *)
  tauto.
  (* Indeed it is. *)
Qed.

(** Our proof is getting better, but there are still a couple of details that we could
   write more succinctly. So we provide yet another proof. *)

Theorem peirce_iff_lem_cool: peirce <-> lem.
Proof.
  unfold peirce, lem.
  (* Here we see an equivalence between two universal statements. From this we know
     that we are going to do a [split] followed by [intros] in each of the subproofs,
     so we perform both steps in on go by combining them with the semicolon. *)
  split; intros.
  (* Now we know that as soon as we tell Coq to prove the statement by applying [H] with
     (q := ~ (r \/ r)), Coq can do the rest with [tauto]. We use semicolon again. *)
  apply H with (q := ~ (r \/ ~r)); tauto.
  (* Similarly, for the other implication we tell Coq to use [H p] and finish it off with
     [tauto]. *)
  destruct (H p); tauto.
  (* That's four lines: one to unfold the definitions, one to split the equivalence,
     and two lines of hints on how to prove each of the resulting implications. *)
Qed.

