Require Import Logic_Type.
Require Import ssreflect ssrfun ssrbool.

(* In this file we study here the basic properties induced by the following *)
(* game: he inhabitants of a type (A : Type) are the points of a category, *)
(* whose morphisms are the identity proofs between to provably equal *)
(*inhabitants of A. An identity proof is a term of type (@identity A) where *)
(* identity is the inductive type: *)
(* Inductive identity (A : Type) (a : A) : A -> Type :=  identity_refl : a = a*)
(* The only constructor identity_refl of identity is hence seen as the identity*)
(* morphism of the category *)


(* An incantation to get a satisfactory behaviour wrt implicit arguments by default *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Instead of what is done in the main branch of HoTT we try to avoid constructing the *)
(* witness paths by an automated tactic but instead provide paths combinators that are *)
(* essentially inspried by the groupoid structure identity proofs are equipped with. *)
(* USING SUCH AUTOMATION TO BUILD THE BODY OF DEFINITIONS IS DANGEROUS. See the *)
(* example of concat2 below *)

(* We also try to be cleaner about the status of reduction : if a constant has a *)
(* computational content we expect to be usefull, as wittness for a "Defined" *)
(* command ending the script governing its definition, then it is probably a bad idea *)
(* in general to use an automation tactic such as hott_simpl in its script, since we *)
(* loose control over the program we define. It is also important for documentation purposes*)
(* and in my (assia) case for pedagogical purposes ...*)
(* I would even like this kind or computationally meaningfull definitions to be defined *)
(* as often as possible using an explicit-body definition, ie with the *)
(* Definition ... := .... syntax. This will probably not scale, but then I would prefer *)
(* the script to use explicitly identified combinators and/or explicit dependent *)
(* eliminations as opposed to calls to autorewrite using a databasis to document better *)
(* what the body of the definition is intended to look like. *)
(* As a consequence automation should only happen in opaque (Qed-ending) definitions.*)
(* But we will try understand also what should be computable and what shouldn't since *)
(* this may severly affects the performances of proof checking. *)

(* The ssreflect libraries are little used here, except that they feature the *)
(* correct declarations of implicit arguments. The ssreflect tacics are also *)
(* seldom unavoidable, except for the control they allow over the selection of *)
(* rewrite patterns, occurrences to be generalized,... The hope is that this improved *)
(* control will allow for getting rid of the automation *)

(* We start by defining group-theory-like notations for the basic operations, and  *)
(* combinators. We declare them in a module to let users decide of their relevance: *)
(* the module is imported, notations become available both at parsing and display *)
(* One des not see them nor can we use them if the module is not imported. *)

(* We declare a notation scope called path_scope to be able to declare notations using *)
(* very widely used symbols like infix (_ * _) for paths and still being non ambguous *)
(* In order to disambiguate when necessary we can surrond an expression to be interpreted *)
(* in that scope by parentheses, labeled with the 'path' label : ( _ )%path *)

Delimit Scope path_scope with path.


(* The path obtained by applying the function f to the path p. *)
(* Was: map *)
(* I am still slightly disturbed by this 'map' vocabulary but could not find a better*)
(* name by lack of culture. I temporarilly use 'resp' instead, following *)
(* Hoffman & Streicher *)
(* Note that it is really importat here that the constant (f_equal) *)
(* hidden by this notation is transparent. *)
(* In our modified version of Coq's prelude we have even declared it *)
(* using an explicit-body definition, using *)
(* the Definition ... := .... syntax. The original standard libray seems to opacify it *)
(* using the Opaque command but this has no effect in fact since it is in a section. *)
(* We reorder the arguments of f_equal so that it behaves more conveniently for *)
(* our purpose *)
Definition resp A B x y f := @f_equal A B f x y.
Arguments resp [A B] [x y] f _.

(* The inverse of a path: was opposite. esym is a definition for identity_sym see ssrfun *)
Notation invp := esym.

(* If there is a morphism (path) r from (f : A -> B) and (g : A -> B), then *)
(* for any morphism (path) p : f x = f y there is exists a path g x = g y *)
(* The operation which computes the path g x = g y from f x= f y is a kind *)
(* of conjugation, hence the name and notation we chose. *)
(* The most natural usefull morphism (path) between (f : A -> B) and *)
(* (g : A -> B) is not really (f = g) but rather the pointwise equality *)
(* (forall x y, f x = g x), which is derivable from (f = g), the converse *)
(* being the axiom of extensional equality.*)
(* (_ =1 _) is the ssreflect notation for unary pointwise equality. see ssrfun.v *)
(* Was not in the original file ? *)
Definition conjp A B (f g : A -> B) (r : f =1 g) (x y : A) (p : f y = f x) :=
  identity_trans (invp (r y)) (identity_trans p (r x)).

(* This is equivalent to 
Module PathNotations.
...
...
End PathNotations.

Import PathNotations.
*)

Module Import PathNotations.
(* Instead of re-defining a type 'paths', we use the type identity present *)
(* in Coq's prelude. Use About identity for more info. *)

(* Was idpath *)
Notation "1" := (identity_refl _) : path_scope.

(* The composition of two paths: was compose or (_ @ _) *)
Notation "p * q" := (identity_trans p q) : path_scope.


Notation "p ^-1" := (invp p) : path_scope.

(* The composition of p with the inverse of q: not present in the original file *)
Notation "p / q" := (p * q^-1)%path : path_scope.

(* We use here the notation suggested by Dan Grayson : to denote the formerly called *)
(* (map f) as f_* . Unfortunately we cannot do that as such since the _ is understood *)
(* by Coq's parser to be part of the identifier, so we insert a backquote in between. *)
(* Not very satisfactory but again, waits for a better ascii art idea...*)
Notation "f `_*" := (resp f) (at level 2, format "f `_*") : path_scope.

(* Conjugation *)
Notation "q ^ p" := (conjp p q)%path : path_scope.
(* Cyril : Notation "q ^ p" := ((p _ * q) / p _)%path : path_scope. *)

End PathNotations.

(* After the end of this module, the notations are assumed the module is imported *)


Section WhyAutomationInDefinitionsIsNotRobust.

(* Inside this section we will only work in notation scope path_scope, so we declare that *)
(* everything should be interpreted as if surrounded by some (_)%path. *)

Open Local Scope path_scope.

(* I still do not know if I will need concat2, but we use it as an example:*)
(* If we want to have an opaque lemma, we use the 'Lemma' vernac command and*)
(* Qed ending keyword. Note that the original Paths.v crafts this def using *)
(* the path_induction tactic, when here a simple non dependent elim as *)
(* performed by the rewrite tactic is sufficient. Note that we have tuned*)
(* the ssreflect rewrite tactic so that it works with 'identity' instead of 'eq'*)
Lemma opaque_concat2 A (x y z : A)(p p' : x = y)(q q' : y = z) :
  p = p' -> q = q' -> p * q = p' * q'.
Proof. by move=> hp hq; rewrite hp hq. Qed.

(* If we want a computational definition, we can still define it using tactics*)
(* but for sake of documentation we should use the 'Definition' vernac command*)
(* and end the definition by a Defined of course. *)
Definition concat2 A (x y z : A)(p p' : x = y)(q q' : y = z) :
  p = p' -> q = q' -> p * q = p' * q'.
Proof. move=> hp hq; rewrite hp hq. reflexivity. Defined.

(* In order to test the transparency of definitions obtained this way we clone it*)
Definition concat2a A (x y z : A)(p p' : x = y)(q q' : y = z) :
  p = p' -> q = q' -> p * q = p' * q'.
Proof. move=> hp1 hq1; rewrite hp1 hq1. reflexivity. Defined.

(* And prove the sanity check lemma *)
Lemma sanity_check_concat2_a A (x y z : A)(p p' : x = y)(q q' : y = z)
  (hp : p = p')(hq : q = q') : concat2a hp hq = concat2 hp hq.
reflexivity.
Qed.

(* Now we define a third version of the lemma *)
Definition concat2b A (x y z : A)(p p' : x = y)(q q' : y = z) :
  p = p' -> q = q' -> p * q = p' * q'.
Proof. move=> hp hq; rewrite hq hp. reflexivity. Defined.

(* And try to prove the associated sanity check lemma *)
Lemma sanity_check_concat2_b A (x y z : A)(p p' : x = y)(q q' : y = z)
  (hp : p = p')(hq : q = q') : concat2a hp hq = concat2b hp hq.
(* reflexivity.*) Abort.

(* Conclusion : an automated tacic, even is it perfectly documents the proof search*)
(* strategy it uses in terms of structuration of the data-base, is a very fragile way*)
(* of defining constants. The explicit script which documents the order in which the*)
(* eliminations have been performed is much more robust. With a little more training*)
(* on Coq dependent types, one could even define concat2 by providing an explicit *)
(* proof term. *)
Definition body_concat2 A (x y z : A)(p p' : x = y)(q q' : y = z)
  (hp : p = p')(hq : q = q') : p * q = p' * q' := 
  match hq in _ = rhsq return p * q = p' * rhsq with
    |identity_refl => 
      match hp in _ = rhsp return p * q = rhsp * q with 
        | identity_refl => 1 end
  end.

(* Note that the deepest match is in fact programming an operation of type:
 (x y z : A)(p p' : x = y) (hp : p = p') : p * q = p' * q
*)

(* I use this notation only in the current section, to make the statement of
concat2_interchange look more like its original version. I have replaced the
infix @@ by ++ just because it is reserved in datatype.v already with a level etc. 
My current bet is that it should be a lemma and not a definition. Hence it would
be acceptable to use automation for this script. Since we have remove the Ltac
machinery, we do it by hand and it is not so long although boring. *)
 
Local Notation "p ++ q" := (concat2 p q).

(** The interchange law for concatenation. *)
Lemma concat2_interchange A (x y z : A) : forall (p p' p'' : x = y) (q q' q'' : y = z)
  (a : p = p') (b : p' = p'') (c : q = q') (d : q' = q''),
  (a ++ c) * (b ++ d) = (a * b) ++ (c * d).
Proof.
intro p; case p; intros p' p''.
intro q; case q; intros q' q''.
intro a; case a; intro b; case b; intro c; case c; intro d; case d.
reflexivity.
Qed.
End WhyAutomationInDefinitionsIsNotRobust.


(* In this section, we review basic properties of the above operations. *)
(* These should be seen as combinators for further proofs/constructions *)
(* One of the main difficulties of this kind of base library is to come up *)
(* with a systematic way of stating and naming facts, and to be comprehensive *)
(*  while nottoo verbose. For the time being we only reproduce things already *)
(* present in Paths.v plus some extra results meant as exemples of what can be *)
(* done with this automation-free infrastructure and we will probably need not *)
(* be more systematic at some point *)
Section GroupoidTheoryOfPaths.

(* Inside this section we will only work in notation scope path_scope, so we declare that *)
(* everything should be interpreted as if surrounded by some (_)%path. *)
Local Open Scope path_scope.


(* Here we use the :> type cast notation of Coq to specify in which type the identity *)
(* path should be taken since the notation hides it and the present context of the lemma *)
(* cannot help infering it. This is also a neat way of documenting the endpoints of *)
(* a path. *)
(* We could use here the reflexivity tactic, which would put here the identity path.*)
(* It would be exactly equivalent... *)
(* Was: opposite_idpath *)
Lemma path1V  A (x : A) : 1 ^-1 = 1 :> (x = x). 
Proof. exact: 1. Qed.

(* Was: idpath_right_unit *)
Lemma mulp1 A (x y : A) (exy : x = y) : exy * 1 = exy.
Proof. reflexivity. Qed.

(* Here we need a dependent case since identity_trans is defined by a match on*)
(* its second argument and not its first *)
(* I state explicitly the proof term here since it took me a while to *)
(* write it by hand (shame on me :-)). Moreover the proof term generated by *)
(* the dependent case as displayed by the Show Proof command is 1) much less *)
(* readable since obtained from a generic pattern, 2) cannot be simply *)
(* copy-pasted, I still have to understand why. *)
(* Note that in the pattern of the branch we cannot use the 1 notation instead of *)
(* identity_refl since 1 is a notation for (@identity_refl _) *)
(* Was: idpath_left_unit *)
Lemma mul1p A (x y : A) (exy : x = y) : 1 * exy = exy.
exact: (match exy as i return 1 * i = i with |identity_refl => 1 end).
Qed.

(* Alternative proof script using the elimination scheme *)
(* Lemma mul1p A (x y : A) (exy : x = y) : 1 * exy = exy. *)
(* pose P := fun (a0 : A)(p : x = a0) => 1 * p = p. *)
(* have h1 : P x 1. *)
(*   rewrite /P. exact: 1. *)
(*   exact: (identity_rect x P h1 y exy). *)
(* Qed. *)

(* Alternative proof using the dependent case tactic 
Lemma mul1p A (x y : A) (exy : x = y) : 1 * exy = exy.
Proof. by case exy. Qed.
*)



(* (case: _ / r) is the ssreflect syntax to perfom dependent elimination on r *)
(* and hence replaces z by t everywhere in the goal. Here we use the 'case' *)
(* standard tactic which performs dependent elimination. *)
(* Conclusion : rewrite r performs the non dependent elimination of an identity proof *)
(* and case: _ /r (resp. case) performs the dependent elimination *)
(* Was: concat_associativity *)
Lemma mulpA A (x y z t : A) (p : x = y) (q : y = z) (r : z = t) :
  p * (q * r) = (p * q) * r.
Proof. case r; case q; reflexivity. Qed.

(* An alternative way of ending the proof in case its content is non computationaly *)
(* usefull: the by prenex tactical is an alias for the done Ltac defined in ssreflect.v *)
(* Here it only does reflexivity but in general it may do also "trivial" (:= auto 1) and *)
(* hence use a customized database. What is of primary importance is to close subgoals with *)
(* tactics which fail if they do not close the current goal. Here it is of little use since *)
(* the proof does not branch but it is good to take this habit in a systematic way to come *)
(* up with scripts that are easy to maintain. *)

(* Was: opposite_right_inverse *)
Lemma mulpV A (x y : A) (p : x = y) : p / p = 1.

Proof. by case p. Qed.

(* Was: opposite_left_inverse *)
Lemma mulVp A (x y : A) (p : x = y) : p^-1 * p = 1.
Proof. by case p. Qed.

(* Was: opposite_left_inverse_with_assoc_right *)
Lemma mulKp A (x y z : A) (p : x = y) (q : y = z) : p^-1 * (p * q) = q.
Proof. by case q; case p. Qed.

(* Was: opposite_right_inverse_with_assoc_right *)
Lemma mulVKp A (x y z : A) (p : x = y) (q : x = z) : p * (p^-1 * q) = q.
Proof. by case q; case p. Qed.

(* Was: opposite_right_inverse_with_assoc_left *)
Lemma mulpK A (x y z : A) (p : x = y) (q : y = z) : (p * q) / q = p.
Proof. by case q; case p. Qed.

(* Here I use the ssreflect dependent case syntax to be able to specify that *)
(* I want to generalize (really 'revert' in a std tac language) q before casing p *)
(* and then perform dependant case elimination on the generalized q in prenex position *)
(* Was: opposite_left_inverse_with_assoc_left *)
Lemma mulpVK A (x y z : A) (p : x = z) (q : y = z) : (p / q) * q = p.
Proof. by case: _ / p q; case: _ /. Qed.

(* Was: opposite_concat *)
Lemma invpM A (x y z : A) (p : x = y) (q : y = z) : (p * q)^-1 =  q^-1 / p.
Proof. by case q; case p. Qed.

(* This lemma has already been proven in ssrfun (see esymK) but we restate it here *)
(* to document its type and provide a consistent name *)
(* Was: opposite_opposite *)
Lemma invpK A (x y : A)(p : x = y) : p ^-1 ^-1 = p. 
Proof. exact: esymK. Qed.

(* Not sure that one really needs to be there *)
(* Note that in ssr syntax, rewrite can be chained as follows: *)
(* Was: opposite_left_inverse_with_assoc_both *)
Lemma mulpVKp A (x y z w : A) (p : x = y) (q : z = y) (r : y = w) : 
  (p * q^-1) * (q * r) = p * r.
Proof. by rewrite mulpA mulpVK. Qed.

(* Not sure that one really needs to be there *)
(* Was: opposite_right_inverse_with_assoc_both *)
Lemma mulpKp A (x y z w : A) (p : x = y) (q : y = z) (r : y = w) : 
  p * q * (q^-1 * r) = p * r.
Proof. by rewrite mulpA mulpK. Qed.

(* Now examples of easy lemmas that were not in the original development but that we *)
(* can prove without difficulties (and withour automation building on the previous *)
(* elementary ones. *)

(* move-> is an ssreflect syntax to rewrite the equality in prenex position without *)
(* having to name it *)
(* Was: concat_moveright_onleft *)
Lemma mulpLRl A (x y z : A) (p : x = z) (q : y = z) (r : y = x) :
  p = r^-1 * q -> r * p = q.
Proof. by move->; rewrite mulVKp. Qed.

(* Was: concat_moveleft_onright, but with equalities in the other direction *)
Lemma mulpLRr A (x y z : A) (p : x = z) (q : y = z) (r : y = x) :
  r = q / p -> r * p = q.
Proof. by move->; rewrite mulpVK. Qed.

(* Was: concat_moveleft_onleft *)
Lemma mulpRLl A (x y z : A) (p : x = z) (q : y = z) (r : y = x) :
  r^-1 * q = p -> q = r * p.
Proof. by move<-; rewrite mulVKp. Qed.

(* Was: concat_moveright_onright, but with equalities in the other direction*)
Lemma mulpRLr A (x y z : A) (p : x = z) (q : y = z) (r : y = x) :
  q / p = r -> q = r * p.
Proof. by move<-; rewrite mulpVK. Qed.

(* Was not in the original file ? *) 
Lemma invp_div A (x y z : A) (p : x = z) (q : y = z) : (p / q)^-1 = q / p.
Proof. by rewrite invpM esymK. Qed.

(* move=> is "intros" *)
(* Was not in the original file ? *)
Lemma mulpN_eq1  A (x y : A) (p q : x = y) : p / q = 1 -> p = q.
Proof. by move=> h; rewrite -(mul1p q) (mulpRLr h). Qed.

(* Was not in the original file ? *) 
Lemma mulp_eq1  A (x y : A) (p : x = y) (q : y = x) : p * q = 1 -> p = q^-1.
Proof. by rewrite -{1}[q]invpK => H; apply: mulpN_eq1. Qed.

(* Consider a type (A : Type) as a category whose points are the inhabitants *)
(* (a : A) and morphisms are inhabitants (p : @identity A a b). Then for *)
(* any (A B : Type), and any f : A -> B, f can be seen as un functor from A to B *)
(* wich transforms objects by a |-> f a and morphisms by p |-> resp f p*)
(* We prove this. *)

(* Was: idpath_map *)
Lemma resp1f A B x (f : A -> B) : f`_* 1 = 1 :> (f x = f x).
Proof. reflexivity. Qed.

(* Was: concat_map *)
Lemma resppM A B (f : A -> B) (x y z : A) (exy : x = y) (eyz : y = z) :
  f`_* (exy * eyz) = (f`_* exy) * (f`_* eyz ).
Proof. by case eyz; case exy. Qed.

(* We can move one level higher in the stack of groupoids: if (A : Type) *)
(* I_A := (@identity A) can also be equipped with a similar categorical structure*)
(* where now objects are the (p : (@identity A x y)) for any (x y : A) and *)
(* morphisms are again the inhabitants of (@identity I_A) *)
(* We also consider the category of types where points are types (A : Type) *)
(* and morphisms between A and B are functions living in the type A -> B *)
(* Now resp is a functor bewteen these two categories which acts on objects as*)
(* A |-> (@identity A) and on morphisms as f |-> resp f. We prove this. *)

(* id is the ssreflect notation for the polymorphic identity function with the appropriate *)
(* implicit args declaration allowing to drop the type argument. see ssrfun.v *) 
(* Was: idmap_map *)
Lemma respidp A (x y : A) (p : x = y) : id`_* p = p.
Proof. by case p. Qed.

(* (_ \o _) is the infix notation for composition of functions according on their resp. *)
(* codomain and domain. see ssrefun.v *)
(* Was: compose_map *)
Lemma resppcomp A B C (f : A -> B) (g : B -> C) (x y : A) (p : x = y) :
  (g \o f)`_* p = g`_* (f`_* p).
Proof. by case p. Qed.

(* Was: opposite_map *)
Lemma resppV A B (f : A -> B) (x y : A) (p : x = y) : (f`_* p)^-1 = f`_* p^-1.
Proof. by case p. Qed.


(* To unfold the definition of a conjugation by a simple rewrite operation *)
(* We use here the _ = _ :> notation to document the endpoints of the obtained path *)
(* The statement does not need it but it is quite convenient to see it explicitely *)
Lemma conjpE A B (f g : A -> B) (r : f =1 g) (x y : A) (p : f y = f x) :
 p ^ r = (r y)^-1 * (p * (r x)) :> (g y = g x).
Proof. reflexivity. Qed.

(* Was not in the original file ? *)
Lemma conjpM A (f g : A -> A) (r : f =1 g) (x y z : A)
  (p : f x = f y) (q : f y = f z) : (p * q) ^ r = p ^ r * q ^ r.
Proof. by rewrite !conjpE !mulpA mulpK. Qed.

(* starting from now (at least) the naming convention starts to be really shaky *)


(* We need to simpl before berforming dependent case on (p x) and that's what => /= does *)
(* Was not in the original file ? *)
Lemma mulprespLR A B (f g : A -> B) (p : f =1 g) (x y : A) (q : x = y) :
  (f`_* q) * (p y) = (p x) * (g`_* q).
Proof. by case q => /=; case (p x). Qed.

(* Was  homotopy_naturality_toid *)
Lemma respeq1mulp A (f : A -> A) (p : f =1 id) (x y : A) (q : x = y) :
  (f`_* q) * (p y) = (p x) * q.
Proof. by rewrite (mulprespLR p) respidp. Qed.

(* Was: homotopy_naturality_fromid, but the equality was stated the other way around*)
Lemma mulprespeq1 A (f : A -> A) (p : id =1 f) (x y : A) (q : x = y) :
  (p x) * (f`_* q) =  q * (p y).
Proof. by rewrite -(mulprespLR p) respidp. Qed. 

(* Here we see how this "conjugation" operation appears in a natural way *)
(* Was not in the original file ? *)
Lemma resp_eqp A B (f g : A -> B) (p : f =1 g)
           (x y : A) (q : x = y) : g`_* q =  (f`_* q) ^ p.
Proof. by rewrite (conjpE p) mulprespLR mulKp. Qed.

(* A slightly different version of the previous lemma was actually in the *)
(* original file *)
Lemma homotopy_naturality {A B} {x y : A} (f g : A -> B) (p : f =1 g) (q : x = y) :
  (f`_* q) * p y = p x * (g`_* q).
Proof. rewrite (resp_eqp p) mulVKp; reflexivity. Qed.

(* Was not in the original file ? *)
Lemma resp_eqidp A (f : A -> A) (p : f =1 id) (x y : A) (q : x = y) : (f`_* q) ^ p = q.
Proof. by rewrite -(resp_eqp p) respidp. Qed.

(* Was not in the original file ? *)
Lemma resp_eqpid A (f : A -> A) (p : id =1 f) (x y : A) (q : x = y) : (f`_* q) = q ^ p.
Proof. by rewrite (resp_eqp p) respidp. Qed.

(* cancel f g := g is a left inverse of f ie f is a right inverse of g see ssrfun.v *)
(* Was not in the original file ? *)
Lemma can_respp A B (f : A -> B) (g : B -> A) (p : cancel f g) 
      (x y : A) (q : x = y) : g`_* (f`_* q) ^ p = q.
Proof. by rewrite -resppcomp (resp_eqidp p). Qed.

(* Was not in the original file ? *)
Lemma conj_canV  A B (f : A -> B) (g : B -> A) (p : id =1 g \o f) 
      (x y : A) (q : x = y) : g`_* (f`_* q) = q ^ p.
Proof. by rewrite -resppcomp (resp_eqpid p). Qed.

(* From now on I just translate the material present in Paths which was not already
   delt with in the previous lemmas. I need to be more cultured to make a more 
   clever job. *)

(* Here is the definition of whisker operations I keep mostly unchanged *)
(* except by keppeing only the whiskering operation defs transparent (and *)
(* explicitly defined). Do not know  if this need to be kept. *)

(** We also have whiskering operations which compose a 1-path with
   a 2-path. We do not introduce even more notation, however. *)

Definition whisker_right {A} {x y z : A} {p p' : x = y} (q : y = z) (hp : p = p'):
 p * q = p' * q := 
 match hp in _ = rhs return p * q = rhs * q with |identity_refl => 1 end.

Definition whisker_left {A} {x y z : A} {q q' : y = z} (p : x = y) (hq : q = q') :
 p * q = p * q' :=
 match hq in _ = rhs return p * q = p * rhs with |identity_refl => 1 end.

(** Basic properties of whiskering. *)

Lemma whisker_right_toid {A} {x y : A} (p : x = x) (q : x = y) :
  p = 1 -> p * q = q.
Proof. by move->; rewrite mul1p. Qed.

Lemma whisker_right_fromid {A} {x y : A} (p : x = x) (q : x = y) :
  1 = p -> q = p * q.
Proof. by move<-; rewrite mul1p. Qed.

Lemma whisker_left_toid {A} {x y : A} (p : y = y) (q : x = y) :
  p = 1 -> q * p = q.
Proof. by move->; rewrite mulp1. Qed.

Definition whisker_left_fromid {A} {x y : A} (p : y = y) (q : x = y) :
  1 = p -> q = q * p.
Proof. by move<-; rewrite mulp1. Qed.

(** The interchange law for whiskering. *)
Definition whisker_interchange {A} {x y z : A} : forall (p p' : x = y) (q q' : y = z)
  (a : p = p') (b : q = q'),
  (whisker_right q a) * (whisker_left p' b) = (whisker_left p b) * (whisker_right q' a).
Proof.
intro p; case p; intro p'. 
intro q; case q; intro q'.
intro a; case a; intro b; case b. 
reflexivity.
Qed.

(** Taking opposites of 1-paths is functorial on 2-paths. *)
Definition opposite2 {A} {x y : A} {p q : x = y} (a : p = q) : (p^-1 = q^-1) :=
  (invp)`_* a.

Lemma constmap_map {A B : Type} {b : B} {x y : A} (p : x = y) :
  (fun _ => b)`_* p = 1.
Proof. by case p. Qed.

(* May be should I define a constant or abbreviation for resp, something like
  (resp (resp f)) is for more readable *)
(** We can also map paths between paths. **)
Definition resp2 {A B} {x y : A} (p q : x = y) (f : A -> B)(u : p = q) : (f`_* p = f`_* q) :=
  (resp f)`_* u.

(** The type of "homotopies" between two functions [f] and [g] is
   [forall x, f x = g x].  These can be derived from "paths" between
   functions [f = g]; the converse is function extensionality. *)

Definition happly {A B} {f g : A -> B} : (f = g) -> (forall x, f x = g x) :=
  fun p x => (fun h => h x)`_* p.

(** Similarly, [happly] for dependent functions. *)

Definition happly_dep {A} {P : A -> Type} {f g : forall x, P x} :
  (f = g) -> (forall x, f x = g x) := fun p x => (fun h => h x)`_* p.

(** [happly] preserves path-concatenation and opposites. *)

(* Was : happly_concat *)
Lemma happlyM {A B} (f g h : A -> B) (p : f = g) (q : g = h) (x : A) :
  happly (p * q) x = happly p x * happly q x.
Proof. revert q; case p; intro q; case q. reflexivity. Qed.

(* Was: happly_opp *)
Lemma happlyV {A B} (f g : A -> B) (p : f = g) (x : A) :
  happly p^-1 x = (happly p x)^-1.
Proof. case p. reflexivity. Qed.

Lemma happly_depM {A} P (f g h : forall a : A, P a) (p : f = g) (q : g = h) (x:A) :
  happly_dep (p * q) x = happly_dep p x * happly_dep q x.
Proof. move: q; case: p; intro p; intro q; case q. reflexivity. Qed.

Lemma happly_depV {A} P (f g : forall a : A, P a) (p : f = g) (x : A) :
  happly_dep p^-1 x = (happly_dep p x)^-1.
Proof. case p; reflexivity. Qed.

(** How happly interacts with resp. *)

Lemma map_precompose {A B C} (f g : B -> C) (h : A -> B)
  (p : f = g) (a : A) :
  happly ((fun f' => f' \o h)`_* p) a = happly p (h a).
Proof. case p; reflexivity. Qed.

Lemma map_postcompose {A B C} (f g : A -> B) (h : B -> C)
  (p : f = g) (a : A) :
  happly ((fun f' => h o f')`_* p) a = h`_* (happly p a).
Proof. case p; reflexivity. Qed.

Lemma map_precompose_dep {A B} P (f g : forall b : B, P b) (h : A -> B)
  (p : f = g) (a : A) :
  happly_dep ((fun f' => fun a => f' (h a))`_* p) a = happly_dep p (h a).
Proof. case p; reflexivity. Qed.

(** Paths in cartesian products. *)

Definition prod_path {X Y} {x x' : X} {y y' : Y} (px : x = x') (py : y = y')
  : (x, y) = (x', y') := 
  match px in _ = rhsx return (x, y) = (rhsx, y') with
    |identity_refl => 
      match py in _ = rhsy return (x, y) = (x, rhsy) with | identity_refl => 1 end
  end.

(** Cancellability of concatenation on both sides. *)
(* Here we use the std 'case' tactic which peforms a dependent case, combined with the*)
(* '=>' introduction tactical of ssreflect. See how rewrite switch close the goal *)
(* Was: concat_cancel_right *)
Lemma mulp_injr {A} {x y z : A} (r : y = z) : forall (p q : x = y), p * r = q * r -> p = q.
Proof. case r => p q; rewrite !mulp1; exact. Qed.

(* Here I explicitely ask r *not* to be implicit. So that we can provide it *)
(* by hand easily as in the proof of htoid_well_pointed below. Let us see if *)
(* usage confirms that it is what we want *)
Arguments mulp_injr {A} {x y z} r p q _.

(* Was: concat_cancel_left *)
Lemma mulp_injl {A} {x y z : A} (p : x = y): forall  (q r : y = z), (p * q = p * r) -> (q = r).
Proof. case p; intro q; case q => r; rewrite !mul1p; exact. Qed.

Arguments mulp_injl {A} {x y z} p q r _.

(** If a function is homotopic to the identity, then that homotopy
   makes it a "well-pointed" endofunctor in the following sense. *)

(* Seting Arguments of mulp_injr right by hand make possible to avoid the fragile*)
(* syntax 'apply concat_cancel_right with (r := p x)' present in the original *)
(* proof script for this lemma *)
Lemma htoid_well_pointed {A} (f : A -> A) (p : f =1 id) (x : A) :
  f`_* (p x) = p (f x).
Proof. by apply: (mulp_injr (p x)); rewrite respeq1mulp. Qed.

End GroupoidTheoryOfPaths.

