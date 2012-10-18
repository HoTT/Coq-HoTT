(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

(******************************************************************************)
(* The seq type is the ssreflect type for sequences; it is an alias for the   *)
(* standard Coq list type. The ssreflect library equips it with many          *)
(* operations, as well as eqType and predType (and, later, choiceType)        *)
(* structures. The operations are geared towards reflection: they generally   *)
(* expect and provide boolean predicates, e.g., the membership predicate      *)
(* expects an eqType. To avoid any confusion we do not Import the Coq List    *)
(* module.                                                                    *)
(*   As there is no true subtyping in Coq, we don't use a type for non-empty  *)
(* sequences; rather, we pass explicitly the head and tail of the sequence.   *)
(*   The empty sequence is especially bothersome for subscripting, since it   *)
(* forces us to pass a default value. This default value can often be hidden  *)
(* by a notation.                                                             *)
(*   Here is the list of seq operations:                                      *)
(*  ** Constructors:                                                          *)
(*                        seq T == the type of sequences with items of type T *)
(*                       bitseq == seq bool                                   *)
(*             [::], nil, Nil T == the empty sequence (of type T)             *)
(* x :: s, cons x s, Cons T x s == the sequence x followed by s (of type T)   *)
(*                       [:: x] == the singleton sequence                     *)
(*           [:: x_0; ...; x_n] == the explicit sequence of the x_i           *)
(*       [:: x_0, ..., x_n & s] == the sequence of the x_i, followed by s     *)
(*                    rcons s x == the sequence s, followed by x              *)
(*  All of the above, except rcons, can be used in patterns. We define a view *)
(* lastP and and induction principle last_ind that can be used to decompose   *)
(* or traverse a sequence in a right to left order. The view lemma lastP has  *)
(* a dependent family type, so the ssreflect tactic case/lastP: p => [|p' x]  *)
(* will generate two subgoals in which p has been replaced by [::] and by     *)
(* rcons p' x, respectively.                                                  *)
(*  ** Factories:                                                             *)
(*             nseq n x == a sequence of n x's                                *)
(*          ncons n x s == a sequence of n x's, followed by s                 *)
(* seqn n x_0 ... x_n-1 == the sequence of the x_i (can be partially applied) *)
(*             iota m n == the sequence m, m + 1, ..., m + n - 1              *)
(*            mkseq f n == the sequence f 0, f 1, ..., f (n - 1)              *)
(*  ** Sequential access:                                                     *)
(*      head x0 s == the head (zero'th item) of s if s is non-empty, else x0  *)
(*        ohead s == None if s is empty, else Some x where x is the head of s *)
(*       behead s == s minus its head, i.e., s' if s = x :: s', else [::]     *)
(*       last x s == the last element of x :: s (which is non-empty)          *)
(*     belast x s == x :: s minus its last item                               *)
(*  ** Dimensions:                                                            *)
(*         size s == the number of items (length) in s                        *)
(*       shape ss == the sequence of sizes of the items of the sequence of    *)
(*                   sequences ss                                             *)
(*  ** Random access:                                                         *)
(*         nth x0 s i == the item i of s (numbered from 0), or x0 if s does   *)
(*                       not have at least i+1 items (i.e., size x <= i)      *)
(*               s`_i == standard notation for nth x0 s i for a default x0,   *)
(*                       e.g., 0 for rings.                                   *)
(*   set_nth x0 s i y == s where item i has been changed to y; if s does not  *)
(*                       have an item i it is first padded with copieds of x0 *)
(*                       to size i+1.                                         *)
(*       incr_nth s i == the nat sequence s with item i incremented (s is     *)
(*                       first padded with 0's to size i+1, if needed).       *)
(*  ** Predicates:                                                            *)
(*          nilp s == s is [::]                                               *)
(*                 := (size s == 0)                                           *)
(*         x \in s == x appears in s (this requires an eqType for T)          *)
(*       index x s == the first index at which x appears in s, or size s if   *)
(*                    x \notin s                                              *)
(*         has p s == the (applicative, boolean) predicate p holds for some   *)
(*                    item in s                                               *)
(*         all p s == p holds for all items in s                              *)
(*        find p s == the index of the first item in s for which p holds,     *)
(*                    or size s if no such item is found                      *)
(*       count p s == the number of items of s for which p holds              *)
(*      constant s == all items in s are identical (trivial if s = [::])      *)
(*          uniq s == all the items in s are pairwise different               *)
(*    subseq s1 s2 == s1 is a subsequence of s2, i.e., s1 = mask m s2 for     *)
(*                    some m : bitseq (see below).                            *)
(*   perm_eq s1 s2 == s2 is a permutation of s1, i.e., s1 and s2 have the     *)
(*                    items (with the same repetitions), but possibly in a    *)
(*                    different order.                                        *)
(*  perm_eql s1 s2 <-> s1 and s2 behave identically on the left of perm_eq    *)
(*  perm_eqr s1 s2 <-> s1 and s2 behave identically on the rightt of perm_eq  *)
(*    These left/right transitive versions of perm_eq make it easier to chain *)
(* a sequence of equivalences.                                                *)
(*  ** Filtering:                                                             *)
(*           filter p s == the subsequence of s consisting of all the items   *)
(*                         for which the (boolean) predicate p holds          *)
(* subfilter s : seq sT == when sT has a subType p structure, the sequence    *)
(*                         of items of type sT corresponding to items of s    *)
(*                         for which p holds.                                 *)
(*              rem x s == the subsequence of s, where the first occurrence   *)
(*                         of x has been removed (compare filter (predC1 x) s *)
(*                         where ALL occurrences of x are removed).           *)
(*              undup s == the subsequence of s containing only the first     *)
(*                         occurrence of each item in s, i.e., s with all     *)
(*                         duplicates removed.                                *)
(*             mask m s == the subsequence of s selected by m : bitseq, with  *)
(*                         item i of s selected by bit i in m (extra items or *)
(*                         bits are ignored.                                  *)
(*  ** Surgery:                                                               *)
(* s1 ++ s2, cat s1 s2 == the concatenation of s1 and s2.                     *)
(*            take n s == the sequence containing only the first n items of s *)
(*                        (or all of s if size s <= n).                       *)
(*            drop n s == s minus its first n items ([::] if size s <= n)     *)
(*             rot n s == s rotated left n times (or s if size s <= n).       *)
(*                     := drop n s ++ take n s                                *)
(*            rotr n s == s rotated right n times (or s if size s <= n).      *)
(*               rev s == the (linear time) reversal of s.                    *)
(*        catrev s1 s2 == the reversal of s1 followed by s2 (this is the      *)
(*                        recursive form of rev).                             *)
(*  ** Iterators: for s == [:: x_1, ..., x_n], t == [:: y_1, ..., y_m],       *)
(*        map f s == the sequence [:: f x_1, ..., f x_n].                     *)
(* allpairs f s t == the sequence of all the f x y, with x and y drawn from   *)
(*                  s and t, respectievly, in row-major order.                *)
(*               := [:: f x_1 y_1; ...; f x_1 y_m; f x_2 y_1; ...; f x_n y_m] *)
(*      pmap pf s == the sequence [:: y_i1, ..., y_ik] where i1 < ... < ik,   *)
(*                   pf x_i = Some y_i, and pf x_j = None iff j is not in     *)
(*                   {i1, ..., ik}.                                           *)
(*   foldr f a s == the right fold of s by f (i.e., the natural iterator).    *)
(*               := f x_1 (f x_2 ... (f x_n a))                               *)
(*        sumn s == x_1 + (x_2 + ... + (x_n + 0)) (when s : seq nat).         *)
(*   foldl f a s == the left fold of s by f.                                  *)
(*               := f (f ... (f a x_1) ... x_n-1) x_n                         *)
(*   scanl f a s == the sequence of partial accumulators of foldl f a s.      *)
(*               := [:: f a x_1; ...; foldl f a s]                            *)
(* pairmap f a s == the sequence of f applied to consecutie items in a :: s.  *)
(*               := [:: f a x_1; f x_1 x_2; ...; f x_n-1 x_n]                 *)
(*       zip s t == itemwise pairing of s and t (dropping any extra items).   *)
(*               := [:: (x_1, y_1); ...; (x_mn, y_mn)] with mn = minn n m.    *)
(*      unzip1 s == [:: (x_1).1; ...; (x_n).1] when s : seq (S * T).          *)
(*      unzip2 s == [:: (x_1).2; ...; (x_n).2] when s : seq (S * T).          *)
(*     flatten s == x_1 ++ ... ++ x_n ++ [::] when s : seq (seq T).           *)
(*   reshape r s == s reshaped into a sequence of sequences whose sizes are   *)
(*                  given by r (trucating if s is too long or too short).     *)
(*               := [:: [:: x_1; ...; x_r1];                                  *)
(*                      [:: x_(r1 + 1); ...; x_(r0 + r1)];                    *)
(*                      ...;                                                  *)
(*                      [:: x_(r1 + ... + r(k-1) + 1); ...; x_(r0 + ... rk)]] *)
(*  ** Notation for manifest comprehensions:                                  *)
(*         [seq x <- s | C] := filter (fun x => C) s.                         *)
(*         [seq E | x <- s] := map (fun x => E) s.                            *)
(* [seq E | x <- s, y <- t] := allpairs (fun x y => E) s t.                   *)
(*   [seq x <- s | C1 & C2] := [seq x <- s | C1 && C2].                       *)
(*     [seq E | x <- s & C] := [seq E | x <- [seq x | C]].                    *)
(*  --> The above allow optional type casts on the eigenvariables, as in      *)
(*  [seq x : T <- s | C] or [seq E | x : T <- s, y : U <- t]. The cast may be *)
(*  needed as type inference considers E or C before s.                       *)
(*   We are quite systematic in providing lemmas to rewrite any composition   *)
(* of two operations. "rev", whose simplifications are not natural, is        *)
(* protected with nosimpl.                                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope seq_scope with SEQ.
Open Scope seq_scope.

(* Inductive seq (T : Type) : Type := Nil | Cons of T & seq T. *)
Notation seq := list.
Prenex Implicits cons.
Notation Cons T := (@cons T) (only parsing).
Notation Nil T := (@nil T) (only parsing).

Bind Scope seq_scope with list.
Arguments Scope cons [type_scope _ seq_scope].

(* As :: and ++ are (improperly) declared in Init.datatypes, we only rebind   *)
(* them here.                                                                 *)
Infix "::" := cons : seq_scope.

(* GG - this triggers a camlp4 warning, as if this Notation had been Reserved *)
Notation "[ :: ]" := nil (at level 0, format "[ :: ]") : seq_scope.

Notation "[ :: x1 ]" := (x1 :: [::])
  (at level 0, format "[ ::  x1 ]") : seq_scope.

Notation "[ :: x & s ]" := (x :: s) (at level 0, only parsing) : seq_scope.

Notation "[ :: x1 , x2 , .. , xn & s ]" := (x1 :: x2 :: .. (xn :: s) ..)
  (at level 0, format
  "'[hv' [ :: '['  x1 , '/'  x2 , '/'  .. , '/'  xn ']' '/ '  &  s ] ']'"
  ) : seq_scope.

Notation "[ :: x1 ; x2 ; .. ; xn ]" := (x1 :: x2 :: .. [:: xn] ..)
  (at level 0, format "[ :: '['  x1 ; '/'  x2 ; '/'  .. ; '/'  xn ']' ]"
  ) : seq_scope.

Section Sequences.

Variable n0 : nat.  (* numerical parameter for take, drop et al *)
Variable T : Type.  (* must come before the implicit Type     *)
Variable x0 : T.    (* default for head/nth *)

Implicit Types x y z : T.
Implicit Types m n : nat.
Implicit Type s : seq T.

Fixpoint size s := if s is _ :: s' then (size s').+1 else 0.

Lemma size0nil s : size s = 0 -> s = [::]. Proof. by case: s. Qed.

Definition nilp s := size s == 0.

Lemma nilP s : reflect (s = [::]) (nilp s).
Proof. by case: s => [|x s]; constructor. Qed.

Definition ohead s := if s is x :: _ then Some x else None.
Definition head s := if s is x :: _ then x else x0.

Definition behead s := if s is _ :: s' then s' else [::].

Lemma size_behead s : size (behead s) = (size s).-1.
Proof. by case: s. Qed.

(* Factories *)

Definition ncons n x := iter n (cons x).
Definition nseq n x := ncons n x [::].

Lemma size_ncons n x s : size (ncons n x s) = n + size s.
Proof. by elim: n => //= n ->. Qed.

Lemma size_nseq n x : size (nseq n x) = n.
Proof. by rewrite size_ncons addn0. Qed.

(* n-ary, dependently typed constructor. *)

Fixpoint seqn_type n := if n is n'.+1 then T -> seqn_type n' else seq T.

Fixpoint seqn_rec f n : seqn_type n :=
  if n is n'.+1 return seqn_type n then
    fun x => seqn_rec (fun s => f (x :: s)) n'
  else f [::].
Definition seqn := seqn_rec id.

(* Sequence catenation "cat".                                               *)

Fixpoint cat s1 s2 := if s1 is x :: s1' then x :: s1' ++ s2 else s2
where "s1 ++ s2" := (cat s1 s2) : seq_scope.

Lemma cat0s s : [::] ++ s = s. Proof. by []. Qed.
Lemma cat1s x s : [:: x] ++ s = x :: s. Proof. by []. Qed.
Lemma cat_cons x s1 s2 : (x :: s1) ++ s2 = x :: s1 ++ s2. Proof. by []. Qed.

Lemma cat_nseq n x s : nseq n x ++ s = ncons n x s.
Proof. by elim: n => //= n ->. Qed.

Lemma cats0 s : s ++ [::] = s.
Proof. by elim: s => //= x s ->. Qed.

Lemma catA s1 s2 s3 : s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3.
Proof. by elim: s1 => //= x s1 ->. Qed.

Lemma size_cat s1 s2 : size (s1 ++ s2) = size s1 + size s2.
Proof. by elim: s1 => //= x s1 ->. Qed.

(* last, belast, rcons, and last induction. *)

Fixpoint rcons s z := if s is x :: s' then x :: rcons s' z else [:: z].

Lemma rcons_cons x s z : rcons (x :: s) z = x :: rcons s z.
Proof. by []. Qed.

Lemma cats1 s z : s ++ [:: z] = rcons s z.
Proof. by elim: s => //= x s ->. Qed.

Fixpoint last x s := if s is x' :: s' then last x' s' else x.
Fixpoint belast x s := if s is x' :: s' then x :: (belast x' s') else [::].

Lemma lastI x s : x :: s = rcons (belast x s) (last x s).
Proof. by elim: s x => [|y s IHs] x //=; rewrite IHs. Qed.

Lemma last_cons x y s : last x (y :: s) = last y s.
Proof. by []. Qed.

Lemma size_rcons s x : size (rcons s x) = (size s).+1.
Proof. by rewrite -cats1 size_cat addnC. Qed.

Lemma size_belast x s : size (belast x s) = size s.
Proof. by elim: s x => [|y s IHs] x //=; rewrite IHs. Qed.

Lemma last_cat x s1 s2 : last x (s1 ++ s2) = last (last x s1) s2.
Proof. by elim: s1 x => [|y s1 IHs] x //=; rewrite IHs. Qed.

Lemma last_rcons x s z : last x (rcons s z) = z.
Proof. by rewrite -cats1 last_cat. Qed.

Lemma belast_cat x s1 s2 :
  belast x (s1 ++ s2) = belast x s1 ++ belast (last x s1) s2.
Proof. by elim: s1 x => [|y s1 IHs] x //=; rewrite IHs. Qed.

Lemma belast_rcons x s z : belast x (rcons s z) = x :: s.
Proof. by rewrite lastI -!cats1 belast_cat. Qed.

Lemma cat_rcons x s1 s2 : rcons s1 x ++ s2 = s1 ++ x :: s2.
Proof. by rewrite -cats1 -catA. Qed.

Lemma rcons_cat x s1 s2 : rcons (s1 ++ s2) x = s1 ++ rcons s2 x.
Proof. by rewrite -!cats1 catA. Qed.

CoInductive last_spec : seq T -> Type :=
  | LastNil        : last_spec [::]
  | LastRcons s x  : last_spec (rcons s x).

Lemma lastP s : last_spec s.
Proof. case: s => [|x s]; [left | rewrite lastI; right]. Qed.

Lemma last_ind P :
  P [::] -> (forall s x, P s -> P (rcons s x)) -> forall s, P s.
Proof.
move=> Hnil Hlast s; rewrite -(cat0s s).
elim: s [::] Hnil => [|x s2 IHs] s1 Hs1; first by rewrite cats0.
by rewrite -cat_rcons; auto.
Qed.

(* Sequence indexing. *)

Fixpoint nth s n {struct n} :=
  if s is x :: s' then if n is n'.+1 then @nth s' n' else x else x0.

Fixpoint set_nth s n y {struct n} :=
  if s is x :: s' then if n is n'.+1 then x :: @set_nth s' n' y else y :: s'
  else ncons n x0 [:: y].

Lemma nth0 s : nth s 0 = head s. Proof. by []. Qed.

Lemma nth_default s n : size s <= n -> nth s n = x0.
Proof. by elim: s n => [|x s IHs] [|n]; try exact (IHs n). Qed.

Lemma nth_nil n : nth [::] n = x0.
Proof. by case: n. Qed.

Lemma last_nth x s : last x s = nth (x :: s) (size s).
Proof. by elim: s x => [|y s IHs] x /=. Qed.

Lemma nth_last s : nth s (size s).-1 = last x0 s.
Proof. by case: s => //= x s; rewrite last_nth. Qed.

Lemma nth_behead s n : nth (behead s) n = nth s n.+1.
Proof. by case: s n => [|x s] [|n]. Qed.

Lemma nth_cat s1 s2 n :
  nth (s1 ++ s2) n = if n < size s1 then nth s1 n else nth s2 (n - size s1).
Proof. by elim: s1 n => [|x s1 IHs] [|n]; try exact (IHs n). Qed.

Lemma nth_rcons s x n :
  nth (rcons s x) n =
    if n < size s then nth s n else if n == size s then x else x0.
Proof. by elim: s n => [|y s IHs] [|n] //=; rewrite ?nth_nil ?IHs. Qed.

Lemma nth_ncons m x s n :
  nth (ncons m x s) n = if n < m then x else nth s (n - m).
Proof. by elim: m n => [|m IHm] [|n] //=; exact: IHm. Qed.

Lemma nth_nseq m x n : nth (nseq m x) n = (if n < m then x else x0).
Proof. by elim: m n => [|m IHm] [|n] //=; exact: IHm. Qed.

Lemma eq_from_nth s1 s2 :
    size s1 = size s2 -> (forall i, i < size s1 -> nth s1 i = nth s2 i) ->
  s1 = s2.
Proof.
elim: s1 s2 => [|x1 s1 IHs1] [|x2 s2] //= [eq_sz] eq_s12.
rewrite [x1](eq_s12 0) // (IHs1 s2) // => i; exact: (eq_s12 i.+1).
Qed.

Lemma size_set_nth s n y : size (set_nth s n y) = maxn n.+1 (size s).
Proof.
elim: s n => [|x s IHs] [|n] //=.
- by rewrite size_ncons addn1 maxn0.
- by rewrite maxnE subn1.
by rewrite IHs -add1n addn_maxr.
Qed.

Lemma set_nth_nil n y : set_nth [::] n y = ncons n x0 [:: y].
Proof. by case: n. Qed.

Lemma nth_set_nth s n y : nth (set_nth s n y) =1 [eta nth s with n |-> y].
Proof.
elim: s n => [|x s IHs] [|n] [|m] //=; rewrite ?nth_nil ?IHs // nth_ncons eqSS.
case: ltngtP => // [lt_nm | ->]; last by rewrite subnn.
by rewrite nth_default // subn_gt0.
Qed.

Lemma set_set_nth s n1 y1 n2 y2 (s2 := set_nth s n2 y2) :
  set_nth (set_nth s n1 y1) n2 y2 = if n1 == n2 then s2 else set_nth s2 n1 y1.
Proof.
have [-> | ne_n12] := altP eqP.
  apply: eq_from_nth => [|i _]; first by rewrite !size_set_nth maxnA maxnn.
  by do 2!rewrite !nth_set_nth /=; case: eqP.
apply: eq_from_nth => [|i _]; first by rewrite !size_set_nth maxnCA.
do 2!rewrite !nth_set_nth /=; case: eqP => // ->.
by rewrite eq_sym -if_neg ne_n12.
Qed.

(* find, count, has, all. *)

Section SeqFind.

Variable a : pred T.

Fixpoint find s := if s is x :: s' then if a x then 0 else (find s').+1 else 0.

Fixpoint filter s :=
  if s is x :: s' then if a x then x :: filter s' else filter s' else [::].

Fixpoint count s := if s is x :: s' then a x + count s' else 0.

Fixpoint has s := if s is x :: s' then a x || has s' else false.

Fixpoint all s := if s is x :: s' then a x && all s' else true.

Lemma count_filter s : count s = size (filter s).
Proof. by elim: s => //= x s ->; case (a x). Qed.

Lemma has_count s : has s = (0 < count s).
Proof. by elim: s => //= x s ->; case (a x). Qed.

Lemma count_size s : count s <= size s.
Proof. by elim: s => //= x s; case: (a x); last exact: leqW. Qed.

Lemma all_count s : all s = (count s == size s).
Proof.
elim: s => //= x s; case: (a x) => _ //=.
by rewrite add0n eqn_leq andbC ltnNge count_size.
Qed.

Lemma filter_all s : all (filter s).
Proof. by elim: s => //= x s IHs; case: ifP => //= ->. Qed.

Lemma all_filterP s : reflect (filter s = s) (all s).
Proof.
apply: (iffP idP) => [| <-]; last exact: filter_all.
by elim: s => //= x s IHs /andP[-> Hs]; rewrite IHs.
Qed.

Lemma filter_id s : filter (filter s) = filter s.
Proof. by apply/all_filterP; exact: filter_all. Qed.

Lemma has_find s : has s = (find s < size s).
Proof. by elim: s => //= x s IHs; case (a x); rewrite ?leqnn. Qed.

Lemma find_size s : find s <= size s.
Proof. by elim: s => //= x s IHs; case (a x). Qed.

Lemma find_cat s1 s2 :
  find (s1 ++ s2) = if has s1 then find s1 else size s1 + find s2.
Proof.
by elim: s1 => //= x s1 IHs; case: (a x) => //; rewrite IHs (fun_if succn).
Qed.

Lemma has_nil : has [::] = false. Proof. by []. Qed.

Lemma has_seq1 x : has [:: x] = a x.
Proof. exact: orbF. Qed.

Lemma has_seqb (b : bool) x : has (nseq b x) = b && a x.
Proof. by case: b => //=; exact: orbF. Qed.

Lemma all_nil : all [::] = true. Proof. by []. Qed.

Lemma all_seq1 x : all [:: x] = a x.
Proof. exact: andbT. Qed.

Lemma nth_find s : has s -> a (nth s (find s)).
Proof. by elim: s => //= x s IHs; case Hx: (a x). Qed.

Lemma before_find s i : i < find s -> a (nth s i) = false.
Proof.
by elim: s i => //= x s IHs; case Hx: (a x) => [|] // [|i] //; exact: (IHs i).
Qed.

Lemma filter_cat s1 s2 : filter (s1 ++ s2) = filter s1 ++ filter s2.
Proof. by elim: s1 => //= x s1 ->; case (a x). Qed.

Lemma filter_rcons s x :
  filter (rcons s x) = if a x then rcons (filter s) x else filter s.
Proof. by rewrite -!cats1 filter_cat /=; case (a x); rewrite /= ?cats0. Qed.

Lemma count_cat s1 s2 : count (s1 ++ s2) = count s1 + count s2.
Proof. by rewrite !count_filter filter_cat size_cat. Qed.

Lemma has_cat s1 s2 : has (s1 ++ s2) = has s1 || has s2.
Proof. by elim: s1 => [|x s1 IHs] //=; rewrite IHs orbA. Qed.

Lemma has_rcons s x : has (rcons s x) = a x || has s.
Proof. by rewrite -cats1 has_cat has_seq1 orbC. Qed.

Lemma all_cat s1 s2 : all (s1 ++ s2) = all s1 && all s2.
Proof. by elim: s1 => [|x s1 IHs] //=; rewrite IHs andbA. Qed.

Lemma all_rcons s x : all (rcons s x) = a x && all s.
Proof. by rewrite -cats1 all_cat all_seq1 andbC. Qed.

End SeqFind.

Lemma eq_find a1 a2 : a1 =1 a2 -> find a1 =1 find a2.
Proof. by move=> Ea; elim=> //= x s IHs; rewrite Ea IHs. Qed.

Lemma eq_filter a1 a2 : a1 =1 a2 -> filter a1 =1 filter a2.
Proof. by move=> Ea; elim=> //= x s IHs; rewrite Ea IHs. Qed.

Lemma eq_count a1 a2 : a1 =1 a2 -> count a1 =1 count a2.
Proof. by move=> Ea s; rewrite !count_filter (eq_filter Ea). Qed.

Lemma eq_has a1 a2 : a1 =1 a2 -> has a1 =1 has a2.
Proof. by move=> Ea s; rewrite !has_count (eq_count Ea). Qed.

Lemma eq_all a1 a2 : a1 =1 a2 -> all a1 =1 all a2.
Proof. by move=> Ea s; rewrite !all_count (eq_count Ea). Qed.

Section SubPred.

Variable (a1 a2 : pred T).
Hypothesis s12 : subpred a1 a2.

Lemma sub_find s : find a2 s <= find a1 s.
Proof. by elim: s => //= x s IHs; case: ifP => // /(contraFF (@s12 x))->. Qed.

Lemma sub_has s : has a1 s -> has a2 s.
Proof. by rewrite !has_find; exact: leq_ltn_trans (sub_find s). Qed.

Lemma sub_count s : count a1 s <= count a2 s.
Proof.
by elim: s => //= x s; apply: leq_add; case a1x: (a1 x); rewrite // s12.
Qed.

Lemma sub_all s : all a1 s -> all a2 s.
Proof.
by rewrite !all_count !eqn_leq !count_size => /leq_trans-> //; exact: sub_count.
Qed.

End SubPred.

Lemma filter_pred0 s : filter pred0 s = [::]. Proof. by elim: s. Qed.

Lemma filter_predT s : filter predT s = s.
Proof. by elim: s => //= x s ->. Qed.

Lemma filter_predI a1 a2 s : filter (predI a1 a2) s = filter a1 (filter a2 s).
Proof.
elim: s => //= x s IHs; rewrite andbC IHs.
by case: (a2 x) => //=; case (a1 x).
Qed.

Lemma count_pred0 s : count pred0 s = 0.
Proof. by rewrite count_filter filter_pred0. Qed.

Lemma count_predT s : count predT s = size s.
Proof. by rewrite count_filter filter_predT. Qed.

Lemma count_predUI a1 a2 s :
 count (predU a1 a2) s + count (predI a1 a2) s = count a1 s + count a2 s.
Proof.
elim: s => //= x s IHs; rewrite /= addnCA -addnA IHs addnA addnC.
by rewrite -!addnA; do 2 nat_congr; case (a1 x); case (a2 x).
Qed.

Lemma count_predC a s : count a s + count (predC a) s = size s.
Proof.
by elim: s => //= x s IHs; rewrite addnCA -addnA IHs addnA addn_negb.
Qed.

Lemma has_pred0 s : has pred0 s = false.
Proof. by rewrite has_count count_pred0. Qed.

Lemma has_predT s : has predT s = (0 < size s).
Proof. by rewrite has_count count_predT. Qed.

Lemma has_predC a s : has (predC a) s = ~~ all a s.
Proof. by elim: s => //= x s ->; case (a x). Qed.

Lemma has_predU a1 a2 s : has (predU a1 a2) s = has a1 s || has a2 s.
Proof. by elim: s => //= x s ->; rewrite -!orbA; do !bool_congr. Qed.

Lemma all_pred0 s : all pred0 s = (size s == 0).
Proof. by rewrite all_count count_pred0 eq_sym. Qed.

Lemma all_predT s : all predT s.
Proof. by rewrite all_count count_predT. Qed.

Lemma all_predC a s : all (predC a) s = ~~ has a s.
Proof. by elim: s => //= x s ->; case (a x). Qed.

Lemma all_predI a1 a2 s : all (predI a1 a2) s = all a1 s && all a2 s.
Proof.
apply: (can_inj negbK); rewrite negb_and -!has_predC -has_predU.
by apply: eq_has => x; rewrite /= negb_and.
Qed.

(* Surgery: drop, take, rot, rotr.                                        *)

Fixpoint drop n s {struct s} :=
  match s, n with
  | _ :: s', n'.+1 => drop n' s'
  | _, _ => s
  end.

Lemma drop_behead : drop n0 =1 iter n0 behead.
Proof. by elim: n0 => [|n IHn] [|x s] //; rewrite iterSr -IHn. Qed.

Lemma drop0 s : drop 0 s = s. Proof. by case: s. Qed.

Lemma drop1 : drop 1 =1 behead. Proof. by case=> [|x [|y s]]. Qed.

Lemma drop_oversize n s : size s <= n -> drop n s = [::].
Proof. by elim: n s => [|n IHn] [|x s]; try exact (IHn s). Qed.

Lemma drop_size s : drop (size s) s = [::].
Proof. by rewrite drop_oversize // leqnn. Qed.

Lemma drop_cons x s :
  drop n0 (x :: s) = if n0 is n.+1 then drop n s else x :: s.
Proof. by []. Qed.

Lemma size_drop s : size (drop n0 s) = size s - n0.
Proof. by elim: s n0 => [|x s IHs] [|n]; try exact (IHs n). Qed.

Lemma drop_cat s1 s2 :
  drop n0 (s1 ++ s2) =
    if n0 < size s1 then drop n0 s1 ++ s2 else drop (n0 - size s1) s2.
Proof. by elim: s1 n0 => [|x s1 IHs] [|n]; try exact (IHs n). Qed.

Lemma drop_size_cat n s1 s2 : size s1 = n -> drop n (s1 ++ s2) = s2.
Proof. by move <-; elim: s1 => //=; rewrite drop0. Qed.

Lemma nconsK n x : cancel (ncons n x) (drop n).
Proof. by elim: n => //; case. Qed.

Fixpoint take n s {struct s} :=
  match s, n with
  | x :: s', n'.+1 => x :: take n' s'
  | _, _ => [::]
  end.

Lemma take0 s : take 0 s = [::]. Proof. by case: s. Qed.

Lemma take_oversize n s : size s <= n -> take n s = s.
Proof. by elim: n s => [|n IHn] [|x s] Hsn; try (congr cons; apply: IHn). Qed.

Lemma take_size s : take (size s) s = s.
Proof. by rewrite take_oversize // leqnn. Qed.

Lemma take_cons x s :
  take n0 (x :: s) = if n0 is n.+1 then x :: (take n s) else [::].
Proof. by []. Qed.

Lemma drop_rcons s : n0 <= size s ->
  forall x, drop n0 (rcons s x) = rcons (drop n0 s) x.
Proof. by elim: s n0 => [|y s IHs] [|n]; try exact (IHs n). Qed.

Lemma cat_take_drop s : take n0 s ++ drop n0 s = s.
Proof. by elim: s n0 => [|x s IHs] [|n]; try exact (congr1 _ (IHs n)). Qed.

Lemma size_takel s : n0 <= size s -> size (take n0 s) = n0.
Proof.
by move/subnKC; rewrite -{2}(cat_take_drop s) size_cat size_drop => /addIn.
Qed.

Lemma size_take s : size (take n0 s) = if n0 < size s then n0 else size s.
Proof.
have [le_sn | lt_ns] := leqP (size s) n0; first by rewrite take_oversize.
by rewrite size_takel // ltnW.
Qed.

Lemma take_cat s1 s2 :
 take n0 (s1 ++ s2) =
   if n0 < size s1 then take n0 s1 else s1 ++ take (n0 - size s1) s2.
Proof.
elim: s1 n0 => [|x s1 IHs] [|n] //=.
by rewrite ltnS subSS -(fun_if (cons x)) -IHs.
Qed.

Lemma take_size_cat n s1 s2 : size s1 = n -> take n (s1 ++ s2) = s1.
Proof. by move <-; elim: s1 => [|x s1 IHs]; rewrite ?take0 //= IHs. Qed.

Lemma takel_cat s1 :
    n0 <= size s1 ->
  forall s2, take n0 (s1 ++ s2) = take n0 s1.
Proof.
move=> Hn0 s2; rewrite take_cat ltn_neqAle Hn0 andbT.
by case: (n0 =P size s1) => //= ->; rewrite subnn take0 cats0 take_size.
Qed.

Lemma nth_drop s i : nth (drop n0 s) i = nth s (n0 + i).
Proof.
have [lt_n0_s | le_s_n0] := ltnP n0 (size s).
  rewrite -{2}[s]cat_take_drop nth_cat size_take lt_n0_s /= addKn.
  by rewrite ltnNge leq_addr.
rewrite !nth_default //; first exact: leq_trans (leq_addr _ _).
by rewrite size_drop (eqnP le_s_n0).
Qed.

Lemma nth_take i : i < n0 -> forall s, nth (take n0 s) i = nth s i.
Proof.
move=> lt_i_n0 s; case lt_n0_s: (n0 < size s).
  by rewrite -{2}[s]cat_take_drop nth_cat size_take lt_n0_s /= lt_i_n0.
by rewrite -{1}[s]cats0 take_cat lt_n0_s /= cats0.
Qed.

(* drop_nth and take_nth below do NOT use the default n0, because the "n"  *)
(* can be inferred from the condition, whereas the nth default value x0    *)
(* will have to be given explicitly (and this will provide "d" as well).   *)

Lemma drop_nth n s : n < size s -> drop n s = nth s n :: drop n.+1 s.
Proof. by elim: s n => [|x s IHs] [|n] Hn //=; rewrite ?drop0 1?IHs. Qed.

Lemma take_nth n s : n < size s -> take n.+1 s = rcons (take n s) (nth s n).
Proof. by elim: s n => [|x s IHs] //= [|n] Hn /=; rewrite ?take0 -?IHs. Qed.

(* Rotation *)

Definition rot n s := drop n s ++ take n s.

Lemma rot0 s : rot 0 s = s.
Proof. by rewrite /rot drop0 take0 cats0. Qed.

Lemma size_rot s : size (rot n0 s) = size s.
Proof. by rewrite -{2}[s]cat_take_drop /rot !size_cat addnC. Qed.

Lemma rot_oversize n s : size s <= n -> rot n s = s.
Proof. by move=> le_s_n; rewrite /rot take_oversize ?drop_oversize. Qed.

Lemma rot_size s : rot (size s) s = s.
Proof. exact: rot_oversize. Qed.

Lemma has_rot s a : has a (rot n0 s) = has a s.
Proof. by rewrite has_cat orbC -has_cat cat_take_drop. Qed.

Lemma rot_size_cat s1 s2 : rot (size s1) (s1 ++ s2) = s2 ++ s1.
Proof. by rewrite /rot take_size_cat ?drop_size_cat. Qed.

Definition rotr n s := rot (size s - n) s.

Lemma rotK : cancel (rot n0) (rotr n0).
Proof.
move=> s; rewrite /rotr size_rot -size_drop {2}/rot.
by rewrite rot_size_cat cat_take_drop.
Qed.

Lemma rot_inj : injective (rot n0). Proof. exact (can_inj rotK). Qed.

Lemma rot1_cons x s : rot 1 (x :: s) = rcons s x.
Proof. by rewrite /rot /= take0 drop0 -cats1. Qed.

(* (efficient) reversal *)

Fixpoint catrev s1 s2 := if s1 is x :: s1' then catrev s1' (x :: s2) else s2.

End Sequences.

(* rev must be defined outside a Section because Coq's end of section *)
(* "cooking" removes the nosimpl guard.                               *)

Definition rev T (s : seq T) := nosimpl (catrev s [::]).

Implicit Arguments nilP [T s].
Implicit Arguments all_filterP [T a s].

Prenex Implicits size nilP head ohead behead last rcons belast.
Prenex Implicits cat take drop rev rot rotr.
Prenex Implicits find count nth all has filter all_filterP.

Infix "++" := cat : seq_scope.

Notation "[ 'seq' x <- s | C ]" := (filter (fun x => C%B) s)
 (at level 0, x at level 99,
  format "[ '[hv' 'seq'  x  <-  s '/ '  |  C ] ']'") : seq_scope.
Notation "[ 'seq' x <- s | C1 & C2 ]" := [seq x <- s | C1 && C2]
 (at level 0, x at level 99,
  format "[ '[hv' 'seq'  x  <-  s '/ '  |  C1 '/ '  &  C2 ] ']'") : seq_scope.
Notation "[ 'seq' x : T <- s | C ]" := (filter (fun x : T => C%B) s)
 (at level 0, x at level 99, only parsing).
Notation "[ 'seq' x : T <- s | C1 & C2 ]" := [seq x : T <- s | C1 && C2]
 (at level 0, x at level 99, only parsing).

Section Rev.

Variable T : Type.
Implicit Types s t : seq T.

Lemma catrev_catl s t u : catrev (s ++ t) u = catrev t (catrev s u).
Proof. by elim: s u => /=. Qed.

Lemma catrev_catr s t u : catrev s (t ++ u) = catrev s t ++ u.
Proof. by elim: s t => //= x s IHs t; rewrite -IHs. Qed.

Lemma catrevE s t : catrev s t = rev s ++ t.
Proof. by rewrite -catrev_catr. Qed.

Lemma rev_cons x s : rev (x :: s) = rcons (rev s) x.
Proof. by rewrite -cats1 -catrevE. Qed.

Lemma size_rev s : size (rev s) = size s.
Proof. by elim: s => // x s IHs; rewrite rev_cons size_rcons IHs. Qed.

Lemma rev_cat s t : rev (s ++ t) = rev t ++ rev s.
Proof. by rewrite -catrev_catr -catrev_catl. Qed.

Lemma rev_rcons s x : rev (rcons s x) = x :: rev s.
Proof. by rewrite -cats1 rev_cat. Qed.

Lemma revK : involutive (@rev T).
Proof. by elim=> //= x s IHs; rewrite rev_cons rev_rcons IHs. Qed.

Lemma nth_rev x0 n s :
  n < size s -> nth x0 (rev s) n = nth x0 s (size s - n.+1).
Proof.
elim/last_ind: s => // s x IHs in n *.
rewrite rev_rcons size_rcons ltnS subSS -cats1 nth_cat /=.
case: n => [|n] lt_n_s; first by rewrite subn0 ltnn subnn.
by rewrite -{2}(subnK lt_n_s) -addSnnS leq_addr /= -IHs.
Qed.

End Rev.

(* Equality and eqType for seq.                                          *)

Section EqSeq.

Variables (n0 : nat) (T : eqType) (x0 : T).
Notation Local nth := (nth x0).
Implicit Type s : seq T.
Implicit Types x y z : T.

Fixpoint eqseq s1 s2 {struct s2} :=
  match s1, s2 with
  | [::], [::] => true
  | x1 :: s1', x2 :: s2' => (x1 == x2) && eqseq s1' s2'
  | _, _ => false
  end.

Lemma eqseqP : Equality.axiom eqseq.
Proof.
move; elim=> [|x1 s1 IHs] [|x2 s2]; do [by constructor | simpl].
case: (x1 =P x2) => [<-|neqx]; last by right; case.
by apply: (iffP (IHs s2)) => [<-|[]].
Qed.

Canonical seq_eqMixin := EqMixin eqseqP.
Canonical seq_eqType := Eval hnf in EqType (seq T) seq_eqMixin.

Lemma eqseqE : eqseq = eq_op. Proof. by []. Qed.

Lemma eqseq_cons x1 x2 s1 s2 :
  (x1 :: s1 == x2 :: s2) = (x1 == x2) && (s1 == s2).
Proof. by []. Qed.

Lemma eqseq_cat s1 s2 s3 s4 :
  size s1 = size s2 -> (s1 ++ s3 == s2 ++ s4) = (s1 == s2) && (s3 == s4).
Proof.
elim: s1 s2 => [|x1 s1 IHs] [|x2 s2] //= [sz12].
by rewrite !eqseq_cons -andbA IHs.
Qed.

Lemma eqseq_rcons s1 s2 x1 x2 :
  (rcons s1 x1 == rcons s2 x2) = (s1 == s2) && (x1 == x2).
Proof.
elim: s1 s2 => [|y1 s1 IHs] [|y2 s2] /=;
  rewrite ?eqseq_cons ?andbT ?andbF // ?IHs 1?andbA // andbC;
  by [case s2 | case s1].
Qed.

Lemma has_filter a s : has a s = (filter a s != [::]).
Proof. by rewrite has_count count_filter; case (filter a s). Qed.

Lemma size_eq0 s : (size s == 0) = (s == [::]).
Proof. apply/eqP/eqP=> [|-> //]; exact: size0nil. Qed.

(* mem_seq and index. *)
(* mem_seq defines a predType for seq. *)

Fixpoint mem_seq (s : seq T) :=
  if s is y :: s' then xpredU1 y (mem_seq s') else xpred0.

Definition eqseq_class := seq T.
Identity Coercion seq_of_eqseq : eqseq_class >-> seq.

Coercion pred_of_eq_seq (s : eqseq_class) : pred_class := [eta mem_seq s].

Canonical seq_predType := @mkPredType T (seq T) pred_of_eq_seq.
(* The line below makes mem_seq a canonical instance of topred. *)
Canonical mem_seq_predType := mkPredType mem_seq.

Lemma in_cons y s x : (x \in y :: s) = (x == y) || (x \in s).
Proof. by []. Qed.

Lemma in_nil x : (x \in [::]) = false.
Proof. by []. Qed.

Lemma mem_seq1 x y : (x \in [:: y]) = (x == y).
Proof. by rewrite in_cons orbF. Qed.

 (* to be repeated after the Section discharge. *)
Let inE := (mem_seq1, in_cons, inE).

Lemma mem_seq2 x y1 y2 : (x \in [:: y1; y2]) = xpred2 y1 y2 x.
Proof. by rewrite !inE. Qed.

Lemma mem_seq3  x y1 y2 y3 : (x \in [:: y1; y2; y3]) = xpred3 y1 y2 y3 x.
Proof. by rewrite !inE. Qed.

Lemma mem_seq4  x y1 y2 y3 y4 :
  (x \in [:: y1; y2; y3; y4]) = xpred4 y1 y2 y3 y4 x.
Proof. by rewrite !inE. Qed.

Lemma mem_cat x s1 s2 : (x \in s1 ++ s2) = (x \in s1) || (x \in s2).
Proof. by elim: s1 => //= y s1 IHs; rewrite !inE /= -orbA -IHs. Qed.

Lemma mem_rcons s y : rcons s y =i y :: s.
Proof. by move=> x; rewrite -cats1 /= mem_cat mem_seq1 orbC in_cons. Qed.

Lemma mem_head x s : x \in x :: s.
Proof. exact: predU1l. Qed.

Lemma mem_last x s : last x s \in x :: s.
Proof. by rewrite lastI mem_rcons mem_head. Qed.

Lemma mem_behead s : {subset behead s <= s}.
Proof. by case: s => // y s x; exact: predU1r. Qed.

Lemma mem_belast s y : {subset belast y s <= y :: s}.
Proof. by move=> x ys'x; rewrite lastI mem_rcons mem_behead. Qed.

Lemma mem_nth s n : n < size s -> nth s n \in s.
Proof.
by elim: s n => [|x s IHs] // [_|n sz_s]; rewrite ?mem_head // mem_behead ?IHs.
Qed.

Lemma mem_take s x : x \in take n0 s -> x \in s.
Proof. by move=> s0x; rewrite -(cat_take_drop n0 s) mem_cat /= s0x. Qed.

Lemma mem_drop s x : x \in drop n0 s -> x \in s.
Proof. by move=> s0'x; rewrite -(cat_take_drop n0 s) mem_cat /= s0'x orbT. Qed.

Lemma mem_rev s : rev s =i s.
Proof.
by move=> y; elim: s => // x s IHs; rewrite rev_cons /= mem_rcons in_cons IHs.
Qed.

Section Filters.

Variable a : pred T.

Lemma hasP s : reflect (exists2 x, x \in s & a x) (has a s).
Proof.
elim: s => [|y s IHs] /=; first by right; case.
case ay: (a y); first by left; exists y; rewrite ?mem_head.
apply: (iffP IHs) => [] [x ysx ax]; exists x => //; first exact: mem_behead.
by case: (predU1P ysx) ax => [->|//]; rewrite ay.
Qed.

Lemma hasPn s : reflect (forall x, x \in s -> ~~ a x) (~~ has a s).
Proof.
apply: (iffP idP) => not_a_s => [x s_x|].
  by apply: contra not_a_s => a_x; apply/hasP; exists x.
by apply/hasP=> [[x s_x]]; apply/negP; exact: not_a_s.
Qed.

Lemma allP s : reflect (forall x, x \in s -> a x) (all a s).
Proof.
elim: s => [|x s IHs]; first by left.
rewrite /= andbC; case: IHs => IHs /=.
  apply: (iffP idP) => [Hx y|]; last by apply; exact: mem_head.
  by case/predU1P=> [->|Hy]; auto.
by right=> H; case IHs => y Hy; apply H; exact: mem_behead.
Qed.

Lemma allPn s : reflect (exists2 x, x \in s & ~~ a x) (~~ all a s).
Proof.
elim: s => [|x s IHs]; first by right=> [[x Hx _]].
rewrite /= andbC negb_and; case: IHs => IHs /=.
  by left; case: IHs => y Hy Hay; exists y; first exact: mem_behead.
apply: (iffP idP) => [|[y]]; first by exists x; rewrite ?mem_head.
by case/predU1P=> [-> // | s_y not_a_y]; case: IHs; exists y.
Qed.

Lemma mem_filter x s : (x \in filter a s) = a x && (x \in s).
Proof.
rewrite andbC; elim: s => //= y s IHs.
rewrite (fun_if (fun s' : seq T => x \in s')) !in_cons {}IHs.
by case: eqP => [->|_]; case (a y); rewrite /= ?andbF.
Qed.

End Filters.

Section EqIn.

Variables a1 a2 : pred T.

Lemma eq_in_filter s : {in s, a1 =1 a2} -> filter a1 s = filter a2 s.
Proof.
elim: s => //= x s IHs eq_a.
rewrite eq_a ?mem_head ?IHs // => y s_y; apply: eq_a; exact: mem_behead.
Qed.

Lemma eq_in_find s : {in s, a1 =1 a2} -> find a1 s = find a2 s.
Proof.
elim: s => //= x s IHs eq_a12; rewrite eq_a12 ?mem_head // IHs // => y s'y.
by rewrite eq_a12 // mem_behead.
Qed.

Lemma eq_in_count s : {in s, a1 =1 a2} -> count a1 s = count a2 s.
Proof. by move/eq_in_filter=> eq_a12; rewrite !count_filter eq_a12. Qed.

Lemma eq_in_all s : {in s, a1 =1 a2} -> all a1 s = all a2 s.
Proof. by move=> eq_a12; rewrite !all_count eq_in_count. Qed.

Lemma eq_in_has s : {in s, a1 =1 a2} -> has a1 s = has a2 s.
Proof. by move/eq_in_filter=> eq_a12; rewrite !has_filter eq_a12. Qed.

End EqIn.

Lemma eq_has_r s1 s2 : s1 =i s2 -> has^~ s1 =1 has^~ s2.
Proof.
move=> Es12 a; apply/(hasP a s1)/(hasP a s2) => [] [x Hx Hax];
 by exists x; rewrite // ?Es12 // -Es12.
Qed.

Lemma eq_all_r s1 s2 : s1 =i s2 -> all^~ s1 =1 all^~ s2.
Proof.
by move=> Es12 a; apply/(allP a s1)/(allP a s2) => Hs x Hx;
  apply: Hs; rewrite Es12 in Hx *.
Qed.

Lemma has_sym s1 s2 : has (mem s1) s2 = has (mem s2) s1.
Proof. by apply/(hasP _ s2)/(hasP _ s1) => [] [x]; exists x. Qed.

Lemma has_pred1 x s : has (pred1 x) s = (x \in s).
Proof. by rewrite -(eq_has (mem_seq1^~ x)) (has_sym [:: x]) /= orbF. Qed.

(* Constant sequences, i.e., the image of nseq. *)

Definition constant s := if s is x :: s' then all (pred1 x) s' else true.

Lemma all_pred1P x s : reflect (s = nseq (size s) x) (all (pred1 x) s).
Proof.
elim: s => [|y s IHs] /=; first by left.
case: eqP => [->{y} | ne_xy]; last by right=> [] [? _]; case ne_xy.
by apply: (iffP IHs) => [<- //| []].
Qed.

Lemma all_pred1_constant x s : all (pred1 x) s -> constant s.
Proof. by case: s => //= y s /andP[/eqP->]. Qed.

Lemma all_pred1_nseq x y n : all (pred1 x) (nseq n y) = (n == 0) || (x == y).
Proof.
case: n => //= n; rewrite eq_sym; apply: andb_idr => /eqP->{x}.
by elim: n => //= n ->; rewrite eqxx.
Qed.

Lemma constant_nseq n x : constant (nseq n x).
Proof. by case: n => //= n; rewrite all_pred1_nseq eqxx orbT. Qed.

(* Uses x0 *)
Lemma constantP s : reflect (exists x, s = nseq (size s) x) (constant s).
Proof.
apply: (iffP idP) => [| [x ->]]; last exact: constant_nseq.
case: s => [|x s] /=; first by exists x0.
by move/all_pred1P=> def_s; exists x; rewrite -def_s.
Qed.

(* Duplicate-freenes. *)

Fixpoint uniq s := if s is x :: s' then (x \notin s') && uniq s' else true.

Lemma cons_uniq x s : uniq (x :: s) = (x \notin s) && uniq s.
Proof. by []. Qed.

Lemma cat_uniq s1 s2 :
  uniq (s1 ++ s2) = [&& uniq s1, ~~ has (mem s1) s2 & uniq s2].
Proof.
elim: s1 => [|x s1 IHs]; first by rewrite /= has_pred0.
by rewrite has_sym /= mem_cat !negb_or has_sym IHs -!andbA; do !bool_congr.
Qed.

Lemma uniq_catC s1 s2 : uniq (s1 ++ s2) = uniq (s2 ++ s1).
Proof. by rewrite !cat_uniq has_sym andbCA andbA andbC. Qed.

Lemma uniq_catCA s1 s2 s3 : uniq (s1 ++ s2 ++ s3) = uniq (s2 ++ s1 ++ s3).
Proof.
by rewrite !catA -!(uniq_catC s3) !(cat_uniq s3) uniq_catC !has_cat orbC.
Qed.

Lemma rcons_uniq s x : uniq (rcons s x) = (x \notin s) && uniq s.
Proof. by rewrite -cats1 uniq_catC. Qed.

Lemma filter_uniq s a : uniq s -> uniq (filter a s).
Proof.
elim: s => [|x s IHs] //= /andP[Hx Hs]; case (a x); auto.
by rewrite /= mem_filter /= (negbTE Hx) andbF; auto.
Qed.

Lemma rot_uniq s : uniq (rot n0 s) = uniq s.
Proof. by rewrite /rot uniq_catC cat_take_drop. Qed.

Lemma rev_uniq s : uniq (rev s) = uniq s.
Proof.
elim: s => // x s IHs.
by rewrite rev_cons -cats1 cat_uniq /= andbT andbC mem_rev orbF IHs.
Qed.

Lemma count_uniq_mem s x : uniq s -> count (pred1 x) s = (x \in s).
Proof.
elim: s => //= [y s IHs] /andP[/negbTE Hy /IHs-> {IHs}].
by rewrite in_cons eq_sym; case: eqP => // ->; rewrite Hy.
Qed.

Lemma filter_pred1_uniq s x : uniq s -> x \in s -> filter (pred1 x) s = [:: x].
Proof.
move=> uniq_s s_x; rewrite (all_pred1P _ _ (filter_all _ _)).
by rewrite -count_filter count_uniq_mem ?s_x.
Qed.

(* Removing duplicates *)

Fixpoint undup s :=
  if s is x :: s' then if x \in s' then undup s' else x :: undup s' else [::].

Lemma size_undup s : size (undup s) <= size s.
Proof. by elim: s => //= x s IHs; case: (x \in s) => //=; exact: ltnW. Qed.

Lemma mem_undup s : undup s =i s.
Proof.
move=> x; elim: s => //= y s IHs.
by case Hy: (y \in s); rewrite in_cons IHs //; case: eqP => // ->.
Qed.

Lemma undup_uniq s : uniq (undup s).
Proof.
by elim: s => //= x s IHs; case s_x: (x \in s); rewrite //= mem_undup s_x.
Qed.

Lemma undup_id s : uniq s -> undup s = s.
Proof. by elim: s => //= x s IHs /andP[/negbTE-> /IHs->]. Qed.

Lemma ltn_size_undup s : (size (undup s) < size s) = ~~ uniq s.
Proof.
by elim: s => //= x s IHs; case Hx: (x \in s); rewrite //= ltnS size_undup.
Qed.

Lemma filter_undup p s : filter p (undup s) = undup (filter p s).
Proof.
elim: s => //= x s IHs; rewrite (fun_if undup) fun_if /= mem_filter /=.
by rewrite (fun_if (filter p)) /= IHs; case: ifP => -> //=; exact: if_same.
Qed.

(* Lookup *)

Definition index x := find (pred1 x).

Lemma index_size x s : index x s <= size s.
Proof. by rewrite /index find_size. Qed.

Lemma index_mem x s : (index x s < size s) = (x \in s).
Proof. by rewrite -has_pred1 has_find. Qed.

Lemma nth_index x s : x \in s -> nth s (index x s) = x.
Proof. by rewrite -has_pred1 => /(nth_find x0)/eqP. Qed.

Lemma index_cat x s1 s2 :
 index x (s1 ++ s2) = if x \in s1 then index x s1 else size s1 + index x s2.
Proof. by rewrite /index find_cat has_pred1. Qed.

Lemma index_uniq i s : i < size s -> uniq s -> index (nth s i) s = i.
Proof.
elim: s i => [|x s IHs] //= [|i]; rewrite /= ?eqxx // ltnS => lt_i_s.
case/andP=> not_s_x /(IHs i)-> {IHs}//.
by case: eqP not_s_x => // ->; rewrite mem_nth.
Qed.

Lemma index_head x s : index x (x :: s) = 0.
Proof. by rewrite /= eqxx. Qed.

Lemma index_last x s : uniq (x :: s) -> index (last x s) (x :: s) = size s.
Proof.
rewrite lastI rcons_uniq -cats1 index_cat size_belast.
by case: ifP => //=; rewrite eqxx addn0.
Qed.

Lemma nth_uniq s i j :
  i < size s -> j < size s -> uniq s -> (nth s i == nth s j) = (i == j).
Proof.
move=> lt_i_s lt_j_s Us; apply/eqP/eqP=> [eq_sij|-> //].
by rewrite -(index_uniq lt_i_s Us) eq_sij index_uniq.
Qed.

Lemma mem_rot s : rot n0 s =i s.
Proof. by move=> x; rewrite -{2}(cat_take_drop n0 s) !mem_cat /= orbC. Qed.

Lemma eqseq_rot s1 s2 : (rot n0 s1 == rot n0 s2) = (s1 == s2).
Proof. by apply: inj_eq; exact: rot_inj. Qed.

CoInductive rot_to_spec s x := RotToSpec i s' of rot i s = x :: s'.

Lemma rot_to s x : x \in s -> rot_to_spec s x.
Proof.
move=> s_x; pose i := index x s; exists i (drop i.+1 s ++ take i s).
rewrite -cat_cons {}/i; congr cat; elim: s s_x => //= y s IHs.
by rewrite eq_sym in_cons; case: eqP => // -> _; rewrite drop0.
Qed.

End EqSeq.

Definition inE := (mem_seq1, in_cons, inE).

Prenex Implicits mem_seq1 uniq undup index.

Implicit Arguments eqseqP [T x y].
Implicit Arguments hasP [T a s].
Implicit Arguments hasPn [T a s].
Implicit Arguments allP [T a s].
Implicit Arguments allPn [T a s].
Prenex Implicits eqseqP hasP hasPn allP allPn.

Section NseqthTheory.

Lemma nthP (T : eqType) (s : seq T) x x0 :
  reflect (exists2 i, i < size s & nth x0 s i = x) (x \in s).
Proof.
apply: (iffP idP) => [|[n Hn <-]]; last by apply mem_nth.
by exists (index x s); [rewrite index_mem | apply nth_index].
Qed.

Variable T : Type.

Lemma has_nthP (a : pred T) s x0 :
  reflect (exists2 i, i < size s & a (nth x0 s i)) (has a s).
Proof.
elim: s => [|x s IHs] /=; first by right; case.
case nax: (a x); first by left; exists 0.
by apply: (iffP IHs) => [[i]|[[|i]]]; [exists i.+1 | rewrite nax | exists i].
Qed.

Lemma all_nthP (a : pred T) s x0 :
  reflect (forall i, i < size s -> a (nth x0 s i)) (all a s).
Proof.
rewrite -(eq_all (fun x => negbK (a x))) all_predC.
case: (has_nthP _ _ x0) => [na_s | a_s]; [right=> a_s | left=> i lti].
  by case: na_s => i lti; rewrite a_s.
by apply/idPn=> na_si; case: a_s; exists i.
Qed.

End NseqthTheory.

Lemma set_nth_default T s (y0 x0 : T) n : n < size s -> nth x0 s n = nth y0 s n.
Proof. by elim: s n => [|y s' IHs] [|n] /=; auto. Qed.

Lemma headI T s (x : T) : rcons s x = head x s :: behead (rcons s x).
Proof. by case: s. Qed.

Implicit Arguments nthP [T s x].
Implicit Arguments has_nthP [T a s].
Implicit Arguments all_nthP [T a s].
Prenex Implicits nthP has_nthP all_nthP.

Definition bitseq := seq bool.
Canonical bitseq_eqType := Eval hnf in [eqType of bitseq].
Canonical bitseq_predType := Eval hnf in [predType of bitseq].

(* Incrementing the ith nat in a seq nat, padding with 0's if needed. This  *)
(* allows us to use nat seqs as bags of nats.                               *)

Fixpoint incr_nth v i {struct i} :=
  if v is n :: v' then if i is i'.+1 then n :: incr_nth v' i' else n.+1 :: v'
  else ncons i 0 [:: 1].

Lemma nth_incr_nth v i j : nth 0 (incr_nth v i) j = (i == j) + nth 0 v j.
Proof.
elim: v i j => [|n v IHv] [|i] [|j] //=; rewrite ?eqSS ?addn0 //; try by case j.
elim: i j => [|i IHv] [|j] //=; rewrite ?eqSS //; by case j.
Qed.

Lemma size_incr_nth v i :
  size (incr_nth v i) = if i < size v then size v else i.+1.
Proof.
elim: v i => [|n v IHv] [|i] //=; first by rewrite size_ncons /= addn1.
rewrite IHv; exact: fun_if.
Qed.

(* equality up to permutation *)

Section PermSeq.

Variable T : eqType.
Implicit Type s : seq T.

Definition same_count1 s1 s2 x := count (pred1 x) s1 == count (pred1 x) s2.

Definition perm_eq s1 s2 := all (same_count1 s1 s2) (s1 ++ s2).

Lemma perm_eqP s1 s2 : reflect (count^~ s1 =1 count^~ s2) (perm_eq s1 s2).
Proof.
apply: (iffP allP) => [eq_cnt1 a | eq_cnt x _]; last exact/eqP.
elim: {a}_.+1 {-2}a (ltnSn (count a (s1 ++ s2))) => // n IHn a le_an.
case: (posnP (count a (s1 ++ s2))).
  by move/eqP; rewrite count_cat addn_eq0; do 2!case: eqP => // ->.
rewrite -has_count => /hasP[x s12x a_x]; pose a' := predD1 a x.
have cnt_a' s : count a s = count (pred1 x) s + count a' s.
  rewrite count_filter -(count_predC (pred1 x)) 2!count_filter.
  rewrite -!filter_predI -!count_filter; congr (_ + _).
  by apply: eq_count => y /=; case: eqP => // ->.
rewrite !cnt_a' (eqnP (eq_cnt1 _ s12x)) (IHn a') // -ltnS.
apply: leq_trans le_an.
by rewrite ltnS cnt_a' -add1n leq_add2r -has_count has_pred1.
Qed.

Lemma perm_eq_refl s : perm_eq s s.
Proof. exact/perm_eqP. Qed.
Hint Resolve perm_eq_refl.

Lemma perm_eq_sym : symmetric perm_eq.
Proof. by move=> s1 s2; apply/perm_eqP/perm_eqP=> ? ?. Qed.

Lemma perm_eq_trans : transitive perm_eq.
Proof.
move=> s2 s1 s3; move/perm_eqP=> eq12; move/perm_eqP=> eq23.
by apply/perm_eqP=> a; rewrite eq12.
Qed.

Notation perm_eql s1 s2 := (perm_eq s1 =1 perm_eq s2).
Notation perm_eqr s1 s2 := (perm_eq^~ s1 =1 perm_eq^~ s2).

Lemma perm_eqlE s1 s2 : perm_eql s1 s2 -> perm_eq s1 s2. Proof. by move->. Qed.

Lemma perm_eqlP s1 s2 : reflect (perm_eql s1 s2) (perm_eq s1 s2).
Proof.
apply: (iffP idP) => [eq12 s3 | -> //].
apply/idP/idP; last exact: perm_eq_trans.
by rewrite -!(perm_eq_sym s3); move/perm_eq_trans; apply.
Qed.

Lemma perm_eqrP s1 s2 : reflect (perm_eqr s1 s2) (perm_eq s1 s2).
Proof.
apply: (iffP idP) => [/perm_eqlP eq12 s3| <- //].
by rewrite !(perm_eq_sym s3) eq12.
Qed.

Lemma perm_catC s1 s2 : perm_eql (s1 ++ s2) (s2 ++ s1).
Proof. by apply/perm_eqlP; apply/perm_eqP=> a; rewrite !count_cat addnC. Qed.

Lemma perm_cat2l s1 s2 s3 : perm_eq (s1 ++ s2) (s1 ++ s3) = perm_eq s2 s3.
Proof.
apply/perm_eqP/perm_eqP=> eq23 a; apply/eqP;
  by move/(_ a)/eqP: eq23; rewrite !count_cat eqn_add2l.
Qed.

Lemma perm_cons x s1 s2 : perm_eq (x :: s1) (x :: s2) = perm_eq s1 s2.
Proof. exact: (perm_cat2l [::x]). Qed.

Lemma perm_cat2r s1 s2 s3 : perm_eq (s2 ++ s1) (s3 ++ s1) = perm_eq s2 s3.
Proof. by do 2!rewrite perm_eq_sym perm_catC; exact: perm_cat2l. Qed.

Lemma perm_catAC s1 s2 s3 : perm_eql ((s1 ++ s2) ++ s3) ((s1 ++ s3) ++ s2).
Proof. by apply/perm_eqlP; rewrite -!catA perm_cat2l perm_catC. Qed.

Lemma perm_catCA s1 s2 s3 : perm_eql (s1 ++ s2 ++ s3) (s2 ++ s1 ++ s3).
Proof. by apply/perm_eqlP; rewrite !catA perm_cat2r perm_catC. Qed.

Lemma perm_rcons x s : perm_eql (rcons s x) (x :: s).
Proof. by move=> /= s2; rewrite -cats1 perm_catC. Qed.

Lemma perm_rot n s : perm_eql (rot n s) s.
Proof. by move=> /= s2; rewrite perm_catC cat_take_drop. Qed.

Lemma perm_rotr n s : perm_eql (rotr n s) s.
Proof. exact: perm_rot. Qed.

Lemma perm_filterC a s : perm_eql (filter a s ++ filter (predC a) s) s.
Proof.
apply/perm_eqlP; elim: s => //= x s IHs.
by case: (a x); last rewrite /= -cat1s perm_catCA; rewrite perm_cons.
Qed.

Lemma perm_eq_mem s1 s2 : perm_eq s1 s2 -> s1 =i s2.
Proof. by move/perm_eqP=> eq12 x; rewrite -!has_pred1 !has_count eq12. Qed.

Lemma perm_eq_size s1 s2 : perm_eq s1 s2 -> size s1 = size s2.
Proof. by move/perm_eqP=> eq12; rewrite -!count_predT eq12. Qed.

Lemma perm_eq_small s1 s2 : size s2 <= 1 -> perm_eq s1 s2 -> s1 = s2.
Proof.
move=> s2_le1 eqs12; move/perm_eq_size: eqs12 s2_le1 (perm_eq_mem eqs12).
by case: s2 s1 => [|x []] // [|y []] // _ _ /(_ x); rewrite !inE eqxx => /eqP->.
Qed.

Lemma uniq_leq_size s1 s2 : uniq s1 -> {subset s1 <= s2} -> size s1 <= size s2.
Proof.
elim: s1 s2 => //= x s1 IHs s2 /andP[not_s1x Us1] /allP/=/andP[s2x /allP ss12].
have [i s3 def_s2] := rot_to s2x; rewrite -(size_rot i s2) def_s2.
apply: IHs => // y s1y; have:= ss12 y s1y.
by rewrite -(mem_rot i) def_s2 inE (negPf (memPn _ y s1y)).
Qed.

Lemma leq_size_uniq s1 s2 :
  uniq s1 -> {subset s1 <= s2} -> size s2 <= size s1 -> uniq s2.
Proof.
elim: s1 s2 => [[] | x s1 IHs s2] // Us1x; have /andP[not_s1x Us1] := Us1x.
case/allP/andP=> /rot_to[i s3 def_s2] /allP ss12 le_s21.
rewrite -(rot_uniq i) -(size_rot i) def_s2 /= in le_s21 *.
have ss13 y (s1y : y \in s1): y \in s3.
  by have:= ss12 y s1y; rewrite -(mem_rot i) def_s2 inE (negPf (memPn _ y s1y)).
rewrite IHs // andbT; apply: contraL _ le_s21 => s3x; rewrite -leqNgt.
by apply/(uniq_leq_size Us1x)/allP; rewrite /= s3x; exact/allP.
Qed.

Lemma uniq_size_uniq s1 s2 :
  uniq s1 -> s1 =i s2 -> uniq s2 = (size s2 == size s1).
Proof.
move=> Us1 eqs12; apply/idP/idP=> [Us2 | /eqP eq_sz12].
  by rewrite eqn_leq !uniq_leq_size // => y; rewrite eqs12.
by apply: (leq_size_uniq Us1) => [y|]; rewrite (eqs12, eq_sz12).
Qed.

Lemma leq_size_perm s1 s2 :
    uniq s1 -> {subset s1 <= s2} -> size s2 <= size s1 ->
  s1 =i s2 /\ size s1 = size s2.
Proof.
move=> Us1 ss12 le_s21; have Us2: uniq s2 := leq_size_uniq Us1 ss12 le_s21.
suffices: s1 =i s2 by split; last by apply/eqP; rewrite -uniq_size_uniq.
move=> x; apply/idP/idP=> [/ss12// | s2x]; apply: contraLR le_s21 => not_s1x.
rewrite -ltnNge (@uniq_leq_size (x :: s1)) /= ?not_s1x //.
by apply/allP; rewrite /= s2x; exact/allP.
Qed.

Lemma perm_uniq s1 s2 : s1 =i s2 -> size s1 = size s2 -> uniq s1 = uniq s2.
Proof.
by move=> Es12 Hs12; apply/idP/idP => Us;
  rewrite (uniq_size_uniq Us) ?Hs12 ?eqxx.
Qed.

Lemma perm_eq_uniq s1 s2 : perm_eq s1 s2 -> uniq s1 = uniq s2.
Proof.
move=> eq_s12; apply: perm_uniq; [exact: perm_eq_mem | exact: perm_eq_size].
Qed.

Lemma uniq_perm_eq s1 s2 : uniq s1 -> uniq s2 -> s1 =i s2 -> perm_eq s1 s2.
Proof.
move=> Us1 Us2 eq12; apply/allP=> x _; apply/eqP.
by rewrite !count_uniq_mem ?eq12.
Qed.

Lemma count_mem_uniq s : (forall x, count (pred1 x) s = (x \in s)) -> uniq s.
Proof.
move=> count1_s; have Uus := undup_uniq s.
suffices: perm_eq s (undup s) by move/perm_eq_uniq->.
by apply/allP=> x _; apply/eqP; rewrite (count_uniq_mem x Uus) mem_undup.
Qed.

Lemma catCA_perm_ind P :
    (forall s1 s2 s3, P (s1 ++ s2 ++ s3) -> P (s2 ++ s1 ++ s3)) ->
  (forall s1 s2, perm_eq s1 s2 -> P s1 -> P s2).
Proof.
move=> PcatCA s1 s2 eq_s12; rewrite -[s1]cats0 -[s2]cats0.
elim: s2 nil => [| x s2 IHs] s3 in s1 eq_s12 *.
  by case: s1 {eq_s12}(perm_eq_size eq_s12).
have /rot_to[i s' def_s1]: x \in s1 by rewrite (perm_eq_mem eq_s12) mem_head.
rewrite -(cat_take_drop i s1) -catA => /PcatCA.
rewrite catA -/(rot i s1) def_s1 /= -cat1s => /PcatCA/IHs/PcatCA; apply.
by rewrite -(perm_cons x) -def_s1 perm_rot.
Qed.

Lemma catCA_perm_subst R F :
    (forall s1 s2 s3, F (s1 ++ s2 ++ s3) = F (s2 ++ s1 ++ s3) :> R) ->
  (forall s1 s2, perm_eq s1 s2 -> F s1 = F s2).
Proof.
move=> FcatCA s1 s2 /catCA_perm_ind => ind_s12.
by apply: (ind_s12 (eq _ \o F)) => //= *; rewrite FcatCA.
Qed.

End PermSeq.

Notation perm_eql s1 s2 := (perm_eq s1 =1 perm_eq s2).
Notation perm_eqr s1 s2 := (perm_eq^~ s1 =1 perm_eq^~ s2).

Implicit Arguments perm_eqP [T s1 s2].
Implicit Arguments perm_eqlP [T s1 s2].
Implicit Arguments perm_eqrP [T s1 s2].
Prenex Implicits perm_eq perm_eqP perm_eqlP perm_eqrP.
Hint Resolve perm_eq_refl.

Section RotrLemmas.

Variables (n0 : nat) (T : Type) (T' : eqType).
Implicit Type s : seq T.

Lemma size_rotr s : size (rotr n0 s) = size s.
Proof. by rewrite size_rot. Qed.

Lemma mem_rotr (s : seq T') : rotr n0 s =i s.
Proof. by move=> x; rewrite mem_rot. Qed.

Lemma rotr_size_cat s1 s2 : rotr (size s2) (s1 ++ s2) = s2 ++ s1.
Proof. by rewrite /rotr size_cat addnK rot_size_cat. Qed.

Lemma rotr1_rcons x s : rotr 1 (rcons s x) = x :: s.
Proof. by rewrite -rot1_cons rotK. Qed.

Lemma has_rotr a s : has a (rotr n0 s) = has a s.
Proof. by rewrite has_rot. Qed.

Lemma rotr_uniq (s : seq T') : uniq (rotr n0 s) = uniq s.
Proof. by rewrite rot_uniq. Qed.

Lemma rotrK : cancel (@rotr T n0) (rot n0).
Proof.
move=> s; have [lt_n0s | ge_n0s] := ltnP n0 (size s).
  by rewrite -{1}(subKn (ltnW lt_n0s)) -{1}[size s]size_rotr; exact: rotK.
by rewrite -{2}(rot_oversize ge_n0s) /rotr (eqnP ge_n0s) rot0.
Qed.

Lemma rotr_inj : injective (@rotr T n0).
Proof. exact (can_inj rotrK). Qed.

Lemma rev_rot s : rev (rot n0 s) = rotr n0 (rev s).
Proof.
rewrite /rotr size_rev -{3}(cat_take_drop n0 s) {1}/rot !rev_cat.
by rewrite -size_drop -size_rev rot_size_cat.
Qed.

Lemma rev_rotr s : rev (rotr n0 s) = rot n0 (rev s).
Proof.
apply: canRL rotrK _; rewrite {1}/rotr size_rev size_rotr /rotr {2}/rot rev_cat.
set m := size s - n0; rewrite -{1}(@size_takel m _ _ (leq_subr _ _)).
by rewrite -size_rev rot_size_cat -rev_cat cat_take_drop.
Qed.

End RotrLemmas.

Section RotCompLemmas.

Variable T : Type.
Implicit Type s : seq T.

Lemma rot_addn m n s : m + n <= size s -> rot (m + n) s = rot m (rot n s).
Proof.
move=> sz_s; rewrite {1}/rot -[take _ s](cat_take_drop n).
rewrite 5!(catA, =^~ rot_size_cat) !cat_take_drop.
by rewrite size_drop !size_takel ?leq_addl ?addnK.
Qed.

Lemma rotS n s : n < size s -> rot n.+1 s = rot 1 (rot n s).
Proof. exact: (@rot_addn 1). Qed.

Lemma rot_add_mod m n s : n <= size s -> m <= size s ->
  rot m (rot n s) = rot (if m + n <= size s then m + n else m + n - size s) s.
Proof.
move=> Hn Hm; case: leqP => [/rot_addn // | /ltnW Hmn]; symmetry.
by rewrite -{2}(rotK n s) /rotr -rot_addn size_rot addnBA ?subnK ?addnK.
Qed.

Lemma rot_rot m n s : rot m (rot n s) = rot n (rot m s).
Proof.
case: (ltnP (size s) m) => Hm.
  by rewrite !(@rot_oversize T m) ?size_rot 1?ltnW.
case: (ltnP (size s) n) => Hn.
  by rewrite !(@rot_oversize T n) ?size_rot 1?ltnW.
by rewrite !rot_add_mod 1?addnC.
Qed.

Lemma rot_rotr m n s : rot m (rotr n s) = rotr n (rot m s).
Proof. by rewrite {2}/rotr size_rot rot_rot. Qed.

Lemma rotr_rotr m n s : rotr m (rotr n s) = rotr n (rotr m s).
Proof. by rewrite /rotr !size_rot rot_rot. Qed.

End RotCompLemmas.

Section Mask.

Variables (n0 : nat) (T : Type).
Implicit Types (m : bitseq) (s : seq T).

Fixpoint mask m s {struct m} :=
  match m, s with
  | b :: m', x :: s' => if b then x :: mask m' s' else mask m' s'
  | _, _ => [::]
  end.

Lemma mask_false s n : mask (nseq n false) s = [::].
Proof. by elim: s n => [|x s IHs] [|n] /=. Qed.

Lemma mask_true s n : size s <= n -> mask (nseq n true) s = s.
Proof. by elim: s n => [|x s IHs] [|n] //= Hn; congr (_ :: _); apply: IHs. Qed.

Lemma mask0 m : mask m [::] = [::].
Proof. by case: m. Qed.

Lemma mask1 b x : mask [:: b] [:: x] = nseq b x.
Proof. by case: b. Qed.

Lemma mask_cons b m x s : mask (b :: m) (x :: s) = nseq b x ++ mask m s.
Proof. by case: b. Qed.

Lemma size_mask m s : size m = size s -> size (mask m s) = count id m.
Proof. by elim: m s => [|b m IHm] [|x s] //= [Hs]; case: b; rewrite /= IHm. Qed.

Lemma mask_cat m1 s1 :
    size m1 = size s1 ->
  forall m2 s2, mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2.
Proof.
move=> Hm1 m2 s2; elim: m1 s1 Hm1 => [|b1 m1 IHm] [|x1 s1] //= [Hm1].
by rewrite (IHm _ Hm1); case b1.
Qed.

Lemma has_mask_cons a b m x s :
  has a (mask (b :: m) (x :: s)) = b && a x || has a (mask m s).
Proof. by case: b. Qed.

Lemma has_mask a m s : has a (mask m s) -> has a s.
Proof.
elim: m s => [|b m IHm] [|x s] //; rewrite has_mask_cons /= andbC.
by case: (a x) => //= /IHm.
Qed.

Lemma mask_rot m s : size m = size s ->
   mask (rot n0 m) (rot n0 s) = rot (count id (take n0 m)) (mask m s).
Proof.
move=> Hs.
have Hsn0: size (take n0 m) = size (take n0 s) by rewrite !size_take Hs.
rewrite -(size_mask Hsn0) {1 2}/rot mask_cat ?size_drop ?Hs //.
rewrite -{4}(cat_take_drop n0 m) -{4}(cat_take_drop n0 s) mask_cat //.
by rewrite rot_size_cat.
Qed.

End Mask.

Section EqMask.

Variables (n0 : nat) (T : eqType).
Implicit Types (s : seq T) (m : bitseq).

Lemma mem_mask_cons x b m y s :
  (x \in mask (b :: m) (y :: s)) = b && (x == y) || (x \in mask m s).
Proof. by case: b. Qed.

Lemma mem_mask x m s : x \in mask m s -> x \in s.
Proof. by rewrite -!has_pred1 => /has_mask. Qed.

Lemma mask_uniq s : uniq s -> forall m, uniq (mask m s).
Proof.
elim: s => [|x s IHs] Uxs [|b m] //=.
case: b Uxs => //= /andP[s'x Us]; rewrite {}IHs // andbT.
by apply: contra s'x; exact: mem_mask.
Qed.

Lemma mem_mask_rot m s :
  size m = size s -> mask (rot n0 m) (rot n0 s) =i mask m s.
Proof. by move=> Hm x; rewrite mask_rot // mem_rot. Qed.

End EqMask.

Section Subseq.

Variable T : eqType.
Implicit Type s : seq T.

Fixpoint subseq s1 s2 :=
  if s2 is y :: s2' then
    if s1 is x :: s1' then subseq (if x == y then s1' else s1) s2' else true
  else s1 == [::].

Lemma sub0seq s : subseq [::] s. Proof. by case: s. Qed.

Lemma subseq0 s : subseq s [::] = (s == [::]). Proof. by []. Qed.

Lemma subseqP s1 s2 :
  reflect (exists2 m, size m = size s2 & s1 = mask m s2) (subseq s1 s2).
Proof.
elim: s2 s1 => [|y s2 IHs2] [|x s1].
- by left; exists [::].
- by right; do 2!case.
- by left; exists (nseq (size s2).+1 false); rewrite ?size_nseq //= mask_false.
apply: {IHs2}(iffP (IHs2 _)) => [] [m sz_m def_s1].
  by exists ((x == y) :: m); rewrite /= ?sz_m // -def_s1; case: eqP => // ->.
case: eqP => [_ | ne_xy]; last first.
  by case: m def_s1 sz_m => [//|[m []//|m]] -> [<-]; exists m.
pose i := index true m; have def_m_i: take i m = nseq (size (take i m)) false.
  apply/all_pred1P; apply/(all_nthP true) => j.
  rewrite size_take ltnNge geq_min negb_or -ltnNge; case/andP=> lt_j_i _.
  rewrite nth_take //= -negb_add addbF -addbT -negb_eqb.
  by rewrite [_ == _](before_find _ lt_j_i).
have lt_i_m: i < size m.
  rewrite ltnNge; apply/negP=> le_m_i; rewrite take_oversize // in def_m_i.
  by rewrite def_m_i mask_false in def_s1.
rewrite size_take lt_i_m in def_m_i.
exists (take i m ++ drop i.+1 m).
  rewrite size_cat size_take size_drop lt_i_m.
  by rewrite sz_m in lt_i_m *; rewrite subnKC.
rewrite {s1 def_s1}[s1](congr1 behead def_s1).
rewrite -[s2](cat_take_drop i) -{1}[m](cat_take_drop i) {}def_m_i -cat_cons.
have sz_i_s2: size (take i s2) = i by apply: size_takel; rewrite sz_m in lt_i_m.
rewrite lastI cat_rcons !mask_cat ?size_nseq ?size_belast ?mask_false //=.
by rewrite (drop_nth true) // nth_index -?index_mem.
Qed.

Lemma subseq_trans : transitive subseq.
Proof.
move=> _ _ s /subseqP[m2 _ ->] /subseqP[m1 _ ->].
elim: s => [|x s IHs] in m2 m1 *; first by rewrite !mask0.
case: m1 => [|[] m1]; first by rewrite mask0.
  case: m2 => [|[] m2] //; first by rewrite /= eqxx IHs.
  case/subseqP: (IHs m2 m1) => m sz_m def_s; apply/subseqP.
  by exists (false :: m); rewrite //= sz_m.
case/subseqP: (IHs m2 m1) => m sz_m def_s; apply/subseqP.
by exists (false :: m); rewrite //= sz_m.
Qed.

Lemma subseq_refl s : subseq s s.
Proof. by elim: s => //= x s IHs; rewrite eqxx. Qed.
Hint Resolve subseq_refl.

Lemma cat_subseq s1 s2 s3 s4 :
  subseq s1 s3 -> subseq s2 s4 -> subseq (s1 ++ s2) (s3 ++ s4).
Proof.
case/subseqP=> m1 sz_m1 ->; case/subseqP=> m2 sz_m2 ->; apply/subseqP.
by exists (m1 ++ m2); rewrite ?size_cat ?mask_cat ?sz_m1 ?sz_m2.
Qed.

Lemma prefix_subseq s1 s2 : subseq s1 (s1 ++ s2).
Proof. by rewrite -{1}[s1]cats0 cat_subseq ?sub0seq. Qed.

Lemma suffix_subseq s1 s2 : subseq s2 (s1 ++ s2).
Proof. by rewrite -{1}[s2]cat0s cat_subseq ?sub0seq. Qed.

Lemma mem_subseq s1 s2 : subseq s1 s2 -> {subset s1 <= s2}.
Proof. by case/subseqP=> m _ -> x; exact: mem_mask. Qed.

Lemma sub1seq x s : subseq [:: x] s = (x \in s).
Proof.
by elim: s => //= y s; rewrite inE; case: (x == y); rewrite ?sub0seq.
Qed.

Lemma size_subseq s1 s2 : subseq s1 s2 -> size s1 <= size s2.
Proof. by case/subseqP=> m sz_m ->; rewrite size_mask -sz_m ?count_size. Qed.

Lemma size_subseq_leqif s1 s2 :
  subseq s1 s2 -> size s1 <= size s2 ?= iff (s1 == s2).
Proof.
move=> sub12; split; first exact: size_subseq.
apply/idP/eqP=> [|-> //]; case/subseqP: sub12 => m sz_m ->{s1}.
rewrite size_mask -sz_m // -all_count -(eq_all eqb_id).
by move/(@all_pred1P _ true)->; rewrite sz_m mask_true.
Qed.

Lemma subseq_cons s x : subseq s (x :: s).
Proof. by exact: (@cat_subseq [::] s [:: x]). Qed.

Lemma subseq_rcons s x : subseq s (rcons s x).
Proof. by rewrite -{1}[s]cats0 -cats1 cat_subseq. Qed.

Lemma subseq_uniq s1 s2 : subseq s1 s2 -> uniq s2 -> uniq s1.
Proof. by case/subseqP=> m _ -> Us2; exact: mask_uniq. Qed.

End Subseq.

Prenex Implicits subseq.
Implicit Arguments subseqP [T s1 s2].

Hint Resolve subseq_refl.

Section Rem.

Variables (T : eqType) (x : T).

Fixpoint rem s := if s is y :: t then (if y == x then t else y :: rem t) else s.

Lemma rem_id s : x \notin s -> rem s = s.
Proof.
by elim: s => //= y s IHs /norP[neq_yx /IHs->]; rewrite eq_sym (negbTE neq_yx).
Qed.

Lemma perm_to_rem s : x \in s -> perm_eq s (x :: rem s).
Proof.
elim: s => // y s IHs; rewrite inE /= eq_sym perm_eq_sym.
case: eqP => [-> // | _ /IHs].
by rewrite (perm_catCA [:: x] [:: y]) perm_cons perm_eq_sym.
Qed.

Lemma size_rem s : x \in s -> size (rem s) = (size s).-1.
Proof. by move/perm_to_rem/perm_eq_size->. Qed.

Lemma rem_subseq s : subseq (rem s) s.
Proof.
elim: s => //= y s IHs; rewrite eq_sym.
by case: ifP => _; [exact: subseq_cons | rewrite eqxx].
Qed.

Lemma rem_uniq s : uniq s -> uniq (rem s).
Proof. by apply: subseq_uniq; exact: rem_subseq. Qed.

Lemma mem_rem s : {subset rem s <= s}.
Proof. exact: mem_subseq (rem_subseq s). Qed.

Lemma rem_filter s : uniq s -> rem s = filter (predC1 x) s.
Proof.
elim: s => //= y s IHs /andP[not_s_y /IHs->].
by case: eqP => //= <-; apply/esym/all_filterP; rewrite all_predC has_pred1.
Qed.

Lemma mem_rem_uniq s : uniq s -> rem s =i [predD1 s & x].
Proof. by move/rem_filter=> -> y; rewrite mem_filter. Qed.

End Rem.

Section Map.

Variables (n0 : nat) (T1 : Type) (x1 : T1).
Variables (T2 : Type) (x2 : T2) (f : T1 -> T2).

Fixpoint map s := if s is x :: s' then f x :: map s' else [::].

Lemma map_cons x s : map (x :: s) = f x :: map s.
Proof. by []. Qed.

Lemma map_nseq x : map (nseq n0 x) = nseq n0 (f x).
Proof. by elim: n0 => // *; congr (_ :: _). Qed.

Lemma map_cat s1 s2 : map (s1 ++ s2) = map s1 ++ map s2.
Proof. by elim: s1 => [|x s1 IHs] //=; rewrite IHs. Qed.

Lemma size_map s : size (map s) = size s.
Proof. by elim: s => //= x s ->. Qed.

Lemma behead_map s : behead (map s) = map (behead s).
Proof. by case: s. Qed.

Lemma nth_map n s : n < size s -> nth x2 (map s) n = f (nth x1 s n).
Proof. by elim: s n => [|x s IHs] [|n]; try exact (IHs n). Qed.

Lemma map_rcons s x : map (rcons s x) = rcons (map s) (f x).
Proof. by rewrite -!cats1 map_cat. Qed.

Lemma last_map s x : last (f x) (map s) = f (last x s).
Proof. by elim: s x => /=. Qed.

Lemma belast_map s x : belast (f x) (map s) = map (belast x s).
Proof. by elim: s x => //= y s IHs x; rewrite IHs. Qed.

Lemma filter_map a s : filter a (map s) = map (filter (preim f a) s).
Proof. by elim: s => //= x s IHs; rewrite (fun_if map) /= IHs. Qed.

Lemma find_map a s : find a (map s) = find (preim f a) s.
Proof. by elim: s => //= x s ->. Qed.

Lemma has_map a s : has a (map s) = has (preim f a) s.
Proof. by elim: s => //= x s ->. Qed.

Lemma all_map a s : all a (map s) = all (preim f a) s.
Proof. by elim: s => //= x s ->. Qed.

Lemma count_map a s : count a (map s) = count (preim f a) s.
Proof. by elim: s => //= x s ->. Qed.

Lemma map_take s : map (take n0 s) = take n0 (map s).
Proof. by elim: n0 s => [|n IHn] [|x s] //=; rewrite IHn. Qed.

Lemma map_drop s : map (drop n0 s) = drop n0 (map s).
Proof. by elim: n0 s => [|n IHn] [|x s] //=; rewrite IHn. Qed.

Lemma map_rot s : map (rot n0 s) = rot n0 (map s).
Proof. by rewrite /rot map_cat map_take map_drop. Qed.

Lemma map_rotr s : map (rotr n0 s) = rotr n0 (map s).
Proof. by apply: canRL (@rotK n0 T2) _; rewrite -map_rot rotrK. Qed.

Lemma map_rev s : map (rev s) = rev (map s).
Proof. by elim: s => //= x s IHs; rewrite !rev_cons -!cats1 map_cat IHs. Qed.

Lemma map_mask m s : map (mask m s) = mask m (map s).
Proof. by elim: m s => [|[|] m IHm] [|x p] //=; rewrite IHm. Qed.

Lemma inj_map : injective f -> injective map.
Proof.
by move=> injf; elim=> [|y1 s1 IHs] [|y2 s2] //= [/injf-> /IHs->].
Qed.

End Map.

Notation "[ 'seq' E | i <- s ]" := (map (fun i => E) s)
  (at level 0, E at level 99, i ident,
   format "[ '[hv' 'seq'  E '/ '  |  i  <-  s ] ']'") : seq_scope.

Notation "[ 'seq' E | i <- s & C ]" := [seq E | i <- [seq i <- s | C]]
  (at level 0, E at level 99, i ident,
   format "[ '[hv' 'seq'  E '/ '  |  i  <-  s '/ '  &  C ] ']'") : seq_scope.

Notation "[ 'seq' E | i : T <- s ]" := (map (fun i : T => E) s)
  (at level 0, E at level 99, i ident, only parsing) : seq_scope.

Notation "[ 'seq' E | i : T <- s & C ]" :=
  [seq E | i : T <- [seq i : T <- s | C]]
  (at level 0, E at level 99, i ident, only parsing) : seq_scope.

Lemma filter_mask T a (s : seq T) : filter a s = mask (map a s) s.
Proof. by elim: s => //= x s <-; case: (a x). Qed.

Section FilterSubseq.

Variable T : eqType.
Implicit Types (s : seq T) (a : pred T).

Lemma filter_subseq a s : subseq (filter a s) s.
Proof. by apply/subseqP; exists (map a s); rewrite ?size_map ?filter_mask. Qed.

Lemma subseq_filter s1 s2 a :
  subseq s1 (filter a s2) = all a s1 && subseq s1 s2.
Proof.
elim: s2 s1 => [|x s2 IHs] [|y s1] //=; rewrite ?andbF ?sub0seq //.
by case a_x: (a x); rewrite /= !IHs /=; case: eqP => // ->; rewrite a_x.
Qed.

Lemma subseq_uniqP s1 s2 :
  uniq s2 -> reflect (s1 = filter (mem s1) s2) (subseq s1 s2).
Proof.
move=> uniq_s2; apply: (iffP idP) => [ss12 | ->]; last exact: filter_subseq.
apply/eqP; rewrite -size_subseq_leqif ?subseq_filter ?(introT allP) //.
apply/eqP/esym/perm_eq_size.
rewrite uniq_perm_eq ?filter_uniq ?(subseq_uniq ss12) // => x.
by rewrite mem_filter; apply: andb_idr; exact: (mem_subseq ss12).
Qed.

Lemma perm_to_subseq s1 s2 :
  subseq s1 s2 -> {s3 | perm_eq s2 (s1 ++ s3)}.
Proof.
elim Ds2: s2 s1 => [|y s2' IHs] [|x s1] //=; try by exists s2; rewrite Ds2.
case: eqP => [-> | _] /IHs[s3 perm_s2] {IHs}.
  by exists s3; rewrite perm_cons.
by exists (rcons s3 y); rewrite -cat_cons -perm_rcons -!cats1 catA perm_cat2r.
Qed.

End FilterSubseq.

Implicit Arguments subseq_uniqP [T s1 s2].

Section EqMap.

Variables (n0 : nat) (T1 : eqType) (x1 : T1).
Variables (T2 : eqType) (x2 : T2) (f : T1 -> T2).
Implicit Type s : seq T1.

Lemma map_f s x : x \in s -> f x \in map f s.
Proof.
elim: s => [|y s IHs] //=.
by case/predU1P=> [->|Hx]; [exact: predU1l | apply: predU1r; auto].
Qed.

Lemma mapP s y : reflect (exists2 x, x \in s & y = f x) (y \in map f s).
Proof.
elim: s => [|x s IHs]; first by right; case.
rewrite /= in_cons eq_sym; case Hxy: (f x == y).
  by left; exists x; [rewrite mem_head | rewrite (eqP Hxy)].
apply: (iffP IHs) => [[x' Hx' ->]|[x' Hx' Dy]].
  by exists x'; first exact: predU1r.
by move: Dy Hxy => ->; case/predU1P: Hx' => [->|]; [rewrite eqxx | exists x'].
Qed.

Lemma map_uniq s : uniq (map f s) -> uniq s.
Proof.
elim: s => //= x s IHs /andP[not_sfx /IHs->]; rewrite andbT.
by apply: contra not_sfx => sx; apply/mapP; exists x.
Qed.

Lemma map_inj_in_uniq s : {in s &, injective f} -> uniq (map f s) = uniq s.
Proof.
elim: s => //= x s IHs //= injf; congr (~~ _ && _).
  apply/mapP/idP=> [[y sy /injf] | ]; last by exists x.
  by rewrite mem_head mem_behead // => ->.
apply: IHs => y z sy sz; apply: injf => //; exact: predU1r.
Qed.

Lemma map_subseq s1 s2 : subseq s1 s2 -> subseq (map f s1) (map f s2).
Proof.
case/subseqP=> m sz_m ->; apply/subseqP.
by exists m; rewrite ?size_map ?map_mask.
Qed.

Lemma nth_index_map s x0 x :
  {in s &, injective f} -> x \in s -> nth x0 s (index (f x) (map f s)) = x.
Proof.
elim: s => //= y s IHs inj_f s_x; rewrite (inj_in_eq inj_f) ?mem_head //.
move: s_x; rewrite inE eq_sym; case: eqP => [-> | _] //=; apply: IHs.
by apply: sub_in2 inj_f => z; exact: predU1r.
Qed.

Lemma perm_map s t : perm_eq s t -> perm_eq (map f s) (map f t).
Proof. by move/perm_eqP=> Est; apply/perm_eqP=> a; rewrite !count_map Est. Qed.

Hypothesis Hf : injective f.

Lemma mem_map s x : (f x \in map f s) = (x \in s).
Proof. by apply/mapP/idP=> [[y Hy /Hf->] //|]; exists x. Qed.

Lemma index_map s x : index (f x) (map f s) = index x s.
Proof. by rewrite /index; elim: s => //= y s IHs; rewrite (inj_eq Hf) IHs. Qed.

Lemma map_inj_uniq s : uniq (map f s) = uniq s.
Proof. apply: map_inj_in_uniq; exact: in2W. Qed.

End EqMap.

Implicit Arguments mapP [T1 T2 f s y].
Prenex Implicits mapP.

Lemma map_of_seq (T1 : eqType) T2 (s : seq T1) (fs : seq T2) (y0 : T2) :
  {f | uniq s -> size fs = size s -> map f s = fs}.
Proof.
exists (fun x => nth y0 fs (index x s)) => uAs eq_sz.
apply/esym/(@eq_from_nth _ y0); rewrite ?size_map eq_sz // => i ltis.
have x0 : T1 by [case: (s) ltis]; by rewrite (nth_map x0) // index_uniq.
Qed.

Section MapComp.

Variable T1 T2 T3 : Type.

Lemma map_id (s : seq T1) : map id s = s.
Proof. by elim: s => //= x s ->. Qed.

Lemma eq_map (f1 f2 : T1 -> T2) : f1 =1 f2 -> map f1 =1 map f2.
Proof. by move=> Ef; elim=> //= x s ->; rewrite Ef. Qed.

Lemma map_comp (f1 : T2 -> T3) (f2 : T1 -> T2) s :
  map (f1 \o f2) s = map f1 (map f2 s).
Proof. by elim: s => //= x s ->. Qed.

Lemma mapK (f1 : T1 -> T2) (f2 : T2 -> T1) :
  cancel f1 f2 -> cancel (map f1) (map f2).
Proof. by move=> eq_f12; elim=> //= x s ->; rewrite eq_f12. Qed.

End MapComp.

Lemma eq_in_map (T1 : eqType) T2 (f1 f2 : T1 -> T2) (s : seq T1) :
  {in s, f1 =1 f2} <-> map f1 s = map f2 s.
Proof.
elim: s => //= x s IHs; split=> [eqf12 | [f12x /IHs eqf12]]; last first.
  by move=> y /predU1P[-> | /eqf12].
rewrite eqf12 ?mem_head //; congr (_ :: _).
by apply/IHs=> y s_y; rewrite eqf12 // mem_behead.
Qed.

Lemma map_id_in (T : eqType) f (s : seq T) : {in s, f =1 id} -> map f s = s.
Proof. by move/eq_in_map->; apply: map_id. Qed.

(* Map a partial function *)

Section Pmap.

Variables (aT rT : Type) (f : aT -> option rT) (g : rT -> aT).

Fixpoint pmap s :=
  if s is x :: s' then let r := pmap s' in oapp (cons^~ r) r (f x) else [::].

Lemma map_pK : pcancel g f -> cancel (map g) pmap.
Proof. by move=> gK; elim=> //= x s ->; rewrite gK. Qed.

Lemma size_pmap s : size (pmap s) = count [eta f] s.
Proof. by elim: s => //= x s <-; case: (f _). Qed.

Lemma pmapS_filter s : map some (pmap s) = map f (filter [eta f] s).
Proof. by elim: s => //= x s; case fx: (f x) => //= [u] <-; congr (_ :: _). Qed.

Hypothesis fK : ocancel f g.

Lemma pmap_filter s : map g (pmap s) = filter [eta f] s.
Proof. by elim: s => //= x s <-; rewrite -{3}(fK x); case: (f _). Qed.

End Pmap.

Section EqPmap.

Variables (aT rT : eqType) (f : aT -> option rT) (g : rT -> aT).

Lemma eq_pmap (f1 f2 : aT -> option rT) : f1 =1 f2 -> pmap f1 =1 pmap f2.
Proof. by move=> Ef; elim=> //= x s ->; rewrite Ef. Qed.

Lemma mem_pmap s u : (u \in pmap f s) = (Some u \in map f s).
Proof. by elim: s => //= x s IHs; rewrite in_cons -IHs; case: (f x). Qed.

Hypothesis fK : ocancel f g.

Lemma can2_mem_pmap : pcancel g f -> forall s u, (u \in pmap f s) = (g u \in s).
Proof.
by move=> gK s u; rewrite -(mem_map (pcan_inj gK)) pmap_filter // mem_filter gK.
Qed.

Lemma pmap_uniq s : uniq s -> uniq (pmap f s).
Proof.
by move/(filter_uniq [eta f]); rewrite -(pmap_filter fK); exact: map_uniq.
Qed.

End EqPmap.

Section PmapSub.

Variables (T : Type) (p : pred T) (sT : subType p).

Lemma size_pmap_sub s : size (pmap (insub : T -> option sT) s) = count p s.
Proof. by rewrite size_pmap (eq_count (isSome_insub _)). Qed.

End PmapSub.

Section EqPmapSub.

Variables (T : eqType) (p : pred T) (sT : subType p).

Let insT : T -> option sT := insub.

Lemma mem_pmap_sub s u : (u \in pmap insT s) = (val u \in s).
Proof. apply: (can2_mem_pmap (insubK _)); exact: valK. Qed.

Lemma pmap_sub_uniq s : uniq s -> uniq (pmap insT s).
Proof. exact: (pmap_uniq (insubK _)). Qed.

End EqPmapSub.

(* Index sequence *)

Fixpoint iota m n := if n is n'.+1 then m :: iota m.+1 n' else [::].

Lemma size_iota m n : size (iota m n) = n.
Proof. by elim: n m => //= n IHn m; rewrite IHn. Qed.

Lemma iota_add m n1 n2 : iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2.
Proof.
by elim: n1 m => //= [|n1 IHn1] m; rewrite ?addn0 // -addSnnS -IHn1.
Qed.

Lemma iota_addl m1 m2 n : iota (m1 + m2) n = map (addn m1) (iota m2 n).
Proof. by elim: n m2 => //= n IHn m2; rewrite -addnS IHn. Qed.

Lemma nth_iota m n i : i < n -> nth 0 (iota m n) i = m + i.
Proof.
by move/subnKC <-; rewrite addSnnS iota_add nth_cat size_iota ltnn subnn.
Qed.

Lemma mem_iota m n i : (i \in iota m n) = (m <= i) && (i < m + n).
Proof.
elim: n m => [|n IHn] /= m; first by rewrite addn0 ltnNge andbN.
rewrite -addSnnS leq_eqVlt in_cons eq_sym.
by case: eqP => [->|_]; [rewrite leq_addr | exact: IHn].
Qed.

Lemma iota_uniq m n : uniq (iota m n).
Proof. by elim: n m => //= n IHn m; rewrite mem_iota ltnn /=. Qed.

(* Making a sequence of a specific length, using indexes to compute items. *)

Section MakeSeq.

Variables (T : Type) (x0 : T).

Definition mkseq f n : seq T := map f (iota 0 n).

Lemma size_mkseq f n : size (mkseq f n) = n.
Proof. by rewrite size_map size_iota. Qed.

Lemma eq_mkseq f g : f =1 g -> mkseq f =1 mkseq g.
Proof. by move=> Efg n; exact: eq_map Efg _. Qed.

Lemma nth_mkseq f n i : i < n -> nth x0 (mkseq f n) i = f i.
Proof. by move=> Hi; rewrite (nth_map 0) ?nth_iota ?size_iota. Qed.

Lemma mkseq_nth s : mkseq (nth x0 s) (size s) = s.
Proof.
by apply: (@eq_from_nth _ x0); rewrite size_mkseq // => i Hi; rewrite nth_mkseq.
Qed.

End MakeSeq.

Section MakeEqSeq.

Variable T : eqType.

Lemma mkseq_uniq (f : nat -> T) n : injective f -> uniq (mkseq f n).
Proof. by move/map_inj_uniq->; apply: iota_uniq. Qed.

Lemma perm_eq_iotaP {s t : seq T} x0 (It := iota 0 (size t)) :
  reflect (exists2 Is, perm_eq Is It & s = map (nth x0 t) Is) (perm_eq s t).
Proof.
apply: (iffP idP) => [Est | [Is eqIst ->]]; last first.
  by rewrite -{2}[t](mkseq_nth x0) perm_map.
elim: t => [|x t IHt] in s It Est *.
  by rewrite (perm_eq_small _ Est) //; exists [::].
have /rot_to[k s1 Ds]: x \in s by rewrite (perm_eq_mem Est) mem_head.
have [|Is1 eqIst1 Ds1] := IHt s1; first by rewrite -(perm_cons x) -Ds perm_rot.
exists (rotr k (0 :: map succn Is1)).
  by rewrite perm_rot /It /= perm_cons (iota_addl 1) perm_map.
by rewrite map_rotr /= -map_comp -(@eq_map _ _ (nth x0 t)) // -Ds1 -Ds rotK.
Qed.

End MakeEqSeq.

Implicit Arguments perm_eq_iotaP [[T] [s] [t]].

Section FoldRight.

Variables (T R : Type) (f : T -> R -> R) (z0 : R).

Fixpoint foldr s := if s is x :: s' then f x (foldr s') else z0.

End FoldRight.

Section FoldRightComp.

Variables (T1 T2 : Type) (h : T1 -> T2).
Variables (R : Type) (f : T2 -> R -> R) (z0 : R).

Lemma foldr_cat s1 s2 : foldr f z0 (s1 ++ s2) = foldr f (foldr f z0 s2) s1.
Proof. by elim: s1 => //= x s1 ->. Qed.

Lemma foldr_map s : foldr f z0 (map h s) = foldr (fun x z => f (h x) z) z0 s.
Proof. by elim: s => //= x s ->. Qed.

End FoldRightComp.

(* Quick characterization of the null sequence. *)

Definition sumn := foldr addn 0.

Lemma sumn_nseq x n : sumn (nseq n x) = x * n.
Proof. by rewrite mulnC; elim: n => //= n ->. Qed.

Lemma sumn_cat s1 s2 : sumn (s1 ++ s2) = sumn s1 + sumn s2.
Proof. by elim: s1 => //= x s1 ->; rewrite addnA. Qed.

Lemma natnseq0P s : reflect (s = nseq (size s) 0) (sumn s == 0).
Proof.
apply: (iffP idP) => [|->]; last by rewrite sumn_nseq.
by elim: s => //= x s IHs; rewrite addn_eq0 => /andP[/eqP-> /IHs <-].
Qed.

Section FoldLeft.

Variables (T R : Type) (f : R -> T -> R).

Fixpoint foldl z s := if s is x :: s' then foldl (f z x) s' else z.

Lemma foldl_rev z s : foldl z (rev s) = foldr (fun x z => f z x) z s.
Proof.
elim/last_ind: s z => [|s x IHs] z //=.
by rewrite rev_rcons -cats1 foldr_cat -IHs.
Qed.

Lemma foldl_cat z s1 s2 : foldl z (s1 ++ s2) = foldl (foldl z s1) s2.
Proof.
by rewrite -(revK (s1 ++ s2)) foldl_rev rev_cat foldr_cat -!foldl_rev !revK.
Qed.

End FoldLeft.

Section Scan.

Variables (T1 : Type) (x1 : T1) (T2 : Type) (x2 : T2).
Variables (f : T1 -> T1 -> T2) (g : T1 -> T2 -> T1).

Fixpoint pairmap x s := if s is y :: s' then f x y :: pairmap y s' else [::].

Lemma size_pairmap x s : size (pairmap x s) = size s.
Proof. by elim: s x => //= y s IHs x; rewrite IHs. Qed.

Lemma pairmap_cat x s1 s2 :
  pairmap x (s1 ++ s2) = pairmap x s1 ++ pairmap (last x s1) s2.
Proof. by elim: s1 x => //= y s1 IHs1 x; rewrite IHs1. Qed.

Lemma nth_pairmap s n : n < size s ->
  forall x, nth x2 (pairmap x s) n = f (nth x1 (x :: s) n) (nth x1 s n).
Proof. by elim: s n => [|y s IHs] [|n] //= Hn x; apply: IHs. Qed.

Fixpoint scanl x s :=
  if s is y :: s' then let x' := g x y in x' :: scanl x' s' else [::].

Lemma size_scanl x s : size (scanl x s) = size s.
Proof. by elim: s x => //= y s IHs x; rewrite IHs. Qed.

Lemma scanl_cat x s1 s2 :
  scanl x (s1 ++ s2) = scanl x s1 ++ scanl (foldl g x s1) s2.
Proof. by elim: s1 x => //= y s1 IHs1 x; rewrite IHs1. Qed.

Lemma nth_scanl s n : n < size s ->
  forall x, nth x1 (scanl x s) n = foldl g x (take n.+1 s).
Proof. by elim: s n => [|y s IHs] [|n] Hn x //=; rewrite ?take0 ?IHs. Qed.

Lemma scanlK :
  (forall x, cancel (g x) (f x)) -> forall x, cancel (scanl x) (pairmap x).
Proof. by move=> Hfg x s; elim: s x => //= y s IHs x; rewrite Hfg IHs. Qed.

Lemma pairmapK :
  (forall x, cancel (f x) (g x)) -> forall x, cancel (pairmap x) (scanl x).
Proof. by move=> Hgf x s; elim: s x => //= y s IHs x; rewrite Hgf IHs. Qed.

End Scan.

Prenex Implicits mask map pmap foldr foldl scanl pairmap.

Section Zip.

Variables S T : Type.

Fixpoint zip (s : seq S) (t : seq T) {struct t} :=
  match s, t with
  | x :: s', y :: t' => (x, y) :: zip s' t'
  | _, _ => [::]
  end.

Definition unzip1 := map (@fst S T).
Definition unzip2 := map (@snd S T).

Lemma zip_unzip s : zip (unzip1 s) (unzip2 s) = s.
Proof. by elim: s => [|[x y] s /= ->]. Qed.

Lemma unzip1_zip s t : size s <= size t -> unzip1 (zip s t) = s.
Proof. by elim: s t => [|x s IHs] [|y t] //= le_s_t; rewrite IHs. Qed.

Lemma unzip2_zip s t : size t <= size s -> unzip2 (zip s t) = t.
Proof. by elim: s t => [|x s IHs] [|y t] //= le_t_s; rewrite IHs. Qed.

Lemma size1_zip s t : size s <= size t -> size (zip s t) = size s.
Proof. by elim: s t => [|x s IHs] [|y t] //= Hs; rewrite IHs. Qed.

Lemma size2_zip s t : size t <= size s -> size (zip s t) = size t.
Proof. by elim: s t => [|x s IHs] [|y t] //= Hs; rewrite IHs. Qed.

Lemma size_zip s t : size (zip s t) = minn (size s) (size t).
Proof.
by elim: s t => [|x s IHs] [|t2 t] //=; rewrite IHs -add1n addn_minr.
Qed.

Lemma zip_cat s1 s2 t1 t2 :
  size s1 = size t1 -> zip (s1 ++ s2) (t1 ++ t2) = zip s1 t1 ++ zip s2 t2.
Proof. by move/eqP; elim: s1 t1 => [|x s IHs] [|y t] //= /IHs->. Qed.

Lemma nth_zip x y s t i :
  size s = size t -> nth (x, y) (zip s t) i = (nth x s i, nth y t i).
Proof. by move/eqP; elim: i s t => [|i IHi] [|y1 s1] [|y2 t] //= /IHi->. Qed.

Lemma nth_zip_cond p s t i :
   nth p (zip s t) i
     = (if i < size (zip s t) then (nth p.1 s i, nth p.2 t i) else p).
Proof.
rewrite size_zip ltnNge geq_min.
by elim: s t i => [|x s IHs] [|y t] [|i] //=; rewrite ?orbT -?IHs.
Qed.

Lemma zip_rcons s1 s2 z1 z2 :
    size s1 = size s2 ->
  zip (rcons s1 z1) (rcons s2 z2) = rcons (zip s1 s2) (z1, z2).
Proof. by move=> eq_sz; rewrite -!cats1 zip_cat //= eq_sz. Qed.

Lemma rev_zip s1 s2 :
  size s1 = size s2 -> rev (zip s1 s2) = zip (rev s1) (rev s2).
Proof.
elim: s1 s2 => [|x s1 IHs] [|y s2] //= [eq_sz].
by rewrite !rev_cons zip_rcons ?IHs ?size_rev.
Qed.

End Zip.

Prenex Implicits zip unzip1 unzip2.

Section Flatten.

Variable T : Type.
Implicit Types (s : seq T) (ss : seq (seq T)).

Definition flatten := foldr cat (Nil T).
Definition shape := map (@size T).
Fixpoint reshape sh s :=
  if sh is n :: sh' then take n s :: reshape sh' (drop n s) else [::].

Lemma size_flatten ss : size (flatten ss) = sumn (shape ss).
Proof. by elim: ss => //= s ss <-; rewrite size_cat. Qed.

Lemma flatten_cat ss1 ss2 :
  flatten (ss1 ++ ss2) = flatten ss1 ++ flatten ss2.
Proof. by elim: ss1 => //= s ss1 ->; rewrite catA. Qed.

Lemma flattenK ss : reshape (shape ss) (flatten ss) = ss.
Proof.
by elim: ss => //= s ss IHss; rewrite take_size_cat ?drop_size_cat ?IHss.
Qed.

Lemma reshapeKr sh s : size s <= sumn sh -> flatten (reshape sh s) = s.
Proof.
elim: sh s => [[]|n sh IHsh] //= s sz_s; rewrite IHsh ?cat_take_drop //.
by rewrite size_drop leq_subLR.
Qed.

Lemma reshapeKl sh s : size s >= sumn sh -> shape (reshape sh s) = sh.
Proof.
elim: sh s => [[]|n sh IHsh] //= s sz_s.
rewrite size_takel; last exact: leq_trans (leq_addr _ _) sz_s.
by rewrite IHsh // -(leq_add2l n) size_drop -maxnE leq_max sz_s orbT.
Qed.

End Flatten.

Prenex Implicits flatten shape reshape.

Section EqFlatten.

Variables S T : eqType.

Lemma flattenP (A : seq (seq T)) x :
  reflect (exists2 s, s \in A & x \in s) (x \in flatten A).
Proof.
elim: A => /= [|s A /iffP IH_A]; [by right; case | rewrite mem_cat].
have [s_x|s'x] := @idP (x \in s); first by left; exists s; rewrite ?mem_head.
by apply: IH_A => [[t] | [t /predU1P[->|]]]; exists t; rewrite // mem_behead.
Qed.
Implicit Arguments flattenP [A x].

Lemma flatten_mapP (A : S -> seq T) s y :
  reflect (exists2 x, x \in s & y \in A x) (y \in flatten (map A s)).
Proof.
apply: (iffP flattenP) => [[_ /mapP[x sx ->]] | [x sx]] Axy; first by exists x.
by exists (A x); rewrite ?map_f.
Qed.

End EqFlatten.

Implicit Arguments flattenP [T A x].
Implicit Arguments flatten_mapP [S T A s y].

Section AllPairs.

Variables (S T R : Type) (f : S -> T -> R).
Implicit Types (s : seq S) (t : seq T).

Definition allpairs s t := foldr (fun x => cat (map (f x) t)) [::] s.

Lemma size_allpairs s t : size (allpairs s t) = size s * size t.
Proof. by elim: s => //= x s IHs; rewrite size_cat size_map IHs. Qed.

Lemma allpairs_cat s1 s2 t :
  allpairs (s1 ++ s2) t = allpairs s1 t ++ allpairs s2 t.
Proof. by elim: s1 => //= x s1 ->; rewrite catA. Qed.

End AllPairs.

Prenex Implicits allpairs.

Notation "[ 'seq' E | i <- s , j <- t ]" := (allpairs (fun i j => E) s t)
  (at level 0, E at level 99, i ident, j ident,
   format "[ '[hv' 'seq'  E '/ '  |  i  <-  s , '/   '  j  <-  t ] ']'")
   : seq_scope.
Notation "[ 'seq' E | i : T <- s , j : U <- t ]" :=
  (allpairs (fun (i : T) (j : U) => E) s t)
  (at level 0, E at level 99, i ident, j ident, only parsing) : seq_scope.

Section EqAllPairs.

Variables S T : eqType.
Implicit Types (R : eqType) (s : seq S) (t : seq T).

Lemma allpairsP R (f : S -> T -> R) s t z :
  reflect (exists p, [/\ p.1 \in s, p.2 \in t & z = f p.1 p.2])
          (z \in allpairs f s t).
Proof.
elim: s => [|x s IHs /=]; first by right=> [[p []]].
rewrite mem_cat; have [fxt_z | not_fxt_z] := altP mapP.
  by left; have [y t_y ->] := fxt_z; exists (x, y); rewrite mem_head.
apply: (iffP IHs) => [] [[x' y] /= [s_x' t_y def_z]]; exists (x', y).
  by rewrite !inE predU1r.
by have [def_x' | //] := predU1P s_x'; rewrite def_z def_x' map_f in not_fxt_z.
Qed.

Lemma mem_allpairs R (f : S -> T -> R) s1 t1 s2 t2 :
  s1 =i s2 -> t1 =i t2 -> allpairs f s1 t1 =i allpairs f s2 t2.
Proof.
move=> eq_s eq_t z.
by apply/allpairsP/allpairsP=> [] [p fpz]; exists p; rewrite eq_s eq_t in fpz *.
Qed.

Lemma allpairs_catr R (f : S -> T -> R) s t1 t2 :
  allpairs f s (t1 ++ t2) =i allpairs f s t1 ++ allpairs f s t2.
Proof.
move=> z; rewrite mem_cat.
apply/allpairsP/orP=> [[p [sP1]]|].
  by rewrite mem_cat; case/orP; [left | right]; apply/allpairsP; exists p.
by case=> /allpairsP[p [sp1 sp2 ->]]; exists p; rewrite mem_cat sp2 ?orbT.
Qed.

Lemma allpairs_uniq R (f : S -> T -> R) s t :
    uniq s -> uniq t ->
    {in [seq (x, y) | x <- s, y <- t] &, injective (prod_curry f)} ->
  uniq (allpairs f s t).
Proof.
move=> Us Ut inj_f; have: all (mem s) s by exact/allP.
elim: {-2}s Us => //= x s1 IHs /andP[s1'x Us1] /andP[sx1 ss1].
rewrite cat_uniq {}IHs // andbT map_inj_in_uniq ?Ut // => [|y1 y2 *].
  apply/hasPn=> _ /allpairsP[z [s1z tz ->]]; apply/mapP=> [[y ty Dy]].
  suffices [Dz1 _]: (z.1, z.2) = (x, y) by rewrite -Dz1 s1z in s1'x.
  apply: inj_f => //; apply/allpairsP; last by exists (x, y).
  by have:= allP ss1 _ s1z; exists z.
suffices: (x, y1) = (x, y2) by case.
by apply: inj_f => //; apply/allpairsP; [exists (x, y1) | exists (x, y2)].
Qed.

End EqAllPairs.

