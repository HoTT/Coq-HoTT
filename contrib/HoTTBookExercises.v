(** The HoTT Book Exercises formalization. *)

(** This file records formalized solutions to the HoTT Book exercises.
    See HoTTBook.v for an IMPORTANT NOTE FOR THE HoTT DEVELOPERS. *)

(*  PROCEDURE FOR UPDATING THE FILE:

   1. Compile the latest version of the HoTT Book to update the LaTeX
      labels. Do not forget to pull in changes from HoTT/HoTT.

   2. Run `etc/Book.py` using the `--exercises` flag (so your command
      should look like `cat ../book/\*.aux | etc/Book.py --exercises contrib/HoTTBookExercises.v`)
      If it complains, fix things.

   3. Add contents to new entries.

   4. Run `etc/Book.py` again to make sure it is happy.

   5. Compile this file with `make contrib` or `make contrib/HoTTBookExercises.vo`.

   6. Do the git thing to submit your changes.

*)

Require Import HoTT.

(* END OF PREAMBLE *)
(* ================================================== ex:composition *)
(** Exercise 1.1 *)

Definition Book_1_1 := @compose.

(* ================================================== ex:pr-to-rec *)
(** Exercise 1.2 *)



(* ================================================== ex:pr-to-ind *)
(** Exercise 1.3 *)



(* ================================================== ex:iterator *)
(** Exercise 1.4 *)



(* ================================================== ex:sum-via-bool *)
(** Exercise 1.5 *)



(* ================================================== ex:prod-via-bool *)
(** Exercise 1.6 *)



(* ================================================== ex:pm-to-ml *)
(** Exercise 1.7 *)



(* ================================================== ex:nat-semiring *)
(** Exercise 1.8 *)



(* ================================================== ex:fin *)
(** Exercise 1.9 *)



(* ================================================== ex:ackermann *)
(** Exercise 1.10 *)

Fixpoint ack (n m : nat) : nat :=
  match n with
  | O => S m
  | S p => let fix ackn (m : nat) :=
               match m with
                 | O => ack p 1
                 | S q => ack p (ackn q)
               end
           in ackn m
  end.

Definition Book_1_10 := ack.

(* ================================================== ex:neg-ldn *)
(** Exercise 1.11 *)



(* ================================================== ex:tautologies *)
(** Exercise 1.12 *)



(* ================================================== ex:not-not-lem *)
(** Exercise 1.13 *)



(* ================================================== ex:without-K *)
(** Exercise 1.14 *)



(* ================================================== ex:subtFromPathInd *)
(** Exercise 1.15 *)

(* concat_A1p? *)

(* ================================================== ex:basics:concat *)
(** Exercise 2.1 *)



(* ================================================== ex:npaths *)
(** Exercise 2.4 *)



(* ================================================== ex:equiv-concat *)
(** Exercise 2.6 *)



(* ================================================== ex:ap-sigma *)
(** Exercise 2.7 *)



(* ================================================== ex:coprod-ump *)
(** Exercise 2.9 *)



(* ================================================== ex:sigma-assoc *)
(** Exercise 2.10 *)



(* ================================================== ex:pullback *)
(** Exercise 2.11 *)



(* ================================================== ex:pullback-pasting *)
(** Exercise 2.12 *)



(* ================================================== ex:eqvboolbool *)
(** Exercise 2.13 *)



(* ================================================== ex:equality-reflection *)
(** Exercise 2.14 *)



(* ================================================== ex:strong-from-weak-funext *)
(** Exercise 2.16 *)



(* ================================================== ex:isset-coprod *)
(** Exercise 3.2 *)



(* ================================================== ex:isset-sigma *)
(** Exercise 3.3 *)



(* ================================================== ex:prop-endocontr *)
(** Exercise 3.4 *)



(* ================================================== ex:prop-inhabcontr *)
(** Exercise 3.5 *)



(* ================================================== ex:lem-mereprop *)
(** Exercise 3.6 *)



(* ================================================== ex:disjoint-or *)
(** Exercise 3.7 *)



(* ================================================== ex:brck-qinv *)
(** Exercise 3.8 *)



(* ================================================== ex:lem-impred *)
(** Exercise 3.10 *)



(* ================================================== ex:lem-brck *)
(** Exercise 3.14 *)



(* ================================================== ex:impred-brck *)
(** Exercise 3.15 *)



(* ================================================== ex:prop-trunc-ind *)
(** Exercise 3.17 *)



(* ================================================== ex:lem-ldn *)
(** Exercise 3.18 *)



(* ================================================== ex:decidable-choice *)
(** Exercise 3.19 *)



(* ================================================== ex:omit-contr2 *)
(** Exercise 3.20 *)



(* ================================================== ex:symmetric-equiv *)
(** Exercise 4.2 *)



(* ================================================== ex:qinv-autohtpy-no-univalence *)
(** Exercise 4.3 *)



(* ================================================== ex:unstable-octahedron *)
(** Exercise 4.4 *)



(* ================================================== ex:2-out-of-6 *)
(** Exercise 4.5 *)



(* ================================================== ex:qinv-univalence *)
(** Exercise 4.6 *)



(* ================================================== ex:same-recurrence-not-defeq *)
(** Exercise 5.2 *)



(* ================================================== ex:one-function-two-recurrences *)
(** Exercise 5.3 *)



(* ================================================== ex:bool *)
(** Exercise 5.4 *)



(* ================================================== ex:loop *)
(** Exercise 5.7 *)



(* ================================================== ex:loop2 *)
(** Exercise 5.8 *)



(* ================================================== ex:torus *)
(** Exercise 6.1 *)



(* ================================================== ex:suspS1 *)
(** Exercise 6.2 *)



(* ================================================== ex:torus-s1-times-s1 *)
(** Exercise 6.3 *)



(* ================================================== ex:nspheres *)
(** Exercise 6.4 *)



(* ================================================== ex:free-monoid *)
(** Exercise 6.8 *)



(* ================================================== ex:unnatural-endomorphisms *)
(** Exercise 6.9 *)



(* ================================================== ex:funext-from-interval *)
(** Exercise 6.10 *)



(* ================================================== ex:susp-lump *)
(** Exercise 6.11 *)



(* ================================================== ex:s2-colim-unit *)
(** Exercise 7.2 *)



(* ================================================== ex:ntypes-closed-under-wtypes *)
(** Exercise 7.3 *)



(* ================================================== ex:ntype-from-nconn-const *)
(** Exercise 7.5 *)



(* ================================================== ex:connectivity-inductively *)
(** Exercise 7.6 *)



(* ================================================== ex:lemnm *)
(** Exercise 7.7 *)



(* ================================================== ex:acnm *)
(** Exercise 7.8 *)



(* ================================================== ex:acnm-surjset *)
(** Exercise 7.9 *)



(* ================================================== ex:acconn *)
(** Exercise 7.10 *)



(* ================================================== ex:trunc-spokes-no-hub *)
(** Exercise 7.15 *)



(* ================================================== ex:unique-fiber *)
(** Exercise 8.5 *)



(* ================================================== ex:ap-path-inversion *)
(** Exercise 8.6 *)



(* ================================================== ex:pointed-equivalences *)
(** Exercise 8.7 *)



(* ================================================== ex:HopfJr *)
(** Exercise 8.8 *)



(* ================================================== ex:SuperHopf *)
(** Exercise 8.9 *)



(* ================================================== ex:vksusppt *)
(** Exercise 8.10 *)



(* ================================================== ex:vksuspnopt *)
(** Exercise 8.11 *)



(* ================================================== ct:pre2cat *)
(** Exercise 9.4 *)



(* ================================================== ct:2cat *)
(** Exercise 9.5 *)



(* ================================================== ct:groupoids *)
(** Exercise 9.6 *)



(* ================================================== ct:ex:hocat *)
(** Exercise 9.9 *)



(* ================================================== ex:rezk-vankampen *)
(** Exercise 9.11 *)



(* ================================================== ex:stack *)
(** Exercise 9.12 *)



(* ================================================== ex:well-pointed *)
(** Exercise 10.3 *)



(* ================================================== ex:prop-ord *)
(** Exercise 10.7 *)



(* ================================================== ex:ninf-ord *)
(** Exercise 10.8 *)



(* ================================================== ex:choice-function *)
(** Exercise 10.10 *)



(* ================================================== ex:cumhierhit *)
(** Exercise 10.11 *)



(* ================================================== ex:RD-extended-reals *)
(** Exercise 11.2 *)



(* ================================================== ex:RD-lower-cuts *)
(** Exercise 11.3 *)



(* ================================================== ex:RD-interval-arithmetic *)
(** Exercise 11.4 *)



(* ================================================== ex:RD-lt-vs-le *)
(** Exercise 11.5 *)



(* ================================================== ex:reals-non-constant-into-Z *)
(** Exercise 11.6 *)



(* ================================================== ex:traditional-archimedean *)
(** Exercise 11.7 *)



(* ================================================== RC-Lipschitz-on-interval *)
(** Exercise 11.8 *)



(* ================================================== ex:metric-completion *)
(** Exercise 11.9 *)



(* ================================================== ex:reals-apart-neq-MP *)
(** Exercise 11.10 *)



(* ================================================== ex:reals-apart-zero-divisors *)
(** Exercise 11.11 *)



(* ================================================== ex:finite-cover-lebesgue-number *)
(** Exercise 11.12 *)



(* ================================================== ex:mean-value-theorem *)
(** Exercise 11.13 *)



