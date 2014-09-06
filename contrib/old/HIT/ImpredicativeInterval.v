Add LoadPath "..".
Require Import Paths Fibrations Funext UnivalenceAxiom.

(* By using impredicative set and functional extensionality, we can
   *define* a higher inductive type and prove its non-dependent
   computation rule.  Here we do the interval. *)

Definition interval : Set := forall (X : Set) (a b : X) (p : a == b), X.

Definition zero : interval := fun X a b p => a.

Definition one : interval := fun X a b p => b.

Definition segment : zero == one.
Proof.
  apply funext_dep with (f := zero) (g := one); intro X.
  apply funext_dep; intro a.
  apply funext_dep; intro b.
  apply funext_dep; intro p.
  unfold zero, one; exact p.
Defined.

Definition interval_rec : forall (X : Set) (a b : X) (p : a == b), interval -> X :=
  fun X a b p i => i X a b p.

(* It's sort of stupid to use this interval to prove functional
   extensionality, since we already had to assume funext in order to
   define [segment], but it shows that the computation rules really do
   hold definitionally. *)

Definition funext_dep_statement_inSet :=
  forall (X : Set) (P : X -> Set) (f g : forall x : X, P x),
    (forall x : X, f x == g x) -> f == g.

Theorem interval_implies_funext_dep : funext_dep_statement_inSet.
Proof.
  intros X P f g p.
  set (mate := fun (i:interval) x => interval_rec _ _ _ (p x) i).
  path_via (mate zero).
  apply opposite.
  path_via (fun x => f x).
  apply funext_dep; auto.
  path_via (mate one).
  exact segment.
  path_via (fun x => g x).
  apply funext_dep; auto.
Defined.

Definition interval_compute_segment :
  forall (X : Set) (a b : X) (p : a == b),
    map (interval_rec X a b p) segment == p.
Proof.
  intros X a b p.
  unfold interval_rec.
  (* First we change this map into a bunch of [happly_dep]s. *)
  path_via (map ((fun z => z p) ○ (fun z => z b) ○ (fun z => z a) ○ (fun i => i X)) segment).
  do_compose_map.
  change (happly_dep (happly_dep (happly_dep (happly_dep segment X) a) b) p == p).
  unfold segment.
  (* Now each [happly_dep] matches up exactly with one occurrence of
     [funext_dep] in [segment].  Thus we just have to kill them off one
     by one from the inside out. *)
  repeat match goal with | |- ?s == ?t =>
    match s with
      | context cxt [ happly_dep (funext_dep ?P' _ _ ?p') ?x' ] =>
        let mid := context cxt [ p' x' ] in
          apply @concat with (y := mid);
            [ repeat (apply_happly; apply map);
              apply funext_dep_compute with (P := P') (x := x')
              | ]
    end
  end.
  auto.
Defined.

(*
Local Variables:
coq-prog-args: ("-emacs" "-impredicative-set")
End:
*)
