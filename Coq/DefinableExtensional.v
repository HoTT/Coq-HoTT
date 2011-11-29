(** Peter Aczel suggested that we include a meta-theorem which states that
   predicates on functions obey a substitution principle with respect to
   extensional equality, as long as they are built from "standard" constructors.
*)

Require Import Paths Fibrations Contractible Funext Equivalences.

(** Let us first observe the following easy fact. If [P] is a fibration and [x ~~> y]
    then [P x] and [P y] are connected by a path (and so also equivalent). *)

Lemma path_fibers {A} {P : A -> Type} {x y : A} : x ~~> y -> P x ~~> P y.
Proof.
  path_induction.
Defined.

(** Let us call a fibration [P : (A -> B) -> Type] _extensional_ if it takes
   extensionally equal maps to equivalent fibers. *)

Definition extensional {A B} (P : (A -> B) -> Type) :=
  forall f g : A -> B, f == g -> P f ~=> P g.

(** If we assume the Univalence Axiom then [equiv_fibers] implies that every
   fibration on a function space is extensional. But even without UA we can
   show that fibrations built from basic operations are extensional. *)

(* This should go to Paths.v. *)
Definition path_pair {A B} {x y : A * B} : (fst x ~~> fst y) -> (snd x ~~> snd y) -> x ~~> y.  
Proof.
  intros p q.
  destruct x, y.
  simpl in * |- *.
  path_induction.
Defined.

Definition path_fst {A B} {a b : A} {c d : B} : (a,c) ~~> (b,d) -> a ~~> b.
Proof.
  intros pq.
  exact (map (@fst A B) pq).
Qed.

Definition path_snd {A B} {a b : A} {c d : B} : (a,c) ~~> (b,d) -> c ~~> d.
Proof.
  intros pq.
  exact (map (@snd A B) pq).
Qed.

(* This should go to Fibrations.v. *)
Lemma path_in_total {A} {P : A -> Type} : forall (u v : total P),
  { p : pr1 u ~~> pr1 v & transport p (pr2 u) ~~> (pr2 v) } -> u ~~> v.
Proof.
  intros [x u] [y v] [p q].
  simpl in * |- *.
  induction p.
  simpl in q.
  induction q.
  apply idpath.
Defined.

Lemma equiv_prod {A B} {C D} : forall (f : A ~=> B) (g : C ~=> D), A * C ~=> B * D.
Proof.
  intros f g.
  exists (fun u => (f (fst u), g (snd u))).
  apply @hequiv_is_equiv with (g := fun v => (inv f (fst v), inv g (snd v))).
  intros (b,d).
  simpl.
  apply path_pair; apply inverse_is_section.
  intros [a c]; simpl.
  apply path_pair; apply inverse_is_retraction.
Defined.

Lemma equiv_sum {A B} {C D} : forall (f : A ~=> B) (g : C ~=> D), A + C ~=> B + D.
Proof.
  intros f g.
  exists (fun u => match u with
                     | inl a => inl D (f a)
                     | inr c => inr B (g c)
                   end).
  apply @hequiv_is_equiv with (g := fun v => match v with
                                               | inl b => inl C (inv f b)
                                               | inr d => inr A (inv g d)
                                             end).
  intros [? | ?]; apply map; apply inverse_is_section.
  intros [? | ?]; apply map; apply inverse_is_retraction.
Defined.

Lemma ext_prod {A B P Q}:
  extensional P -> extensional Q -> extensional (fun (h : A -> B) => prod (P h) (Q h)).
Proof.
  intros EP EQ f g E.
  exists (fun u => (EP f g E (fst u), EQ f g E (snd u))).
  apply @hequiv_is_equiv with
    (g := fun v => (inv (EP f g E) (fst v), inv (EQ f g E) (snd v))).
  intros; apply path_pair; apply inverse_is_section.
  intros; apply path_pair; apply inverse_is_retraction.
Qed.

Lemma ext_sum {A B P Q} :
  extensional P -> extensional Q -> extensional (fun (h : A -> B) => P h + Q h)%type.
Proof.
  intros EP EQ f g E.
  exists (fun u => match u with
                     | inl a => inl _ (EP f g E a)
                     | inr b => inr _ (EQ f g E b)
                   end).
  apply @hequiv_is_equiv with
    (g := fun v => match v with
                     | inl a => inl _ (inv (EP f g E) a)
                     | inr b => inr _ (inv (EQ f g E) b)
                   end).
  intros [? | ?]; apply map; apply inverse_is_section.
  intros [? | ?]; apply map; apply inverse_is_retraction.
Qed.

(* Without extensionality these won't work, it seems. *)

Lemma ext_forall A B C (P : (A -> B) -> C -> Type) :
  (forall z : C, extensional (fun h => P h z)) -> extensional (fun h => forall z, P h z).
Proof.
  intros EC f g E.
  exists (fun h z => EC z f g E (h z)).
  apply @hequiv_is_equiv with
    (g := fun h z => inv (EC z f g E) (h z)).
  intro h.
  set (r := fun z h => (EC z f g E) (inv (EC z f g E) (h z))).
  simpl in r.
Admitted.

Lemma ext_imp {A B P Q} :
  extensional P -> extensional Q -> extensional (fun (h : A -> B) => P h -> Q h)%type.
Proof.
  intros EP EQ f g E.
  exists (fun h x => EQ f g E (h (inv (EP f g E) x))).
  apply @hequiv_is_equiv with
    (g := fun h y => inv (EQ f g E) (h (EP f g E y))).
  intro h.
Admitted.

Lemma ext_sig A B C (P : (A -> B) -> C -> Type) :
  (forall z : C, extensional (fun h => P h z)) -> extensional (fun h => sigT (P h)).
Proof.
  intros EC f g E.
  exists (fun t => tpair (pr1 t) (EC (pr1 t) f g E (pr2 t))).
  apply @hequiv_is_equiv with
    (g := fun t => tpair (pr1 t) (inv (EC (pr1 t) f g E) (pr2 t))).
  intros [c u].
  apply total_path with (p := idpath c).
  apply inverse_is_section.
  intros [c u].
  apply total_path with (p := idpath c).
  apply inverse_is_retraction.
Defined.

Lemma ext_sig_dep A B (C : (A -> B) -> Type) (P : forall h, C h -> Type)  :
  { c : extensional C & (forall f g (E : f == g) u v,  (c f g E u ~~> v) -> P f u ~=> P g v) } ->
  extensional (fun h => sigT (P h)).
Proof.
  intros [EC EP] f g E.
  exists (fun t =>
    let z := pr1 t in
    let u := pr2 t in
      tpair (EC f g E z) (EP f g E z (EC f g E z) (idpath _) u)).
  apply @hequiv_is_equiv with
    (g := fun s =>
      let z := pr1 s in
        let v := pr2 s in
          tpair (inv (EC f g E) z) (inv (EP f g E (inv (EC f g E) z) z (inverse_is_section _ z)) v)).
  intros [c u].
  simpl in * |- *.
  set (ec := EC f g E).
  set (ep := EP f g E).
  apply total_path with (p := inverse_is_section ec c).
  simpl.

Defined.

Ltac auto_ext :=
  match goal with
    | [ |- extensional (fun _ => prod _ _) ] => apply ext_prod; auto_ext
    | [ |- extensional (fun _ => sum _ _) ] => apply ext_sum; auto_ext
    | [ |- extensional (fun _ => (_ -> _))] => apply ext_imp; auto_ext
    | [ |- extensional (fun _ => forall c : _, _) ] => apply ext_forall; auto_ext
    | [ |- extensional (fun _ => sigT _)] => apply ext_sig; auto_ext
    | [ |- forall x : ?A, extensional _ ] => intros; auto_ext
    | _ => auto
  end.

Lemma extensional_hfiber A B (y : B) : extensional (fun h : A -> B => hfiber h y).
Proof.
  intros A B y.
  unfold hfiber.
  auto_ext.
  intros f g E p.
  path_via (f z).
Defined.

(** This goes to the main library. *)
Lemma contractible_retract A B (s : A -> B) (r : B -> A) :
  (r o s == idmap A) -> is_contr B -> is_contr A.
Proof.
  intros A B s r E [b p].
  split with (r b).
  intro a.
  path_via (r (s a)).
  apply opposite.
  apply E.
Qed.

Lemma extensional_is_equiv A B : extensional (@is_equiv A B).
Proof.
  intros A B.
  unfold is_equiv.
  auto_ext.
  unfold is_contr.
  apply ext_sig_dep.
  assert (c : extensional (fun h : A -> B => hfiber h z)).
  apply extensional_hfiber.
  split with c.
  intros f g E u v p q y.
  unfold extensional in c.
  Check (c f g E).




