(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the universe, including the Univalence Axiom. *)

Require Import HoTT.Basics.
Require Import Types.Sigma Types.Forall Types.Arrow Types.Paths Types.Equiv Types.Bool Types.Prod.

Local Open Scope path_scope.

Generalizable Variables A B f.

(** ** Paths *)

Global Instance isequiv_path {A B : Type} (p : A = B)
  : IsEquiv (transport (fun X:Type => X) p) | 0
  := BuildIsEquiv _ _ _ (transport (fun X:Type => X) p^)
  (transport_pV idmap p)
  (transport_Vp idmap p)
  (fun a => match p in _ = C return
              (transport_pp idmap p^ p (transport idmap p a))^ @
                 transport2 idmap (concat_Vp p) (transport idmap p a) =
              ap (transport idmap p) ((transport_pp idmap p p^ a) ^ @
                transport2 idmap (concat_pV p) a) with idpath => 1 end).

Definition equiv_path (A B : Type) (p : A = B) : A <~> B
  := BuildEquiv _ _ (transport (fun X:Type => X) p) _.

Definition equiv_path_V `{Funext} (A B : Type) (p : A = B) :
  equiv_path B A (p^) = (equiv_path A B p)^-1%equiv.
Proof.
  destruct p. simpl. unfold equiv_path, equiv_inverse. simpl. apply ap.
  refine (@path_ishprop _ (hprop_isequiv _) _ _).
Defined.

(** See the note by [Funext] in Overture.v *)
Monomorphic Axiom Univalence : Type0.
Existing Class Univalence.
Axiom isequiv_equiv_path : forall `{Univalence} (A B : Type), IsEquiv (equiv_path A B).
Global Existing Instance isequiv_equiv_path.

Section Univalence.
Context `{Univalence}.

Definition path_universe_uncurried {A B : Type} (f : A <~> B) : A = B
  := (equiv_path A B)^-1 f.

Definition path_universe {A B : Type} (f : A -> B) {feq : IsEquiv f} : (A = B)
  := path_universe_uncurried (BuildEquiv _ _ f feq).

Global Arguments path_universe {A B}%type_scope f%function_scope {feq}.

Definition eta_path_universe {A B : Type} (p : A = B)
  : path_universe (equiv_path A B p) = p
  := eissect (equiv_path A B) p.

Definition eta_path_universe_uncurried {A B : Type} (p : A = B)
  : path_universe_uncurried (equiv_path A B p) = p
  := eissect (equiv_path A B) p.

Definition isequiv_path_universe {A B : Type}
  : IsEquiv (@path_universe_uncurried A B)
 := _.

Definition equiv_path_universe (A B : Type) : (A <~> B) <~> (A = B)
  := BuildEquiv _ _ (@path_universe_uncurried A B) isequiv_path_universe.


Definition equiv_equiv_path  (A B : Type) : (A = B) <~> (A <~> B)
  := (equiv_path_universe A B)^-1%equiv.

(** These operations have too many names, making [rewrite] a pain.  So we give lots of names to the computation laws. *)
Definition path_universe_equiv_path {A B : Type} (p : A = B)
  : path_universe (equiv_path A B p) = p
  := eissect (equiv_path A B) p.
Definition path_universe_uncurried_equiv_path {A B : Type} (p : A = B)
  : path_universe_uncurried (equiv_path A B p) = p
  := eissect (equiv_path A B) p.
Definition path_universe_transport_idmap {A B : Type} (p : A = B)
  : path_universe (transport idmap p) = p
  := eissect (equiv_path A B) p.
Definition path_universe_uncurried_transport_idmap {A B : Type} (p : A = B)
  : path_universe_uncurried (equiv_transport idmap A B p) = p
  := eissect (equiv_path A B) p.
Definition equiv_path_path_universe {A B : Type} (f : A <~> B)
  : equiv_path A B (path_universe f) = f
  := eisretr (equiv_path A B) f.
Definition equiv_path_path_universe_uncurried {A B : Type} (f : A <~> B)
  : equiv_path A B (path_universe_uncurried f) = f
  := eisretr (equiv_path A B) f.
Definition transport_idmap_path_universe {A B : Type} (f : A <~> B)
  : transport idmap (path_universe f) = f
  := ap equiv_fun (eisretr (equiv_path A B) f).
Definition transport_idmap_path_universe_uncurried {A B : Type} (f : A <~> B)
  : transport idmap (path_universe_uncurried f) = f
  := ap equiv_fun (eisretr (equiv_path A B) f).

(** ** Behavior on path operations *)

Definition equiv_path_pp `{Funext} {A B C : Type} (p : A = B) (q : B = C)
: equiv_path A C (p @ q) = equiv_path B C q oE equiv_path A B p.
Proof.
  destruct p, q. simpl.
  apply path_equiv, path_arrow.
  intros x; reflexivity.
Defined.

Definition path_universe_compose_uncurried `{Funext} {A B C : Type}
           (f : A <~> B) (g : B <~> C)
: path_universe_uncurried (equiv_compose g f)
= path_universe_uncurried f @ path_universe_uncurried g.
Proof.
  revert f. equiv_intro (equiv_path A B) f.
  revert g. equiv_intro (equiv_path B C) g.
  refine ((ap path_universe_uncurried (equiv_path_pp f g))^ @ _).
  refine (eta_path_universe (f @ g) @ _).
  apply concat2; symmetry; apply eta_path_universe.
Defined.

Definition path_universe_compose `{Funext} {A B C : Type}
           (f : A <~> B) (g : B <~> C)
: path_universe (g o f) = path_universe f @ path_universe g.
Proof.
  revert f. equiv_intro (equiv_path A B) f.
  revert g. equiv_intro (equiv_path B C) g.
  refine ((ap path_universe_uncurried (equiv_path_pp f g))^ @ _).
  refine (eta_path_universe (f @ g) @ _).
  apply concat2; symmetry; apply eta_path_universe.
Defined.

Definition path_universe_1 {A : Type}
: path_universe (equiv_idmap A) = 1
  := eta_path_universe 1.

Definition path_universe_V_uncurried `{Funext} {A B : Type} (f : A <~> B)
  : path_universe_uncurried f^-1 = (path_universe_uncurried f)^.
Proof.
  revert f. equiv_intro ((equiv_path_universe A B)^-1) p. simpl.
  transitivity (p^).
    2: exact (inverse2 (eisretr (equiv_path_universe A B) p)^).
  transitivity (path_universe_uncurried (equiv_path B A p^)).
    by refine (ap _ (equiv_path_V A B p)^).
  by refine (eissect (equiv_path B A) p^).
Defined.

Definition path_universe_V `{Funext} `(f : A -> B) `{IsEquiv A B f}
  : path_universe (f^-1) = (path_universe f)^
  := path_universe_V_uncurried (BuildEquiv A B f _).

(** ** Path operations vs Type operations *)

(** [ap (Equiv A)] behaves like postcomposition. *)
Definition ap_equiv_path_universe `{Funext} A {B C} (f : B <~> C)
: equiv_path (A <~> B) (A <~> C) (ap (Equiv A) (path_universe f))
  = equiv_functor_equiv (equiv_idmap A) f.
Proof.
  revert f. equiv_intro (equiv_path B C) f.
  rewrite (eissect (equiv_path B C) f : path_universe (equiv_path B C f) = f).
  destruct f; simpl.
  apply path_equiv, path_forall; intros g.
  apply path_equiv, path_forall; intros a.
  reflexivity.
Defined.

(** [ap (prod A)] behaves like [equiv_functor_prod_l]. *)
Definition ap_prod_l_path_universe `{Funext} A {B C} (f : B <~> C)
  : equiv_path (A * B) (A * C) (ap (prod A) (path_universe f))
    = equiv_functor_prod_l f.
Proof.
  revert f. equiv_intro (equiv_path B C) f.
  rewrite (eissect (equiv_path B C) f : path_universe (equiv_path B C f) = f).
  destruct f.
  apply path_equiv, path_arrow; intros x; reflexivity.
Defined.

(** [ap (fun Z => Z * A)] behaves like [equiv_functor_prod_r]. *)
Definition ap_prod_r_path_universe `{Funext} A {B C} (f : B <~> C)
  : equiv_path (B * A) (C * A) (ap (fun Z => Z * A) (path_universe f))
    = equiv_functor_prod_r f.
Proof.
  revert f. equiv_intro (equiv_path B C) f.
  rewrite (eissect (equiv_path B C) f : path_universe (equiv_path B C f) = f).
  destruct f.
  apply path_equiv, path_arrow; intros x; reflexivity.
Defined.

(** ** Transport *)

(** There are two ways we could define [transport_path_universe]: we could give an explicit definition, or we could reduce it to paths by [equiv_ind] and give an explicit definition there.  The two should be equivalent, but we choose the second for now as it makes the currently needed coherence lemmas easier to prove. *)
Definition transport_path_universe_uncurried
           {A B : Type} (f : A <~> B) (z : A)
  : transport (fun X:Type => X) (path_universe_uncurried f) z = f z.
Proof.
  revert f.  equiv_intro (equiv_path A B) p.
  exact (ap (fun s => transport idmap s z) (eissect _ p)).
Defined.

Definition transport_path_universe
           {A B : Type} (f : A -> B) {feq : IsEquiv f} (z : A)
  : transport (fun X:Type => X) (path_universe f) z = f z
  := transport_path_universe_uncurried (BuildEquiv A B f feq) z.
(* Alternatively, [ap10_equiv (eisretr (equiv_path A B) (BuildEquiv _ _ f feq)) z]. *)

Definition transport_path_universe_equiv_path
           {A B : Type} (p : A = B) (z : A)
  : transport_path_universe (equiv_path A B p) z =
    (ap (fun s => transport idmap s z) (eissect _ p))
  := equiv_ind_comp _ _ _.

(* This somewhat fancier version is useful when working with HITs. *)
Definition transport_path_universe'
  {A : Type} (P : A -> Type) {x y : A} (p : x = y)
  (f : P x <~> P y) (q : ap P p = path_universe f) (u : P x)
  : transport P p u = f u
  := transport_compose idmap P p u
   @ ap10 (ap (transport idmap) q) u
   @ transport_path_universe f u.

(** And a version for transporting backwards. *)

Definition transport_path_universe_V_uncurried `{Funext}
           {A B : Type} (f : A <~> B) (z : B)
  : transport (fun X:Type => X) (path_universe_uncurried f)^ z = f^-1 z.
Proof.
  revert f. equiv_intro (equiv_path A B) p.
  exact (ap (fun s => transport idmap s z) (inverse2 (eissect _ p))).
Defined.

Definition transport_path_universe_V `{Funext}
           {A B : Type} (f : A -> B) {feq : IsEquiv f} (z : B)
  : transport (fun X:Type => X) (path_universe f)^ z = f^-1 z
  := transport_path_universe_V_uncurried (BuildEquiv _ _ f feq) z.
(* Alternatively, [(transport2 idmap (path_universe_V f) z)^ @ (transport_path_universe (f^-1) z)]. *)

Definition transport_path_universe_V_equiv_path `{Funext}
           {A B : Type} (p : A = B) (z : B)
  : transport_path_universe_V (equiv_path A B p) z =
    ap (fun s => transport idmap s z) (inverse2 (eissect _ p))
  := equiv_ind_comp _ _ _.

(** And some coherence for it. *)

Definition transport_path_universe_Vp_uncurried `{Funext}
           {A B : Type} (f : A <~> B) (z : A)
: ap (transport idmap (path_universe f)^) (transport_path_universe f z)
  @ transport_path_universe_V f (f z)
  @ eissect f z
  = transport_Vp idmap (path_universe f) z.
Proof.
  pattern f.
  refine (equiv_ind (equiv_path A B) _ _ _); intros p.
  (* Something slightly sneaky happens here: by definition of [equiv_path], [eissect (equiv_path A B p)] is judgmentally equal to [transport_Vp idmap p].  Thus, we can apply [ap_transport_Vp_idmap]. *)
  refine (_ @ ap_transport_Vp_idmap p (path_universe (equiv_path A B p))
            (eissect (equiv_path A B) p) z).
  apply whiskerR. apply concat2.
  - apply ap. apply transport_path_universe_equiv_path.
  - apply transport_path_universe_V_equiv_path.
Defined.

Definition transport_path_universe_Vp `{Funext}
           {A B : Type} (f : A -> B) {feq : IsEquiv f} (z : A)
: ap (transport idmap (path_universe f)^) (transport_path_universe f z)
  @ transport_path_universe_V f (f z)
  @ eissect f z
  = transport_Vp idmap (path_universe f) z
:= transport_path_universe_Vp_uncurried (BuildEquiv A B f feq) z.

(** ** 2-paths *)

Definition equiv_path2_universe `{Funext}
           {A B : Type} (f g : A <~> B)
: (f == g) <~> (path_universe f = path_universe g).
Proof.
  refine (_ oE equiv_path_arrow f g).
  refine (_ oE equiv_path_equiv f g).
  exact (equiv_ap (equiv_path A B)^-1 _ _).
Defined.

Definition path2_universe `{Funext}
           {A B : Type} {f g : A <~> B}
: (f == g) -> (path_universe f = path_universe g)
  := equiv_path2_universe f g.

Definition equiv_path2_universe_1 `{Funext}
           {A B : Type} (f : A <~> B)
: equiv_path2_universe f f (fun x => 1) = 1.
Proof.
  simpl.
  rewrite concat_1p, concat_p1, path_forall_1, path_sigma_hprop_1.
  reflexivity.
Qed.

Definition path2_universe_1 `{Funext}
           {A B : Type} (f : A <~> B)
: @path2_universe _ _ _ f f (fun x => 1) = 1
  := equiv_path2_universe_1 f.

(** There ought to be a lemma which says something like this:

<<
Definition path2_universe_postcompose `{Funext}
           {A B C : Type} {f1 f2 : A <~> B} (p : f1 == f2)
           (g : B <~> C)
: equiv_path2_universe (g o f1)
                       (g o f2)
                       (fun a => ap g (p a))
  = path_universe_compose f1 g
    @ whiskerR (path2_universe p) (path_universe g)
    @ (path_universe_compose f2 g)^.
>>

and similarly

<<
Definition path2_universe_precompose `{Funext}
           {A B C : Type} {f1 f2 : B <~> C} (p : f1 == f2)
           (g : A <~> B)
: equiv_path2_universe (f1 o g)
                       (f2 o g)
                       (fun a => (p (g a)))
  = path_universe_compose g f1
    @ whiskerL (path_universe g) (path2_universe p)
    @ (path_universe_compose g f2)^.
>>

but I haven't managed to prove them yet.  Fortunately, for existing applications what we actually need is the following rather different-looking version that applies only when [f1] and [f2] are identities. *)

(** Coq is too eager about unfolding [equiv_path_equiv] in the following proofs, so we tell it not to.  We go into a section in order to limit the scope of the [simpl never] command. *)
Section PathEquivSimplNever.
  Local Arguments equiv_path_equiv : simpl never.

  Definition path2_universe_postcompose_idmap `{Funext}
             {A C : Type} (p : forall a:A, a = a)
             (g : A <~> C)
  : equiv_path2_universe g g (fun a => ap g (p a))
    = (concat_1p _)^
      @ whiskerR (path_universe_1)^ (path_universe g)
      @ whiskerR (equiv_path2_universe (equiv_idmap A) (equiv_idmap A) p)
        (path_universe g)
      @ whiskerR path_universe_1 (path_universe g)
      @ concat_1p _.
  Proof.
    transitivity ((eta_path_universe (path_universe g))^
                  @ equiv_path2_universe
                    (equiv_path A C (path_universe g))
                    (equiv_path A C (path_universe g))
                    (fun a => ap (equiv_path A C (path_universe g)) (p a))
                    @ eta_path_universe (path_universe g)).
    - refine ((apD (fun g' => equiv_path2_universe g' g'
                                (fun a => ap g' (p a)))
                   (eisretr (equiv_path A C) g))^ @ _).
      refine (transport_paths_FlFr (eisretr (equiv_path A C) g) _ @ _).
      apply concat2.
      + apply whiskerR.
        apply inverse2, symmetry.
        refine (eisadj (equiv_path A C)^-1 g).
      + symmetry; refine (eisadj (equiv_path A C)^-1 g).
    - generalize (path_universe g).
      intros h. destruct h. cbn.
      rewrite !concat_1p, !concat_p1.
      refine (_ @ whiskerR (whiskerR_pp 1 path_universe_1^ _) _).
      refine (_ @ whiskerR_pp 1 _ path_universe_1).
      refine (_ @ (whiskerR_p1_1 _)^).
      apply whiskerR, whiskerL, ap, ap, ap.
      apply path_forall; intros x; apply ap_idmap.
  Defined.

  Definition path2_universe_precompose_idmap `{Funext}
             {A B : Type} (p : forall b:B, b = b)
             (g : A <~> B)
  : equiv_path2_universe g g (fun a => (p (g a)))
    = (concat_p1 _)^
      @ whiskerL (path_universe g) (path_universe_1)^
      @ whiskerL (path_universe g)
          (equiv_path2_universe (equiv_idmap B) (equiv_idmap B) p)
      @ whiskerL (path_universe g) (path_universe_1)
      @ concat_p1 _.
  Proof.
  transitivity ((eta_path_universe (path_universe g))^
                @ equiv_path2_universe
                  (equiv_path A B (path_universe g))
                  (equiv_path A B (path_universe g))
                  (fun a => p (equiv_path A B (path_universe g) a))
                @ eta_path_universe (path_universe g)).
  - refine ((apD (fun g' => equiv_path2_universe g' g'
                              (fun a => p (g' a)))
              (eisretr (equiv_path A B) g))^ @ _).
    refine (transport_paths_FlFr (eisretr (equiv_path A B) g) _ @ _).
    apply concat2.
    + apply whiskerR.
      apply inverse2, symmetry.
      refine (eisadj (equiv_path A B)^-1 g).
    + symmetry; refine (eisadj (equiv_path A B)^-1 g).
  - generalize (path_universe g).
    intros h. destruct h. cbn.
    rewrite !concat_p1.
    refine (_ @ (((concat_1p (whiskerL 1 path_universe_1^))^ @@ 1) @@ 1)).
    refine (_ @ whiskerR (whiskerL_pp 1 path_universe_1^ _) _).
    refine (_ @ whiskerL_pp 1 _ path_universe_1).
    exact ((whiskerL_1p_1 _)^).
  Defined.

End PathEquivSimplNever.

(** ** 3-paths *)

Definition equiv_path3_universe `{Funext}
           {A B : Type} {f g : A <~> B} (p q : f == g)
: (p == q) <~> (path2_universe p = path2_universe q).
Proof.
  refine (_ oE equiv_path_forall p q).
  refine (_ oE equiv_ap (equiv_path_arrow f g) p q).
  refine (_ oE equiv_ap (equiv_path_equiv f g) _ _).
  unfold path2_universe, equiv_path2_universe.
  simpl. refine (equiv_ap (ap (equiv_path A B)^-1) _ _).
Defined.

Definition path3_universe `{Funext}
           {A B : Type} {f g : A <~> B} {p q : f == g}
: (p == q) -> (path2_universe p = path2_universe q)
  := equiv_path3_universe p q.

Definition transport_path_universe_pV_uncurried `{Funext}
           {A B : Type} (f : A <~> B) (z : B)
: transport_path_universe f (transport idmap (path_universe f)^ z)
  @ ap f (transport_path_universe_V f z)
  @ eisretr f z
  = transport_pV idmap (path_universe f) z.
Proof.
  pattern f.
  refine (equiv_ind (equiv_path A B) _ _ _); intros p.
  refine (_ @ ap_transport_pV_idmap p (path_universe (equiv_path A B p))
            (eissect (equiv_path A B) p) z).
  apply whiskerR.
  refine ((concat_Ap _ _)^ @ _).
  apply concat2.
  - apply ap.
    refine (transport_path_universe_V_equiv_path _ _ @ _).
    unfold inverse2. symmetry; apply (ap_compose inverse (fun s => transport idmap s z)).
  - apply transport_path_universe_equiv_path.
Defined.

Definition transport_path_universe_pV `{Funext}
           {A B : Type} (f : A -> B) {feq : IsEquiv f } (z : B)
: transport_path_universe f (transport idmap (path_universe f)^ z)
  @ ap f (transport_path_universe_V f z)
  @ eisretr f z
  = transport_pV idmap (path_universe f) z
:= transport_path_universe_pV_uncurried (BuildEquiv A B f feq) z.

(** ** Equivalence induction *)

(** Paulin-Mohring style *)
Theorem equiv_induction {U : Type} (P : forall V, U <~> V -> Type) :
  (P U (equiv_idmap U)) -> (forall V (w : U <~> V), P V w).
Proof.
  intros H0 V w.
  apply (equiv_ind (equiv_path U V)).
  exact (paths_ind U (fun Y p => P Y (equiv_path U Y p)) H0 V).
Defined.

Definition equiv_induction_comp {U : Type} (P : forall V, U <~> V -> Type)
  (didmap : P U (equiv_idmap U))
  : equiv_induction P didmap U (equiv_idmap U) = didmap
  := (equiv_ind_comp (P U) _ 1).

(** Martin-Lof style *)
Theorem equiv_induction' (P : forall U V, U <~> V -> Type) :
  (forall T, P T T (equiv_idmap T)) -> (forall U V (w : U <~> V), P U V w).
Proof.
  intros H0 U V w.
  apply (equiv_ind (equiv_path U V)).
  exact (paths_ind' (fun X Y p => P X Y (equiv_path X Y p)) H0 U V).
Defined.

Definition equiv_induction'_comp (P : forall U V, U <~> V -> Type)
  (didmap : forall T, P T T (equiv_idmap T)) (U : Type)
  : equiv_induction' P didmap U U (equiv_idmap U) = didmap U
  := (equiv_ind_comp (P U U) _ 1).

(** ** Based equivalence types *)

Global Instance contr_basedequiv {X : Type}
: Contr {Y : Type & X <~> Y}.
Proof.
  refine (trunc_equiv' {Y : Type & X = Y}
           (equiv_functor_sigma' (equiv_idmap Type)
             (fun Y => equiv_equiv_path X Y))).
Defined.

Global Instance contr_basedequiv' {X : Type}
: Contr {Y : Type & Y <~> X}.
Proof.
  refine (trunc_equiv' {Y : Type & Y = X}
           (equiv_functor_sigma' (equiv_idmap Type)
             (fun Y => equiv_equiv_path Y X))).
Defined.

(** ** Truncations *)

(** Truncatedness of the universe is a subtle question, but with univalence we can conclude things about truncations of certain of its path-spaces. *)
Global Instance istrunc_paths_Type `{Funext}
       {n : trunc_index} {A B : Type} `{IsTrunc n.+1 B}
: IsTrunc n.+1 (A = B).
Proof.
  refine (trunc_equiv _ path_universe_uncurried).
Defined.

(** We can also say easily that the universe is not a set. *)
Definition not_hset_Type : ~ (IsHSet Type).
Proof.
  intro HT.
  apply true_ne_false.
  pose (r := path_ishprop (path_universe equiv_negb) 1).
  refine (_ @ (ap (fun q => transport idmap q false) r)).
  symmetry; apply transport_path_universe.
Defined.

End Univalence.
