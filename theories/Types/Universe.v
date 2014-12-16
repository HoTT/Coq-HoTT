(* -*- mode: coq; mode: visual-line -*- *)
(** * Theorems about the universe, including the Univalence Axiom. *)

Require Import HoTT.Basics.
Require Import Types.Sigma Types.Arrow Types.Paths Types.Equiv.
Local Open Scope path_scope.
Local Open Scope equiv_scope.

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
  equiv_path B A (p^) = equiv_inverse (equiv_path A B p).
Proof.
  destruct p. simpl. unfold equiv_path, equiv_inverse. simpl. apply ap.
  refine (@path_ishprop _ (hprop_isequiv _) _ _).
Defined.

Definition equiv_path_pp `{Funext} {A B C : Type} (p : A = B) (q : B = C)
: equiv_path A C (p @ q) = equiv_compose' (equiv_path B C q) (equiv_path A B p).
Proof.
  destruct p, q. simpl.
  apply path_equiv, path_arrow.
  intros x; reflexivity.
Defined.

(** See the note by [Funext] in Overture.v *)
Class Univalence.
Axiom isequiv_equiv_path : forall `{Univalence} (A B : Type), IsEquiv (equiv_path A B).

Section Univalence.
Context `{Univalence}.

Definition path_universe_uncurried {A B : Type} (f : A <~> B) : A = B
  := (equiv_path A B)^-1 f.

Definition path_universe {A B : Type} (f : A -> B) {feq : IsEquiv f} : (A = B)
  := path_universe_uncurried (BuildEquiv _ _ f feq).

Definition eta_path_universe {A B : Type} (p : A = B)
  : path_universe (equiv_path A B p) = p
  := eissect (equiv_path A B) p.

Definition isequiv_path_universe {A B : Type}
  : IsEquiv (@path_universe_uncurried A B)
 := _.

Definition equiv_path_universe (A B : Type) : (A <~> B) <~> (A = B)
  := BuildEquiv _ _ (@path_universe_uncurried A B) isequiv_path_universe.

Definition path_universe_V_uncurried `{Funext} {A B : Type} (f : A <~> B)
  : path_universe_uncurried (equiv_inverse f) = (path_universe_uncurried f)^.
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
(* Alternatively, [ap10 (ap equiv_fun (eisretr (equiv_path A B) (BuildEquiv _ _ f feq))) z]. *)

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

End Univalence.
