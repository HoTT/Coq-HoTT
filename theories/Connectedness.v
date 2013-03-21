(* -*- mode: coq; mode: visual-line -*-  *)
(** * Connectedness *)

Require Import Overture Fibrations Equivalences Trunc.
Local Open Scope equiv_scope.
Local Open Scope path_scope.

(** There is a slight controversy of indexing for connectedness — in particular, how the indexing for maps shoud relate to the indexing for types.  One may reasonably take the connectedness of a map to correspond either to that of its *fibers*, or of its *cofiber*; these differ by 1.  The traditional topological indexing uses the cofiber.  We use the fiber, as does Lurie in [HTT]; but we choose to agree with the traditional indexing on types, while Lurie agrees with it on maps.

Currently, the translation is therefore as follows:

       HoTT              Traditional       Lurie

Map    (n-1)-connected   n-connected       n-connective
Type   n-connected       n-connected       (n+1)-connective

There is a further choice in the definition.  Connectedness can either be defined as contractibility of the truncation, or by elimination into truncated types.  The former requires HIT’s, but keeps the type [IsConnected] small; the latter (which we use for now) requires only core Coq, but blows up the size of [IsConnected], since it quantifies over types. *)

Class IsConnected (n : trunc_index) (A : Type)
 := isconnected_elim :> 
      forall (C : Type) `{IsTrunc n C} (f : A -> C),
        exists c:C, (forall a:A, f a = c).

(* TODO: probably remove — with type classes, one is supposed to avoid using this sort of type, right?
Record ConnectedType (n : trunc_index) := BuildConnectedType {
  Type_of_ConnectedType :> Type ; 
  isconnected_ConnectedType :> IsTrunc n Type_of_ConnectedType
}.

Existing Instance isconnected_ConnectedType.
*)

Class IsConnMap (n : trunc_index) {A B : Type} (f : A -> B)
  := isconnected_hfiber_connmap :>
       forall b:B, IsConnected n (hfiber f b).
(* TODO: question — why do the implicit arguments of this not seem to work, i.e. seem to need to be given explicitly? *)

(** n-connected maps are orthogonal to n-truncated maps (i.e. familes of n-truncated types). *)
Definition connmap_elim {n : trunc_index}
  {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
  (P : B -> Type) {HP : forall b:B, IsTrunc n (P b)}
  (d : forall a:A, P (f a))
: forall b:B, P b.
Proof.
  intros b. 
  apply isconnected_elim.
    apply HP.
    instantiate (1 := b). intros [a p]. 
    exact (transport P p (d a)).
Defined.

Definition connmap_comp {n : trunc_index}
  {A B : Type} (f : A -> B) `{IsConnMap n _ _ f}
  (P : B -> Type) {HP : forall b:B, IsTrunc n (P b)}
  (d : forall a:A, P (f a))
: forall a:A, connmap_elim f P d (f a) = d a.
Proof.
  intros a. unfold connmap_elim.
  set (fibermap := (fun a0p : hfiber f (f a)
    => let (a0, p) := a0p in transport P p (d a0))).
  destruct (isconnected_elim (P (f a)) fibermap) as [x e].
  change (d a) with (fibermap (a;1)).
  apply inverse, e.
Defined.

(*TODO: converse of these two lemmas — if a map has such an elim/comp, then it is connected. *)

(** Very useful lemma: the connectivity of the wedge into the product, for a pair of pointed spaces.  The version here is reformulated to avoid mentioning the wedge itself. *)
Definition isconn_wedge_incl {m n : trunc_index}
  (A : Type) (a0 : A) `{IsConnected (trunc_S m) A} 
  (B : Type) (b0 : B) `{IsConnected (trunc_S n) B} 
  (P : A -> B -> Type) `{forall a b, IsTrunc (m -2+ n) (P a b)}
  (f_a0 : forall b:B, P a0 b)
  (f_b0 : forall a:A, P a b0)
  (f_a0b0 : f_a0 b0 = f_b0 a0)
: { f : forall a b, P a b
  & { e_a0 : forall b, f a0 b = f_a0 b
  & { e_b0 : forall a, f a b0 = f_b0 a
  & (e_a0 b0) @ f_a0b0 = (e_b0 a0) }}}.
Proof.
Admitted.