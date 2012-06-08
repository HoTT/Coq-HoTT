(** Univalence is about equating equivalences between types with paths between types.
   Without the axiom of univalence, we can still fake things by showing that equivalences
   behave like paths. In this file we show that for definable types, equivalences give us
   a (non-dependent) substitution principle. More precisely, if [P] is a definable type
   constructor then whenever [A <~> B] we also get [P A <~> P B].

   You can think of this is an exercise towards showing that the universe of definable
   types satisfies univalence, which is done in [UnivalentTypes.v].
*)

Add LoadPath "..".

Require Import Paths Fibrations Contractible Funext HLevel
  Equivalences FiberEquivalences FunextEquivalences Univalence.
Require Import ExtensionalityAxiom.

(** Suppose [P : Type -> Type] and [A <~> B]. Is it the case that [P A <~> P B], or more
   precisely, can we always convert [e : A <~> B] to [map P e : P A <~> P B]? Let us call
   a [P] *equivariant* when it has this property. As it turns out, we need to additionally
   require that the passage [eq_map] from [A <~> B] to [P A <~> P B] commute with identities.
   *)

Structure Equivariant := {
  eq_ty :> Type -> Type ;
  eq_map : forall (A B : Type), A <~> B -> eq_ty A <~> eq_ty B ;
  eq_id : forall (A : Type) (x : eq_ty A), eq_map A A (idequiv A) x == x
}.

Implicit Arguments eq_map [A B].
Implicit Arguments eq_id [A].

(** We would like to show that equivariance is closed under dependent sums and products.
   For this purpose we need a notion of an equivariant family over an equivariant family *)

Structure EquivariantFamily (P : Equivariant) := {
  fam :> forall (A : Type), P A -> Type ; 
  fam_map : forall (A B : Type) (e : A <~> B) (x : P A), fam A x <~> fam B (eq_map P e x) ;
  fam_id : forall (A : Type) (x : P A) (y : fam A x), eq_id P x # fam_map A A (idequiv A) x y == y
}.

Implicit Arguments fam [P].
Implicit Arguments fam_map [P A B].

(** We expect all definable families to be equivariant. So we start showing that equivariance
   is closed under various operations.*)

Section CartesianProduct.
  (* An exercise: cartesian products *)

  Definition prod_map (P Q : Equivariant) (A B : Type) (e : A <~> B) :
    (P A * Q A <~> P B * Q B)%type.
  Proof.
    apply product_equiv.
    exact (eq_map P e).
    exact (eq_map Q e).
  Defined.

  Theorem prod_equivariant (P Q : Equivariant) : Equivariant.
  Proof.
    refine
      {| eq_ty := fun A => (P A * Q A)%type ;
         eq_map := prod_map P Q
      |}.
    intros A [x y]; apply prod_path_equiv; simpl; split; apply eq_id.
  Defined.
End CartesianProduct.

Section DisjointSum.
  (** Another exercise: disjoint sums *)

  (** We would expect this lemma in [UsefulEquivalences]. *)
  Lemma sum_equiv (A A' B B' : Type) :
    (A <~> A') -> (B <~> B') -> (A + B <~> A' + B').
  Proof.
    intros e f.
    apply (equiv_from_hequiv
      (fun (u : A + B) => match u with inl x => inl _ (e x) | inr y => inr _ (f y) end)
      (fun (v : A' + B') => match v with inl x' => inl _ (e^-1 x') | inr y' => inr _ (f^-1 y') end)).
    intros [x'|y']; apply map, inverse_is_section.
    intros [x|y]; apply map, inverse_is_retraction.
  Defined.

  Definition sum_map (P Q : Equivariant) (A B : Type) (e : A <~> B) :
    (P A + Q A <~> P B + Q B)%type.
  Proof.
    apply sum_equiv; apply eq_map; exact e.
  Defined.
    
  Theorem sum_equivariant (P Q : Equivariant) : Equivariant.
  Proof.
    refine
      {| eq_ty := fun A => (P A + Q A)%type ;
         eq_map := sum_map P Q
       |}.
    intros A [u|v]; unfold sum_map, sum_equiv; simpl; apply map, eq_id.
  Defined.
End DisjointSum.

Section DependentSum.
  (** Now something slightly more involved: total spaces. *)

  (** This one should go to [FiberEquivalences]. *)
  Lemma total_equiv (A B : Type) (P : fibration A) (Q : fibration B) (e : A <~> B)
    (f : (forall x : A, P x <~> Q (e x))) :
    total P <~> total Q.
  Proof.
    apply fibseq_total_equiv with (e := e) (g := (fun x => f x)).
    intro x; apply (equiv_is_equiv (f x)).
  Defined.

  Definition total_map (P : Equivariant) (Q : EquivariantFamily P)
    (A B : Type) (e : A <~> B) : total (Q A) <~> total (Q B).
  Proof.
    apply total_equiv with (e := eq_map P e) (P := Q A) (Q := Q B).
    intro x.
    apply fam_map.
  Defined.
  
  (** The dependent sum of an equivariant family is equivariant. *)
  Theorem total_equivariant (P : Equivariant) (Q : EquivariantFamily P) : Equivariant.
  Proof.
    refine
      {| eq_ty := (fun A => total (Q A)) ;
         eq_map := total_map P Q
      |}.
    intros A [x y]; apply total_paths_equiv; simpl.
    exists (eq_id P x).
    now apply fam_id.
  Defined.
End DependentSum.

Section DependentProduct.
  (* Again something that should find its place elsewhere. *)

  Lemma section_equiv (A B : Type) (P : fibration A) (Q : fibration B)
    (e : A <~> B) (f : forall x : A, P x <~> Q (e x)) :
    section P <~> section Q.
  Proof.
    pose (j := fun (h : section P) (y : B) => inverse_is_section e y # f (e^-1 y) (h (e^-1 y))).
    pose (k := fun (g : section Q) (x : A) => (f _)^-1 (g (e x))).
    apply (equiv_from_hequiv j k).
    intros s.
    unfold j, k.
    apply funext_dep; intro y.
    rewrite (inverse_is_section (f (e^-1 y))).
    rewrite (inverse_is_section e).
    now auto.
    intros s; unfold j, k.
    apply funext_dep; intro x.
    rewrite <- inverse_triangle.
    rewrite (inverse_is_retraction e x).
    now hott_simpl.
  Defined.
  
  Variable (P : Equivariant).
  Variable (Q : EquivariantFamily P).

  Definition section_map (X Y : Type) (g : X <~> Y) : section (Q X) <~> section (Q Y).
  Proof.
    apply section_equiv with (P := Q X) (Q := Q Y) (e := eq_map P g).
    apply (fam_map Q g).
  Defined.

  (* The main theorem of this section. *)
  Definition section_equivariant : Equivariant.
  Proof.
    refine
      {| eq_ty := (fun A => section (Q A)) ;
         eq_map := section_map
      |}.
    (* Identity *)
    intros A s.
    apply funext_dep; intro x.
    unfold section_map, section_equiv; simpl.
    generalize (inverse_is_section (eq_map P (idequiv A)) x).
    generalize ((eq_map P (idequiv A))^-1 x).
    intros x' p.
    pose (q := (!(eq_id P x') @ p)).
    assert (h : p == eq_id P x' @ q); unfold q; hott_simpl.
    rewrite h.
    generalize q; intro r; induction r.
    hott_simpl.
    now apply fam_id.
  Defined.
End DependentProduct.

