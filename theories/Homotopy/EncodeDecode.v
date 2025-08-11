Require Import Basics Pointed.
Require Import Truncations.Core.
Require Import Truncations.Connectedness.
Require Import Types.Prod.

(** ** Encode-decode method of characterizing identity types *)
(** See Homotopy/IdentitySystems.v for a related characterization of identity types. *)
Definition encode_decode
  (A : Type) (a0 : A) (code : A -> Type)
  (c0 : code a0) (decode : forall x, code x -> a0 = x)
  (s : forall (c : code a0), decode _ c # c0 = c)
  (r : decode _ c0 = idpath) (a1 : A)
  : a0 = a1 <~> code a1.
Proof.
  srapply equiv_adjointify.
  - exact (fun p => p # c0).
  - apply decode.
  - intro p.
    destruct (decode _ p) in p.
    apply s.
  - intros [].
    exact r.
Defined.
(** Encode-decode for truncated identity-types *)
Definition encode_decode_trunc n
  (A : Type) (a0 : A) (code : A -> Type) `{forall a, IsTrunc n (code a)}
  (c0 : code a0) (decode : forall x, code x -> Tr n (a0 = x))
  (s : forall (c : code a0), Trunc_rec (fun p => p # c0) (decode _ c) = c)
  (r : decode _ c0 = tr idpath) (a1 : A)
  : Tr n (a0 = a1) <~> code a1.
Proof.
  srapply equiv_adjointify.
  - exact (Trunc_rec (fun p => p # c0)).
  - apply decode.
  - intro p.
    pose (decode _ p) as p'.
    clearbody p'.
    strip_truncations.
    destruct p' in p.
    apply s.
  - intros p.
    strip_truncations.
    destruct p.
    exact r.
Defined.
(** Encode-decode for loop spaces *)
Definition encode_decode_loops
  (A : pType) (code : pFam A)
  (decode : forall x, code x -> point A = x)
  (s : forall (c : code (point A)), decode _ c # (dpoint code) = c)
  (r : decode _ (dpoint code) = idpath)
  : loops A <~> code (point A)
  := encode_decode A (point A) code (dpoint code) decode s r (point A).
(** Encode-decode for truncated loop spaces *)
Definition encode_decode_trunc_loops n
  (A : pType) (code : pFam A) `{forall a, IsTrunc n (code a)}
  (decode : forall x, code x -> Tr n (point A = x))
  (s : forall (c : code (point A)),
    Trunc_rec (fun (p : loops A) => p # (dpoint code)) (decode _ c) = c)
  (r : decode _ (dpoint code) = tr idpath)
  : pTr n (loops A) <~> code (point A)
  := encode_decode_trunc n A (point A) code (dpoint code) decode s r (point A).

(** ** Systematic framework for homotopy group computation *)

Section HomotopyGroupFramework.
  Context {A : Type} {a : A} 
          (Code : A -> Type)
          (encode_refl : Code a)
          (decode : forall x, Code x -> (a = x))
          (encode : forall x, (a = x) -> Code x).
  
  (** General encode-decode equivalence from round-trip properties *)
  Definition generic_encode_decode_equiv 
    (decode_encode : forall x (p : a = x), decode x (encode x p) = p)
    (encode_decode : forall x (c : Code x), encode x (decode x c) = c)
    : forall x, IsEquiv (decode x)
    := fun x => isequiv_adjointify (decode x) (encode x) 
                  (decode_encode x) (encode_decode x).

  (** Fundamental group computation via encode-decode *)
  Definition fundamental_group_via_encode_decode
    `{IsHSet (Code a)}
    `{IsConnected 0%trunc A}
    (decode_encode : forall x (p : a = x), decode x (encode x p) = p)
    (encode_decode : forall x (c : Code x), encode x (decode x c) = c)
    : Tr 0 (a = a) <~> Code a
    := equiv_adjointify 
         (Trunc_rec (encode a))
         (fun c => tr (decode a c))
         (encode_decode a)
         (Trunc_ind (fun _ => _) (fun p => ap tr (decode_encode a p))).

  (** Generalization to higher homotopy groups *)
  Definition higher_group_via_encode_decode
    (n : trunc_index)
    `{IsTrunc n (Code a)}
    `{IsConnected (trunc_S n) A}
    (decode_encode : forall x (p : a = x), decode x (encode x p) = p)
    (encode_decode : forall x (c : Code x), encode x (decode x c) = c)
    : Tr n (a = a) <~> Code a
    := equiv_adjointify 
         (Trunc_rec (encode a))
         (fun c => tr (decode a c))
         (encode_decode a)
         (Trunc_ind (fun _ => _) (fun p => ap tr (decode_encode a p))).

  (** Computational extraction of group elements *)
  Definition compute_fundamental_element
    (loop : a = a)
    : Code a
    := encode a loop.

  Fixpoint loop_power (n : nat) (loop : a = a) : a = a :=
    match n with
    | O => idpath
    | S n' => loop @ (loop_power n' loop)
    end.

  Definition compute_iterated_fundamental_element
    (n : nat)
    (loop : a = a)
    : Code a
    := encode a (loop_power n loop).

  Definition compute_inverse_element
    (c : Code a)
    : a = a
    := decode a c.

End HomotopyGroupFramework.

(** ** Encode-decode from covering space data *)
Section CoveringSpace.
  Context {A : Type} {a : A}
          (P : A -> Type)
          `{forall x, IsHSet (P x)}
          (p0 : P a).

  Definition encode_from_covering : forall x, (a = x) -> P x
    := fun x p => transport P p p0.

  Definition covering_to_code : A -> Type := P.

  Context (path_lift : forall x, P x -> (a = x)).

  Definition decode_from_covering : forall x, P x -> (a = x)
    := path_lift.

End CoveringSpace.

(** ** Compositional encode-decode for product spaces *)
Section Compositional.

  Context {A B : Type} {a : A} {b : B}
          (CodeA : A -> Type) (CodeB : B -> Type).

  (** π₁(A × B) ≃ π₁(A) × π₁(B) *)
  Definition encode_decode_product
    : (A * B) -> Type
    := fun xy => CodeA (fst xy) * CodeB (snd xy).

  Definition encode_product
    (encodeA : forall x, (a = x) -> CodeA x)
    (encodeB : forall y, (b = y) -> CodeB y)
    : forall xy, ((a,b) = xy) -> (CodeA (fst xy) * CodeB (snd xy))
    := fun xy p => (encodeA (fst xy) (ap fst p), encodeB (snd xy) (ap snd p)).

  Definition decode_product
    (decodeA : forall x, CodeA x -> (a = x))
    (decodeB : forall y, CodeB y -> (b = y))
    : forall xy, (CodeA (fst xy) * CodeB (snd xy)) -> ((a,b) = xy)
    := fun xy cc => path_prod (a,b) xy (decodeA (fst xy) (fst cc)) (decodeB (snd xy) (snd cc)).

End Compositional.

(** ** Type class for encode-decode structure *)
Module Synthesis.

  Class HasEncodeDecode (A : Type) (a : A) :=
  { ed_code : A -> Type;
    ed_encode_refl : ed_code a;
    ed_decode : forall x, ed_code x -> (a = x);
    ed_encode : forall x, (a = x) -> ed_code x;
    ed_decode_encode : forall x (p : a = x), ed_decode x (ed_encode x p) = p;
    ed_encode_decode : forall x (c : ed_code x), ed_encode x (ed_decode x c) = c;
    ed_code_is_set : IsHSet (ed_code a)
  }.

  (** Automatic fundamental group computation via type class *)
  Definition auto_fundamental_group 
    {A : Type} {a : A} `{H : HasEncodeDecode A a}
    `{IsConnected 0%trunc A}
    : Tr 0 (a = a) <~> ed_code a
    := @fundamental_group_via_encode_decode 
         A a ed_code ed_decode ed_encode 
         ed_code_is_set _ ed_decode_encode ed_encode_decode.

End Synthesis.
    
