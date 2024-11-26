Require Import Basics Pointed.
Require Import Truncations.Core.

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
  - apply (Trunc_rec (fun p => p # c0)).
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
  := encode_decode _ _ code (dpoint code) decode s r _.

(** Encode-decode for truncated loop spaces *)
Definition encode_decode_trunc_loops n
  (A : pType) (code : pFam A) `{forall a, IsTrunc n (code a)}
  (decode : forall x, code x -> Tr n (point A = x))
  (s : forall (c : code (point A)),
    Trunc_rec (fun (p : loops A) => p # (dpoint code)) (decode _ c) = c)
  (r : decode _ (dpoint code) = tr idpath)
  : pTr n (loops A) <~> code (point A)
  := encode_decode_trunc _ _ _ code (dpoint code) decode s r _.

