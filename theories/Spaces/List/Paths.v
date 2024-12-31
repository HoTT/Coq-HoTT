Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Trunc.
Require Import Basics.Equivalences Types.Empty Types.Unit Types.Prod.
Require Import Modalities.ReflectiveSubuniverse Truncations.Core.
Require Import Spaces.List.Core.

(** * Path spaces of lists *)

(** This proof was adapted from a proof given in agda/cubical by Evan Cavallo. *)

Section PathList.
  Context {A : Type}.
  
  (** We'll show that this type is equivalent to the path space [l = l'] in [list A]. *)
  Fixpoint ListEq (l l' : list A) : Type :=
    match l, l' with
      | nil, nil => Unit
      | cons x xs, cons x' xs' => (x = x') * ListEq xs xs'
      | _, _ => Empty
    end.

  Global Instance reflexive_listeq : Reflexive ListEq. 
  Proof.
    intros l.
    induction l as [| a l IHl].
    - exact tt.
    - exact (idpath, IHl).
  Defined.

  Local Definition encode {l1 l2} (p : l1 = l2) : ListEq l1 l2.
  Proof.
    by destruct p.
  Defined.

  Local Definition decode {l1 l2} (q : ListEq l1 l2) : l1 = l2.
  Proof.
    induction l1 as [| a l1 IHl1 ] in l2, q |- *.
    1: by destruct l2.
    destruct l2.
    1: contradiction.
    destruct q as [p q].
    exact (ap011 (cons (A:=_)) p (IHl1 _ q)).
  Defined.

  Local Definition decode_refl {l} : decode (reflexivity l) = idpath.
  Proof.
    induction l.
    1: reflexivity.
    exact (ap02 (cons a) IHl).
  Defined.

  Local Definition decode_encode {l1 l2} (p : l1 = l2)
    : decode (encode p) = p.
  Proof.
    destruct p.
    apply decode_refl.
  Defined.

  (** By case analysis on both lists, it's easy to show that [ListEq] is [n.+1]-truncated if [A] is [n.+2]-truncated. *)
  Global Instance istrunc_listeq n {l1 l2} {H : IsTrunc n.+2 A}
    : IsTrunc n.+1 (ListEq l1 l2).
  Proof.
    induction l1 in l2 |- *.
    - destruct l2.
      1,2: exact _.
    - destruct l2.
      1: exact _.
      rapply istrunc_prod.
  Defined.

  (** The path space of lists is a retract of [ListEq], therefore it is [n.+1]-truncated if [ListEq] is [n.+1]-truncated. By the previous result, this holds when [A] is [n.+2]-truncated. *) 
  Global Instance istrunc_list n {H : IsTrunc n.+2 A} : IsTrunc n.+2 (list A).
  Proof.
    apply istrunc_S.
    intros x y.
    rapply (inO_retract_inO n.+1 _ _ encode decode decode_encode).
  Defined.

  (** With a little more work, we can show that [ListEq] is also a retract of the path space. *)
  Local Definition encode_decode {l1 l2} (p : ListEq l1 l2)
    : encode (decode p) = p.
  Proof.
    induction l1 in l2, p |- *.
    1: destruct l2; by destruct p.
    destruct l2.
    1: by destruct p.
    cbn in p.
    destruct p as [r p].
    apply path_prod.
    - simpl.
      destruct (decode p).
      by destruct r.
    - rhs_V nrapply IHl1.
      simpl.
      destruct (decode p).
      by destruct r.
  Defined.

  (** Giving us a way of characterising paths in lists. *)
  Definition equiv_path_list {l1 l2}
    : ListEq l1 l2 <~> l1 = l2
    := equiv_adjointify decode encode decode_encode encode_decode.

End PathList.
