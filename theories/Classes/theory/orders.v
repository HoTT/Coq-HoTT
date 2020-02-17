Require Import
        HoTT.Classes.interfaces.canonical_names
        HoTT.Classes.interfaces.orders.

Section pseudo.
  Context {A : Type}.
  Context `{PseudoOrder A}.

  Lemma pseudo_not_lt_lt {x y z : A} : ~ y < x -> y < z -> x < z.
  Proof.
    intros nltyx ltyz.
    set (disj := cotransitive ltyz x).
    refine (@Trunc_rec _ _ _ _ _ disj). intro disj'.
    destruct disj' as [ltyx|ltxz].
    - destruct (nltyx ltyx).
    - exact ltxz.
  Qed.

  Lemma pseudo_lt_not_lt {x y z : A} : x < y -> ~ z < y -> x < z.
  Proof.
    intros ltxy nltzy.
    set (disj := cotransitive ltxy z).
    refine (@Trunc_rec _ _ _ _ _ disj). intro disj'.
    destruct disj' as [ltxz|ltzy].
    - exact ltxz.
    - destruct (nltzy ltzy).
  Qed.

End pseudo.
