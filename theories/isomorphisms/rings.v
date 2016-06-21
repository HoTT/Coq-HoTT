Require Import
  HoTT.Types.Record
  HoTT.Types.Universe
  HoTT.Types.Sigma
  HoTT.Types.Prod
  HoTT.Types.Arrow.
Require Export
  HoTTClasses.interfaces.abstract_algebra.
Require Import HoTTClasses.theory.rings.

Class SemiRingOperations
  := semiringoperations : sigT (fun T => Plus T * Mult T * Zero T * One T)%type.

Definition BuildSemiRingOperations (T : Type) `{Plus T} `{Mult T} `{Zero T} `{One T}
  : SemiRingOperations
  := existT _ T (plus,mult,zero,one).

Coercion SR_carrier (s : SemiRingOperations) : Type := s.1.
Instance SR_plus (s : SemiRingOperations) : Plus s := fst (fst (fst s.2)).
Instance SR_mult (s : SemiRingOperations) : Mult s := snd (fst (fst s.2)).
Instance SR_zero (s : SemiRingOperations) : Zero s := snd (fst s.2).
Instance SR_one (s : SemiRingOperations) : One s := snd s.2.

Section iso.

Context `{Funext} `{Univalence}.
Context (A B : SemiRingOperations).

Context (f : A -> B) `{!IsEquiv f} `{!SemiRing_Morphism f}.

Lemma iso_same_semirings : A = B.
Proof.
apply path_sigma_uncurried.
destruct A as [TA [[[plA mlA] zA] uA]], B as [TB [[[plB mlB] zB] uB]];simpl in *.
change plA with (@plus TA plA);change plB with (@plus TB plB);
change mlA with (@mult TA mlA);change mlB with (@mult TB mlB);
change zA with (@zero TA zA);change zB with (@zero TB zB);
change uA with (@one TA uA);change uB with (@one TB uB).
exists (path_universe f).
rewrite !transport_prod;simpl.
unfold Plus,Mult,Zero,One.
repeat apply path_prod;simpl;try
( apply path_forall;intros x;rewrite transport_arrow;
  apply path_forall;intros y;rewrite transport_arrow);
rewrite transport_path_universe, ?transport_path_universe_V.
- rewrite (preserves_plus (f:=f)).
  apply ap2;apply eisretr.
- rewrite (preserves_mult (f:=f)).
  apply ap2;apply eisretr.
- apply preserves_0.
- apply preserves_1.
Qed.

Lemma iso_leibnitz : forall P : SemiRingOperations -> Type, P A -> P B.
Proof.
rewrite iso_same_semirings. trivial.
Qed.

End iso.
