Require Import
  HoTT.Types.Universe
  HoTT.Types.Sigma
  HoTT.Types.Prod
  HoTT.Types.Arrow.
Require Export
  HoTT.Classes.interfaces.abstract_algebra.
Require Import HoTT.Classes.theory.rings.


Module SemiRings.

Class Operations
  := operations : sigT (fun T => Plus T * Mult T * Zero T * One T)%type.

Definition BuildOperations (T : Type) `{Plus T} `{Mult T} `{Zero T} `{One T}
  : Operations
  := existT _ T (plus,mult,zero,one).

Coercion SR_carrier (s : Operations) : Type := s.1.
Instance SR_plus (s : Operations) : Plus s := fst (fst (fst s.2)).
Instance SR_mult (s : Operations) : Mult s := snd (fst (fst s.2)).
Instance SR_zero (s : Operations) : Zero s := snd (fst s.2).
Instance SR_one (s : Operations) : One s := snd s.2.

Arguments SR_plus !_ / _ _.
Arguments SR_mult !_ / _ _.
Arguments SR_zero !_ /.
Arguments SR_one !_ /.


Section contents.
Universe U V.
Context `{Funext} `{Univalence}.
Context (A B : Operations@{U V}).

Context (f : A -> B) `{!IsEquiv f} `{!SemiRingPreserving f}.

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

Lemma iso_leibnitz : forall P : Operations -> Type, P A -> P B.
Proof.
intros P;apply transport.
(* Coq pre 8.8 produces phantom universes, see GitHub Coq/Coq#1033. *)
first [exact iso_same_semirings|exact iso_same_semirings@{V V}].
Qed.

End contents.

End SemiRings.

Module Rings.

Class Operations
  := operations : sigT (fun T => Plus T * Mult T * Zero T * One T * Negate T)%type.

Definition BuildOperations (T : Type)
  `{Plus T} `{Mult T} `{Zero T} `{One T} `{Negate T}
  : Operations
  := existT _ T (plus,mult,zero,one,negate).

Coercion R_carrier (s : Operations) : Type := s.1.
Instance R_plus (s : Operations) : Plus s := fst (fst (fst (fst s.2))).
Instance R_mult (s : Operations) : Mult s := snd (fst (fst (fst s.2))).
Instance R_zero (s : Operations) : Zero s := snd (fst (fst s.2)).
Instance R_one (s : Operations) : One s := snd (fst s.2).
Instance R_negate (s : Operations) : Negate s := snd s.2.

Arguments R_plus !_ / _ _.
Arguments R_mult !_ / _ _.
Arguments R_zero !_ /.
Arguments R_one !_ /.
Arguments R_negate !_ / _.

Section contents.
Universe U V.
Context `{Funext} `{Univalence}.
Context (A B : Operations@{U V}).

(* NB: we need to know they're rings for preserves_negate *)
Context (f : A -> B) `{!IsEquiv f} `{!Ring A} `{!Ring B} `{!SemiRingPreserving f}.

Lemma iso_same_rings : A = B.
Proof.
apply path_sigma_uncurried.
destruct A as [TA [[[[plA mlA] zA] uA] nA]],
  B as [TB [[[[plB mlB] zB] uB] nB]];simpl in *.
change plA with (@plus TA plA);change plB with (@plus TB plB);
change mlA with (@mult TA mlA);change mlB with (@mult TB mlB);
change zA with (@zero TA zA);change zB with (@zero TB zB);
change uA with (@one TA uA);change uB with (@one TB uB);
change nA with (@negate TA nA);change nB with (@negate TB nB).
exists (path_universe f).
rewrite !transport_prod;simpl.
unfold Plus,Mult,Zero,One,Negate.
repeat apply path_prod;simpl;try
( apply path_forall;intros x;rewrite transport_arrow;
  try (apply path_forall;intros y;rewrite transport_arrow));
rewrite transport_path_universe, ?transport_path_universe_V.
- rewrite (preserves_plus (f:=f)).
  apply ap2;apply eisretr.
- rewrite (preserves_mult (f:=f)).
  apply ap2;apply eisretr.
- apply preserves_0.
- apply preserves_1.
- rewrite (preserves_negate (f:=f)).
  apply ap,eisretr.
Qed.

Lemma iso_leibnitz : forall P : Operations -> Type, P A -> P B.
Proof.
intros P;apply transport.
(* Coq pre 8.8 produces phantom universes, see GitHub Coq/Coq#1033. *)
first [exact iso_same_rings|exact iso_same_rings@{V V}].
Qed.

End contents.

End Rings.
