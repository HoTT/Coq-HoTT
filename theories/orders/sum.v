Require Import
  HoTTClasses.interfaces.canonical_names
  HoTTClasses.interfaces.orders.

Instance sum_lt `{Lt A} `{Lt B} : Lt (A + B) | 2
  := fun s1 s2 =>
  match s1, s2 with
  | inl a1, inl a2 => a1 < a2
  | inr b1, inr b2 => b1 < b2
  | inl _, inr _ => Unit
  | inr _, inl _ => Empty
  end.

Instance sum_tricho `{Alt : Lt A} `{Blt : Lt B}
  `{!Trichotomy (_:Lt A)} `{!Trichotomy (_:Lt B)}
  : Trichotomy (_:Lt (A+B)).
Proof.
hnf. intros [a1|b1] [a2|b2];simpl.
- destruct (trichotomy _ a1 a2) as [?|[?|?]];auto.
- auto.
- auto.
- destruct (trichotomy _ b1 b2) as [?|[?|?]];auto.
Defined.

Instance Empty_lt : Lt Empty.
Proof. intros []. Defined.

Instance Unit_lt : Lt Unit := fun _ _ => Empty.

Instance empty_tricho : Trichotomy (_:Lt Empty).
Proof.
intros [].
Qed.

Instance unit_tricho : Trichotomy (_:Lt Unit).
Proof.
intros [] [];auto.
Defined.
