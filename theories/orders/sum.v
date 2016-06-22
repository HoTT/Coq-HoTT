Require Import
  HoTTClasses.interfaces.canonical_names
  HoTTClasses.interfaces.orders.

Section contents.
Universe U.


Global Instance Empty_lt : Lt@{U U} Empty@{U}.
Proof. intros []. Defined.

Global Instance Unit_lt : Lt Unit@{U} := fun _ _ => Empty@{U}.

Global Instance empty_tricho : Trichotomy@{U U U} (_:Lt Empty).
Proof.
intros [].
Qed.

Global Instance unit_tricho : Trichotomy@{U U U} (_:Lt Unit).
Proof.
intros [] [];auto.
Defined.

Context `{Alt : Lt@{U U} A} `{Blt : Lt@{U U} B}.

Global Instance sum_lt : Lt@{U U} (A + B) | 2
  := fun s1 s2 =>
  match s1, s2 with
  | inl a1, inl a2 => a1 < a2
  | inr b1, inr b2 => b1 < b2
  | inl _, inr _ => Unit@{U}
  | inr _, inl _ => Empty@{U}
  end.

Global Instance sum_tricho `{!Trichotomy@{U U U} Alt} `{!Trichotomy@{U U U} Blt}
  : Trichotomy@{U U U} sum_lt.
Proof.
hnf. intros [a1|b1] [a2|b2];simpl.
- destruct (trichotomy _ a1 a2) as [?|[?|?]];auto.
- auto.
- auto.
- destruct (trichotomy _ b1 b2) as [?|[?|?]];auto.
Defined.

End contents.
