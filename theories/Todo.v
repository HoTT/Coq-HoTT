Ltac todo g := let goalname := fresh "goal" in assert (goalname : g) by admit; exact goalname.
