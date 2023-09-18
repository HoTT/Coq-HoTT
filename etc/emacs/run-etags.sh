#!/bin/sh
etags --language=none -r '/^[ \t]*\(\(Local\|Global\|Cumulative\|NonCumulative\|Monomorphic\|Polymorphic\|Private\)[ \t]+\)*\(Axiom\|Theorem\|Class\|Instance\|Let\|Ltac\|Definition\|Lemma\|Record\|Remark\|Structure\|Fixpoint\|Fact\|Corollary\|Inductive\|CoInductive\|Proposition\)[ \t]+\([a-zA-Z0-9_'\'']+\)/\4/' -r '/^[ \t]*\([a-zA-Z0-9_'\'']+\)[ \t]*:/\1/' "$@"
