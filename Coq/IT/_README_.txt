Inductive types in Homotopy Type Theory: Coq proofs

This repository IT contains Coq proofs formalizing the development of 
inductive types
in the setting of Homotopy Type Theory. 
The files in the folder "univalent_foundations"
are by V. Voevodsky.  
All other files have been created and are maintained by 
S. Awodey,
N. Gambino, and K. Sojakova (awodey@cmu.edu, ngambino@math.unipa.it, kristinas@cmu.edu).

The Coq version used is 8.3pl3.

The main results formalized in the repository are the proofs of the following
statements:
  -- weak 2-types arise as h-initial algebras
  -- weak W-types arise as h-initial algebras
  -- weak natural numbers reduce to weak W-types
  -- second number class reduces to weak W-types
  
The organization is as follows:

1) The folder "univalent_foundations" contains the up-to-date development
   of Voevodsky's Univalent Foundations program, which aims to provide
   computational foundations for mathematics based on homotopically-motivated
   type theories. For our purposes only the following files will be needed:
        -- "Generalities/uuu.v"
        -- "Generalities/uu0.v"
   The above files introduce the identity types, Sigma types, and the (simple) function
   extensionality axiom. Dependent function extensionality is derived as a consequence
   and a homotopy equivalence is established between the types of pointwise vs global
   function equalities.
   
2) The file "identity.v" in the folder "identity" introduces various lemmas concerning
   the basic homotopical properties of propositional equalities and the interaction
   of identity types with other type constructors.
   
3) The folder "inductive_types" contains the definitions of various weak inductive
   types, namely the types Zero, One, Two, Three with 0,1,2,3 constructors respectively;
   the type Sum of weak sums; weak natural numbers and lists; and weak W-types.
   The types are presented in the standard form by giving the formation, introduction,
   elimination, and computation rules (here called beta). The corresponding eta rules
   are derived.

4) The folder "two_is_hinitial" contains the proof that the type Two arises as an
   h-initial algebra. The proof is structured as follows:
         i)   First the analogous simple rules for Two are formulated; the corresponding
	      eta rules are no longer derivable and are stated as axioms. This is done
	      in the file "two_simp.v".
	 ii)  We show that the dependent rules for Two imply the simple ones and
	      vice versa. This is done in the files "simp_implies_dep.v" and
	      "dep_implies_simp.v".
	 iii) The notions of algebra homomorphisms, algebra 2-cells, and homotopy-initial
	      algebras are formulated for Two. It is furthermore shown that two algebra
	      homomorphisms are propositionally equal if and only if there exists an
	      algebra 2-cell between them. This is done in the file "two_algebras.v".
	 iv)  We show that the simple rules for Two are equivalent to the assertion
	      that there exists a homotopy-initial 2-algebra. This is done in the files
	      "simp_implies_hinitial.v" and "hinitial_implies_simp.v".
			  
5) The folder "w_is_hinitial" contains the proof that weak W-types arise as h-initial
   algebras for polynomial functors. The proof is structured as follows:
         i)   First we introduce the notion of polynomial functors and prove a number
	      of useful lemmas. This is done in the file "polynomial_functors.v".
         ii)  We show the main result, i.e. that the dependent rules for W are
              equivalent to the assertion that there exists a homotopy-initial algebra
              for the associated polynomial functor. This is done in the files
              "w_implies_hinitial.v" and "hinitial_implies_w.v".
			  
6) The file "nat_as_w_type.v" in the folder "nat_as_w_type" formalizes the proof that
   weak natural numbers are encodable as weak W-types in the presence of the types
   Zero, One, and (a type-level version of) Two.   
   
7) The file "o2_as_w_type.v" in the folder "nat_as_w_type" formalizes the proof that the
   second number class is encodable as a weak W-type in the presence of the types
   Zero, One, Two, and (a type-level version of) Three.

Order of compilation:

1) univalent_foundations:
         1.1) Generalities/uuu.v
	 2.1) Generalities/uu0.v
2) identity/identity.v
3) inductive_types/*.v
4) two_is_hinitial: 
         4.1) two_simp.v, two_algebras.v
	 4.2) dep_implies_simp.v, simp_implies_dep.v,
	      simp_implies_hinitial.v, hinitial_implies_simp.v
5) w_is_hinitial:
         5.1) polynomial_functors.v
	 5.2) hinitial_implies_w.v, w_implies_hinitial.v
6) nat_as_w_type:
         6.1) nat_as_w_type.v
	 6.2) o2_as_w_type.v
	 
Repository last updated : 17 Jan 2012.