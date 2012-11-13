## Reducing all HIT’s to 1-HIT’s ##

For a while, Mike Shulman and I (and others) have wondered on and off whether it might be possible to represent all HIT’s (i.e. with constructors of arbitrary dimension) just using 1-HIT’s (0- and 1-cell constructors only), somewhat analogously with the reduction of all standard inductive types to a few specific instances — W-types, Id-types, etc.  The other week we realised that yes, it can be done, and quite prettily.  To start you off, here are a couple of 2-cells, represented using just 0- and 1-cells:

http://www.flickr.com/photos/ne/3893796919/
http://www.flickr.com/photos/velo_city/32011058/
http://www.flickr.com/photos/27376974@N02/4429320063/

And here’s a 3-cell similarly represented:

http://www.flickr.com/photos/jpott/2409337382/

As a topologist would say it: the (n+1)-disc is the cone on the n-sphere.  To implement this logically, we first construct the spheres as a 1-HIT, using iterated suspension:

    Inductive Sphere : Nat -> Type :=
      | north (n:Nat) : Sphere n
      | south (n:Nat) : Sphere n
      | longitude (n:Nat) (x:Sphere n) : Paths (north (n+1)) (south (n+1)).

Then we define (it’s a little fiddly, but do-able) a way to, given any parallel pair `s`, `t` of *n*-cells in a space `X`, represent them as a map `rep s t : Sphere n -> X`.  (I’m suppressing a bunch of implicit arguments for all the lower dimensional sources/targets.)

Now, whenever we have an (n+1)-cell constructor in a higher inductive type

    HigherInductive X : Type :=
      (…earlier constructors…)
      | constr (a:A) : HigherPaths X (n+1) (constr_s a) (constr_t a) 
      (…later constructors…)

we replace it by a pair of constructors

      | constr_hub (a:A) : X
      | constr_spoke (a:A) (t : Sphere n) : Paths X (rep (s a) (t a)) (constr_hub a)

Assuming functional extensionality, we can give from this a derived term `constr' : forall (a:A), HigherPaths (n+1) (constr_s a) (constr_t a)`; we use this for all occurences of `constr` in later constructors.  The universal property of the modified HIT should then be equivalent to that of the original one.

(Here for readability `X` was non-dependent and `constr` had only one argument; but the general case has no essential extra difficulties.)

What can one gain from this?  Again analogously with the traditional reduction of inductive types to a few special cases, the main use I can imagine is in constructing models: once you’ve modeled 1-HIT’s, arbitrary *n*-HIT’s then come for free.  It also could be a stepping-stone for reducing yet further to a few specific 1-HIT’s… ideas, anyone?

On a side note, while I’m here I’ll take the opportunity to briefly plug two notes I’ve put online recently but haven’t yet advertised much: 

- [Model Structures from Higher Inductive Types], which pretty much does what it says on the tin: giving a second factorisation system on C_T (using [mapping cylinders] for the factorisations), which along with the [Gambino-Garner weak factorisation system] gives C_T most of the structure of a model category — all but the completeness and functoriality conditions.  The weak equivalences are, as one would hope, the [type-theoretic Equiv] we know and love.

- [Univalence in Simplicial Sets], joint with Chris Kapulkin and Vladimir Voevodsky.  This gives essentially the homotopy-theoretic aspects of the construction of the univalent model in simplicial sets, and these aspects only — type theory isn’t mentioned.  Specifically, the main theorems are the construction of a (fibrant) universe that (weakly) classifies fibrations, and the proof that it is (in a homotopy-theoretic sense) univalent.  The results are not new, but are taken from Voevodsky’s [Notes on Type Theory] and Oberwolfach lectures, with some proofs modified; the aim here is to give an accessible and self-contained account of the material.

(Photos above by [ne], [velo_city], [???], and [jpott], via the [flickr Creative Commons pool].  Photos licensed under CC-NonCom-Attrib-NoDerivs.)
