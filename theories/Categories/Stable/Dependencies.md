# Module Dependency List

## 📘 Core Files

- **ZeroObjects.v**  
  *Requires: None*

- **ZeroMorphismLemmas.v**  
  *Requires: ZeroObjects*

## ➕ Additive & Structural Foundations

- **Biproducts.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas*

- **AdditiveCategories.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, Biproducts*

- **OppositeCategories.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, Biproducts, AdditiveCategories*

## 🧱 Pre-stable & Semi-stable Categories

- **PreStableCategories.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, Biproducts, AdditiveCategories*

- **SemiStableCategories.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, Biproducts, AdditiveCategories, PreStableCategories*

## 🔼 Opposites & Rotations

- **OppositePreStable.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, Biproducts, AdditiveCategories, PreStableCategories, OppositeCategories*

- **TriangleRotation.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, AdditiveCategories, PreStableCategories, Triangles, TriangleMorphisms*

## 🔺 Triangles & Related Structures

- **Triangles.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, AdditiveCategories, PreStableCategories*

- **TriangleMorphisms.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, AdditiveCategories, PreStableCategories, Triangles*

- **PreStableCofiber.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, Biproducts, AdditiveCategories, PreStableCategories, Triangles*

## ⚙️ Transformations & Lemmas

- **ZeroTransformations.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, AdditiveCategories, PreStableCategories, SemiStableCategories*

- **OctahedralLemmas.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, AdditiveCategories, PreStableCategories, Triangles, PreStableCofiber*

## 🧩 Proper and Advanced Structures

- **ProperStableCategories.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, Biproducts, AdditiveCategories, PreStableCategories, SemiStableCategories, OppositeCategories, OppositePreStable*

- **SuspensionFixedPoints.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, AdditiveCategories, PreStableCategories, ProperStableCategories, SemiStableCategories*

- **AdvancedStructures.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, Biproducts, AdditiveCategories, PreStableCategories, ProperStableCategories, SemiStableCategories, OppositeCategories, OppositePreStable*

## 🔄 Axioms and Triangulated Theory

- **OctahedralAxiom.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, AdditiveCategories, PreStableCategories, Triangles, PreStableCofiber, OctahedralLemmas*

- **TriangulatedAxiomsTR123.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, AdditiveCategories, PreStableCategories, Triangles, TriangleMorphisms, TriangleRotation, PreStableCofiber*

- **StableTriangulated.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, AdditiveCategories, PreStableCategories, PreStableCofiber, Triangles, TriangleMorphisms, TriangleRotation, TriangulatedAxiomsTR123, OctahedralLemmas, OctahedralAxiom, ProperStableCategories*

## ♻️ Duality Theory

- **DualityPrinciple.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, Biproducts, AdditiveCategories, PreStableCategories, SemiStableCategories, ProperStableCategories, Triangles, TriangleMorphisms, OppositeCategories, OppositePreStable*

- **DualityApplications.v**  
  *Requires: ZeroObjects, ZeroMorphismLemmas, AdditiveCategories, PreStableCategories, ProperStableCategories, Triangles, TriangleMorphisms, TriangleRotation, OppositeCategories, OppositePreStable, DualityPrinciple, SemiStableCategories*
