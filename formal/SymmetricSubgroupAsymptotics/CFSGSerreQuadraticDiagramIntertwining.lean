import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixOperators
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorExt
import SymmetricSubgroupAsymptotics.CFSGSerreDiagramLattice
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Actual diagram covariance through a quadratic Serre realization.
Matching the original integer generator images proves intertwining on
the universal rational quotient, the SAME original integral lattice,
and every literal tensor base change. No representation injectivity is
assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticDiagramIntertwining
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSerreQuadraticMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]

def reindexLieHom (σ : Equiv.Perm I) : Matrix I I ℚ→ₗ⁅ℚ⁆Matrix I I ℚ where
  __ := (Matrix.reindexAlgEquiv ℚ ℚ σ).toLinearMap
  map_lie' := by
    intro x y
    change Matrix.reindexAlgEquiv ℚ ℚ σ (x*y-y*x)=
      Matrix.reindexAlgEquiv ℚ ℚ σ x*Matrix.reindexAlgEquiv ℚ ℚ σ y-
        Matrix.reindexAlgEquiv ℚ ℚ σ y*Matrix.reindexAlgEquiv ℚ ℚ σ x
    simp only [map_sub,map_mul]

theorem reindex_integerCast (K : Type*) [CommRing K] (σ : Equiv.Perm I) (M : Matrix I I ℤ) :
    (Int.castRingHom K).mapMatrix (Matrix.reindexAlgEquiv ℤ ℤ σ M)=
      Matrix.reindexAlgEquiv K K σ ((Int.castRingHom K).mapMatrix M) := by
  ext i j
  rfl

variable (D : Data A I) (p : Equiv.Perm (Fin n)) (hA : ∀ i j,A (p i) (p j)=A i j)
    (σ : Equiv.Perm I)
    (hgen : ∀ g,Matrix.reindexAlgEquiv ℤ ℤ σ (D.integerGenerator g)=
      D.integerGenerator (nodeRename p g))

include hgen

theorem rational_intertwining (x : RationalLie A) :
    Matrix.reindexAlgEquiv ℚ ℚ σ (D.rational x)=D.rational (rationalEquiv A p hA x) := by
  have he : (reindexLieHom σ).comp D.rational=
      D.rational.comp (rationalEquiv A p hA).toLieHom := by
    apply CFSGSerreGeneratorExt.hom_ext
    intro g
    change Matrix.reindexAlgEquiv ℚ ℚ σ (D.rational (generator A g))=
      D.rational (rationalEquiv A p hA (generator A g))
    rw [rationalEquiv_generator]
    have hg:=congrArg (Int.castRingHom ℚ).mapMatrix (hgen g)
    rw [reindex_integerCast,D.generator_cast,D.generator_cast] at hg
    exact hg
  exact congrArg (fun f : RationalLie A→ₗ⁅ℚ⁆Matrix I I ℚ=>f x) he

theorem integral_intertwining (x : integralLattice A) :
    Matrix.reindexAlgEquiv ℤ ℤ σ (integralRepresentation D x)=
      integralRepresentation D (integralEquiv A p hA x) := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective I
  change (Int.castRingHom ℚ).mapMatrix
    (Matrix.reindexAlgEquiv ℤ ℤ σ (integralRepresentation D x))=
      (Int.castRingHom ℚ).mapMatrix (integralRepresentation D (integralEquiv A p hA x))
  rw [reindex_integerCast]
  change Matrix.reindexAlgEquiv ℚ ℚ σ
    (CFSGSerreSquareZeroMatrix.integerCast I (integralRepresentation D x))=
      CFSGSerreSquareZeroMatrix.integerCast I (integralRepresentation D (integralEquiv A p hA x))
  rw [integralRepresentation_cast,integralRepresentation_cast]
  exact rational_intertwining D p hA σ hgen x.val

theorem baseChange_intertwining (K : Type*) [CommRing K]
    (x : K⊗[ℤ]integralLattice A) :
    Matrix.reindexAlgEquiv K K σ (baseChange D K x)=
      baseChange D K ((integralEquiv A p hA).baseChange ℤ K (integralLattice A) (integralLattice A) x) := by
  induction x using TensorProduct.induction_on with
  | zero=>simp only [map_zero]
  | tmul a x=>
    rw [LinearEquiv.baseChange_tmul,baseChange_tmul,baseChange_tmul,map_smul,
      ←reindex_integerCast,integral_intertwining D p hA σ hgen]
  | add x y hx hy=>simp only [map_add,hx,hy]

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticDiagramIntertwining
