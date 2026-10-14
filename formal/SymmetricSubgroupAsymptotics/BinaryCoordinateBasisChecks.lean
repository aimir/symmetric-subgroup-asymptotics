import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates

/-! Build a reversible binary chart from basis and dual masks by checking
only basis vectors. No quantification over all binary vectors is needed. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

def binaryMaskInclusion (w d : ℕ) (basis : Fin d → ℕ) :
    (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2) :=
  (binaryRectangularMatrixOfColumnMasks w d basis).mulVecLin

def binaryMaskCoordinates (w d : ℕ) (dual : Fin d → ℕ) :
    (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) :=
  (binaryRectangularMatrixOfColumnMasks w d dual).transpose.mulVecLin

/-- A `d × d` inverse equation on displayed basis vectors suffices for a
reversible chart with `d` coordinates. -/
def binaryCoordinateSpaceOfBasisMasks (w d : ℕ) (basis dual : Fin d → ℕ)
    (h : ∀ i : Fin d, binaryMaskCoordinates w d dual
      (binaryMaskInclusion w d basis (Pi.single i 1)) = Pi.single i 1) :
    BinaryCoordinateSpace w d where
  inclusion := binaryMaskInclusion w d basis
  coordinates := binaryMaskCoordinates w d dual
  left_inverse v := by
    have hm : (binaryMaskCoordinates w d dual).comp
        (binaryMaskInclusion w d basis) = LinearMap.id := by
      apply (Pi.basisFun (ZMod 2) (Fin d)).ext
      intro i
      rw [Pi.basisFun_apply]
      exact h i
    exact LinearMap.congr_fun hm v

end SymmetricSubgroupAsymptotics

end
