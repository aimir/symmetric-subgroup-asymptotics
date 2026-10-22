import SymmetricSubgroupAsymptotics.CFSGTwistedDRationalDiagramIntertwining
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIntegralRealization

/-! Equivariance on the ORIGINAL integral Serre lattice and its tensor
base change. Integral equality follows from rational casts, not from
faithfulness of the natural representation or division in finite fields. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDIntegralDiagramIntertwining
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGSerreDiagram CFSG.Models.Chevalley CFSGSerreSquareZeroMatrix

def integerFlip (s : ℕ) : Mat ℤ (s + 2) ≃ₐ[ℤ] Mat ℤ (s + 2) :=
  Matrix.reindexAlgEquiv ℤ ℤ (CFSGOrthogonalDGenerationForkTorus.flip s)

theorem integerFlip_cast (K : Type) [Field K] (s : ℕ) (M : Mat ℤ (s + 2)) :
    (Int.castRingHom K).mapMatrix (integerFlip s M) =
      flipAlgebra K s ((Int.castRingHom K).mapMatrix M) := by
  ext i j
  rfl

theorem integral_intertwining (s : ℕ) (x : integralLattice (CartanMatrix.D (s + 4))) :
    integerFlip (s + 2) (integralOrthogonalRepresentation (s + 4) (by omega) x) =
      integralOrthogonalRepresentation (s + 4) (by omega)
        (integralEquiv (CartanMatrix.D (s + 4)) (dPermutation (s + 4))
          (d_preserves (s + 4)) x) := by
  apply integerCast_injective (Index (s + 4))
  change (Int.castRingHom ℚ).mapMatrix (integerFlip (s + 2)
    (integralRepresentation (realizationData (s + 4) (by omega)) x)) =
      (Int.castRingHom ℚ).mapMatrix (integralRepresentation
        (realizationData (s + 4) (by omega))
        (integralEquiv (CartanMatrix.D (s + 4)) (dPermutation (s + 4))
          (d_preserves (s + 4)) x))
  rw [integerFlip_cast]
  change flipAlgebra ℚ (s + 2) (integerCast (Index (s + 4))
    (integralRepresentation (realizationData (s + 4) (by omega)) x)) =
      integerCast (Index (s + 4)) (integralRepresentation
        (realizationData (s + 4) (by omega))
        (integralEquiv (CartanMatrix.D (s + 4)) (dPermutation (s + 4))
          (d_preserves (s + 4)) x))
  rw [integralRepresentation_cast, integralRepresentation_cast]
  change flipAlgebra ℚ (s + 2) (rationalOrthogonalRepresentation (s + 4) (by omega) x.val) =
    rationalOrthogonalRepresentation (s + 4) (by omega)
      (rationalEquiv (CartanMatrix.D (s + 4)) (dPermutation (s + 4))
        (d_preserves (s + 4)) x.val)
  exact CFSGTwistedDRationalDiagramIntertwining.rational_intertwining s x.val

theorem baseChange_intertwining (K : Type) [Field K] (s : ℕ)
    (x : Space (CartanMatrix.D (s + 4)) K) :
    flipAlgebra K (s + 2) (orthogonalBaseChange K (s + 4) (by omega) x) =
      orthogonalBaseChange K (s + 4) (by omega)
        (spaceEquiv (CartanMatrix.D (s + 4)) K (dPermutation (s + 4))
          (d_preserves (s + 4)) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    rw [spaceEquiv, LinearEquiv.baseChange_tmul, baseChange_tmul, baseChange_tmul,
      map_smul, ← integerFlip_cast, integral_intertwining]
  | add x y hx hy => simp only [map_add, hx, hy]

end SymmetricSubgroupAsymptotics.CFSGTwistedDIntegralDiagramIntertwining
