import SymmetricSubgroupAsymptotics.CFSGTwistedDIntegralDiagramIntertwining
import SymmetricSubgroupAsymptotics.CFSGSerreMatrixFieldIntertwining

/-! The combined original diagram--field action intertwines the actual
natural D realization, with the original lattice/tensor carrier retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFieldDiagramIntertwining
open CFSG.Models.Chevalley CFSGOrthogonalDSerreMatrices CFSGSerreDiagram
open CFSGTwistedDIntegralDiagramIntertwining CFSGTwistedDNaturalFieldTwist

theorem baseChange_field_diagram (K : Type) [Field K] (s : ℕ) (σ : K ≃+* K)
    (x : Space (CartanMatrix.D (s + 4)) K) :
    orthogonalBaseChange K (s + 4) (by omega)
      (spaceEquiv (CartanMatrix.D (s + 4)) K (dPermutation (s + 4)) (d_preserves (s + 4))
        (CFSGSerreField.semilinearEquiv (CartanMatrix.D (s + 4)) K σ x)) =
      matrixTwist K (s + 2) σ (orthogonalBaseChange K (s + 4) (by omega) x) := by
  rw [← baseChange_intertwining]
  change CFSGOrthogonalDGenerationForkTorus.flipAlgebra K (s + 2)
    (CFSGSerreSquareZeroMatrix.baseChange (realizationData (s + 4) (by omega)) K
      (CFSGSerreField.semilinearEquiv (CartanMatrix.D (s + 4)) K σ x)) = _
  rw [CFSGSerreSquareZeroMatrix.baseChange_semilinear]
  rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedDFieldDiagramIntertwining
