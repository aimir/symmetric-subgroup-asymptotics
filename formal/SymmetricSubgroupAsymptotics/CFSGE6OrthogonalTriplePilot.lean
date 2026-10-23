import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalTripleAdjoint
import SymmetricSubgroupAsymptotics.CFSGFFourE6Generators

/-! A concrete D4 outer triple inside the actual E6 Geck model.
Arbitrary rational coefficients are retained. This proves adjoint-four
truncation on the actual generated Lie algebra; it does NOT assert that
the matrix cube vanishes or install quadratic data for an orbit of size three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGE6OrthogonalTriplePilot
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoGeckColumns
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckHomogeneousSpan CFSGGradedMatrixSupport
open CFSGFFourSerreMatrices
local instance triplePilotDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

def d4OuterNode : Fin 3→Fin 6 := ![2,4,1]

theorem d4Outer_orthogonal (i j : Fin 3) (hij : i≠j) :
    integerPairing CartanMatrix.E₆ (E6Index (d4OuterNode i):Roots CartanMatrix.E₆).val
      (E6Index (d4OuterNode j):Roots CartanMatrix.E₆).val=0 := by
  change CartanMatrix.E₆.toBilin'
    (Pi.single (d4OuterNode i) (1:ℤ) : Fin 6→ℤ)
    (Pi.single (d4OuterNode j) (1:ℤ) : Fin 6→ℤ)=0
  rw [Matrix.toBilin'_single]
  fin_cases i <;> fin_cases j
  all_goals first | exact False.elim (hij rfl) | decide

def positiveOrbit (coeff : Fin 3→ℚ) : Mat := ∑i,coeff i • e6E (d4OuterNode i)
def negativeOrbit (coeff : Fin 3→ℚ) : Mat := ∑i,coeff i • e6F (d4OuterNode i)

theorem positiveOrbit_ad_four (coeff : Fin 3→ℚ) (X : Mat)
    (hX : X∈RootPairing.GeckConstruction.lieAlgebra E6Base) :
    (LieAlgebra.ad ℚ Mat (positiveOrbit coeff)^4) X=0 := by
  let T := RootPairing.GeckConstruction.lieAlgebra E6Base
  change (LieAlgebra.ad ℚ Mat (∑i,coeff i • e6E (d4OuterNode i))^4) X=0
  apply CFSGNormTwoCoordinateOrthogonalTripleAdjoint.orthogonal_three_ad_four
    CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
    CartanMatrix.E₆_off_diag_nonpos (fun i=>E6Index (d4OuterNode i))
    (d4Outer_orthogonal 0 1 (by decide)) (d4Outer_orthogonal 0 2 (by decide))
    (d4Outer_orthogonal 1 2 (by decide)) (fun i=>coeff i • e6E (d4OuterNode i)) _ _ X hX
  · intro i
    exact T.smul_mem (coeff i) (RootPairing.GeckConstruction.e_mem_lieAlgebra (E6Index (d4OuterNode i)))
  · intro i x y hxy
    dsimp only
    rw [Matrix.smul_apply]
    have hh := rational_E_homogeneous CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base (E6Index (d4OuterNode i)) x y hxy
    change coeff i • RootPairing.GeckConstruction.e (E6Index (d4OuterNode i)) x y=0
    rw [hh,smul_zero]

theorem negativeOrbit_ad_four (coeff : Fin 3→ℚ) (X : Mat)
    (hX : X∈RootPairing.GeckConstruction.lieAlgebra E6Base) :
    (LieAlgebra.ad ℚ Mat (negativeOrbit coeff)^4) X=0 := by
  let T := RootPairing.GeckConstruction.lieAlgebra E6Base
  let a : Fin 3→Roots CartanMatrix.E₆ := fun i=>negativeIndex CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite (E6Index (d4OuterNode i))
  have ha (i j : Fin 3) (hij : i≠j) : integerPairing CartanMatrix.E₆ (a i).val (a j).val=0 := by
    simp only [a,negative_val,map_neg,LinearMap.neg_apply,neg_neg]
    exact d4Outer_orthogonal i j hij
  change (LieAlgebra.ad ℚ Mat (∑i,coeff i • e6F (d4OuterNode i))^4) X=0
  apply CFSGNormTwoCoordinateOrthogonalTripleAdjoint.orthogonal_three_ad_four
    CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
    CartanMatrix.E₆_off_diag_nonpos a (ha 0 1 (by decide)) (ha 0 2 (by decide))
    (ha 1 2 (by decide)) (fun i=>coeff i • e6F (d4OuterNode i)) _ _ X hX
  · intro i
    exact T.smul_mem (coeff i) (RootPairing.GeckConstruction.f_mem_lieAlgebra (E6Index (d4OuterNode i)))
  · intro i x y hxy
    dsimp only
    rw [Matrix.smul_apply]
    have hh : Supported (latticeWeight CartanMatrix.E₆ CartanMatrix.E₆_transpose
        E6_positive_definite E6Base) (fun v=>v+(a i).val) (e6F (d4OuterNode i)) := by
      simpa only [a,negative_val] using rational_F_homogeneous CartanMatrix.E₆
        CartanMatrix.E₆_transpose E6_positive_definite E6Base (E6Index (d4OuterNode i))
    rw [hh x y hxy,smul_zero]

end SymmetricSubgroupAsymptotics.CFSGE6OrthogonalTriplePilot
