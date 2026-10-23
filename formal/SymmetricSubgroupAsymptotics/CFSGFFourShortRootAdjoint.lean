import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrthogonalAdjoint
import SymmetricSubgroupAsymptotics.CFSGFFourRationalImage

/-! Both literal short F4 generators are sums on orthogonal E6 node
orbits. Their adjoint cubes vanish on the actual E6 generated Lie algebra,
for both signs; the original folded rational image lies in that algebra. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoGeckColumns
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckHomogeneousSpan
local instance shortRootAdjointDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

private theorem e6_simple_orthogonal (i j : Fin 6) (hij : CartanMatrix.E₆ i j=0) :
    integerPairing CartanMatrix.E₆ (E6Index i:Roots CartanMatrix.E₆).val
      (E6Index j:Roots CartanMatrix.E₆).val=0 := by
  change CartanMatrix.E₆.toBilin' (Pi.single i (1:ℤ) : Fin 6→ℤ)
    (Pi.single j (1:ℤ) : Fin 6→ℤ)=0
  rw [Matrix.toBilin'_single]
  exact hij

theorem e6_orthogonal_positive_ad_cube (i j : Fin 6) (hij : CartanMatrix.E₆ i j=0)
    (X : Mat) (hX : X∈RootPairing.GeckConstruction.lieAlgebra E6Base) :
    ⁅e6E i+e6E j,⁅e6E i+e6E j,⁅e6E i+e6E j,X⁆⁆⁆=0 := by
  apply CFSGNormTwoCoordinateOrthogonalAdjoint.orthogonal_ad_cube
    CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
    CartanMatrix.E₆_off_diag_nonpos (E6Index i) (E6Index j)
    (e6_simple_orthogonal i j hij) (e6E i) (e6E j)
    (RootPairing.GeckConstruction.e_mem_lieAlgebra (E6Index i))
    (RootPairing.GeckConstruction.e_mem_lieAlgebra (E6Index j))
    (rational_E_homogeneous CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base (E6Index i))
    (rational_E_homogeneous CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base (E6Index j)) X hX

theorem e6_orthogonal_negative_ad_cube (i j : Fin 6) (hij : CartanMatrix.E₆ i j=0)
    (X : Mat) (hX : X∈RootPairing.GeckConstruction.lieAlgebra E6Base) :
    ⁅e6F i+e6F j,⁅e6F i+e6F j,⁅e6F i+e6F j,X⁆⁆⁆=0 := by
  let a : Roots CartanMatrix.E₆ := negativeIndex CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite (E6Index i)
  let b : Roots CartanMatrix.E₆ := negativeIndex CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite (E6Index j)
  have hab : integerPairing CartanMatrix.E₆ a.val b.val=0 := by
    simp only [a,b,negative_val,map_neg,LinearMap.neg_apply,neg_neg]
    exact e6_simple_orthogonal i j hij
  apply CFSGNormTwoCoordinateOrthogonalAdjoint.orthogonal_ad_cube
    CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
    CartanMatrix.E₆_off_diag_nonpos a b hab (e6F i) (e6F j)
    (RootPairing.GeckConstruction.f_mem_lieAlgebra (E6Index i))
    (RootPairing.GeckConstruction.f_mem_lieAlgebra (E6Index j)) _ _ X hX
  · simpa only [a,negative_val] using
      rational_F_homogeneous CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base (E6Index i)
  · simpa only [b,negative_val] using
      rational_F_homogeneous CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base (E6Index j)

theorem short_positive_ad_cube (i : Fin 4) (hi : i=0 ∨ i=1)
    (X : Mat) (hX : X∈RootPairing.GeckConstruction.lieAlgebra E6Base) :
    ⁅positive i,⁅positive i,⁅positive i,X⁆⁆⁆=0 := by
  rcases hi with rfl|rfl
  · exact e6_orthogonal_positive_ad_cube 0 5 (by decide) X hX
  · exact e6_orthogonal_positive_ad_cube 2 4 (by decide) X hX

theorem short_negative_ad_cube (i : Fin 4) (hi : i=0 ∨ i=1)
    (X : Mat) (hX : X∈RootPairing.GeckConstruction.lieAlgebra E6Base) :
    ⁅negative i,⁅negative i,⁅negative i,X⁆⁆⁆=0 := by
  rcases hi with rfl|rfl
  · exact e6_orthogonal_negative_ad_cube 0 5 (by decide) X hX
  · exact e6_orthogonal_negative_ad_cube 2 4 (by decide) X hX

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
