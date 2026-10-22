import SymmetricSubgroupAsymptotics.CFSGFFourOrthogonalRoots
import SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices

/-! Actual quadratic coefficients for folded F4 positive roots.
For each orthogonal pair the coefficient is d_i+d_j+E_i E_j;
no vanishing fourth coefficient on arbitrary matrices is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
local instance fFourQuadraticPositiveDecEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

def positiveSecond (i : Fin 4) : Mat :=
  ![e6Second 0+e6Second 5+e6E 0*e6E 5,
    e6Second 2+e6Second 4+e6E 2*e6E 4,e6Second 3,e6Second 1] i

private theorem pair_identities (i j : Fin 6) (hc : CartanMatrix.E₆ i j=0)
    (hc' : CartanMatrix.E₆ j i=0) :
    (e6E i+e6E j)*(e6E i+e6E j)=
        (e6Second i+e6Second j+e6E i*e6E j)+(e6Second i+e6Second j+e6E i*e6E j) ∧
      (e6E i+e6E j)*(e6Second i+e6Second j+e6E i*e6E j)=0 ∧
      (e6Second i+e6Second j+e6E i*e6E j)*(e6E i+e6E j)=0 ∧
      (e6Second i+e6Second j+e6E i*e6E j)*(e6Second i+e6Second j+e6E i*e6E j)=0 :=
  CFSGQuadraticOrthogonalSum.identities (e6E i) (e6E j) (e6Second i) (e6Second j)
    (e6_commute_of_cartan_zero i j hc) (e6_square i) (e6_square j)
    (e6_mul_second i) (e6_second_mul i) (e6_mul_second j) (e6_second_mul j)
    (e6_mul_other_second i j hc') (e6_mul_other_second j i hc)

private theorem singleton_identities (i : Fin 6) :
    e6E i*e6E i=e6Second i+e6Second i ∧ e6E i*e6Second i=0 ∧
      e6Second i*e6E i=0 ∧ e6Second i*e6Second i=0 := by
  refine ⟨e6_square i,e6_mul_second i,e6_second_mul i,?_⟩
  simpa only [e6Second,pow_two] using CFSGNormTwoGeckTruncation.second_square
    CartanMatrix.E₆ CartanMatrix.E₆_transpose
    CFSGExceptionalCartanPositiveDefinite.E6_positive_definite
    CFSGExceptionalNormTwoBases.E6Base (CFSGExceptionalNormTwoBases.E6Index i)

theorem positive_quadratic (i : Fin 4) :
    positive i*positive i=positiveSecond i+positiveSecond i ∧
      positive i*positiveSecond i=0 ∧ positiveSecond i*positive i=0 ∧
      positiveSecond i*positiveSecond i=0 := by
  fin_cases i
  · exact pair_identities 0 5 (by decide) (by decide)
  · exact pair_identities 2 4 (by decide) (by decide)
  · exact singleton_identities 3
  · exact singleton_identities 1

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
