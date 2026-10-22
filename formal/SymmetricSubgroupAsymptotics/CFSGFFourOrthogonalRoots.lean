import SymmetricSubgroupAsymptotics.CFSGFFourE6Generators
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalColumns
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTruncation
import SymmetricSubgroupAsymptotics.CFSGQuadraticOrthogonalSum

/-! The two nonsingleton E6 diagram orbits are pairs of actual commuting
root operators with zero mixed second columns. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
local instance fFourOrthogonalRootsDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

def e6Second (i : Fin 6) : Mat :=
  CFSGNormTwoGeckQuadratic.secondMatrix CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base (E6Index i)

theorem e6_commute_of_cartan_zero (i j : Fin 6) (hc : CartanMatrix.E₆ i j=0) :
    Commute (e6E i) (e6E j) := by
  have hh := CFSGGeckSerreRepresentation.serreE E6Base E6Index i j
  rw [E6_cartan,hc] at hh
  have hz : ⁅e6E i,e6E j⁆=0 := by
    simpa only [neg_zero,Int.toNat_zero,pow_zero,Module.End.one_apply] using hh
  exact sub_eq_zero.mp (by simpa only [Ring.lie_def] using hz)

theorem e6_mul_other_second (i j : Fin 6) (hc : CartanMatrix.E₆ j i=0) :
    e6E i*e6Second j=0 := by
  apply CFSGNormTwoGeckOrthogonalColumns.E_mul_second_of_pairing_zero
    CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base
      (E6Index i) (E6Index j)
  rw [CFSGNormTwoGeckOrthogonalColumns.integerPairing_eq_cartan]
  have hh := congrFun (congrFun E6_cartan j) i
  change E6Base.cartanMatrix (E6Index i) (E6Index j)=CartanMatrix.E₆ j i at hh
  exact hh.trans hc

theorem e6_square (i : Fin 6) : e6E i*e6E i=e6Second i+e6Second i := by
  simpa only [e6E,CFSGGeckSerreRepresentation.E,e6Second,pow_two,two_smul] using
    CFSGNormTwoGeckQuadratic.E_square CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base (E6Index i)

theorem e6_mul_second (i : Fin 6) : e6E i*e6Second i=0 :=
  CFSGNormTwoGeckTruncation.E_mul_second CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base (E6Index i)
theorem e6_second_mul (i : Fin 6) : e6Second i*e6E i=0 :=
  CFSGNormTwoGeckTruncation.second_mul_E CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base (E6Index i)

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
