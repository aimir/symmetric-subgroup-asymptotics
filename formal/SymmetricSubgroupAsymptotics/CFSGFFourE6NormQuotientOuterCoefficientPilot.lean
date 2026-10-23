import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientCoefficientPilot

/-! The outer short/long pair uses the same sparse integral entry
certificate as the checked middle pair. Only the selected 26 labels are
reduced; the assertions here are coefficient arithmetic, not group maps. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientOuterCoefficientPilot
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6NormQuotientCoefficientPilot
local instance : Fintype PairIndex := by unfold PairIndex;infer_instance
local instance : DecidableEq PairIndex := by unfold PairIndex;infer_instance

def outerShortFirst (r s:RawIndex) : ℤ := stepEntry 0 r s+stepEntry 5 r s
def outerLongFirst (r s:RawIndex) : ℤ := stepEntry 1 r s
def outerShortSecond (r s:RawIndex) : ℤ :=
  secondEntry 0 r s+secondEntry 5 r s+orthogonalProductEntry 0 5 r s
def outerLongSecond (r s:RawIndex) : ℤ := secondEntry 1 r s

theorem outer_short_quotient_linear_zero : ∀j k:PairIndex,
    quotientCoefficient outerShortFirst j k%2=0 := by decide +kernel

theorem outer_short_quotient_quadratic_eq_long_norm_linear : ∀j k:PairIndex,
    quotientCoefficient outerShortSecond j k%2=normCoefficient outerLongFirst j k%2 := by decide +kernel

theorem outer_long_norm_quadratic_zero : ∀j k:PairIndex,
    normCoefficient outerLongSecond j k%2=0 := by decide +kernel

theorem outer_long_quotient_linear_eq_short_norm_linear : ∀j k:PairIndex,
    quotientCoefficient outerLongFirst j k%2=normCoefficient outerShortFirst j k%2 := by decide +kernel

theorem outer_long_quotient_quadratic_eq_short_norm_quadratic : ∀j k:PairIndex,
    quotientCoefficient outerLongSecond j k%2=normCoefficient outerShortSecond j k%2 := by decide +kernel

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientOuterCoefficientPilot
