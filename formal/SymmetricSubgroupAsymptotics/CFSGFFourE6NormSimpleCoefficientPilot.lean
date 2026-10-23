import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientOuterCoefficientPilot

/-! Each positive folded simple root has a coefficient-one linear entry
and a zero quadratic entry on the actual norm-pair labels. This selected
finite pilot only evaluates four sets of 26-by-26 sparse entry formulas. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormSimpleCoefficientPilot
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6NormQuotientCoefficientPilot
open CFSGFFourE6NormQuotientOuterCoefficientPilot
local instance : Fintype PairIndex := by unfold PairIndex;infer_instance
local instance : DecidableEq PairIndex := by unfold PairIndex;infer_instance

def firstEntry (i:Fin 4) : RawIndex→RawIndex→ℤ :=
  ![outerShortFirst,shortFirst,longFirst,outerLongFirst] i

def quadraticEntry (i:Fin 4) : RawIndex→RawIndex→ℤ :=
  ![outerShortSecond,shortSecond,longSecond,outerLongSecond] i

theorem exists_norm_linear_witness : ∀i:Fin 4,∃j k:PairIndex,
    normCoefficient (firstEntry i) j k%2=1 ∧
      normCoefficient (quadraticEntry i) j k%2=0 := by decide +kernel

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormSimpleCoefficientPilot
