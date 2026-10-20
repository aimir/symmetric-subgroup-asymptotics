import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep0
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep1
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep2
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep3
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep4
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep5
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep6
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep7
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep8
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep9
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep10
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep11
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep12
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep13
import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupStep14

/-! Actual exhaustive subgroup conjugacy coverage from the checked local
adjunction equations. No subgroup-classification premise is imported. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupCoverage
open GeneralThreeTwoCayley GeneralThreeTwoSubgroupRows
local instance : Group Source := group

theorem step (i : Fin 15) (g : Source) : ∃ j : Fin 15, ∃ c : Source,
    MulAut.conj c • (rows i ⊔ Subgroup.closure {g}) = rows j := by
  fin_cases i
  · exact GeneralThreeTwoSubgroupStep0.step g
  · exact GeneralThreeTwoSubgroupStep1.step g
  · exact GeneralThreeTwoSubgroupStep2.step g
  · exact GeneralThreeTwoSubgroupStep3.step g
  · exact GeneralThreeTwoSubgroupStep4.step g
  · exact GeneralThreeTwoSubgroupStep5.step g
  · exact GeneralThreeTwoSubgroupStep6.step g
  · exact GeneralThreeTwoSubgroupStep7.step g
  · exact GeneralThreeTwoSubgroupStep8.step g
  · exact GeneralThreeTwoSubgroupStep9.step g
  · exact GeneralThreeTwoSubgroupStep10.step g
  · exact GeneralThreeTwoSubgroupStep11.step g
  · exact GeneralThreeTwoSubgroupStep12.step g
  · exact GeneralThreeTwoSubgroupStep13.step g
  · exact GeneralThreeTwoSubgroupStep14.step g

theorem complete (U : Subgroup Source) :
    ∃ i : Fin 15, ∃ c : Source, MulAut.conj c • U = rows i :=
  FiniteSubgroupAdjunctionCoverage.complete rows ⟨0, row_zero⟩ step U

end SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupCoverage
end
