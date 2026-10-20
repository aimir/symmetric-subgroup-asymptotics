import SymmetricSubgroupAsymptotics.GeneralThreeTwoActualSubgroupCoverage
import SymmetricSubgroupAsymptotics.GeneralThreeTwoMatrixRows

/-! Explicit matrix generators for each exact actual subgroup row. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoRowGenerators

open GeneralThreeTwoCayley GeneralThreeTwoMatrixRows
local instance : Group Source := group

def generators (i : Fin 15) (j : Fin 3) : GeneralThreeTwoMatrixEncoding.Ambient :=
  matrixRows (GeneralThreeTwoSubgroupRows.generators i j).index

theorem rows_eq_closure (i : Fin 15) :
    GeneralThreeTwoActualSubgroupCoverage.rows i =
      Subgroup.closure (Set.range (generators i)) := by
  change (Subgroup.closure (Set.range (GeneralThreeTwoSubgroupRows.generators i))).map
    matrixEquiv.toMonoidHom = _
  rw [MonoidHom.map_closure, ← Set.range_comp']
  apply congrArg Subgroup.closure
  apply congrArg Set.range
  funext j
  exact matrixEquiv_apply _

end SymmetricSubgroupAsymptotics.GeneralThreeTwoRowGenerators

end
