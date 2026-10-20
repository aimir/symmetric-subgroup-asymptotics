import SymmetricSubgroupAsymptotics.GeneralThreeTwoSubgroupCoverage
import SymmetricSubgroupAsymptotics.FiniteSubgroupAdjunctionTransport

/-! Exact coverage of actual GL(3,2) subgroups, retaining the literal image
of every certified row under the actual matrix equivalence. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.GeneralThreeTwoActualSubgroupCoverage

open GeneralThreeTwoCayley
local instance : Group Source := group

def rows (i : Fin 15) : Subgroup GeneralThreeTwoMatrixEncoding.Ambient :=
  (GeneralThreeTwoSubgroupRows.rows i).map matrixEquiv.toMonoidHom

theorem complete (K : Subgroup GeneralThreeTwoMatrixEncoding.Ambient) :
    ∃ i : Fin 15, ∃ c : GeneralThreeTwoMatrixEncoding.Ambient,
      MulAut.conj c • K = rows i :=
  FiniteSubgroupAdjunctionCoverage.complete_of_equiv
    GeneralThreeTwoSubgroupRows.rows matrixEquiv
    GeneralThreeTwoSubgroupCoverage.complete K

end SymmetricSubgroupAsymptotics.GeneralThreeTwoActualSubgroupCoverage

end
