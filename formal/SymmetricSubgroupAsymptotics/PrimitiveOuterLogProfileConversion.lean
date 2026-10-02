import SymmetricSubgroupAsymptotics.PrimitiveOuterLogProfile
import SymmetricSubgroupAsymptotics.PrimitiveOuterOrderNumerics
import SymmetricSubgroupAsymptotics.PrimitiveSemisimpleCompressionProfileData

/-! # Converting the outer-log profile to primitive compression data -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveSemisimpleOuterLogProfile

variable {L : Type} [Group L] {r : ℕ}
  (C : PrimitiveSemisimpleOuterLogProfile L r)

/-- Replace the single logarithmic literature input by the two exact natural
inequalities consumed by the primitive compression API. -/
noncomputable def toCompressionProfile :
    PrimitiveSemisimpleCompressionProfile L r where
  E := C.E
  E_normal := C.E_normal
  chart := C.chart
  factorCount := C.factorCount
  factorCount_pos := C.factorCount_pos
  leastIndex := C.leastIndex
  leastIndex_two_le := (by norm_num : 2 ≤ 5).trans C.leastIndex_five_le
  outerOrder := C.outerOrder
  outerOrder_pos := C.outerOrder_pos
  quotientAction := C.quotientAction
  quotientAction_injective := C.quotientAction_injective
  primitive_index_lower := C.primitive_index_lower
  multiple_factor_base := primitive_outerOrder_square_bound
    C.leastIndex C.outerOrder C.leastIndex_five_le C.outerOrder_log_bound
  large_simple_base := fun hell => primitive_outerOrder_large_simple_bound
    C.leastIndex C.outerOrder hell C.outerOrder_log_bound

end PrimitiveSemisimpleOuterLogProfile
end SymmetricSubgroupAsymptotics

end
