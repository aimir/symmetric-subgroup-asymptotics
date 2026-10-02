import SymmetricSubgroupAsymptotics.PrimitiveCompositionBoundedRows2To11
import SymmetricSubgroupAsymptotics.PrimitiveCompositionBoundedRows12To20
import SymmetricSubgroupAsymptotics.PrimitiveCompositionBoundedRows21To27
import SymmetricSubgroupAsymptotics.PrimitiveCompositionBoundedRows28To36
import SymmetricSubgroupAsymptotics.PrimitiveCompositionBoundedRows37To44

/-!
# Complete bounded primitive three-tenths receipt

The five independently checked degree chunks are assembled here.  Each chunk
checks distinct catalogue locators and its disjoint degree interval; the
aggregator derives the total of 336 rows from their checked sizes without one
large evaluator reduction.
-/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- All PrimGrp rows in degrees 2 through 44, in catalogue order. -/
def primitiveCompositionBoundRows : Array PrimitiveCompositionBoundRow :=
  primitiveCompositionBoundRows2To11 ++
  primitiveCompositionBoundRows12To20 ++
  primitiveCompositionBoundRows21To27 ++
  primitiveCompositionBoundRows28To36 ++
  primitiveCompositionBoundRows37To44

theorem primitiveCompositionBoundRows_size :
    primitiveCompositionBoundRows.size = 336 := by
  simp [primitiveCompositionBoundRows,
    primitiveCompositionBoundRows2To11_size,
    primitiveCompositionBoundRows12To20_size,
    primitiveCompositionBoundRows21To27_size,
    primitiveCompositionBoundRows28To36_size,
    primitiveCompositionBoundRows37To44_size]

/-- Typed access to the complete receipt. -/
def primitiveCompositionBoundRow (i : Fin 336) : PrimitiveCompositionBoundRow :=
  primitiveCompositionBoundRows[i.val]'(by
    rw [primitiveCompositionBoundRows_size]
    exact i.isLt)

end SymmetricSubgroupAsymptotics
