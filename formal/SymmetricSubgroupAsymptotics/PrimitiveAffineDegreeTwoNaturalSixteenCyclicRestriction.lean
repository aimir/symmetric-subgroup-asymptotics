import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenNaturalFiniteRows

/-!
# A small cyclic restriction for the natural degree-sixteen module

The fifteen-cycle fixing the last point is even, hence lies in both natural
tops.  A selected order-fifteen module certificate can therefore be checked
without enumerating `A_16` or `S_16`, then promoted to either ambient top by
`BinaryInvariantCyclicGeneratorBound.uniform_of_comp`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoNaturalSixteenCyclicRestriction

private def generator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 0, 15] :
    Array (Fin 16))[x.val]!
  invFun x := (#[14, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15] :
    Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators : Fin 1 → Equiv.Perm (Fin 16) := ![generator0]

abbrev Top : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range generators)

private theorem generator0_even : generator0 ∈ alternatingGroup (Fin 16) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  native_decide

/-- The selected cyclic restriction lies in the natural alternating top. -/
theorem top_le_alternating : Top ≤ alternatingGroup (Fin 16) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  fin_cases j
  exact generator0_even

/-- Inclusion into `A_16`, used to promote the selected module bound. -/
def toAlternating : Top →* alternatingGroup (Fin 16) :=
  Subgroup.inclusion top_le_alternating

/-- Inclusion into the literal top subgroup representing `S_16`. -/
def toSymmetricTop : Top →*
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.
      DegreeTwoSixteenNaturalFiniteRows.naturalTopSubgroup .symmetric :=
  Subgroup.inclusion le_top

end PrimitiveAffineDegreeTwoNaturalSixteenCyclicRestriction
end SymmetricSubgroupAsymptotics

end
