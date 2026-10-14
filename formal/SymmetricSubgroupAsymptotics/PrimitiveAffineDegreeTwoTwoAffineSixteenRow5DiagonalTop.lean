import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenDiagonalTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27TopCertificate

/-!
# Exact diagonal product for the literal two-affine row 5

The checked row1 point chart also identifies the local order-168 action.
The extra literal generator is the word h^5 f in the retained local tuple.
Forward bindings and reverse words identify the original closure exactly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenRow5DiagonalTop

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DiagonalBinaryPermutationProduct

abbrev Local := Subgroup.closure
  (Set.range PrimitiveAffineEightFrameRow27TopCertificate.generators)
abbrev Top := DegreeTwoTwoAffineSixteenInterfaces.row5.top

def pointEquiv : Fin 16 ≃ Fin 8 × Binary :=
  PrimitiveAffineDegreeTwoTwoAffineSixteenDiagonalTops.Row1.pointEquiv

def localGenerator (i : Fin 3) : Local :=
  ⟨PrimitiveAffineEightFrameRow27TopCertificate.generators i,
    Subgroup.subset_closure (Set.mem_range_self i)⟩

def modelGenerators : Fin 6 → Local × Binary :=
  ![(localGenerator 2, 1),
    (localGenerator 0 ^ 5 * localGenerator 2 * (localGenerator 0 ^ 5)⁻¹, 1),
    (localGenerator 0 ^ 3 * localGenerator 2 * (localGenerator 0 ^ 3)⁻¹, 1),
    (localGenerator 0, 1), (localGenerator 0 ^ 5 * localGenerator 1, 1), (1, bit)]

theorem generators_binding (i : Fin 6) :
    action Local pointEquiv (modelGenerators i) =
      DegreeTwoTwoAffineSixteenInterfaces.row5Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def literalFrobenius : Equiv.Perm (Fin 16) :=
  DegreeTwoTwoAffineSixteenInterfaces.row5Generators 3 ^ 2 *
    DegreeTwoTwoAffineSixteenInterfaces.row5Generators 4

theorem diagonal_generator_words (i : Fin 3) :
    diagonal pointEquiv (PrimitiveAffineEightFrameRow27TopCertificate.generators i) =
      ![DegreeTwoTwoAffineSixteenInterfaces.row5Generators 3, literalFrobenius,
        DegreeTwoTwoAffineSixteenInterfaces.row5Generators 0] i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem diagonal_generators_mem (i : Fin 3) :
    diagonal pointEquiv (PrimitiveAffineEightFrameRow27TopCertificate.generators i) ∈ Top := by
  have hg (j : Fin 6) : DegreeTwoTwoAffineSixteenInterfaces.row5Generators j ∈ Top :=
    Subgroup.subset_closure (Set.mem_range_self j)
  rw [diagonal_generator_words]
  fin_cases i
  · exact hg 3
  · exact Top.mul_mem (Top.pow_mem (hg 3) 2) (hg 4)
  · exact hg 0

theorem toggle_eq : toggle pointEquiv =
    DegreeTwoTwoAffineSixteenInterfaces.row5Generators 5 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem action_range : (action Local pointEquiv).range = Top := by
  exact action_range_eq PrimitiveAffineEightFrameRow27TopCertificate.generators pointEquiv
    DegreeTwoTwoAffineSixteenInterfaces.row5Generators modelGenerators
    generators_binding diagonal_generators_mem (by
      rw [toggle_eq]
      exact Subgroup.subset_closure (Set.mem_range_self (5 : Fin 6)))

/-- The target remains the exact original finite interface's top. -/
def modelEquiv : Local × Binary ≃* Top :=
  (MonoidHom.ofInjective (action_injective Local pointEquiv)).trans
    (MulEquiv.subgroupCongr action_range)

end PrimitiveAffineDegreeTwoTwoAffineSixteenRow5DiagonalTop
end SymmetricSubgroupAsymptotics

end
