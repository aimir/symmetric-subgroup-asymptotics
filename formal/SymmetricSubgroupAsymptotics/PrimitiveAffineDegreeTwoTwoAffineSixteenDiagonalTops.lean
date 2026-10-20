import SymmetricSubgroupAsymptotics.DiagonalBinaryPermutationProduct
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineLiteralTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwoAffineSixteenInterfaces

/-!
# Exact product charts for literal two-affine rows 1 and 11

The local tuples differ from the shared eight-point tuples. Explicit point
charts and short words prove both closure inclusions. The only finite checks
evaluate these words on the original sixteen points.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwoAffineSixteenDiagonalTops

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DiagonalBinaryPermutationProduct

/-- The original first and second eight-point blocks. -/
def blockChart : Fin 16 ≃ Fin 8 × Binary where
  toFun x := (#[
    (0, 1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1),
    (0, bit), (1, bit), (2, bit), (3, bit), (4, bit), (5, bit), (6, bit), (7, bit)
    ] : Array (Fin 8 × Binary))[x.val]!
  invFun p := if p.2 = 1 then
      (#[0, 1, 2, 3, 4, 5, 6, 7] : Array (Fin 16))[p.1.val]!
    else (#[8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[p.1.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

namespace Row1

abbrev Local := DegreeTwoPairedEightSharedTops.Top18
abbrev Top := DegreeTwoTwoAffineSixteenInterfaces.row1.top

/-- Match the retained order-seven cycle, keeping the first translation fixed. -/
def localChart : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 1, 4, 5, 7, 6, 3, 2] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 1, 7, 6, 2, 3, 5, 4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pointEquiv : Fin 16 ≃ Fin 8 × Binary :=
  blockChart.trans (localChart.prodCongr (Equiv.refl Binary))

def localGenerator (i : Fin 2) : Local :=
  ⟨DegreeTwoPairedEightSharedTops.top18Generators i,
    Subgroup.subset_closure (Set.mem_range_self i)⟩

def modelGenerators : Fin 5 → Local × Binary :=
  ![(localGenerator 1, 1),
    (localGenerator 0 ^ 5 * localGenerator 1 * (localGenerator 0 ^ 5)⁻¹, 1),
    (localGenerator 0 ^ 3 * localGenerator 1 * (localGenerator 0 ^ 3)⁻¹, 1),
    (localGenerator 0, 1), (1, bit)]

theorem generators_binding (i : Fin 5) :
    action Local pointEquiv (modelGenerators i) =
      DegreeTwoTwoAffineSixteenInterfaces.row1Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem diagonal_generator_words (i : Fin 2) :
    diagonal pointEquiv (DegreeTwoPairedEightSharedTops.top18Generators i) =
      ![DegreeTwoTwoAffineSixteenInterfaces.row1Generators 3,
        DegreeTwoTwoAffineSixteenInterfaces.row1Generators 0] i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem diagonal_generators_mem (i : Fin 2) :
    diagonal pointEquiv (DegreeTwoPairedEightSharedTops.top18Generators i) ∈ Top := by
  rw [diagonal_generator_words]
  fin_cases i
  · exact Subgroup.subset_closure (Set.mem_range_self (3 : Fin 5))
  · exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 5))

theorem toggle_eq : toggle pointEquiv =
    DegreeTwoTwoAffineSixteenInterfaces.row1Generators 4 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem action_range : (action Local pointEquiv).range = Top := by
  exact action_range_eq DegreeTwoPairedEightSharedTops.top18Generators pointEquiv
    DegreeTwoTwoAffineSixteenInterfaces.row1Generators modelGenerators
    generators_binding diagonal_generators_mem (by
      rw [toggle_eq]
      exact Subgroup.subset_closure (Set.mem_range_self (4 : Fin 5)))

/-- The product equivalence targets the original interface's literal top. -/
def modelEquiv : Local × Binary ≃* Top :=
  (MonoidHom.ofInjective (action_injective Local pointEquiv)).trans
    (MulEquiv.subgroupCongr action_range)

end Row1

namespace Row11

abbrev Local := DegreeTwoPairedEightSharedTops.Top20
abbrev Top := DegreeTwoTwoAffineSixteenInterfaces.row11.top

def pointEquiv : Fin 16 ≃ Fin 8 × Binary := blockChart

def localGenerator (i : Fin 3) : Local :=
  ⟨DegreeTwoPairedEightSharedTops.top20Generators i,
    Subgroup.subset_closure (Set.mem_range_self i)⟩

/-- The literal transvection is a conjugate of the shared coordinate swap. -/
def localTransvection : Local :=
  localGenerator 0 ^ 4 * localGenerator 1 * (localGenerator 0 ^ 4)⁻¹

/-- The literal coordinate rotation, expressed in shared local generators. -/
def localRotation : Local := (localTransvection * localGenerator 0) ^ 2

def modelGenerators : Fin 6 → Local × Binary :=
  ![(localGenerator 2, 1),
    (localGenerator 0 ^ 6 * localGenerator 2 * (localGenerator 0 ^ 6)⁻¹, 1),
    (localGenerator 0 ^ 5 * localGenerator 2 * (localGenerator 0 ^ 5)⁻¹, 1),
    (localTransvection, 1), (localRotation, 1), (1, bit)]

theorem generators_binding (i : Fin 6) :
    action Local pointEquiv (modelGenerators i) =
      DegreeTwoTwoAffineSixteenInterfaces.row11Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def literalSinger : Equiv.Perm (Fin 16) :=
  DegreeTwoTwoAffineSixteenInterfaces.row11Generators 3 *
    DegreeTwoTwoAffineSixteenInterfaces.row11Generators 4 ^ 2

def literalSwap : Equiv.Perm (Fin 16) :=
  (literalSinger ^ 4)⁻¹ * DegreeTwoTwoAffineSixteenInterfaces.row11Generators 3 *
    literalSinger ^ 4

theorem diagonal_generator_words (i : Fin 3) :
    diagonal pointEquiv (DegreeTwoPairedEightSharedTops.top20Generators i) =
      ![literalSinger, literalSwap, DegreeTwoTwoAffineSixteenInterfaces.row11Generators 0] i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem diagonal_generators_mem (i : Fin 3) :
    diagonal pointEquiv (DegreeTwoPairedEightSharedTops.top20Generators i) ∈ Top := by
  have hg (j : Fin 6) : DegreeTwoTwoAffineSixteenInterfaces.row11Generators j ∈ Top :=
    Subgroup.subset_closure (Set.mem_range_self j)
  have hs : literalSinger ∈ Top := Top.mul_mem (hg 3) (Top.pow_mem (hg 4) 2)
  have hq : literalSwap ∈ Top :=
    Top.mul_mem (Top.mul_mem (Top.inv_mem (Top.pow_mem hs 4)) (hg 3)) (Top.pow_mem hs 4)
  rw [diagonal_generator_words]
  fin_cases i
  · exact hs
  · exact hq
  · exact hg 0

theorem toggle_eq : toggle pointEquiv =
    DegreeTwoTwoAffineSixteenInterfaces.row11Generators 5 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

theorem action_range : (action Local pointEquiv).range = Top := by
  exact action_range_eq DegreeTwoPairedEightSharedTops.top20Generators pointEquiv
    DegreeTwoTwoAffineSixteenInterfaces.row11Generators modelGenerators
    generators_binding diagonal_generators_mem (by
      rw [toggle_eq]
      exact Subgroup.subset_closure (Set.mem_range_self (5 : Fin 6)))

/-- The product equivalence targets the original interface's literal top. -/
def modelEquiv : Local × Binary ≃* Top :=
  (MonoidHom.ofInjective (action_injective Local pointEquiv)).trans
    (MulEquiv.subgroupCongr action_range)

end Row11

end PrimitiveAffineDegreeTwoTwoAffineSixteenDiagonalTops
end SymmetricSubgroupAsymptotics

end
