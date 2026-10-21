import SymmetricSubgroupAsymptotics.BinaryPairLayerPreimageCards
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts
import SymmetricSubgroupAsymptotics.BinaryPairOriginalKernelCoordinateCard

/-! The actual regular45 upper layer with full lower layer is the
literal sixteen-coordinate augmentation, not merely an abstract module
of the same dimension. Only seven original basis sums are evaluated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
local instance regularAugmentationPreimagePrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private theorem regular45_basis_sum_zero : ∀ j : Fin 7,
    (∑ i : Fin 8,BinaryRegularEightNaturalRegistry.chart45.inclusion (Pi.single j 1) i)=0 := by
  decide +kernel

theorem regular45_space_eq_permutation_augmentation :
    BinaryRegularEightNaturalRegistry.chart45.space=
      PermutationAugmentation.space (ZMod 2) (Fin 8) := by
  have hle : BinaryRegularEightNaturalRegistry.chart45.space≤
      PermutationAugmentation.space (ZMod 2) (Fin 8) := by
    apply BinaryRegularEightNaturalRegistry.chart45.le_of_basis_mem
    intro j
    change PermutationAugmentation.coordinateSum (ZMod 2) (Fin 8)
      (BinaryRegularEightNaturalRegistry.chart45.inclusion (Pi.single j 1))=0
    rw [permutation_coordinateSum_apply]
    exact regular45_basis_sum_zero j
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [BinaryRegularEightNaturalRegistry.chart45.finrank]
  have hd := PermutationAugmentation.space_finrank_add_one (k := ZMod 2) (0 : Fin 8)
  norm_num only [Nat.card_fin] at hd
  omega

namespace BinaryPairFrame
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin w))

theorem pairSum_preimage_augmentation_eq :
    (PermutationAugmentation.space (ZMod 2) (Fin w)).comap E.pairSum=
      PermutationAugmentation.space (ZMod 2) X := by
  ext v
  change PermutationAugmentation.coordinateSum (ZMod 2) (Fin w) (E.pairSum v)=0 ↔
    PermutationAugmentation.coordinateSum (ZMod 2) X v=0
  rw [E.coordinateSum_eq_pairSum]

theorem regular45_full_lower_kernel_eq_augmentation
    {Y : Type} [Finite Y] {G : Subgroup (Equiv.Perm Y)}
    (F : BinaryPairFrame G (Fin 16)) (Q : BinaryPairFrame F.top.range (Fin 8))
    (hSum : (Q.pairSumModuleLayer (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=
      (BinaryRegularEightNaturalRegistry.charts 45).2.space)
    (hLow : (Q.pairConstantModuleLayer (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=⊤) :
    F.kernelSpace=PermutationAugmentation.space (ZMod 2) (Fin 16) := by
  have he := Q.pairModule_eq_pairSum_preimage_of_constant_top
    (F.axisNaturalSubrepresentation F.top.ker) hLow
  change F.ambientAxis F.top.ker=
    (Q.pairSumModuleLayer (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule.comap Q.pairSum at he
  rw [F.original_ambientAxis_kernel,hSum] at he
  change F.kernelSpace=BinaryRegularEightNaturalRegistry.chart45.space.comap Q.pairSum at he
  rw [regular45_space_eq_permutation_augmentation,Q.pairSum_preimage_augmentation_eq] at he
  exact he

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
