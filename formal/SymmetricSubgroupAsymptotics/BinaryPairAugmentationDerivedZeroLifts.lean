import SymmetricSubgroupAsymptotics.BinaryPairDerivedZeroLifts
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The codimension-one actual kernel is the even-parity hyperplane.
Its quotient action is trivial for EVERY actual top permutation; only
actual derived top elements then receive a proved zero-offset lift. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

private theorem augmentation_kernel_mem_sum : ∀ v : Fin 8 → ZMod 2,
    v ∈ BinaryRegularEightNaturalRegistry.chart45.space ↔ ∑ i : Fin 8, v i = 0 := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel

variable {X : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))

theorem affineQuotient_trivial_of_augmentation_kernel
    (hK : F.kernelSpace = BinaryRegularEightNaturalRegistry.chart45.space) :
    ∀ (t : F.top.range) a, F.affineQuotientRepresentation t a = a := by
  intro t a
  obtain ⟨v,rfl⟩ := F.kernelSpace.mkQ_surjective a
  change F.kernelSpace.mkQ
    (permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 8) t v) =
      F.kernelSpace.mkQ v
  apply (Submodule.Quotient.eq F.kernelSpace).mpr
  rw [hK]
  apply (augmentation_kernel_mem_sum _).mpr
  change (∑ i : Fin 8, (v (t.val.symm i) - v i)) = 0
  rw [Finset.sum_sub_distrib,Equiv.sum_comp,sub_self]

theorem affinePermutation_zero_mem_of_augmentation_derived_top
    (hK : F.kernelSpace = BinaryRegularEightNaturalRegistry.chart45.space)
    (t : F.top.range) (ht : t ∈ commutator F.top.range) :
    F.affinePermutation t.val 0 ∈ U :=
  F.affinePermutation_zero_mem_of_derived_top
    (F.affineQuotient_trivial_of_augmentation_kernel hK) t ht

end SymmetricSubgroupAsymptotics.BinaryPairFrame
