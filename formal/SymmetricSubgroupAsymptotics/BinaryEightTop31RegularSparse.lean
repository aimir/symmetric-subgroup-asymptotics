import SymmetricSubgroupAsymptotics.BinaryEightTop31ProperFLinear

/-! The actual regularE8 subgroup of31 from just THREE sparse generator
identities. This avoids unfolding the older64-row inclusion certificate
inside dependent representation restriction terms. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightTop31RegularSparse
private theorem first : BinaryMenuCayley8T3.generators 0 = BinaryMenuCayley8T31.generators 1 := by
  apply Equiv.ext
  decide +kernel
private theorem second : BinaryMenuCayley8T3.generators 1 = BinaryMenuCayley8T31.generators 2 := by
  apply Equiv.ext
  decide +kernel

theorem regular_le : BinaryRegularEightNaturalRegistry.H ≤ BinaryEightTop31CoordinateAction.H := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · change BinaryMenuCayley8T3.generators (0 : Fin 3) ∈ BinaryEightTop31CoordinateAction.H
    rw [first]
    exact Subgroup.subset_closure (Set.mem_range_self _)
  · change BinaryMenuCayley8T3.generators (1 : Fin 3) ∈ BinaryEightTop31CoordinateAction.H
    rw [second]
    exact Subgroup.subset_closure (Set.mem_range_self _)
  · change BinaryMenuCayley8T3.generators (2 : Fin 3) ∈ BinaryEightTop31CoordinateAction.H
    rw [← BinaryEightTop31ProperFLinear.z_coe]
    exact BinaryEightTop31ProperFLinear.z.property
end SymmetricSubgroupAsymptotics.BinaryEightTop31RegularSparse
