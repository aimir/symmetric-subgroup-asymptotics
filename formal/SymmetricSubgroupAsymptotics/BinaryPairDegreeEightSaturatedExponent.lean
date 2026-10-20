import SymmetricSubgroupAsymptotics.BinaryPairDegreeEightAxisModels
import SymmetricSubgroupAsymptotics.BinaryPairLiftCarryExponent

/-! At a literal exceptional degree-eight top, saturation of the full
abelianization extension bound forces exponent two in the original whole
abelianization. All actual lifts and the full correlated kernel remain in
the original physical pair frame. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 8)) (hU : IsPGroup 2 U)


theorem ambientAxis_kernel : F.ambientAxis F.top.ker = F.kernelSpace := by
  apply le_antisymm (F.ambientAxis_le_kernelSpace F.top.ker)
  rintro v ⟨a, rfl⟩
  exact (F.bits_mem_ambientAxis F.top.ker a.toMul).mpr a.toMul.property

include hU

theorem saturated_pair_kernel_radical
    (hsat : Nat.card (Abelianization U) =
      2 ^ MarkedC4.normalGen F.top.ker * Nat.card (Abelianization F.top.range)) :
    primeRelativeRadical 2 F.top.ker = F.top.ker ⊓ commutator U := by
  have he := pGroup_relativeRadical_eq_inf_commutator_of_abelianization_saturation
    2 hU F.top.rangeRestrict F.top.rangeRestrict_surjective
    (fun k => F.physical_kernel_pow_two ⟨k.val, by
      simpa only [MonoidHom.ker_rangeRestrict] using k.property⟩)
    (by simpa only [MonoidHom.ker_rangeRestrict] using hsat)
  simpa only [MonoidHom.ker_rangeRestrict] using he

theorem regular_abelianization_pow_two_of_saturated_kernel
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hlarge : 2 < MarkedC4.normalGen F.top.ker)
    (hsat : Nat.card (Abelianization U) =
      2 ^ MarkedC4.normalGen F.top.ker * Nat.card (Abelianization F.top.range)) :
    ∀ a : Abelianization U, a ^ 2 = 1 := by
  have hlift : ∀ i : Fin 3, ∃ u : U, F.top u = BinaryMenuCayley8T3.generators i := by
    intro i
    have hm : BinaryMenuCayley8T3.generators i ∈ F.top.range := by
      rw [hH ]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    exact hm
  choose u hp using hlift
  have hpoints : ∀ i j, F.top (u i) j = BinaryRegularEightSquareCarry.generatorImages i j := by
    intro i j
    rw [hp]
    exact (BinaryRegularEightSquareCarry.generatorImages_eq_original i j).symm
  have hrad := F.saturated_pair_kernel_radical hU hsat
  rcases F.regular_large_axis_models hU F.top.ker le_rfl hH hlarge with
    ⟨hK, hR⟩ | ⟨hK, hR⟩
  · apply F.regular45_abelianization_pow_two u hpoints hH
      ((F.ambientAxis_kernel).symm.trans hK) hrad
    intro k
    rw [← hR, F.bits_mem_ambientAxis]
  · apply F.regular46_abelianization_pow_two u hpoints hH
      ((F.ambientAxis_kernel).symm.trans hK) hrad
    intro k
    rw [← hR, F.bits_mem_ambientAxis]

theorem heisenberg_abelianization_pow_two_of_saturated_kernel
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))
    (hlarge : 1 < MarkedC4.normalGen F.top.ker)
    (hsat : Nat.card (Abelianization U) =
      2 ^ MarkedC4.normalGen F.top.ker * Nat.card (Abelianization F.top.range)) :
    ∀ a : Abelianization U, a ^ 2 = 1 := by
  have hlift : ∀ i : Fin 4, ∃ u : U, F.top u = BinaryHeisenbergEightSquareCarry.originalSelected i := by
    intro i
    have hm : BinaryHeisenbergEightSquareCarry.originalSelected i ∈ F.top.range := by
      rw [hH, ← BinaryHeisenbergEightSquareCarry.selected_closure_eq_original ]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    exact hm
  choose u hp using hlift
  have hrad := F.saturated_pair_kernel_radical hU hsat
  rcases F.heisenberg_large_axis_models hU F.top.ker le_rfl hH hlarge with
    ⟨hK, hR⟩ | ⟨hK, hR⟩ | ⟨hK, hR⟩
  · apply F.heisenberg12_abelianization_pow_two u hp hH
      ((F.ambientAxis_kernel).symm.trans hK) hrad
    intro k
    rw [← hR, F.bits_mem_ambientAxis]
  · apply F.heisenberg13_abelianization_pow_two u hp hH
      ((F.ambientAxis_kernel).symm.trans hK) hrad
    intro k
    rw [← hR, F.bits_mem_ambientAxis]
  · apply F.heisenberg14_abelianization_pow_two u hp hH
      ((F.ambientAxis_kernel).symm.trans hK) hrad
    intro k
    rw [← hR, F.bits_mem_ambientAxis]

end SymmetricSubgroupAsymptotics.BinaryPairFrame
