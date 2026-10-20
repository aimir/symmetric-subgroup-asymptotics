import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.CyclicQuotientSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! The first literal twelve-point top is cyclic. Two generator identities
and twelve point identities close its quotient-socle and natural-module
bounds through generic structural theorems. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow1Symbolic

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def cycle : Equiv.Perm (Fin 12) := (row1Generators 0)⁻¹ * row1Generators 1

theorem cycle_mem : cycle ∈ Row1Top :=
  Subgroup.mul_mem _
    (Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self 0)))
    (Subgroup.subset_closure (Set.mem_range_self 1))

theorem generators_pow (i : Fin 2) :
    row1Generators i = cycle ^ (![3, 4] i : ℕ) := by
  fin_cases i <;> ext x <;> decide +kernel +revert

theorem top_eq_zpowers : Row1Top = Subgroup.zpowers cycle := by
  apply le_antisymm
  · apply (Subgroup.closure_le (Subgroup.zpowers cycle)).mpr
    rintro x ⟨i, rfl⟩
    rw [generators_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers cycle) _
  · exact Subgroup.zpowers_le.mpr cycle_mem

instance : IsCyclic Row1Top :=
  Row1Top.isCyclic_iff_exists_zpowers_eq_top.mpr ⟨cycle, top_eq_zpowers.symm⟩

def orbitWitness : LiteralCyclicOrbitWitness Row1Top 1 where
  element := ⟨cycle, cycle_mem⟩
  representative := fun _ ↦ 0
  orbitIndex := fun _ ↦ 0
  exponent := id
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row1Interface.top (Fin 12)) 1 :=
  orbitWitness.uniform (ZMod 2)

noncomputable def family : row1Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocle_one_of_isCyclic (G := Row1Top) N.1)

end PrimitiveAffineDegreeTwoTwelveRow1Symbolic
end SymmetricSubgroupAsymptotics
end
