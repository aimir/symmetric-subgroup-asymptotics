import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301
import SymmetricSubgroupAsymptotics.AlternatingGeneratorBridge
import SymmetricSubgroupAsymptotics.AlternatingSymmetricNormalChain
import SymmetricSubgroupAsymptotics.NaturalBinaryAlternatingCyclic
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import Mathlib.GroupTheory.Perm.Fin

/-!
# The literal natural twelve-point alternating and symmetric tops

The last two displayed generator tuples generate the natural alternating
and symmetric groups. These identities supply both the uniform natural
module bound and every quotient's one-generator socle bound, without
enumerating either permutation group.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveNaturalTops

open DegreeTwoTwelvePairFiniteCatalogue

theorem row300_eq_alternating : Row300Top = alternatingGroup (Fin 12) := by
  have hrange : Set.range row300Generators =
      ({row300Generators 0, row300Generators 1} : Set (Equiv.Perm (Fin 12))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  change Subgroup.closure (Set.range row300Generators) = _
  rw [hrange]
  apply evenPairClosure_eq_alternating (by simp)
    (row300Generators 0) (Equiv.swap (10 : Fin 12) 11) (row300Generators 1)
    (Equiv.swap_inv _ _)
  · apply closure_pair_top_of_mul_right
    have hrotate : row300Generators 0 * Equiv.swap (10 : Fin 12) 11 =
        finRotate 12 := by decide +kernel
    rw [hrotate]
    simpa only [show finRotate 12 (10 : Fin 12) = 11 from rfl] using
      Equiv.Perm.closure_cycle_adjacent_swap
        (isCycle_finRotate_of_le (by decide))
        (support_finRotate_of_le (by decide)) (10 : Fin 12)
  · apply Equiv.Perm.mem_alternatingGroup.mpr
    decide +kernel
  · decide +kernel
  · right
    decide +kernel

theorem row301_eq_top : Row301Top = (⊤ : Subgroup (Equiv.Perm (Fin 12))) := by
  have h0 : row301Generators 0 = finRotate 12 := by decide +kernel
  have h1 : row301Generators 1 = Equiv.swap (0 : Fin 12) 1 := by decide +kernel
  have hrange : Set.range row301Generators =
      ({finRotate 12, Equiv.swap (0 : Fin 12) 1} : Set (Equiv.Perm (Fin 12))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [h0, h1]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
  change Subgroup.closure (Set.range row301Generators) = _
  rw [hrange]
  simpa only [finRotate_apply_zero] using
    Equiv.Perm.closure_cycle_adjacent_swap
      (isCycle_finRotate_of_le (by decide))
      (support_finRotate_of_le (by decide)) (0 : Fin 12)

def row300Equiv : Row300Top ≃* alternatingGroup (Fin 12) :=
  MulEquiv.subgroupCongr row300_eq_alternating

def row301Equiv : Row301Top ≃* Equiv.Perm (Fin 12) :=
  (MulEquiv.subgroupCongr row301_eq_top).trans Subgroup.topEquiv

theorem row300_normal_total (A B : Subgroup Row300Top)
    (hA : A.Normal) (hB : B.Normal) : A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective row300Equiv.symm.toMonoidHom
    row300Equiv.symm.surjective
    (AlternatingSymmetricNormalChain.alternating_normal_total (by norm_num))
    A B hA hB

theorem row301_normal_total (A B : Subgroup Row301Top)
    (hA : A.Normal) (hB : B.Normal) : A ≤ B ∨ B ≤ A :=
  normalSubgroups_total_of_surjective row301Equiv.symm.toMonoidHom
    row301Equiv.symm.surjective
    (AlternatingSymmetricNormalChain.symmetric_normal_total (by norm_num))
    A B hA hB

def row300Socle : row300Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocleNormalGeneratorBound_one_of_normal_total row300_normal_total N.1)

def row301Socle : row301Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N ↦ by
    letI := N.2
    exact quotientSocleNormalGeneratorBound_one_of_normal_total row301_normal_total N.1)

theorem row300Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row300Interface.top (Fin 12)) 1 :=
  NaturalBinaryAlternating.uniform_one Row300Top
    (by rw [row300_eq_alternating]) (by norm_num) (by norm_num)

theorem row301Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row301Interface.top (Fin 12)) 1 :=
  NaturalBinaryAlternating.uniform_one Row301Top
    (by rw [row301_eq_top]; exact le_top) (by norm_num) (by norm_num)

end DegreeTwoTwelveNaturalTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
