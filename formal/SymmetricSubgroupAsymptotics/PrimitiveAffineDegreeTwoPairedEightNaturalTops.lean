import SymmetricSubgroupAsymptotics.AlternatingGeneratorBridge
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopInterface
import Mathlib.GroupTheory.Perm.Fin

/-! Literal natural A8/S8 tops, independent of the growing paired catalogue. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoPairedEightSharedTops

/-! The final two tops retain their small published generator tuples even
though their normal lattices are handled structurally.  This lets the
selected module and coupled-head emitters work on the generators without
enumerating either full permutation group. -/

private def top23Generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 2, 3, 4, 5, 6, 0, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[6, 0, 1, 2, 3, 4, 5, 7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def top23Generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 1, 2, 3, 4, 6, 7, 5] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 7, 5, 6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def top23Generators : Fin 2 → Equiv.Perm (Fin 8) :=
  ![top23Generator0, top23Generator1]

abbrev Top23 : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range top23Generators)

/-- The retained row-23 tuple is the natural alternating top. -/
theorem top23_eq_alternating :
    Top23 = alternatingGroup (Fin 8) := by
  have hrange : Set.range top23Generators =
      ({top23Generator0, top23Generator1} : Set (Equiv.Perm (Fin 8))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [top23Generators]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  change Subgroup.closure (Set.range top23Generators) = _
  rw [hrange]
  apply evenPairClosure_eq_alternating (by simp)
    top23Generator0 (Equiv.swap (6 : Fin 8) 7) top23Generator1
    (Equiv.swap_inv _ _)
  · apply closure_pair_top_of_mul_right
    have hrotate : top23Generator0 * Equiv.swap (6 : Fin 8) 7 = finRotate 8 := by
      decide +kernel
    rw [hrotate]
    simpa only [show finRotate 8 (6 : Fin 8) = 7 from rfl] using
      Equiv.Perm.closure_cycle_adjacent_swap
        (isCycle_finRotate_of_le (by decide))
        (support_finRotate_of_le (by decide)) (6 : Fin 8)
  · apply Equiv.Perm.mem_alternatingGroup.mpr
    decide +kernel
  · decide +kernel
  · right
    decide +kernel

private def top24Generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 2, 3, 4, 5, 6, 7, 0] : Array (Fin 8))[x.val]!
  invFun x := (#[7, 0, 1, 2, 3, 4, 5, 6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def top24Generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 0, 2, 3, 4, 5, 6, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[1, 0, 2, 3, 4, 5, 6, 7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def top24Generators : Fin 2 → Equiv.Perm (Fin 8) :=
  ![top24Generator0, top24Generator1]

abbrev Top24 : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range top24Generators)

/-- The retained row-24 tuple is the full natural symmetric top. -/
theorem top24_eq_top :
    Top24 = (⊤ : Subgroup (Equiv.Perm (Fin 8))) := by
  have hrange : Set.range top24Generators =
      ({finRotate 8, Equiv.swap (0 : Fin 8) 1} : Set (Equiv.Perm (Fin 8))) := by
    have h0 : top24Generator0 = finRotate 8 := by decide +kernel
    have h1 : top24Generator1 = Equiv.swap (0 : Fin 8) 1 := by decide +kernel
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [top24Generators, h0, h1]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
  change Subgroup.closure (Set.range top24Generators) = _
  rw [hrange]
  simpa only [finRotate_apply_zero] using
    Equiv.Perm.closure_cycle_adjacent_swap
      (isCycle_finRotate_of_le (by decide))
      (support_finRotate_of_le (by decide)) (0 : Fin 8)

noncomputable def top23 : DegreeTwoPairTopFiniteInterface 8 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries Top23

noncomputable def top24 : DegreeTwoPairTopFiniteInterface 8 :=
  DegreeTwoPairTopFiniteInterface.withCanonicalRegistries Top24

end DegreeTwoPairedEightSharedTops
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
