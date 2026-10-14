import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10LinearRelations
import SymmetricSubgroupAsymptotics.BinaryFourAffineImage

/-! Rows4/7 retain the two commuting ternary tensor rotations and one or
both factor reflections. The following formulas use the original bitmask
labels; the irreducibility witness only concerns four-bit vectors. -/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRows4And7LinearRelations

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10LinearRelations

/-- The second factor reflection in the original row7 coordinates. -/
def d : LinearGroup where
  toFun v := ![v 0, v 0 + v 1, v 2, v 2 + v 3]
  invFun v := ![v 0, v 0 + v 1, v 2, v 2 + v 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by decide +kernel
  map_smul' := by decide +kernel

theorem a4_original : BinaryFourAffineImage.linearPerm a =
    DegreeTwoPrimitiveSixteenInterfaces.row4Generators 0 := linearPerm_a_row8
theorem b4_original : BinaryFourAffineImage.linearPerm b =
    DegreeTwoPrimitiveSixteenInterfaces.row4Generators 1 := linearPerm_b_row8
theorem s4_original : BinaryFourAffineImage.linearPerm s =
    DegreeTwoPrimitiveSixteenInterfaces.row4Generators 2 := linearPerm_s_row10
theorem a7_original : BinaryFourAffineImage.linearPerm a =
    DegreeTwoPrimitiveSixteenInterfaces.row7Generators 0 := linearPerm_a_row8
theorem b7_original : BinaryFourAffineImage.linearPerm b =
    DegreeTwoPrimitiveSixteenInterfaces.row7Generators 1 := linearPerm_b_row8
theorem s7_original : BinaryFourAffineImage.linearPerm s =
    DegreeTwoPrimitiveSixteenInterfaces.row7Generators 2 := linearPerm_s_row10
theorem d7_original : BinaryFourAffineImage.linearPerm d =
    DegreeTwoPrimitiveSixteenInterfaces.row7Generators 3 := by
  apply Equiv.ext; intro x; revert x; decide +kernel

def linearGenerators4 : Fin 3 → LinearGroup := ![a, b, s]
def linearGenerators7 : Fin 4 → LinearGroup := ![a, b, s, d]
abbrev R4 : Subgroup LinearGroup := Subgroup.closure (Set.range linearGenerators4)
abbrev R7 : Subgroup LinearGroup := Subgroup.closure (Set.range linearGenerators7)

theorem a_mem4 : a ∈ R4 := Subgroup.subset_closure ⟨0, rfl⟩
theorem b_mem4 : b ∈ R4 := Subgroup.subset_closure ⟨1, rfl⟩
theorem s_mem4 : s ∈ R4 := Subgroup.subset_closure ⟨2, rfl⟩
theorem a_mem7 : a ∈ R7 := Subgroup.subset_closure ⟨0, rfl⟩
theorem b_mem7 : b ∈ R7 := Subgroup.subset_closure ⟨1, rfl⟩
theorem s_mem7 : s ∈ R7 := Subgroup.subset_closure ⟨2, rfl⟩
theorem d_mem7 : d ∈ R7 := Subgroup.subset_closure ⟨3, rfl⟩

theorem R4_le_R7 : R4 ≤ R7 := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact a_mem7
  · exact b_mem7
  · exact s_mem7

/-- Projection onto one of the two ternary-character planes. -/
def projection (x : Vector) : Vector := x + (a * b) x + ((a * b) ^ 2) x
def seed (x : Vector) : Vector := if projection x = 0 then s x else projection x
def orbitBasis (x : Vector) : Fin 4 → Vector :=
  ![seed x, a (seed x), s (seed x), a (s (seed x))]
def orbitCombination (x : Vector) (k : Fin 16) : Vector :=
  ∑ i : Fin 4, if k.val.testBit i.val then orbitBasis x i else 0

theorem orbit_spans : ∀ x : Vector, x ≠ 0 → ∀ y : Vector,
    ∃ k : Fin 16, orbitCombination x k = y := by decide +kernel

theorem irreducible4 : AffineModel.Irreducible R4 := by
  intro S hS
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  have hx : ∃ x ∈ S, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hbot
    apply le_antisymm _ bot_le
    intro x hx
    exact AddSubgroup.mem_bot.mpr (h x hx)
  obtain ⟨x, hx, hx0⟩ := hx
  have hp : projection x ∈ S :=
    S.add_mem (S.add_mem hx (hS (a * b) (R4.mul_mem a_mem4 b_mem4) x hx))
      (hS ((a * b) ^ 2) (R4.pow_mem (R4.mul_mem a_mem4 b_mem4) 2) x hx)
  have hs : seed x ∈ S := by
    unfold seed
    split
    · exact hS s s_mem4 x hx
    · exact hp
  have hb : ∀ i : Fin 4, orbitBasis x i ∈ S := by
    intro i
    fin_cases i
    · exact hs
    · exact hS a a_mem4 _ hs
    · exact hS s s_mem4 _ hs
    · exact hS a a_mem4 _ (hS s s_mem4 _ hs)
  apply top_unique
  intro y _hy
  obtain ⟨k, hk⟩ := orbit_spans x hx0 y
  rw [← hk]
  unfold orbitCombination
  apply S.sum_mem
  intro i _hi
  split
  · exact hb i
  · exact S.zero_mem

theorem irreducible7 : AffineModel.Irreducible R7 := by
  intro S hS
  exact irreducible4 S (fun r hr x hx ↦ hS r (R4_le_R7 hr) x hx)

end PrimitiveAffineDegreeTwoPrimitiveSixteenRows4And7LinearRelations
end SymmetricSubgroupAsymptotics

end
