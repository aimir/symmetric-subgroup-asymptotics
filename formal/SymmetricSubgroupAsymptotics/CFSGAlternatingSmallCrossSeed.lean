import SymmetricSubgroupAsymptotics.CFSGAlternatingCrossJoin
import SymmetricSubgroupAsymptotics.CFSGPermutationKleinMatching
import Mathlib.Data.Fin.VecNotation

/-! The common length-five seed for degrees seven and eight. The reflection
is `4−x`, the cross swap is `(1 A)(3 B)`, and the central matching is
`(1 3)(A B)`. Their genuine dihedral two-group relations precede Sylow selection. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSmallCrossSeed
open CFSGAlternatingCyclicReflection CFSGAlternatingSumSupport
open CFSGAlternatingCrossSeed CFSGPermutationCrossSwapWords

def baseReflection : Equiv.Perm (Cycle 1) where
  toFun x := 4 - x
  invFun x := 4 - x
  left_inv x := by ring
  right_inv x := by ring

def p (r : ℕ) : Equiv.Perm (X 1 r) := extensionHom (Cycle 1) r baseReflection

def q (r : ℕ) (hr : 2 ≤ r) : Equiv.Perm (X 1 r) :=
  doubleSwap (Sum.inl 1) (Sum.inr ⟨0, by omega⟩)
    (Sum.inl 3) (Sum.inr ⟨1, by omega⟩)

def b (r : ℕ) (hr : 2 ≤ r) : Equiv.Perm (X 1 r) :=
  doubleSwap (Sum.inl 1) (Sum.inl 3)
    (Sum.inr ⟨0, by omega⟩) (Sum.inr ⟨1, by omega⟩)

theorem baseReflection_square : baseReflection ^ 2 = 1 := by
  apply Equiv.ext
  intro x
  change (4 : Cycle 1) - (4 - x) = x
  ring

theorem baseReflection_even : Equiv.Perm.sign baseReflection = 1 := by decide +kernel

theorem baseReflection_inverts :
    baseReflection * rotation 1 * baseReflection⁻¹ = (rotation 1)⁻¹ := by
  apply Equiv.ext
  intro x
  change (4 : Cycle 1) - ((4 - x) + 1) = x - 1
  ring

theorem p_square (r : ℕ) : p r ^ 2 = 1 := by
  change extensionHom (Cycle 1) r baseReflection ^ 2 = 1
  rw [← map_pow, baseReflection_square, map_one]

theorem q_square (r : ℕ) (hr : 2 ≤ r) : q r hr ^ 2 = 1 := by
  apply doubleSwap_square
  · intro h
    exact (by decide : (1 : Cycle 1) ≠ 3) (Sum.inl_injective h)
  · intro h; cases h
  · intro h; cases h
  · intro h
    have he := congrArg Fin.val (Sum.inr_injective h)
    change (0 : ℕ) = 1 at he
    omega

theorem b_square (r : ℕ) (hr : 2 ≤ r) : b r hr ^ 2 = 1 := by
  apply doubleSwap_square <;> intro h <;> cases h

theorem p_q_fourth (r : ℕ) (hr : 2 ≤ r) : (p r * q r hr) ^ 4 = 1 := by
  apply involution_cross_rotation_pow_four
  · exact p_square r
  · change Sum.inl ((4 : Cycle 1) - 1) = Sum.inl 3
    congr 1
  · change Sum.inl ((4 : Cycle 1) - 3) = Sum.inl 1
    congr 1
  · rfl
  · rfl
  · intro h
    exact (by decide : (1 : Cycle 1) ≠ 3) (Sum.inl_injective h)
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro h
    have he := congrArg Fin.val (Sum.inr_injective h)
    change (0 : ℕ) = 1 at he
    omega

theorem b_commute_p (r : ℕ) (hr : 2 ≤ r) : Commute (b r hr) (p r) := by
  apply CFSGPermutationKleinMatching.paired_doubleSwap_commute
  · change Sum.inl ((4 : Cycle 1) - 1) = Sum.inl 3
    congr 1
  · change Sum.inl ((4 : Cycle 1) - 3) = Sum.inl 1
    congr 1
  · rfl
  · rfl

theorem b_commute_q (r : ℕ) (hr : 2 ≤ r) : Commute (b r hr) (q r hr) := by
  let f : Fin 4 → X 1 r := ![Sum.inl 1, Sum.inl 3,
    Sum.inr ⟨0, by omega⟩, Sum.inr ⟨1, by omega⟩]
  have hf : Function.Injective f := by
    intro i j h
    have h13 : (1 : Cycle 1) ≠ 3 := by decide
    fin_cases i <;> fin_cases j <;> simp [f, Fin.ext_iff, h13, Ne.symm h13] at h ⊢
  exact CFSGPermutationKleinMatching.matching_commute f hf

theorem seed_isPGroup (r : ℕ) (hr : 2 ≤ r) :
    IsPGroup 2 (Subgroup.closure ({p r, q r hr, b r hr} : Set (Equiv.Perm (X 1 r)))) := by
  exact CFSGDihedralTwoGroupWords.closure_three_involutions_isPGroup _ _ _
    (p_square r) (q_square r hr) (b_square r hr) (p_q_fourth r hr)
    (b_commute_p r hr) (b_commute_q r hr)

theorem seed_le_alternating (r : ℕ) (hr : 2 ≤ r) :
    Subgroup.closure ({p r, q r hr, b r hr} : Set (Equiv.Perm (X 1 r))) ≤
      alternatingGroup (X 1 r) := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx
  · subst x
    exact extension_even (Cycle 1) r baseReflection
      (Equiv.Perm.mem_alternatingGroup.mpr baseReflection_even)
  · subst x
    apply Equiv.Perm.mem_alternatingGroup.mpr
    change Equiv.Perm.sign (Equiv.swap (Sum.inl (1 : Cycle 1)) (Sum.inr (⟨0, by omega⟩ : Fin r)) *
      Equiv.swap (Sum.inl (3 : Cycle 1)) (Sum.inr (⟨1, by omega⟩ : Fin r))) = 1
    rw [map_mul, Equiv.Perm.sign_swap (by intro h; cases h),
      Equiv.Perm.sign_swap (by intro h; cases h)]
    norm_num
  · subst x
    apply Equiv.Perm.mem_alternatingGroup.mpr
    change Equiv.Perm.sign (Equiv.swap (Sum.inl (1 : Cycle 1)) (Sum.inl 3) *
      Equiv.swap (Sum.inr (⟨0, by omega⟩ : Fin r)) (Sum.inr (⟨1, by omega⟩ : Fin r))) = 1
    have h13 : (Sum.inl (1 : Cycle 1) : X 1 r) ≠ Sum.inl 3 :=
      fun h => (by decide : (1 : Cycle 1) ≠ 3) (Sum.inl_injective h)
    have h01 : (Sum.inr (⟨0, by omega⟩ : Fin r) : X 1 r) ≠ Sum.inr ⟨1, by omega⟩ := by
      intro h
      have he := congrArg Fin.val (Sum.inr_injective h)
      change (0 : ℕ) = 1 at he
      omega
    rw [map_mul, Equiv.Perm.sign_swap h13, Equiv.Perm.sign_swap h01]
    norm_num

end SymmetricSubgroupAsymptotics.CFSGAlternatingSmallCrossSeed
