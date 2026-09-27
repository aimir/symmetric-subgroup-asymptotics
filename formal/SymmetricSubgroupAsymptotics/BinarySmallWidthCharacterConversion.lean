import SymmetricSubgroupAsymptotics.BinaryTransitivePowerSevenCriterion

/-!
# Rechecking original character entries at widths four, eight and sixteen

At these three widths, the old exact gap forces a central dimension small
enough for the new seven-power criterion. The original group, central
involution cardinality and dimension are unchanged. This is a bounded
integer comparison, not a comparison of the two class-count inputs or
a conversion at arbitrary physical widths.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The old integer gap always forces this weaker integral rank bound.
The lower comparison uses only `38^8 ≥ 2^4 * 25^8`. -/
theorem binaryCharacter_four_mul_dimension_lt {w z : ℕ}
    (hgap : 38^(8*z) < 2^w * 25^(8*z)) : 4*z < w := by
  have hpow : 2^(4*z) * 25^(8*z) ≤ 38^(8*z) := by
    calc
      _ = (2^4 * 25^8)^z := by simp only [mul_pow, pow_mul]
      _ ≤ (38^8)^z := Nat.pow_le_pow_left (by decide : 2^4 * 25^8 ≤ (38:ℕ)^8) z
      _ = _ := by rw [pow_mul]
  by_contra h
  have hw : w ≤ 4*z := Nat.le_of_not_gt h
  have hm : 2^w * 25^(8*z) ≤ 2^(4*z) * 25^(8*z) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0 < 2) hw)
  exact (not_lt_of_ge (hm.trans hpow)) hgap

/-- Precisely these physical widths turn the integral rank saving into
the sufficient budget for the new class rate. -/
theorem binaryCharacter_small_width_seven_budget {w z : ℕ}
    (hw : w = 4 ∨ w = 8 ∨ w = 16)
    (hgap : 38^(8*z) < 2^w * 25^(8*z)) : 16*z ≤ 3*w := by
  have hz := binaryCharacter_four_mul_dimension_lt hgap
  rcases hw with rfl | rfl | rfl <;> omega

namespace BinaryNormalCharacterCriterion

variable {G : Type*} [Group G] {w : ℕ}

/-- Recheck the new gap while retaining the same original central
subgroup and its exact cardinality. No binary or finite-group assumption
is needed for this purely numerical conversion of structural criteria. -/
def toSevenOfSmallWidth (C : BinaryNormalCharacterCriterion G w)
    (hw : w = 4 ∨ w = 8 ∨ w = 16) : BinarySevenCharacterCriterion G w where
  dimension := C.dimension
  cardinal := C.cardinal
  gap := binarySeven_character_gap_of_sixteen_mul_le w C.dimension
    (by rcases hw with rfl | rfl | rfl <;> omega)
    (binaryCharacter_small_width_seven_budget hw C.gap)

@[simp] theorem toSevenOfSmallWidth_dimension (C : BinaryNormalCharacterCriterion G w)
    (hw : w = 4 ∨ w = 8 ∨ w = 16) :
    (C.toSevenOfSmallWidth hw).dimension = C.dimension := rfl

end BinaryNormalCharacterCriterion
end SymmetricSubgroupAsymptotics

end
