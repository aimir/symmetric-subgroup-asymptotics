import SymmetricSubgroupAsymptotics.CFSGSymplecticSerreEF

/-! Exact support/triangularity of the literal symplectic positive simple
roots. These are uniform index arguments, not finite matrix certificates. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem positive_lower_left (i a b : Fin r) :
    positive R r i (Sum.inr a) (Sum.inl b) = 0 := by
  by_cases hi : i.val + 1 < r <;> simp [positive, hi, Matrix.single]

theorem positive_left_below (i a b : Fin r) (hab : b.val ≤ a.val) :
    positive R r i (Sum.inl a) (Sum.inl b) = 0 := by
  by_cases hi : i.val + 1 < r
  · have hne : ¬(i = a ∧ (⟨i.val + 1, hi⟩ : Fin r) = b) := by
      rintro ⟨ha, hb⟩
      have hva := congrArg Fin.val ha
      have hvb := congrArg Fin.val hb
      change i.val + 1 = b.val at hvb
      omega
    simp [positive, hi, Matrix.single, hne]
  · simp [positive, hi, Matrix.single]

theorem positive_right_above (i a b : Fin r) (hab : a.val ≤ b.val) :
    positive R r i (Sum.inr a) (Sum.inr b) = 0 := by
  by_cases hi : i.val + 1 < r
  · have hne : ¬((⟨i.val + 1, hi⟩ : Fin r) = a ∧ i = b) := by
      rintro ⟨ha, hb⟩
      have hva := congrArg Fin.val ha
      have hvb := congrArg Fin.val hb
      change i.val + 1 = a.val at hva
      omega
    simp [positive, hi, Matrix.single, hne]
  · simp [positive, hi, Matrix.single]

theorem positive_cross_diagonal (i a : Fin r) :
    positive R r i (Sum.inl a) (Sum.inr a) =
      if ¬i.val + 1 < r ∧ i = a then 1 else 0 := by
  by_cases hi : i.val + 1 < r <;> simp [positive, hi, Matrix.single]

theorem not_neg_two_forbids_terminal_successor (i j : Fin r)
    (hij : CartanMatrix.B r i j ≠ -2) : ¬(i.val + 1 = j.val ∧ j.val + 1 = r) := by
  rintro ⟨hs, ht⟩
  have hne : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    omega
  have hlast : j.val = r - 1 := by omega
  apply hij
  simp [CartanMatrix.B, hne, hs, hlast]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
