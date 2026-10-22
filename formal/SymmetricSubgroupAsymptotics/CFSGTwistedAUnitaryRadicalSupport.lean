import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryRadicalGroup

/-! Entrywise support characterization of the literal radical arrays,
and a generic two-axis conjugation support lemma. This is actual matrix
algebra, with no triality/unitary/normal-closure hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays
variable {K J : Type*} [CommRing K] [Fintype J] [DecidableEq J]

theorem mem_arrayGroup_iff_support (u : (Matrix (Index J) (Index J) K)ˣ) :
    u ∈ arrayGroup ↔
      (∀ i, (u : Matrix (Index J) (Index J) K) i i = 1) ∧
      ∀ i j, i ≠ .inl () → j ≠ .inr (.inr ()) →
        (u : Matrix (Index J) (Index J) K) i j = (1 : Matrix (Index J) (Index J) K) i j := by
  constructor
  · rintro ⟨w, v, b, rfl⟩
    constructor
    · intro i
      rcases i with x | (i | x) <;> simp [upperUnit, upperArray]
    · intro i j hi hj
      rcases i with x | (i | x) <;> rcases j with y | (j | y)
      all_goals try cases x
      all_goals try cases y
      all_goals simp_all [upperUnit, upperArray, Matrix.one_apply]
  · rintro ⟨hd, hs⟩
    refine ⟨(fun j => (u : Matrix (Index J) (Index J) K) (.inl ()) (.inr (.inl j))),
      (fun i => (u : Matrix (Index J) (Index J) K) (.inr (.inl i)) (.inr (.inr ()))),
      (u : Matrix (Index J) (Index J) K) (.inl ()) (.inr (.inr ())), ?_⟩
    apply Units.ext
    ext (x | (i | x)) (y | (j | y))
    all_goals try cases x
    all_goals try cases y
    all_goals simp_all [upperUnit, upperArray, Matrix.one_apply]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryUpperArrays

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMatrixSupport
variable {K I : Type*} [CommRing K] [Fintype I] [DecidableEq I]

theorem conjugate_support (W : (Matrix I I K)ˣ) (R : Matrix I I K)
    (a b c d : I)
    (hR : ∀ i j, i ≠ a → j ≠ b → R i j = (1 : Matrix I I K) i j)
    (hleft : ∀ i, i ≠ c → (↑(W⁻¹) : Matrix I I K) i a = 0)
    (hright : ∀ j, j ≠ d → (W : Matrix I I K) b j = 0) :
    ∀ i j, i ≠ c → j ≠ d →
      ((↑(W⁻¹) : Matrix I I K) * R * (W : Matrix I I K)) i j = (1 : Matrix I I K) i j := by
  intro i j hic hjd
  have hz : ((↑(W⁻¹) : Matrix I I K) * (R - 1) * (W : Matrix I I K)) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l = b
    · subst l
      rw [hright j hjd, mul_zero]
    · have hh : (((↑(W⁻¹) : Matrix I I K) * (R - 1)) i l) = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hk : k = a
        · subst k
          rw [hleft i hic, zero_mul]
        · have hs : (R - 1) k l = 0 := sub_eq_zero.mpr (hR k l hk hl)
          rw [hs, mul_zero]
      rw [hh, zero_mul]
  have he : (↑(W⁻¹) : Matrix I I K) * (R - 1) * (W : Matrix I I K) =
      (↑(W⁻¹) : Matrix I I K) * R * (W : Matrix I I K) - 1 := by
    rw [mul_sub, sub_mul, mul_one, Units.inv_mul]
  rw [he] at hz
  exact sub_eq_zero.mp hz

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryMatrixSupport
