import SymmetricSubgroupAsymptotics.OrbitProfileUpperAssembly

/-! Real-valued original profile weights for insertion of a proved model
count. These are the same normalizers and occurrence factorials as in the
exact atlas cardinal identity. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

theorem labelledOrbitAtlas_card_real {ι : Type*} [Fintype ι] (Ω : ι → Type*)
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (m : ι → ℕ)
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) :
    (Nat.card (LabelledOrbitAtlas Ω m U) : ℝ) =
      ((∑ i, m i * Fintype.card (Ω i)).factorial : ℝ) /
        (∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) : ℝ) ^ m i *
          (m i).factorial) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (labelledOrbitAtlas_card_rat Ω m U)
  push_cast at h
  exact h

/-- Insert a proved count of the actual model family under the original
physical profile weight. Invariance acts jointly on all subgroup data. -/
theorem assembledOrbitProfile_card_le_real_of_model_bound
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (hnatural : OrbitProfileFamilyNatural Ω m U P) {C : ℝ}
    (hC : (Nat.card {K // P K} : ℝ) ≤ C) :
    (Nat.card (AssembledOrbitProfile P) : ℝ) ≤
      ((∑ i, m i * Fintype.card (Ω i)).factorial : ℝ) * C /
        (∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) : ℝ) ^ m i *
          (m i).factorial) := by
  have h : (Nat.card (AssembledOrbitProfile P) : ℝ) ≤
      Nat.card (LabelledOrbitAtlas Ω m U) * Nat.card {K // P K} := by
    exact_mod_cast assembledOrbitProfile_card_le hnatural
  have hb := h.trans (mul_le_mul_of_nonneg_left hC
    (Nat.cast_nonneg (Nat.card (LabelledOrbitAtlas Ω m U))))
  rw [labelledOrbitAtlas_card_real Ω m U] at hb
  convert hb using 1 <;> ring

theorem assembledOrbitProfileOn_card_le_real_of_model_bound
    {ι X : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}
    (hnatural : OrbitProfileFamilyNatural Ω m U P) (e : OrbitProfilePoints Ω m ≃ X)
    {C : ℝ} (hC : (Nat.card {K // P K} : ℝ) ≤ C) :
    (Nat.card (AssembledOrbitProfileOn P X) : ℝ) ≤
      ((∑ i, m i * Fintype.card (Ω i)).factorial : ℝ) * C /
        (∏ i, (Nat.card (Subgroup.normalizer (U i : Set (Equiv.Perm (Ω i)))) : ℝ) ^ m i *
          (m i).factorial) := by
  rw [← Nat.card_congr (assembledOrbitProfileEquivOn P e)]
  exact assembledOrbitProfile_card_le_real_of_model_bound hnatural hC

end SymmetricSubgroupAsymptotics
