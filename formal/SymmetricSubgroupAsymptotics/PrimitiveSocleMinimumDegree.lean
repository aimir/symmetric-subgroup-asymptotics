import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScott

/-! A component proper-index lower bound transfers through either raw
socle degree form. No identification of the primitive action is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.degree_lower_of_proper_index_lower
    (D : NonaffineData G X) (n : ℕ)
    (hindex : ∀ H : Subgroup D.Simple, H ≠ ⊤ → n ≤ H.index) :
    n ≤ Nat.card X := by
  rcases D.indexForm with ⟨H, hH, hdegree⟩ | ⟨a, ha, hdegree⟩
  · rw [hdegree]
    exact (hindex H hH).trans
      (Nat.le_self_pow (Nat.ne_of_gt D.factorCount_pos) H.index)
  · have ha0 : a ≠ 0 := by have hp := D.factorCount_pos; omega
    have hbot : n ≤ Nat.card D.Simple := by
      have hb := hindex ⊥ bot_ne_top
      simpa only [Subgroup.index_bot] using hb
    rw [hdegree]
    exact hbot.trans (Nat.le_self_pow ha0 (Nat.card D.Simple))

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
