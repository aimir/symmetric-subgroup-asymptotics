import SymmetricSubgroupAsymptotics.SemisimpleCompressionRoundingGap

/-! A strict local degree reduction pays the global parity margin as
soon as there are two blocks. Only one parity unit is lost globally;
it is unnecessary to lose one unit separately on every odd local block. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem strictDegree_manyBlocks_gap {r q s : ℕ} (hq : 0 < q) (hs : 2 ≤ s)
    (hgap : q + 1 ≤ r) :
    2 * max 2 (q*s) + s ≤ 2 * evenWidth (r*s) := by
  have hq1 : 1 ≤ q := hq
  have hqs : 2 ≤ q*s := by
    simpa only [one_mul] using Nat.mul_le_mul hq1 hs
  rw [max_eq_right hqs]
  have hm := Nat.mul_le_mul_right s hgap
  have he := width_le_evenWidth_add_one (r*s)
  simp only [Nat.add_mul,one_mul] at hm
  omega

namespace Non2UnipotentPrefixFiniteMenu.PreE7SemisimpleMarginData

theorem margin_of_strict_degree_manyBlocks {r q s : ℕ}
    (hr : r ≤ 512) (hq : 0 < q) (hs : 2 ≤ s) (hgap : q + 1 ≤ r) :
    preE7CharacterRho * (r*s) ≤
      ((evenWidth (r*s) : ℝ) - (max 2 (q*s) : ℕ)) / 8 := by
  have hg := strictDegree_manyBlocks_gap hq hs hgap
  have hgR : 2 * ((max 2 (q*s) : ℕ) : ℝ) + (s : ℝ) ≤
      2 * (evenWidth (r*s) : ℝ) := by exact_mod_cast hg
  have hrR : (r : ℝ) ≤ 512 := by exact_mod_cast hr
  have hsR : (0 : ℝ) ≤ s := by positivity
  have hm := mul_le_mul_of_nonneg_right hrR hsR
  unfold preE7CharacterRho
  nlinarith

end Non2UnipotentPrefixFiniteMenu.PreE7SemisimpleMarginData
end SymmetricSubgroupAsymptotics
