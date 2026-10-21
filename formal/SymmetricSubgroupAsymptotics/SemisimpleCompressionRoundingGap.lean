import SymmetricSubgroupAsymptotics.SemisimpleCompressionWithMargin
import SymmetricSubgroupAsymptotics.Non2PreE7ExactBlockCompression

/-! A fixed positive local rounding gap survives an arbitrary number of
actual blocks. For local degree at most1024 it pays precisely the existing
rho=1/8192 padding margin, without requiring a two-thirds ratio. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- The largest even width of a product dominates the product of the
largest even local width. No parity of the block count is assumed. -/
theorem evenWidth_mul_le (r s : ℕ) : evenWidth r*s ≤ evenWidth (r*s) := by
  apply even_le_evenWidth
  · refine ⟨halfDegree r*s,?_⟩
    simp only [evenWidth,two_mul,Nat.add_mul]
  · exact Nat.mul_le_mul_right s (evenWidth_le r)

/-- A local gap of one becomes a gap of at least the number of blocks;
`max 2` is carried throughout, including a trivial compressed quotient. -/
theorem roundingGap_mul {r q s : ℕ} (hs : 0 < s)
    (hgap : max 2 q+1 ≤ evenWidth r) :
    max 2 (q*s)+s ≤ evenWidth (r*s) := by
  have hmax : max 2 (q*s) ≤ max 2 q*s := by
    apply max_le
    · have hm := Nat.mul_le_mul_left (max 2 q) (show 1 ≤ s by omega)
      have htwo := le_max_left 2 q
      omega
    · exact Nat.mul_le_mul_right s (le_max_right 2 q)
  have hm := Nat.mul_le_mul_right s hgap
  have he := evenWidth_mul_le r s
  simp only [Nat.add_mul,one_mul] at hm
  omega

namespace Non2UnipotentPrefixFiniteMenu.PreE7SemisimpleMarginData

/-- Every positive local gap suffices uniformly in the block count when
its actual local degree is at most1024. -/
theorem margin_of_local_rounding_gap {r q s : ℕ} (hr : r ≤ 1024) (hs : 0 < s)
    (hgap : max 2 q+1 ≤ evenWidth r) :
    preE7CharacterRho*(r*s) ≤ 
      ((evenWidth (r*s) : ℝ)-(max 2 (q*s) : ℕ))/8 := by
  have hg := roundingGap_mul hs hgap
  have hgR : ((max 2 (q*s) : ℕ) : ℝ)+(s : ℝ) ≤ evenWidth (r*s) := by exact_mod_cast hg
  have hrR : (r : ℝ) ≤ 1024 := by exact_mod_cast hr
  have hsR : (0 : ℝ) ≤ s := by positivity
  have hm := mul_le_mul_of_nonneg_right hrR hsR
  unfold preE7CharacterRho
  nlinarith

/-- The one-block case is available without a lower-degree side condition;
the gap itself already controls the `max 2` seed. -/
theorem margin_of_rounding_gap {r q : ℕ} (hr : r ≤ 1024)
    (hgap : max 2 q+1 ≤ evenWidth r) :
    preE7CharacterRho*r ≤ ((evenWidth r : ℝ)-(max 2 q : ℕ))/8 := by
  simpa only [Nat.mul_one,Nat.cast_one,mul_one] using
    margin_of_local_rounding_gap hr (by decide : 0 < 1) hgap

end Non2UnipotentPrefixFiniteMenu.PreE7SemisimpleMarginData
end SymmetricSubgroupAsymptotics
