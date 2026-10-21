import SymmetricSubgroupAsymptotics.SimpleSocleQuotientOrderBudget

/-! The ordinary simple-index inequality forces one full-socle factor
below degree25. This applies to the actual raw socle chart, without any
bounded primitive correspondence. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.factorCount_one_of_degree_lt_twentyFive
    (D : NonaffineData G X) (hindex : PublishedSimpleIndexBounds)
    (hdegree : Nat.card X < 25) : D.factorCount = 1 := by
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hf : 5 ≤ ell := nonabelianSimple_leastProperIndex_five_le
    (fun hc => D.noncommutative (isMulCommutative_iff.mpr hc)) hell.1
  have horder := (hindex D.Simple D.noncommutative ell hell).1
  have hd := primitiveSocle_power_le_degree hf horder (D.degreeForm hell)
  by_contra h
  have hk : 2 ≤ D.factorCount := by have hp := D.factorCount_pos; omega
  have h25 : 25 ≤ ell ^ D.factorCount := calc
    25 = 5 ^ 2 := by decide
    _ ≤ ell ^ 2 := Nat.pow_le_pow_left hf 2
    _ ≤ ell ^ D.factorCount := pow_le_pow_right₀ (by omega : 1 ≤ ell) hk
  omega

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
