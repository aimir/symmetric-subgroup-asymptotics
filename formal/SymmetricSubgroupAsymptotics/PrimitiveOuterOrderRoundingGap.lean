import SymmetricSubgroupAsymptotics.SimpleSocleQuotientOrderBudget
import SymmetricSubgroupAsymptotics.SemisimpleCompressionRoundingGap

/-! Exact finite-width rounding margins from the existing logarithmic
outer-order bound. The finite receipt is arithmetic on degrees12..44 and
quotient orders at most16, not a group-classification table. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private theorem twelveToFortyFour_rounding_receipt :
    ∀ r : Fin 45,∀ q : Fin 17,12≤r.val → 2^q.val≤r.val^3 →
      max 2 q.val+1≤evenWidth r.val := by decide +kernel

theorem quotientOrder_twoPow_le_cube_of_log {q ell : ℕ} (hell : 0<ell)
    (hq : (q : ℝ)≤3*Real.logb 2 ell) : 2^q≤ell^3 := by
  have hq' : (q : ℝ)≤Real.logb 2 ((ell : ℝ)^3) := by
    simpa only [Real.logb_pow] using hq
  have hp := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ)<2)
    (pow_pos (by exact_mod_cast hell) 3)).mp hq'
  rw [Real.rpow_natCast] at hp
  exact_mod_cast hp

/-- A logarithmic quotient-order bound leaves the exact one-unit parity
margin on every degree12 through44, including odd degrees. -/
theorem quotientOrder_roundingGap_of_cube {r q : ℕ}
    (hr : 12≤r) (h44 : r≤44) (hq : 2^q≤r^3) :
    max 2 q+1≤evenWidth r := by
  have h17 : q<17 := by
    by_contra h
    have hq17 : 17≤q := by omega
    have hbad : (131072 : ℕ)≤85184 := calc
      131072=2^17 := by decide
      _ ≤ 2^q := pow_le_pow_right₀ (by decide : (1 : ℕ)≤2) hq17
      _ ≤ r^3 := hq
      _ ≤ 44^3 := Nat.pow_le_pow_left h44 3
      _ = 85184 := by decide
    omega
  exact twelveToFortyFour_rounding_receipt ⟨r,by omega⟩ ⟨q,h17⟩ hr hq

namespace PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.oneFactor_roundingGap_twelveToFortyFour
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (hindex : PublishedSimpleIndexBounds) (hr : 12≤Nat.card X) (h44 : Nat.card X≤44) :
    max 2 (Nat.card (G⧸finiteGroupSocle G))+1≤evenWidth (Nat.card X) := by
  obtain ⟨ell,_,hf,he,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
  apply quotientOrder_roundingGap_of_cube hr h44
  exact (quotientOrder_twoPow_le_cube_of_log (by omega) hlog).trans
    (Nat.pow_le_pow_left he 3)

end PrimitiveSocleRawStructure
end SymmetricSubgroupAsymptotics
