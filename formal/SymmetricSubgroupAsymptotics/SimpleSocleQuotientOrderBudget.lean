import SymmetricSubgroupAsymptotics.PrimitiveSocleRawProfile
import SymmetricSubgroupAsymptotics.PrimitiveRelativeHeadOrderBudgets

/-! The retained ordinary simple-index bound controls the actual one-factor
socle quotient order. For the bounded head consumer only its ternary
valuation is needed, rather than the stronger half-degree order estimate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open OuterWreathPermutationCompression

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.oneFactor_quotient_log_bound
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (hindex : PublishedSimpleIndexBounds) :
    ∃ ell : ℕ,LeastProperIndex D.Simple ell ∧ 5≤ell ∧ ell≤Nat.card X ∧
      (Nat.card (G⧸finiteGroupSocle G) : ℝ)≤3*Real.logb 2 ell := by
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  have hf : 5≤ell := nonabelianSimple_leastProperIndex_five_le
    (fun h => D.noncommutative (isMulCommutative_iff.mpr h)) hell.1
  obtain ⟨horder,houter⟩ := hindex D.Simple D.noncommutative ell hell
  have hdegree := primitiveSocle_power_le_degree hf horder (D.degreeForm hell)
  have he : ell≤Nat.card X := by simpa only [hk,pow_one] using hdegree
  have hw : Nat.card (Wreath (Outer D.Simple) D.factorCount)=Nat.card (Outer D.Simple) := by
    rw [hk]
    exact wreath_one_card (Outer D.Simple)
  have hc : Nat.card (G⧸finiteGroupSocle G)≤Nat.card (Outer D.Simple) :=
    (Nat.card_le_card_of_injective D.quotientEmbedding D.quotientEmbedding_injective).trans_eq hw
  exact ⟨ell,hell,hf,he,(by exact_mod_cast hc :
    (Nat.card (G⧸finiteGroupSocle G) : ℝ)≤Nat.card (Outer D.Simple)).trans houter⟩

theorem quotient_order_lt_fifteen_of_log {q ell : ℕ}
    (hell : 0<ell) (hsmall : ell<30)
    (hq : (q : ℝ)≤3*Real.logb 2 ell) : q<15 := by
  have hp : ell^3<2^15 := calc
    ell^3≤29^3 := Nat.pow_le_pow_left (by omega) 3
    _ < 2^15 := by decide
  have hpR : ((ell : ℝ)^3)<(2 : ℝ)^15 := by exact_mod_cast hp
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ)<2)
    (pow_pos (by exact_mod_cast hell) 3) hpR
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one] at hl
  have hqR : (q : ℝ)<15 := hq.trans_lt hl
  exact_mod_cast hqR

theorem ternaryValuation_le_two_of_lt_fifteen (q : ℕ) (hq : q<15) :
    q.factorization 3≤2 := by
  have h : ∀ q : Fin 15,q.val.factorization 3≤2 := by decide +kernel
  exact h ⟨q,hq⟩

theorem NonaffineData.oneFactor_quotient_order_lt_fifteen
    (D : NonaffineData G X) (hk : D.factorCount=1)
    (hindex : PublishedSimpleIndexBounds) (hsmall : Nat.card X<30) :
    Nat.card (G⧸finiteGroupSocle G)<15 := by
  obtain ⟨ell,_,hf,he,hlog⟩ := D.oneFactor_quotient_log_bound hk hindex
  exact quotient_order_lt_fifteen_of_log (by omega) (by omega) hlog

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
