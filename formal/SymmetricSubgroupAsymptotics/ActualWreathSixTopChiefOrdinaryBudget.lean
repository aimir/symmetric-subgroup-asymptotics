import SymmetricSubgroupAsymptotics.InducedMinimumSmallPrimeMultipleCapacity
import SymmetricSubgroupAsymptotics.ActualWreathPrimeTopChiefOrdinaryBudget

/-! Exact index-six induced capacities charge at most twice each actual
local elementary dimension. The SAME chief trace pays genuine internal
nonabelian factor ranks, never a normal-generation replacement. In local
order dividing six the whole base costs at most four ordinary generators
above the actual top. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathSixTopChiefOrdinaryBudget
open FiniteGroupPrimeMultiplicityGenerators

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

theorem cost_le_two_cardFactors {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hcard : Fintype.card I = 6) :
    n ≤ 2*ArithmeticFunction.cardFactors (Nat.card S.D) := by
  induction h with
  | terminal S hD => exact Nat.zero_le _
  | vanishing S D' phi hphi hmin hz n next ih =>
      exact ih.trans (Nat.mul_le_mul_left 2 (cardFactors_mono_of_dvd
        (Nat.card_pos (α := D')).ne' (Nat.card_pos (α := S.D)).ne'
        (Subgroup.card_dvd_of_surjective phi hphi)))
  | elementary S D' phi hphi hmin C n next ih =>
      have hc := InducedMinimumSmallPrimeMultipleCapacity.six_index
        (S.topPointStabilizer i) (ActualWreathAffineCapacity.localRepresentation S phi C i)
        ((S.topPointStabilizer_index i).trans hcard)
      change ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i ≤
        2*Module.finrank (ZMod C.p) C.V at hc
      have hk : ArithmeticFunction.cardFactors (Nat.card phi.ker) =
          Module.finrank (ZMod C.p) C.V := by
        rw [ActualWreathChiefHalfOrderBudget.elementary_kernel_card phi C]
        exact ArithmeticFunction.cardFactors_apply_prime_pow C.p_prime
      rw [← hk] at hc
      change n ≤ 2*ArithmeticFunction.cardFactors (Nat.card D') at ih
      have hh := Nat.add_le_add hc ih
      rw [← Nat.mul_add,← ArithmeticFunction.cardFactors_mul
        (Nat.card_pos (α := phi.ker)).ne' (Nat.card_pos (α := D')).ne',
        ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi] at hh
      exact hh
  | nonabelian S D' phi hphi hmin hnc hne C j n next ih =>
      have hc := ActualWreathChiefPrimeMultiplicityBudget.factor_genRank_le_local_cardFactors
        S.rho phi S.rho_injective C j
      have hc2 : MarkedC4.genRank (C.factor j) ≤
          2*ArithmeticFunction.cardFactors (Nat.card phi.ker) := by omega
      change n ≤ 2*ArithmeticFunction.cardFactors (Nat.card D') at ih
      have hh := Nat.add_le_add hc2 ih
      rw [← Nat.mul_add,← ArithmeticFunction.cardFactors_mul
        (Nat.card_pos (α := phi.ker)).ne' (Nat.card_pos (α := D')).ne',
        ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi] at hh
      exact hh

theorem genRank_le_two_cardFactors_add_top (S : ActualWreathCompressionState Q I)
    (i : I) (hcard : Fintype.card I = 6) :
    MarkedC4.genRank S.A ≤ 2*ArithmeticFunction.cardFactors (Nat.card S.D) +
      MarkedC4.genRank Q := by
  obtain ⟨n,hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  exact (ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hn).trans
    (Nat.add_le_add_right (cost_le_two_cardFactors hn hcard) _)

theorem genRank_le_four_add_top_of_card_dvd_six (S : ActualWreathCompressionState Q I)
    (i : I) (hcard : Fintype.card I = 6) (horder : Nat.card S.D ∣ 6) :
    MarkedC4.genRank S.A ≤ 4+MarkedC4.genRank Q := by
  have hOmega : ArithmeticFunction.cardFactors (Nat.card S.D) ≤ 2 :=
    (cardFactors_mono_of_dvd (Nat.card_pos (α := S.D)).ne'
      (by decide : (6 : ℕ) ≠ 0) horder).trans_eq (by decide +kernel)
  have hh := genRank_le_two_cardFactors_add_top S i hcard
  omega

end SymmetricSubgroupAsymptotics.ActualWreathSixTopChiefOrdinaryBudget
