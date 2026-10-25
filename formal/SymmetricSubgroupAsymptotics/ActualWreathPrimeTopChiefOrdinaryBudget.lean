import SymmetricSubgroupAsymptotics.InducedMinimumPrimeIndexCapacity
import SymmetricSubgroupAsymptotics.ActualWreathChiefPrimeMultiplicityBudget

/-! At a prime number of actual blocks, every elementary edge of the SAME
local-chief trace costs at most its local dimension. Nonabelian edges keep
their genuine selected internal simple-factor ranks, bounded by the prime
multiplicity of the same local kernel. The result is an ordinary-generator
budget in the original correlated source, not an assumed module capacity
or a replacement full direct product. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathPrimeTopChiefOrdinaryBudget
open FiniteGroupPrimeMultiplicityGenerators

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

theorem elementary_capacity_le_dimension (S : ActualWreathCompressionState Q I)
    {D' : Type} [Group D'] (phi : S.D →* D')
    (C : ElementaryMinimalNormalChart phi.ker) (i : I)
    (hprime : (Fintype.card I).Prime) :
    ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i ≤
      Module.finrank (ZMod C.p) C.V := by
  exact InducedMinimumPrimeIndexCapacity.prime_index
    (S.topPointStabilizer i)
    (ActualWreathAffineCapacity.localRepresentation S phi C i)
    (Fintype.card I) hprime (S.topPointStabilizer_index i)

/-- The prime-top improvement is obtained at each actual elementary
constructor, before the chief record forgets its inducing representation. -/
theorem cost_le_cardFactors {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hprime : (Fintype.card I).Prime) :
    n ≤ ArithmeticFunction.cardFactors (Nat.card S.D) := by
  induction h with
  | terminal S hD => exact Nat.zero_le _
  | vanishing S D' phi hphi hmin hz n next ih =>
      exact ih.trans (cardFactors_mono_of_dvd
        (Nat.card_pos (α := D')).ne' (Nat.card_pos (α := S.D)).ne'
        (Subgroup.card_dvd_of_surjective phi hphi))
  | elementary S D' phi hphi hmin C n next ih =>
      have hc := elementary_capacity_le_dimension S phi C i hprime
      have hk : ArithmeticFunction.cardFactors (Nat.card phi.ker) =
          Module.finrank (ZMod C.p) C.V := by
        rw [ActualWreathChiefHalfOrderBudget.elementary_kernel_card phi C]
        exact ArithmeticFunction.cardFactors_apply_prime_pow C.p_prime
      rw [← hk] at hc
      change n ≤ ArithmeticFunction.cardFactors (Nat.card D') at ih
      have hh := Nat.add_le_add hc ih
      rw [← ArithmeticFunction.cardFactors_mul
        (Nat.card_pos (α := phi.ker)).ne' (Nat.card_pos (α := D')).ne',
        ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi] at hh
      exact hh
  | nonabelian S D' phi hphi hmin hnc hne C j n next ih =>
      have hc := ActualWreathChiefPrimeMultiplicityBudget.factor_genRank_le_local_cardFactors
        S.rho phi S.rho_injective C j
      change n ≤ ArithmeticFunction.cardFactors (Nat.card D') at ih
      have hh := Nat.add_le_add hc ih
      rw [← ArithmeticFunction.cardFactors_mul
        (Nat.card_pos (α := phi.ker)).ne' (Nat.card_pos (α := D')).ne',
        ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi] at hh
      exact hh

theorem genRank_le_cardFactors_add_top (S : ActualWreathCompressionState Q I)
    (i : I) (hprime : (Fintype.card I).Prime) :
    MarkedC4.genRank S.A ≤ ArithmeticFunction.cardFactors (Nat.card S.D) +
      MarkedC4.genRank Q := by
  obtain ⟨n, hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  exact (ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hn).trans
    (Nat.add_le_add_right (cost_le_cardFactors hn hprime) _)

theorem exists_generating_finset (S : ActualWreathCompressionState Q I)
    (i : I) (hprime : (Fintype.card I).Prime) :
    ∃ F : Finset S.A, Subgroup.closure (F : Set S.A) = ⊤ ∧
      F.card ≤ ArithmeticFunction.cardFactors (Nat.card S.D) + MarkedC4.genRank Q := by
  obtain ⟨F,hcard,hgen⟩ := MarkedC4.genRank_spec (G := S.A)
  exact ⟨F,hgen,hcard.le.trans (genRank_le_cardFactors_add_top S i hprime)⟩

end SymmetricSubgroupAsymptotics.ActualWreathPrimeTopChiefOrdinaryBudget
