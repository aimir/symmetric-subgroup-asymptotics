import SymmetricSubgroupAsymptotics.OriginalBlockOrdinaryCompressionState
import SymmetricSubgroupAsymptotics.ActualWreathChiefUnitMinimumRate
import SymmetricSubgroupAsymptotics.ActualWreathUniformLocalOrderCost
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure

/-! A quadratic-logarithmic ordinary chief charge for the actual affine
component. The regular-normal profile's genuine order bound suffices;
no elementary-abelian inference, primitive action, Tracey or MN premise
is silently added. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineUniformLocalCharge

theorem card_le_binary_log_square
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (P : PrimitiveAffineProfile G X) (x : X) :
    Nat.card G ≤ 2 ^ (Nat.log 2 (Nat.card X) + 1) ^ 2 := by
  let r := Nat.card X
  let l := Nat.log 2 r
  have hr : r ≤ 2 ^ (l + 1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) r).le
  calc
    Nat.card G ≤ Nat.card X * Nat.card X ^ Nat.log 2 (Nat.card X) :=
      P.card_le_domain_pow_log x
    _ = r ^ (l + 1) := by simp only [r,l,pow_succ']
    _ ≤ (2 ^ (l + 1)) ^ (l + 1) := Nat.pow_le_pow_left hr _
    _ = 2 ^ (Nat.log 2 (Nat.card X) + 1) ^ 2 := by
      dsimp only [l,r]
      rw [pow_two,pow_mul]

theorem cardFactors_le_log_square
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (P : PrimitiveAffineProfile G X) (x : X) :
    ArithmeticFunction.cardFactors (Nat.card G) ≤ (Nat.log 2 (Nat.card X) + 1) ^ 2 := by
  have hc := card_le_binary_log_square P x
  have hcR : (Nat.card G : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (Nat.card X) + 1) ^ 2 := by
    exact_mod_cast hc
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (Nat.card_pos (α := G)) : (0 : ℝ) < Nat.card G) hcR
  have hlog : Real.logb 2 (Nat.card G : ℝ) ≤
      (((Nat.log 2 (Nat.card X) + 1) ^ 2 : ℕ) : ℝ) := by
    simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),mul_one]
      using hl
  have hh := (ActualWreathUniformLocalOrderCost.cardFactors_le_logb
    (Nat.card G) (Nat.card_pos (α := G)).ne').trans hlog
  exact_mod_cast hh

theorem original_block_cost
    {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]
    (P : PrimitiveAffineProfile block.Component block.Fibre) (i : block.Points) :
    (MarkedC4.genRank J : ℝ) ≤
      (((Nat.log 2 (Nat.card block.Fibre) + 2 : ℕ) : ℝ) ^ 2) *
        ActualWreathChiefUnitMinimumRate.rate (Nat.card block.Points) +
          MarkedC4.genRank block.Top := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have hs := ActualWreathChiefUnitMinimumRate.genRank_le_cardFactors_mul_rate
    (OriginalBlockOrdinaryCompressionState.initialState J block) i hI
  simp only [Fintype.card_eq_nat_card] at hs
  have hc := cardFactors_le_log_square P (⟨x₀,block.map_base⟩ : block.Fibre)
  have hc' : ArithmeticFunction.cardFactors (Nat.card block.Component) ≤
      (Nat.log 2 (Nat.card block.Fibre) + 2) ^ 2 :=
    hc.trans (Nat.pow_le_pow_left (by omega) 2)
  have hcR : (ArithmeticFunction.cardFactors (Nat.card block.Component) : ℝ) ≤
      (((Nat.log 2 (Nat.card block.Fibre) + 2 : ℕ) : ℝ) ^ 2) := by
    exact_mod_cast hc'
  have hr := ActualWreathChiefUnitMinimumRate.one_le_rate (Nat.card block.Points)
    block.degrees_ge_two.2
  change (MarkedC4.genRank J : ℝ) ≤
    (ArithmeticFunction.cardFactors (Nat.card block.Component) : ℝ) *
      ActualWreathChiefUnitMinimumRate.rate (Nat.card block.Points) +
        MarkedC4.genRank block.Top at hs
  exact hs.trans (add_le_add (mul_le_mul_of_nonneg_right hcR
    (by linarith only [hr])) le_rfl)

end SymmetricSubgroupAsymptotics.PrimitiveAffineUniformLocalCharge
