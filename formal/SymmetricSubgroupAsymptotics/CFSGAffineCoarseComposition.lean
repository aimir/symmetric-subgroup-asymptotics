import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import SymmetricSubgroupAsymptotics.CFSGCompositionLengthCardinality
import SymmetricSubgroupAsymptotics.CFSGFiniteRankCardinality

/-! A catalogue-free logarithm-squared bound for actual affine profiles.
This coarse bound is a shared asymptotic foundation, not the sharp
published primitive composition or normal-generation theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAffineCoarseComposition
variable {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    [FaithfulSMul G X] (P : PrimitiveAffineProfile G X) (x : X)
include P x

theorem logb_card_le_domain_log :
    Real.logb 2 (Nat.card G) ≤
      (1 + (Nat.log 2 (Nat.card X) : ℝ)) * Real.logb 2 (Nat.card X) := by
  letI : Nonempty X := ⟨x⟩
  have hcard := P.card_le_domain_pow_log x
  have hc : (Nat.card G : ℝ) ≤ (Nat.card X : ℝ) * (Nat.card X : ℝ) ^ Nat.log 2 (Nat.card X) := by
    exact_mod_cast hcard
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by exact_mod_cast (Nat.card_pos (α := G))) hc
  have hx : (Nat.card X : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := X)).ne'
  rw [Real.logb_mul hx (pow_ne_zero _ hx), Real.logb_pow] at hh
  nlinarith

theorem composition_length_le_domain_log (s : SubnormalCompositionSeries G) :
    (s.chain.length : ℝ) ≤
      (1 + (Nat.log 2 (Nat.card X) : ℝ)) * Real.logb 2 (Nat.card X) :=
  (CFSGCompositionLengthCardinality.length_le_logb_card s).trans
    (logb_card_le_domain_log P x)

theorem subgroup_rank_le_domain_log (N : Subgroup G) :
    (Group.rank N : ℝ) ≤
      (1 + (Nat.log 2 (Nat.card X) : ℝ)) * Real.logb 2 (Nat.card X) :=
  (CFSGFiniteRankCardinality.subgroup_rank_le_logb_card G N).trans
    (logb_card_le_domain_log P x)

end SymmetricSubgroupAsymptotics.CFSGAffineCoarseComposition
