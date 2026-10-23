import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalFiniteBruhatCover
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckPairNormalizerCardinality
import SymmetricSubgroupAsymptotics.FiniteFourFactorCoverCardinality

/-! An upper bound on the ORIGINAL triality group from the actual
finite U-D-W-U cover. The diagonal factor is bounded by its faithful
scalar actions; no equality with a generated torus is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOrderUpper
open CFSGTrialityGeckOriginalFiniteBruhatCover CFSGTrialityGeckPairNormalizerCardinality
open CFSGTrialityGeckOriginalPairNormalizer CFSGTrialityGeckOriginalRootFamily
open CFSGTrialityGeckGeneratedOriginalProjection CFSGTrialityD4FiniteWeylMenu

local instance (q:CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Finite (CFSG.Models.TrialityD4 q) := Finite.of_surjective
  (generatedToOriginal q) (generatedToOriginal_surjective q)

theorem original_order_le_twelve_mul_power (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (hn:¬IsMulCommutative (CFSG.Models.TrialityD4 q)) :
    Nat.card (CFSG.Models.TrialityD4 q)≤12*q.order^28 := by
  have hc := FiniteFourFactorCoverCardinality.card_le_of_cover
    (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)) (originalPairNormalizer q)
    (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q))
    (originalMenuWord q) (exists_original_finite_cell q)
  calc
    Nat.card (CFSG.Models.TrialityD4 q)≤
        Nat.card (originalSylow q)*Nat.card (originalPairNormalizer q)*Nat.card Menu*
          Nat.card (originalSylow q) := hc
    _≤q.order^12*q.order^4*12*q.order^12 := by
      rw [menu_card]
      exact Nat.mul_le_mul (Nat.mul_le_mul_right 12
        (Nat.mul_le_mul (originalSylow_card_le q) (originalPairNormalizer_card_le q hn)))
        (originalSylow_card_le q)
    _=12*q.order^28 := by ring

theorem original_order_le_power (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (hn:¬IsMulCommutative (CFSG.Models.TrialityD4 q)) :
    Nat.card (CFSG.Models.TrialityD4 q)≤q.order^32 := by
  have hq : 2≤q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have h12 : 12≤q.order^4 := (by decide : 12≤2^4).trans (Nat.pow_le_pow_left hq 4)
  exact (original_order_le_twelve_mul_power q hn).trans
    ((Nat.mul_le_mul_right (q.order^28) h12).trans_eq (by ring))

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOrderUpper
