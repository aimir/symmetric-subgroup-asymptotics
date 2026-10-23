import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalFiniteBruhatCover
import SymmetricSubgroupAsymptotics.CFSGFFourE6PairNormalizerCardinality
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalComponentUpper
import SymmetricSubgroupAsymptotics.FiniteFourFactorCoverCardinality

/-! Upper order of the original F4 group from its actual finite Bruhat cover.
The opposed-pair normalizer is counted directly; no assertion that it equals
the displayed product torus is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalOrderUpper
open CFSG.Models.Chevalley CFSGFFourE6OriginalFiniteBruhatCover
open CFSGFFourE6OriginalPairScalarAction CFSGFFourE6OriginalProjection
open CFSGFFourE6FiniteWeylMenu CFSGFFourE6PairNormalizerCardinality
open PrimitiveSocleRawStructure

theorem original_order_le (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (hn : ¬IsMulCommutative (Projective CartanMatrix.F₄ K)) :
    Nat.card (Projective CartanMatrix.F₄ K) ≤ Nat.card K ^ 63 := by
  letI := original_finite K
  let U : Subgroup (Projective CartanMatrix.F₄ K) := originalPositiveSylow K p
  let N := originalPairNormalizer K p
  have hU : Nat.card U ≤ Nat.card K ^ 24 := originalPositiveSylow_card_le K p
  have hN : Nat.card N ≤ Nat.card K ^ 4 := originalPairNormalizer_card_le K p hn
  have hcover := FiniteFourFactorCoverCardinality.card_le_of_cover U N U
    (originalMenuWord K) (exists_original_finite_cell K p)
  have hsmall : 1152 ≤ Nat.card K ^ 11 :=
    (by decide : 1152 ≤ 2 ^ 11).trans
      (Nat.pow_le_pow_left Finite.one_lt_card 11)
  calc
    Nat.card (Projective CartanMatrix.F₄ K) ≤
        Nat.card K ^ 24 * Nat.card K ^ 4 * 1152 * Nat.card K ^ 24 :=
      hcover.trans (Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul hU hN) relativeWeylRange_card_le) hU)
    _ = 1152 * Nat.card K ^ 52 := by ring
    _ ≤ Nat.card K ^ 11 * Nat.card K ^ 52 := Nat.mul_le_mul_right _ hsmall
    _ = Nat.card K ^ 63 := by rw [← pow_add]

theorem typeFFour_outer_le_cube (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.F4 q)] :
    Nat.card (Outer (CFSG.Models.F4 q)) ≤ q.order ^ 3 := by
  exact (CFSGFFourE6OriginalOuterBound.typeFFour_outer_card_le_two_exponent q).trans
    ((by omega : 2 * q.exponent ≤ 6 * q.exponent).trans
      (CFSGExceptionalOriginalComponentUpper.six_exponent_le_order_cube q))

theorem typeFFour_order_mul_outer_le (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.F4 q)]
    (hn : ¬IsMulCommutative (CFSG.Models.F4 q)) :
    Nat.card (CFSG.Models.F4 q) * Nat.card (Outer (CFSG.Models.F4 q)) ≤ q.order ^ 66 := by
  have h := original_order_le q.Field q.prime hn
  rw [q.card_field] at h
  exact (Nat.mul_le_mul h (typeFFour_outer_le_cube q)).trans_eq (by ring)

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalOrderUpper
