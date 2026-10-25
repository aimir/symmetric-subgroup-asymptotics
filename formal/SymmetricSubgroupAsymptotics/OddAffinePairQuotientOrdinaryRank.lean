import SymmetricSubgroupAsymptotics.OddPrimePowerAffineBlockOrdinaryGeneratorInduction

/-! Retain the genuine ordinary rank of the actual inverse-pair quotient
instead of replacing it by a global smaller-action estimate. Both discarded
kernels are actual abelian kernels, so their proved ambient normal generators
may be used for ordinary extension. No desired quotient rank or global
permutation-generator input is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OddAffinePairQuotientOrdinaryRank
open OddPrimePowerAffineBlockCoordinates OddPrimePowerAffineBlockPairCompression

variable {G Ω X : Type} [Group G] [Finite G] [Finite Ω] [Finite X]
    [MulAction G Ω] [MulAction G X] [MulAction.IsPretransitive G X]
    [FaithfulSMul G Ω]
    (b : Ω → X) (hb : ∀ (g : G) (ω : Ω), b (g • ω) = g • b ω)
    (x₀ : X) [Nontrivial (originalBlockFibre b x₀)]
    (P : PrimitiveAffineProfile (Component b hb x₀) (originalBlockFibre b x₀))
    (hprimitive : MulAction.IsPreprimitive (Component b hb x₀) (originalBlockFibre b x₀))
    (C : P.ElementaryChart hprimitive) (origin : originalBlockFibre b x₀)

include hprimitive C origin in
theorem genRank_le_pairQuotient_add_dimension_mul_half [Nontrivial X] :
    MarkedC4.genRank G ≤
      MarkedC4.genRank (LinearQuotient b hb x₀ P origin ⧸
        pairKernel b hb x₀ P hprimitive C origin) + (C.d+1)*(Nat.card X/2) := by
  let E := pairKernel b hb x₀ P hprimitive C origin
  letI : IsMulCommutative (translationKernel b hb x₀ P origin) :=
    translationKernel_isMulCommutative b hb x₀ P hprimitive C origin
  letI : IsMulCommutative (QuotientGroup.mk' (translationKernel b hb x₀ P origin)).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hG := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    (QuotientGroup.mk' (translationKernel b hb x₀ P origin))
    (QuotientGroup.mk'_surjective (translationKernel b hb x₀ P origin))
  rw [QuotientGroup.ker_mk'] at hG
  letI : IsMulCommutative E := pairKernel_isMulCommutative b hb x₀ P hprimitive C origin
  letI : IsMulCommutative (QuotientGroup.mk' E).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have hQ := AbelianKernelOrdinaryGeneration.genRank_le_quotient_add_normalGen
    (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
  rw [QuotientGroup.ker_mk'] at hQ
  have hsign := normalGen_pairKernel_le_half b hb x₀ P hprimitive C origin
  have htranslation :=
    OddPrimePowerAffineBlockOrdinaryGeneratorInduction.normalGen_translationKernel_le_half
      b hb x₀ P hprimitive C origin
  have hgen : MarkedC4.genRank G ≤
      MarkedC4.genRank (LinearQuotient b hb x₀ P origin ⧸ E) +
        MarkedC4.normalGen E + MarkedC4.normalGen (translationKernel b hb x₀ P origin) :=
    hG.trans (Nat.add_le_add_right hQ _)
  change MarkedC4.normalGen E ≤ Nat.card X/2 at hsign
  change MarkedC4.genRank G ≤
    MarkedC4.genRank (LinearQuotient b hb x₀ P origin ⧸ E) + (C.d+1)*(Nat.card X/2)
  nlinarith only [hgen,hsign,htranslation]

end SymmetricSubgroupAsymptotics.OddAffinePairQuotientOrdinaryRank
