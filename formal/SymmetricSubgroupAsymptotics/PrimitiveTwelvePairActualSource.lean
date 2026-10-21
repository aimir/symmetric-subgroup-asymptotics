import SymmetricSubgroupAsymptotics.TwelvePairOriginalSource
import SymmetricSubgroupAsymptotics.TraceyRefinedInducedModuleProof
import SymmetricSubgroupAsymptotics.TraceyPermutationFormulaConsequences
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileParity
import SymmetricSubgroupAsymptotics.PrimitiveTwelveExactProfileNormalGenerators

/-! A primitive actual twelve-point top supplies the width24 complete
binary-pair source directly. Only the retained ordinary simple-index
estimate and generator theorem are used; neither catalogue correspondence
nor a small quotient/socle assertion is an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveTwelvePairActualSource
open Non2UnipotentPrefixFiniteMenu PrimitiveSocleRawStructure
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- Twelve is not a prime power, so the proved affine alternative cannot
occur on the actual primitive twelve-point action. -/
theorem nonaffine {G : Type} [Group G] [Finite G] [MulAction G (Fin 12)]
    [FaithfulSMul G (Fin 12)] [MulAction.IsPreprimitive G (Fin 12)] :
    Nonempty (NonaffineData G (Fin 12)) := by
  cases Classical.choice (publishedONanScottStructure G (Fin 12)) with
  | inl D => exact ⟨D⟩
  | inr A =>
      have hp : A.p=2 := A.prime_eq_two_of_even_degree (0 : Fin 12) (by decide)
      obtain ⟨d,hd⟩ := A.degree_eq_prime_power (0 : Fin 12)
      rw [hp] at hd
      exact (PrimitiveTwelveExactProfileNormalGenerators.twelve_not_two_power d hd).elim

/-- The actual twelve-point permutation module costs at most four
vectors because the prime-to-three factor is three. -/
theorem natural_uniform {G : Type} [Group G] [Finite G]
    [MulAction G (Fin 12)] [MulAction.IsPretransitive G (Fin 12)] :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) G (Fin 12)) 4 := by
  obtain ⟨H,hb,hu⟩ := traceyRefinedInducedModuleInput_proved.permutation
    G (Fin 12) 0 (by simp)
  have hp := hb.primeTo 3 1 Nat.prime_three (by decide) (by decide)
    (by norm_num : 3^1 ∣ Nat.card (Fin 12))
  have hH : H ≤ 4 := by
    norm_num at hp
    exact_mod_cast hp
  exact uniformSubrepresentationGeneratorBound_mono _ hu hH

variable (p : PreE7PairActionClass 12)
    (F : BinaryPairFrame (preE7PairAction 12 p) (Fin 12))
    [MulAction.IsPreprimitive F.top.range (Fin 12)]

def source
    (hindex : PublishedSimpleIndexBounds)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (hMN : PermutationSubgroupGeneratorBound) :
    PreE7RankTailSourceOrYonedaTopData 24
      (preE7SmallPairNonPairAction 12 (by decide) p) := by
  let D : NonaffineData F.top.range (Fin 12) := Classical.choice nonaffine
  have ht : Nat.card F.top.range ≤ 2^29 := degreeTwelve_group_order_le
  exact TwelvePairOriginalSource.source p F ht (403/150)
    (by norm_num [halfDegree,preE7CharacterRho])
    (fun N _ b => TwelvePairActualKernelQuotientSum.quotient_sum_le F ht
      natural_uniform
      (fun M _ b J => D.degreeTwelve_actual_normal_quotient_epi_le
        hindex hZmud lit hMN M b J) N b)

end SymmetricSubgroupAsymptotics.PrimitiveTwelvePairActualSource
