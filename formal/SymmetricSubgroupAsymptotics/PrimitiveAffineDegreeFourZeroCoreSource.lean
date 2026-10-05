import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCore
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourRegularTranslationSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientSource

/-!
# The degree-four zero-core source

Once the literal ternary core vanishes, the preceding structural theorem
identifies the quotient after the binary translation layer with a faithful
subgroup of the actual block top.  This file packages that faithful action
as the terminal comparator of the one-layer complete-source envelope.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The quotient after translations acting on the literal set of blocks. -/
def degreeFourZeroCoreTopAction :
    DegreeFourComplementQuotient block P →*
      Equiv.Perm (Fin (Nat.card block.Points)) :=
  (Finite.equivFin block.Points).permCongrHom.toMonoidHom.comp
    (block.Top.subtype.comp (binaryAffineQuotientTopMap block P))

theorem degreeFourZeroCoreTopAction_injective
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    Function.Injective (degreeFourZeroCoreTopAction block P) := by
  have htop : Function.Injective (binaryAffineQuotientTopMap block P) := by
    rw [← MonoidHom.ker_eq_bot_iff,
      binaryAffineQuotientTopMap_ker block P]
    exact degreeFourLinearBlockKernel_eq_bot_of_core_eq_bot block P hr hD
  exact (Finite.equivFin block.Points).permCongrHom.injective.comp
    (Subtype.val_injective.comp htop)

/-- Install a selected degree-four translation-layer capacity at the
faithful literal block-top comparator. -/
noncomputable def degreeFourZeroCoreSource_of_jointCapacity
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (hm : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        Real.logb 2 (elementaryChart block P).p /
          (elementaryChart block P).p * H.capacity)
    (hcoeff : ∀ b : ℕ, H.coefficient ≤
      (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1))) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let Q := RelativeCompleteSourceEnvelope.identity
    (DegreeFourComplementQuotient block P)
    (Nat.card block.Points) (degreeFourZeroCoreTopAction block P)
    (degreeFourZeroCoreTopAction_injective block P hr hD)
  let T := translationLayerEnvelopeOver block P H Q
  apply RelativeCompleteSourceEnvelope.toRankTailSourceOrYonedaTopOfMargin
    .acert T
  refine
    { eta_nonneg := ?_
      seedDegree_two_le := ?_
      margin := ?_
      coefficient_bound := ?_ }
  · change 0 ≤ Real.logb 2 (elementaryChart block P).p /
        (elementaryChart block P).p * H.capacity + 0
    have hlog : 0 ≤ Real.logb 2 (elementaryChart block P).p :=
      Real.logb_nonneg (by norm_num)
        (by exact_mod_cast (elementaryChart block P).p_prime.one_le)
    exact add_nonneg
      (mul_nonneg (div_nonneg hlog (by positivity)) H.capacity_nonneg)
      le_rfl
  · simpa only [T, translationLayerEnvelopeOver_v, Q,
      RelativeCompleteSourceEnvelope.identity] using block.degrees_ge_two.2
  · simpa only [T, translationLayerEnvelopeOver_v,
      translationLayerEnvelopeOver_eta, Q,
      RelativeCompleteSourceEnvelope.identity, add_zero] using hm
  · intro b
    simpa only [T, translationLayerEnvelopeOver_coefficient, Q,
      RelativeCompleteSourceEnvelope.identity, mul_one] using hcoeff b

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
