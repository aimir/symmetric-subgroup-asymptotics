import SymmetricSubgroupAsymptotics.ActualWreathAffineTernaryWidthCapacity
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineWholeCore
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeCoefficient
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeSignedQuotientSource

/-!
# Exact degree-three cells with faithful literal block top

If the signed quotient has zero linear block kernel, its quotient by the
correlated translations acts faithfully on the actual blocks.  Restricting
each ternary section to a Sylow-three subgroup gives the canonical Mackey
width.  At block counts 3, 6, 12 and 18 this leaves a strict original-weight
margin after terminating at the literal block top.  The exceptional
four-block value has trivial Sylow-three information and is deliberately
absent.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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

/-- Relabel the actual block top at the terminal permutation boundary. -/
def degreeThreeKernelZeroTopAction :
    (preE7NonPairAction w U ⧸ E block P) →*
      Equiv.Perm (Fin (Nat.card block.Points)) :=
  (Finite.equivFin block.Points).permCongrHom.toMonoidHom.comp
    (block.Top.subtype.comp (degreeNineWholeQuotientTopMap block P))

/-- Vanishing of the literal linear block kernel makes the displayed block
action faithful. -/
theorem degreeThreeKernelZeroTopAction_injective
    (hK : degreeNineLinearBlockKernel block P = ⊥) :
    Function.Injective (degreeThreeKernelZeroTopAction block P) := by
  apply (Finite.equivFin block.Points).permCongrHom.injective.comp
  apply Subtype.val_injective.comp
  rw [← MonoidHom.ker_eq_bot_iff,
    degreeNineWholeQuotientTopMap_ker block P]
  exact hK

/-- The canonical one-dimensional ternary capacity on the actual block
index, retaining the original fixed-top coefficient. -/
noncomputable def degreeThreeTernaryWidthJointCapacity
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3) :
    ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  have hpd := degreeThree_translation_prime_dim block P hr
  let i₀ : block.Points := Classical.choice inferInstance
  exact ActualWreathAffineCapacity.sharpenJointCapacityToTernaryWidthCore
    S (localMap block P) C H hpd.1 hpd.2 i₀

@[simp] theorem degreeThreeTernaryWidthJointCapacity_capacity
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3) :
    (degreeThreeTernaryWidthJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm hr).capacity =
      ternaryWidthCore (Nat.card block.Points)
        ((Nat.card block.Points).factorization 3) := by
  simp only [degreeThreeTernaryWidthJointCapacity,
    ActualWreathAffineCapacity.sharpenJointCapacityToTernaryWidthCore_capacity,
    Fintype.card_eq_nat_card]

@[simp] theorem degreeThreeTernaryWidthJointCapacity_coefficient
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3) :
    (degreeThreeTernaryWidthJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm hr).coefficient =
      (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm).coefficient := rfl

/-- The literal block-top terminal envelope below `U/E`. -/
noncomputable def degreeThreeKernelZeroTopEnvelope
    (hK : degreeNineLinearBlockKernel block P = ⊥) :
    RelativeCompleteSourceEnvelope
      (preE7NonPairAction w U ⧸ E block P) :=
  RelativeCompleteSourceEnvelope.identity
    (preE7NonPairAction w U ⧸ E block P)
    (Nat.card block.Points)
    (degreeThreeKernelZeroTopAction block P)
    (degreeThreeKernelZeroTopAction_injective block P hK)

/-- Numerical Mackey-width margin at every residual count except four. -/
theorem degreeThreeKernelZeroTop_margin
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 3 ∨
      Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12 ∨
      Nat.card block.Points = 18) :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        Real.logb 2 3 / 3 *
          ternaryWidthCore (Nat.card block.Points)
            ((Nat.card block.Points).factorization 3) := by
  have hw : w = 3 * Nat.card block.Points := by
    simpa only [hr] using width_eq block
  have hlog : Real.logb 2 3 ≤ 8 / 5 := by
    have hp : (3 : ℝ) ^ (5 : ℕ) < (2 : ℝ) ^ (8 : ℕ) := by norm_num
    have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      (by positivity : (0 : ℝ) < (3 : ℝ) ^ (5 : ℕ)) hp
    simp only [Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at h
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 5)).2 (by
      simpa only [mul_comm] using le_of_lt h)
  have hf3 : (3 : ℕ).factorization 3 = 1 := by decide +kernel
  have hf6 : (6 : ℕ).factorization 3 = 1 := by decide +kernel
  have hf12 : (12 : ℕ).factorization 3 = 1 := by decide +kernel
  have hf18 : (18 : ℕ).factorization 3 = 2 := by decide +kernel
  rcases hs with hs | hs | hs | hs
  · rw [hs] at hw ⊢
    norm_num [hw, evenWidth, halfDegree, ternaryWidthCore, hf3,
      preE7CharacterRho] at hlog ⊢
    linarith
  · rw [hs] at hw ⊢
    norm_num [hw, evenWidth, halfDegree, ternaryWidthCore, hf6,
      preE7CharacterRho] at hlog ⊢
    linarith
  · rw [hs] at hw ⊢
    norm_num [hw, evenWidth, halfDegree, ternaryWidthCore, hf12,
      preE7CharacterRho] at hlog ⊢
    linarith
  · rw [hs] at hw ⊢
    norm_num [hw, evenWidth, halfDegree, ternaryWidthCore, hf18,
      preE7CharacterRho] at hlog ⊢
    linarith

/-- Every zero-linear-kernel exact-S3 residual outside the four-block slice
has a complete original-weight source ending at the actual block top. -/
noncomputable def degreeThreeKernelZeroTopSource
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 3 ∨
      Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12 ∨
      Nat.card block.Points = 18)
    (hK : degreeNineLinearBlockKernel block P = ⊥) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let H₀ := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  let H := degreeThreeTernaryWidthJointCapacity block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm hr
  let Q := degreeThreeKernelZeroTopEnvelope block P hK
  have hpd := degreeThree_translation_prime_dim block P hr
  have hs2 : 2 ≤ Nat.card block.Points := by
    rcases hs with hs | hs | hs | hs <;> omega
  have hw : w = 3 * Nat.card block.Points := by
    simpa only [hr] using width_eq block
  have hcoeff₀ := translationLayerJointCapacity_coefficient_le block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
  have hp : P.p = 3 := by
    simpa only [localTranslationChart] using hpd.1
  have hcoeff : H₀.coefficient ≤ (3 : ℝ) ^
      traceyAffineCoefficientExponent 1 (Nat.card block.Points)
        (traceyInducedGeneratorCeiling 1 (Nat.card block.Points))
        (traceyPermutationGeneratorCeiling w) w 3 := by
    simpa only [H₀, hpd.1, hpd.2, hp, Fintype.card_eq_nat_card] using hcoeff₀
  have hD₀ := degreeThreeTranslationCoefficient_bound
    (Nat.card block.Points) w hs2 hw H₀.coefficient hcoeff
  have hD : ∀ b : ℕ, H.coefficient ≤
      (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1)) := by
    intro b
    simpa only [H, degreeThreeTernaryWidthJointCapacity_coefficient, H₀] using
      hD₀ b
  let T := translationLayerEnvelopeOver block P H Q
  apply RelativeCompleteSourceEnvelope.toRankTailSourceOrYonedaTopOfMargin
    .acert T
  refine
    { eta_nonneg := ?_
      seedDegree_two_le := ?_
      margin := ?_
      coefficient_bound := ?_ }
  · have hp1 : (1 : ℝ) ≤ (elementaryChart block P).p := by
      exact_mod_cast (elementaryChart block P).p_prime.one_le
    have hlog : 0 ≤ Real.logb 2 (elementaryChart block P).p :=
      Real.logb_nonneg (by norm_num) hp1
    have hp0 : (0 : ℝ) ≤ (elementaryChart block P).p := by positivity
    simpa only [T, translationLayerEnvelopeOver,
      RelativeCompleteSourceEnvelope.elementaryStep,
      Q, degreeThreeKernelZeroTopEnvelope,
      RelativeCompleteSourceEnvelope.identity, add_zero] using
        mul_nonneg (div_nonneg hlog hp0) H.capacity_nonneg
  · simpa only [T, translationLayerEnvelopeOver,
      RelativeCompleteSourceEnvelope.elementaryStep,
      Q, degreeThreeKernelZeroTopEnvelope,
      RelativeCompleteSourceEnvelope.identity] using hs2
  · have hm := degreeThreeKernelZeroTop_margin block hr hs
    have hep : (elementaryChart block P).p = 3 := by
      simpa only [elementaryChart, localTranslationChart] using hpd.1
    have hHcap : H.capacity =
        ternaryWidthCore (Nat.card block.Points)
          ((Nat.card block.Points).factorization 3) := by
      exact degreeThreeTernaryWidthJointCapacity_capacity block P
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr
    simpa only [T, translationLayerEnvelopeOver,
      RelativeCompleteSourceEnvelope.elementaryStep,
      Q, degreeThreeKernelZeroTopEnvelope,
      RelativeCompleteSourceEnvelope.identity, add_zero, hHcap, hep] using hm
  · intro b
    simpa only [T, translationLayerEnvelopeOver,
      RelativeCompleteSourceEnvelope.elementaryStep,
      Q, degreeThreeKernelZeroTopEnvelope,
      RelativeCompleteSourceEnvelope.identity, mul_one] using hD b

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
