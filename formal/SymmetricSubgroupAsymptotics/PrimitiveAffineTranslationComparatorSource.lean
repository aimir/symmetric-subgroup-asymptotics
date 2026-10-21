import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationLayerSource

/-! Transfer the actual translation layer to any proved faithful action of
its SAME quotient. Original normal denominators and their joint Yoneda
fibres are retained by the unchanged elementary envelope engine. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]

/-- A one-layer relative envelope ending at the faithful complement-by-top
action. The complete normal-axis sum and the joint Yoneda fibre are charged
together by H. -/
noncomputable def translationLayerFaithfulComparatorEnvelope
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (v : ℕ)
    (action : (preE7NonPairAction w U ⧸ E block P) →* Equiv.Perm (Fin v))
    (hfaithful : Function.Injective action) :
    RelativeCompleteSourceEnvelope (preE7NonPairAction w U) := by
  letI : Finite (chart block P).V := Finite.of_injective
    (fun v : (chart block P).V =>
      (chart block P).equiv.symm (Multiplicative.ofAdd v))
    (chart block P).equiv.symm.injective
  letI : Finite (TranslationSubmodule block P) :=
    Finite.of_injective (TranslationSubmodule block P).subtype
      (TranslationSubmodule block P).subtype_injective
  letI : Finite (elementaryChart block P).V := by
    change Finite (TranslationSubmodule block P)
    infer_instance
  letI : Finite (elementaryChart block P).quotientRepresentation :=
    inferInstanceAs (Finite (elementaryChart block P).V)
  exact RelativeCompleteSourceEnvelope.elementaryStep
    (p := (elementaryChart block P).p)
    (E block P) (elementaryChart block P) H
    (RelativeCompleteSourceEnvelope.identity
      (preE7NonPairAction w U ⧸ E block P)
      v action hfaithful)

/-- Construction-facing form of the translation stop. -/
noncomputable def translationLayerFaithfulComparatorSource
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (v : ℕ)
    (action : (preE7NonPairAction w U ⧸ E block P) →* Equiv.Perm (Fin v))
    (hfaithful : Function.Injective action)
    (hv : 2 ≤ v)
    (hm : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - v) / 8 -
        Real.logb 2 (elementaryChart block P).p /
          (elementaryChart block P).p * H.capacity)
    (hD : ∀ b : ℕ, H.coefficient ≤
      (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1))) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let T := translationLayerFaithfulComparatorEnvelope block P H v action hfaithful
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
    simpa only [T, translationLayerFaithfulComparatorEnvelope,
      RelativeCompleteSourceEnvelope.elementaryStep,
      RelativeCompleteSourceEnvelope.identity, add_zero] using
      mul_nonneg (div_nonneg hlog hp0) H.capacity_nonneg
  · simpa only [T, translationLayerFaithfulComparatorEnvelope,
      RelativeCompleteSourceEnvelope.elementaryStep,
      RelativeCompleteSourceEnvelope.identity] using hv
  · simpa only [T, translationLayerFaithfulComparatorEnvelope,
      RelativeCompleteSourceEnvelope.elementaryStep,
      RelativeCompleteSourceEnvelope.identity, add_zero] using hm
  · intro b
    simpa only [T, translationLayerFaithfulComparatorEnvelope,
      RelativeCompleteSourceEnvelope.elementaryStep,
      RelativeCompleteSourceEnvelope.identity, mul_one] using hD b

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
