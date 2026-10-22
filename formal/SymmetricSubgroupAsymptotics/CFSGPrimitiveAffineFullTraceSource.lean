import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineFullTraceEnvelope
import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSourceDichotomyClosure

/-! The existing bounded primitive numerical certificate consumes a complete
literal fibre envelope; its fields do not demand nonsolubility. The full
Schur trace therefore supplies that same certificate whenever its proved
exponent fits, without a complement order or generation hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

variable {w : ℕ} {U : PreE7NonPairActionClass w}

namespace CFSGPrimitiveAffineFullTraceSource

variable [Nontrivial (Fin w)]

private noncomputable def coefficient
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (b : ℕ) : ℝ :=
  (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) *
    (T.envelope.constant * (1 + (b : ℝ)) ^ T.envelope.polynomialDegree) *
    ((Nat.card C.V : ℝ) *
      Nat.card (groupCohomology.H1
        (P.complementRepresentation hprimitive C x)) + 1)

private theorem coefficient_nonneg
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (b : ℕ) :
    0 ≤ coefficient P hprimitive x C T b := by
  unfold coefficient
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg T.envelope.constant_nonneg (by positivity)))
    (by positivity)

private theorem coefficient_total_polynomial
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x)) :
    ∃ K : ℝ, ∃ p : ℕ, 0 ≤ K ∧ ∀ b,
      fusionAxisEnvelopeTotal (preE7NonPairAction w U)
          (fun _ => coefficient P hprimitive x C T b) ≤
        K * (1 + (b : ℝ)) ^ p := by
  let q : ℝ :=
    (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ)
  let k : ℝ :=
    (Nat.card C.V : ℝ) *
      Nat.card (groupCohomology.H1
        (P.complementRepresentation hprimitive C x)) + 1
  refine ⟨q ^ 2 * T.envelope.constant * k,
    T.envelope.polynomialDegree,
    mul_nonneg (mul_nonneg (by positivity) T.envelope.constant_nonneg)
      (by positivity), ?_⟩
  intro b
  unfold fusionAxisEnvelopeTotal coefficient
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard :
      @Fintype.card
          {N : Subgroup (preE7NonPairAction w U) // N.Normal}
          (Subtype.fintype Subgroup.Normal) =
        @Fintype.card
          {N : Subgroup (preE7NonPairAction w U) // N.Normal}
          originalNormalFintype :=
    @Fintype.card_congr
      {N : Subgroup (preE7NonPairAction w U) // N.Normal}
      {N : Subgroup (preE7NonPairAction w U) // N.Normal}
      (Subtype.fintype Subgroup.Normal) originalNormalFintype (Equiv.refl _)
  have hcardNat :
      (@Finset.univ
        {N : Subgroup (preE7NonPairAction w U) // N.Normal}
        (Subtype.fintype Subgroup.Normal)).card =
      Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} := by
    change @Fintype.card
        {N : Subgroup (preE7NonPairAction w U) // N.Normal}
        (Subtype.fintype Subgroup.Normal) =
      Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal}
    rw [Nat.card_eq_fintype_card]
    exact hcard
  rw [hcardNat]
  have hmul (a c d e f : ℝ) :
      a * (c * (d * f) * e) ≤ (a * c * d * e) * f := by
    apply le_of_eq
    ring
  simpa only [q, k, pow_two] using hmul
    (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ)
    (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ)
    T.envelope.constant
    ((Nat.card C.V : ℝ) *
      Nat.card (groupCohomology.H1
        (P.complementRepresentation hprimitive C x)) + 1)
    ((1 + (b : ℝ)) ^ T.envelope.polynomialDegree)

/-- The complete NSAPRIM action certificate once the literal traced exponent
has been placed inside the physical window. -/
noncomputable def actionCertificateOfMargin
    (hw : 5 ≤ w) (hw1024 : w ≤ 1024)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - 2) / 8 -
        (fixedTargetCompositionGamma * T.envelope.abelianLength +
          P.bottomFullSlope)) :
    PreE7NsaprimActionCertificate w U where
  width_lower := hw
  width_upper := hw1024
  primitive := hprimitive
  coefficient := coefficient P hprimitive x C T
  eta := fixedTargetCompositionGamma * T.envelope.abelianLength +
    P.bottomFullSlope
  eta_nonneg := by
    have hgamma : 0 ≤ fixedTargetCompositionGamma := by
      unfold fixedTargetCompositionGamma
      have := half_le_logThreeThird
      linarith
    exact add_nonneg (mul_nonneg hgamma (by positivity))
      P.bottomFullSlope_nonneg
  coefficient_nonneg := coefficient_nonneg P hprimitive x C T
  complete_fibre := by
    intro b J
    simpa [coefficient] using
      P.completeQuotientWeight_le_fullTraceEnvelope
        hprimitive x C T b J
  coefficient_total_polynomial :=
    coefficient_total_polynomial P hprimitive x C T
  exponent_margin := hmargin

/-- The original-action source from the proved full Schur trace. -/
noncomputable def rankTailOwnerSourceDataOfMargin
    (hw : 5 ≤ w) (hw1024 : w ≤ 1024)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - 2) / 8 -
        (fixedTargetCompositionGamma * T.envelope.abelianLength +
          P.bottomFullSlope)) : PreE7RankTailOwnerSourceData w U :=
  .ordinary .nsaprim (.semisimple
    ⟨by decide, by decide⟩
    ⟨actionCertificateOfMargin hw hw1024 hprimitive P x C T hmargin⟩)

end CFSGPrimitiveAffineFullTraceSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
