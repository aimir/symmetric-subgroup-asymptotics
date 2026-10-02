import SymmetricSubgroupAsymptotics.PrimitiveAffineNonsolubleNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSourceDichotomyClosure

/-!
# The nonsoluble primitive-affine NSAPRIM source

This file packages the proved complete fibre envelope as the literal NSAPRIM
owner used by the numerical catalogue.  The coefficient is a fixed polynomial
in the source degree.  Its constants are target data and are absorbed by the
finite bounded-width menu theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

variable {w : ℕ} {U : PreE7NonPairActionClass w}

namespace PrimitiveAffineNonsolubleSource

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

/-- Every nonsoluble primitive affine profile in the bounded large range
supplies the complete NSAPRIM action certificate. -/
noncomputable def actionCertificate
    (hcomp : PrimitiveCompositionLengthInput)
    (hw : 128 ≤ w) (hw1024 : w ≤ 1024)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    PreE7NsaprimActionCertificate w U where
  width_lower := by omega
  width_upper := hw1024
  primitive := hprimitive
  coefficient := coefficient P hprimitive x C T
  eta := fixedTargetCompositionGamma * T.envelope.abelianLength +
    P.bottomHalfSlope
  eta_nonneg := by
    have hgamma : 0 ≤ fixedTargetCompositionGamma := by
      unfold fixedTargetCompositionGamma
      have := half_le_logThreeThird
      linarith
    exact add_nonneg (mul_nonneg hgamma (by positivity))
      P.bottomHalfSlope_nonneg
  coefficient_nonneg := coefficient_nonneg P hprimitive x C T
  complete_fibre := by
    intro b J
    simpa [coefficient] using
      P.completeQuotientWeight_le_nonsolubleEnvelope
        hprimitive x C T hnonsolvable b J
  coefficient_total_polynomial :=
    coefficient_total_polynomial P hprimitive x C T
  exponent_margin :=
    P.nonsolubleEnvelope_exponent_margin_large hcomp hw
      (preE7NonPairAction w U) hprimitive x C T hnonsolvable

/-- The same certificate in the concrete source form used by the T1
rank-tail catalogue. -/
noncomputable def rankTailOwnerSourceData
    (hcomp : PrimitiveCompositionLengthInput)
    (hw : 128 ≤ w) (hw1024 : w ≤ 1024)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (C : P.ElementaryChart hprimitive)
    (T : FixedTargetCompositionTrace (P.complement x))
    (hnonsolvable : ¬ IsSolvable (P.complement x)) :
    PreE7RankTailOwnerSourceData w U :=
  .ordinary .nsaprim (.semisimple
    ⟨by decide, by decide⟩
    ⟨actionCertificate hcomp hw hw1024 hprimitive P x C T hnonsolvable⟩)

/-- Canonical charts and chief traces remove all auxiliary choices from the
catalogue-facing constructor. -/
noncomputable def canonicalRankTailOwnerSourceData
    (hcomp : PrimitiveCompositionLengthInput)
    (hw : 128 ≤ w) (hw1024 : w ≤ 1024)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hnonsolvable : ¬ IsSolvable
      (P.complement ⟨0, by omega⟩)) :
    PreE7RankTailOwnerSourceData w U := by
  letI : Nontrivial (Fin w) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let x : Fin w := ⟨0, by omega⟩
  let C := P.elementaryChart hprimitive
  let T := FixedTargetCompositionTrace.canonical (P.complement x)
  exact rankTailOwnerSourceData hcomp hw hw1024 hprimitive P x C T
    hnonsolvable

end PrimitiveAffineNonsolubleSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
