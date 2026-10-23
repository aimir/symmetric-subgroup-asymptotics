import SymmetricSubgroupAsymptotics.CFSGTrialityFixedField
import SymmetricSubgroupAsymptotics.CFSGOrderedCubeOperatorExpansion
import SymmetricSubgroupAsymptotics.CFSGScalarRestrictionSpanRank
import SymmetricSubgroupAsymptotics.CFSGCubicTensorAugmentationDimension
import Mathlib.FieldTheory.Finiteness

/-! Actual base-field spans of the cubic norm curve and its seven raised
coordinates. The base field is the literal Frobenius-fixed subfield in
q.Extension 3. The full envelope has F-dimension eight, never twenty-four;
the augmentation envelope has F-dimension seven. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityMiddleFixedTensorSpan
open CFSGTrialityFixedField CFSGSerreOrdinaryTwists
open CFSGCubicNormMonomialSeparation CFSGCubicNormCurveSpan
open CFSGCubicTensorEnvelopeDimension CFSGCubicTensorAugmentationDimension
open CFSGOrderedCubeOperatorExpansion CFSGScalarRestrictionSpanRank

abbrev F (q : CFSG.PrimePower) := fixedField q
abbrev K (q : CFSG.PrimePower) := q.Extension 3

def sigmaLinear (q : CFSG.PrimePower) : K q →ₗ[F q] K q where
  toFun := definingFieldAutomorphism q 3
  map_add' := map_add _
  map_smul' a x := by
    change definingFieldAutomorphism q 3 (a.val*x) =
      a.val * definingFieldAutomorphism q 3 x
    rw [map_mul, show definingFieldAutomorphism q 3 a.val = a.val from a.property]

def fixedScalarSpace (q : CFSG.PrimePower) : Submodule (F q) (K q) :=
  (Algebra.linearMap (F q) (K q)).range

theorem mem_fixedScalarSpace (q : CFSG.PrimePower) (x : K q) :
    x ∈ fixedScalarSpace q ↔ definingFieldAutomorphism q 3 x = x := by
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem fixedScalarSpace_finrank_le_one (q : CFSG.PrimePower) :
    Module.finrank (F q) (fixedScalarSpace q) ≤ 1 := by
  simpa only [Module.finrank_self] using
    LinearMap.finrank_range_le (Algebra.linearMap (F q) (K q))

theorem extension_finrank (q : CFSG.PrimePower) : Module.finrank (F q) (K q) = 3 := by
  have h := Module.natCard_eq_pow_finrank (K := F q) (V := K q)
  rw [CFSGTrialityTripleFixedRoots.extension_three_card, fixedField_card] at h
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  exact (Nat.pow_right_injective hq h).symm

private theorem cyclicCurve_eq (q : CFSG.PrimePower) (t : K q) :
    cubeParameters t (definingFieldAutomorphism q 3 t)
      (definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 t)) = normCurve q.order t := by
  have h2 : definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 t) = t^(q.order^2) := by
    change (t^q.order)^q.order = t^(q.order^2)
    rw [← pow_mul, pow_two]
  change cubeParameters t (t^q.order) _ = _
  rw [h2, cubeParameters_eq_normCurve]

private theorem cyclicCurve_conditions (q : CFSG.PrimePower) (t : K q) :
    let c := normCurve q.order t
    definingFieldAutomorphism q 3 (c 0) = c 0 ∧
    definingFieldAutomorphism q 3 (c 7) = c 7 ∧
    c 2 = sigmaLinear q (c 1) ∧ c 4 = sigmaLinear q (c 2) ∧
    c 6 = sigmaLinear q (c 3) ∧ c 5 = sigmaLinear q (c 6) := by
  rw [← cyclicCurve_eq]
  have h3 := sigma_thrice q t
  dsimp only [cubeParameters, sigmaLinear]
  refine ⟨map_one _, ?_, rfl, rfl, ?_, ?_⟩
  · rw [map_mul, map_mul, h3]
    ring
  · exact (map_mul _ _ _).symm
  · change definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 t) * t =
      definingFieldAutomorphism q 3
        (definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 t) *
          definingFieldAutomorphism q 3 t)
    rw [map_mul, h3]
    ring

def fullEnvelope (q : CFSG.PrimePower) : Submodule (F q) (Fin 8 → K q) :=
  tensorEnvelope (fixedScalarSpace q) (sigmaLinear q)

def raisedEnvelope (q : CFSG.PrimePower) : Submodule (F q) (Fin 7 → K q) :=
  augmentationEnvelope (fixedScalarSpace q) (sigmaLinear q)

theorem normCurve_mem_fullEnvelope (q : CFSG.PrimePower) (t : K q) :
    normCurve q.order t ∈ fullEnvelope q := by
  obtain ⟨h0,h7,h2,h4,h6,h5⟩ := cyclicCurve_conditions q t
  exact mem_tensorEnvelope _ _ _ ((mem_fixedScalarSpace q _).mpr h0)
    ((mem_fixedScalarSpace q _).mpr h7) h2 h4 h6 h5

theorem augmentationCurve_mem_raisedEnvelope (q : CFSG.PrimePower) (t : K q) :
    augmentationCurve q.order t ∈ raisedEnvelope q := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  have he (i : Fin 7) : augmentationCurve q.order t i = normCurve q.order t i.succ := by
    simp only [augmentationCurve, normCurve_zero_succ (K q) q.order hq, sub_zero]
  obtain ⟨_,h7,h2,h4,h6,h5⟩ := cyclicCurve_conditions q t
  apply mem_augmentationEnvelope
  · rw [he]
    exact (mem_fixedScalarSpace q _).mpr h7
  · simpa only [he] using h2
  · simpa only [he] using h4
  · simpa only [he] using h6
  · simpa only [he] using h5

theorem normCurve_base_span (q : CFSG.PrimePower) :
    Submodule.span (F q) (Set.range (normCurve (K := K q) q.order)) = fullEnvelope q := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  apply base_span_eq_of_dimension_bound (F q) (K q) (Fin 8 → K q) (K q)
    (normCurve q.order) (normCurve_span_eq_top _ _ hq
      (CFSGTrialityTripleFixedRoots.extension_three_card q)) (fullEnvelope q)
    (normCurve_mem_fullEnvelope q)
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Fintype.card_fin,
    smul_eq_mul, mul_one] using tensorEnvelope_finrank_le_eight
      (fixedScalarSpace q) (sigmaLinear q) (fixedScalarSpace_finrank_le_one q)
      (extension_finrank q).le

theorem augmentationCurve_base_span (q : CFSG.PrimePower) :
    Submodule.span (F q) (Set.range (augmentationCurve (K := K q) q.order)) = raisedEnvelope q := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
  apply base_span_eq_of_dimension_bound (F q) (K q) (Fin 7 → K q) (K q)
    (augmentationCurve q.order) (augmentationCurve_span_eq_top _ _ hq
      (CFSGTrialityTripleFixedRoots.extension_three_card q)) (raisedEnvelope q)
    (augmentationCurve_mem_raisedEnvelope q)
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Fintype.card_fin,
    smul_eq_mul, mul_one] using augmentationEnvelope_finrank_le_seven
      (fixedScalarSpace q) (sigmaLinear q) (fixedScalarSpace_finrank_le_one q)
      (extension_finrank q).le

end SymmetricSubgroupAsymptotics.CFSGTrialityMiddleFixedTensorSpan
