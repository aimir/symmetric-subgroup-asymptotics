import SymmetricSubgroupAsymptotics.BinaryFourNonsplitKernelChart
import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators

/-! Two normal generators inside either actual nonsplit translation
kernel. An actual order-three lift supplies the previously checked C3
module; Maschke then gives the bound for every invariant subspace. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourFullBlockCoordinates

open BinaryFourBlockAugmentation SemidirectProduct

theorem fullKlein_include (p : Klein) (x : Coordinates) :
    fullKlein p (includeAugmentation x) = includeAugmentation (kleinLinear p x) := by
  ext i
  fin_cases i <;> simp [fullKlein, fullKleinFun, includeAugmentation, kleinLinear]

theorem fullC_power_include (n : ℕ) (x : Coordinates) :
    (fullC ^ n) (includeAugmentation x) = includeAugmentation ((c ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change fullC ((fullC ^ n) (includeAugmentation x)) =
        includeAugmentation (c ((c ^ n) x))
      rw [ih, fullC_include]

theorem fullLinear_include (r : Complement) (x : Coordinates) :
    fullComplementLinear r (includeAugmentation x) =
      includeAugmentation (complementLinear r x) := by
  change fullKlein r.left ((fullC ^ r.right.toAdd.val) (includeAugmentation x)) =
    includeAugmentation (kleinLinear r.left ((c ^ r.right.toAdd.val) x))
  rw [fullC_power_include, fullKlein_include]

theorem ambient_conjugate_inl (g : Ambient) (x : Multiplicative FullCoordinates) :
    g * inl x * g⁻¹ = inl (fullAction g.right x) := by
  conv_lhs => rw [← inl_left_mul_inr_right g]
  have h : (inr g.right : Ambient) * inl x * (inr g.right)⁻¹ =
      inl (fullAction g.right x) := by
    rw [← map_inv]
    exact (inl_aut _ _).symm
  calc
    (inl g.left * inr g.right : Ambient) * inl x * (inl g.left * inr g.right)⁻¹ =
      (inl g.left : Ambient) *
        ((inr g.right : Ambient) * inl x * (inr g.right)⁻¹) * (inl g.left)⁻¹ := by group
    _ = (inl (g.left * fullAction g.right x * g.left⁻¹) : Ambient) := by
      rw [h, ← map_inv, ← map_mul, ← map_mul]
    _ = _ := by rw [mul_comm g.left, mul_inv_cancel_right]

theorem source_conjugate_translation (full : Bool) (g : NonsplitSource full)
    (x : space full) :
    g * sourceTranslation full (Multiplicative.ofAdd x) * g⁻¹ =
      sourceTranslation full (Multiplicative.ofAdd (restrictedLinear full g.val.right x)) := by
  apply Subtype.ext
  change g.val * inl (Multiplicative.ofAdd (includeAugmentation (x : Coordinates))) * g.val⁻¹ =
    inl (Multiplicative.ofAdd (includeAugmentation (complementLinear g.val.right x)))
  rw [ambient_conjugate_inl]
  apply congrArg inl
  apply Multiplicative.toAdd.injective
  exact fullLinear_include _ _

def sourceC (full : Bool) : NonsplitSource full :=
  ⟨⟨Multiplicative.ofAdd (includeAugmentation correction), cElement⟩, by
    cases full
    · change row10Condition _
      unfold row10Condition
      decide +kernel
    · change row12Condition _
      unfold row12Condition
      decide +kernel⟩

def sourceOdd (full : Bool) : NonsplitSource full := sourceC full ^ 4

theorem ambientCommonC_twelve :
    (⟨Multiplicative.ofAdd (includeAugmentation correction), cElement⟩ : Ambient) ^ 12 = 1 := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    ext i
    revert i
    decide +kernel
  · apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      ext i
      revert i
      decide +kernel
    · apply Multiplicative.toAdd.injective
      decide +kernel

theorem sourceOdd_cube (full : Bool) : sourceOdd full ^ 3 = 1 := by
  apply Subtype.ext
  change ((⟨Multiplicative.ofAdd (includeAugmentation correction), cElement⟩ : Ambient) ^ 4) ^ 3 = 1
  rw [← pow_mul]
  exact ambientCommonC_twelve

theorem sourceOdd_projection (full : Bool) : blockProjection full (sourceOdd full) = cElement := by
  change blockProjection full (sourceC full ^ 4) = cElement
  rw [map_pow]
  change cElement ^ 4 = cElement
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    ext i
    revert i
    decide +kernel
  · apply Multiplicative.toAdd.injective
    decide +kernel

def sourceTernary (full : Bool) : Ternary →* NonsplitSource full :=
  powersHom 3 (sourceOdd full) (sourceOdd_cube full)

theorem cElement_power (z : Ternary) : cElement ^ z.toAdd.val = (inr z : Complement) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    ext i
    revert z i
    decide +kernel
  · apply Multiplicative.toAdd.injective
    revert z
    decide +kernel

theorem sourceTernary_projection (full : Bool) (z : Ternary) :
    blockProjection full (sourceTernary full z) = inr z := by
  change blockProjection full (sourceOdd full ^ z.toAdd.val) = inr z
  rw [map_pow, sourceOdd_projection, cElement_power]

theorem augmentationQuotientChart_ternary (full : Bool) (z : Ternary) (x : space full) :
    augmentationQuotientChart full (restrictedLinear full (inr z) x) =
      quotientLinear full z (augmentationQuotientChart full x) := by
  change augmentationQuotientChart full ((restrictedLinearHom full) (inr z) x) = _
  rw [← cElement_power, map_pow]
  change augmentationQuotientChart full ((restrictedLinear full cElement ^ z.toAdd.val) x) =
    (quotientCycle full ^ z.toAdd.val) (augmentationQuotientChart full x)
  generalize z.toAdd.val = n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change augmentationQuotientChart full
          (restrictedLinear full cElement ((restrictedLinear full cElement ^ n) x)) =
        quotientCycle full ((quotientCycle full ^ n) (augmentationQuotientChart full x))
      rw [augmentationQuotientChart_cycle, ih]

theorem sourceElementaryChart_translation (full : Bool) (x : space full) :
    (sourceElementaryChart full).equiv
        ⟨sourceTranslation full (Multiplicative.ofAdd x), sourceTranslation_kernel full _⟩ =
      Multiplicative.ofAdd (augmentationQuotientChart full x) := by
  change (augmentationQuotientChart full).toAddEquiv.toMultiplicative
    ((sourceKernelEquiv full) ((sourceKernelEquiv full).symm (Multiplicative.ofAdd x))) = _
  rw [(sourceKernelEquiv full).apply_symm_apply]
  rfl

theorem sourceElementaryChart_conjugate (full : Bool) (g : NonsplitSource full)
    (x : space full) :
    ((sourceElementaryChart full).equiv
      (MulAut.conjNormal g
        ⟨sourceTranslation full (Multiplicative.ofAdd x), sourceTranslation_kernel full _⟩)).toAdd =
      augmentationQuotientChart full (restrictedLinear full g.val.right x) := by
  have he : MulAut.conjNormal g
      (⟨sourceTranslation full (Multiplicative.ofAdd x), sourceTranslation_kernel full _⟩ :
        sourceKernel full) =
      ⟨sourceTranslation full (Multiplicative.ofAdd (restrictedLinear full g.val.right x)),
        sourceTranslation_kernel full _⟩ := by
    apply Subtype.ext
    exact source_conjugate_translation full g x
  rw [he, sourceElementaryChart_translation]
  rfl

theorem sourceKernel_restrictedRepresentation (full : Bool) :
    (sourceElementaryChart full).quotientRepresentation.ρ.comp
        ((QuotientGroup.mk' (sourceKernel full)).comp (sourceTernary full)) =
      LinearSemidirectCoprimeSocleBounds.linearRepresentation (quotientLinear full) := by
  apply MonoidHom.ext
  intro z
  apply LinearMap.ext
  intro v
  let x := (augmentationQuotientChart full).symm v
  let e : sourceKernel full :=
    ⟨sourceTranslation full (Multiplicative.ofAdd x), sourceTranslation_kernel full _⟩
  have he : ((sourceElementaryChart full).equiv e).toAdd = v := by
    rw [sourceElementaryChart_translation]
    exact (augmentationQuotientChart full).apply_symm_apply v
  have h := (sourceElementaryChart full).quotientRepresentation_apply (sourceTernary full z) e
  rw [he] at h
  rw [sourceElementaryChart_conjugate] at h
  have hp : (sourceTernary full z).val.right = inr z := sourceTernary_projection full z
  rw [hp, augmentationQuotientChart_ternary] at h
  simpa only [x, (augmentationQuotientChart full).apply_symm_apply] using h

theorem sourceKernel_uniform (full : Bool) :
    UniformSubrepresentationGeneratorBound
      (sourceElementaryChart full).quotientRepresentation.ρ 2 := by
  have hcard : Nat.card Ternary = 3 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Ternary ≃ ZMod 3), Nat.card_zmod]
  letI : NeZero (Nat.card Ternary : Scalar) := ⟨by rw [hcard]; decide⟩
  apply UniformSubrepresentationGeneratorBound.of_comp
    (sourceElementaryChart full).quotientRepresentation.ρ
    ((QuotientGroup.mk' (sourceKernel full)).comp (sourceTernary full))
  rw [sourceKernel_restrictedRepresentation]
  exact RepresentationGeneratedBy.uniform_of_invertible_order (k := Scalar)
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation (quotientLinear full))
    (quotientRepresentation_generated full)

theorem sourceKernel_normalGen_le_two (full : Bool)
    (N : Subgroup (NonsplitSource full)) [N.Normal] (hN : N ≤ sourceKernel full) :
    MarkedC4.normalGen N ≤ 2 :=
  ElementaryUniformNormalGenerators.kernel_normalGen_le
    (sourceKernel full) (sourceElementaryChart full) 2 (sourceKernel_uniform full) N hN

end BinaryFourFullBlockCoordinates
end SymmetricSubgroupAsymptotics

end
