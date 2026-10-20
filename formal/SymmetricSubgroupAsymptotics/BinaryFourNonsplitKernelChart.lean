import SymmetricSubgroupAsymptotics.BinaryFourNonsplitBlockModels
import SymmetricSubgroupAsymptotics.BinaryFourAugmentationQuotientCoordinates

/-! The actual translation kernels of the two nonsplit sources, in a
common elementary chart. The chart's corrected diagonal coordinates are
the same C3 module used in the checked augmentation quotient theorem. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourFullBlockCoordinates

open BinaryFourBlockAugmentation SemidirectProduct

def nonsplitSubgroup (full : Bool) : Subgroup Ambient :=
  if full then row12Subgroup else row10Subgroup

abbrev NonsplitSource (full : Bool) := nonsplitSubgroup full

def blockProjection (full : Bool) : NonsplitSource full →* Complement :=
  (SemidirectProduct.rightHom : Ambient →* Complement).comp (nonsplitSubgroup full).subtype

theorem blockProjection_surjective (full : Bool) : Function.Surjective (blockProjection full) := by
  cases full
  · exact row10Projection_surjective
  · exact row12Projection_surjective

def sourceKernel (full : Bool) : Subgroup (NonsplitSource full) := (blockProjection full).ker

instance (full : Bool) : (sourceKernel full).Normal := inferInstanceAs (blockProjection full).ker.Normal

theorem source_translation_iff (full : Bool) (x : FullCoordinates) :
    (inl (Multiplicative.ofAdd x) : Ambient) ∈ nonsplitSubgroup full ↔
      augmentation x = 0 ∧ (full = false → x 5 = 0) := by
  cases full
  · change (augmentation x = 0 ∧ x 5 = quadratic 0) ↔ _
    simp [quadratic]
  · change augmentation x = localCycle 0 ↔ _
    simp

theorem source_kernel_coordinates (full : Bool) (g : NonsplitSource full)
    (hg : g ∈ sourceKernel full) :
    augmentation g.val.left.toAdd = 0 ∧ (full = false → g.val.left.toAdd 5 = 0) := by
  have hr : g.val.right = 1 := hg
  have he : g.val = inl (Multiplicative.ofAdd g.val.left.toAdd) :=
    SemidirectProduct.ext rfl hr
  apply (source_translation_iff full _).mp
  rw [← he]
  exact g.property

def includeAugmentationHom (full : Bool) :
    Multiplicative (space full) →* Multiplicative FullCoordinates where
  toFun x := Multiplicative.ofAdd (includeAugmentation (x.toAdd : Coordinates))
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> rfl

def sourceTranslation (full : Bool) : Multiplicative (space full) →* NonsplitSource full :=
  ((inl : Multiplicative FullCoordinates →* Ambient).comp (includeAugmentationHom full)).codRestrict
    (nonsplitSubgroup full) (fun x => by
      apply (source_translation_iff full _).mpr
      constructor
      · ext i
        fin_cases i <;> rfl
      · exact x.toAdd.property)

theorem sourceTranslation_kernel (full : Bool) (x : Multiplicative (space full)) :
    sourceTranslation full x ∈ sourceKernel full := by
  change (inl (includeAugmentationHom full x) : Ambient).right = 1
  rfl

theorem include_head_of_augmentation_zero (x : FullCoordinates) (h : augmentation x = 0) :
    includeAugmentation (head x) = x := by
  have h6 := congrFun h 0
  have h7 := congrFun h 1
  change x 6 = 0 at h6
  change x 7 = 0 at h7
  ext i
  fin_cases i <;> simp [includeAugmentation, head, h6, h7]

def sourceKernelEquiv (full : Bool) : sourceKernel full ≃* Multiplicative (space full) where
  toFun x := Multiplicative.ofAdd
    ⟨head x.val.val.left.toAdd, (source_kernel_coordinates full x.val x.property).2⟩
  invFun x := ⟨sourceTranslation full x, sourceTranslation_kernel full x⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      exact include_head_of_augmentation_zero _
        (source_kernel_coordinates full x.val x.property).1
    · exact (show x.val.val.right = 1 from x.property).symm
  right_inv x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    ext i
    fin_cases i <;> rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change head (x.val.val.left.toAdd +
      fullComplementLinear x.val.val.right y.val.val.left.toAdd) =
      head x.val.val.left.toAdd + head y.val.val.left.toAdd
    rw [show x.val.val.right = 1 from x.property, map_one]
    ext i
    fin_cases i <;> rfl

def augmentationQuotientChart (full : Bool) : space full ≃ₗ[Scalar] QuotientVector full where
  toFun x := (tailMap full x, ![(x : Coordinates) 0 + (x : Coordinates) 5,
    (x : Coordinates) 1])
  invFun w := ⟨![w.2 0 + (w.1 : TailCoordinates) 3, w.2 1,
    (w.1 : TailCoordinates) 0, (w.1 : TailCoordinates) 1,
    (w.1 : TailCoordinates) 2, (w.1 : TailCoordinates) 3], w.1.property⟩
  left_inv x := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [tailMap, tail] <;> ring_nf <;>
      simp only [show (2 : Scalar) = 0 from by decide +kernel, mul_zero, add_zero]
  right_inv w := by
    apply Prod.ext
    · apply Subtype.ext
      ext i
      fin_cases i <;> rfl
    · ext i
      fin_cases i <;> simp <;> ring_nf <;>
        simp only [show (2 : Scalar) = 0 from by decide +kernel, mul_zero, add_zero]
  map_add' x y := by
    apply Prod.ext
    · exact (tailMap full).map_add x y
    · ext i
      fin_cases i <;> simp <;> ring
  map_smul' a x := by
    apply Prod.ext
    · exact (tailMap full).map_smul a x
    · ext i
      fin_cases i <;> simp <;> ring

def sourceElementaryChart (full : Bool) : ElementaryMinimalNormalChart (sourceKernel full) where
  p := 2
  p_prime := by decide
  V := QuotientVector full
  equiv := (sourceKernelEquiv full).trans
    (augmentationQuotientChart full).toAddEquiv.toMultiplicative

theorem augmentationQuotientChart_cycle (full : Bool) (x : space full) :
    augmentationQuotientChart full (restrictedLinear full cElement x) =
      quotientCycle full (augmentationQuotientChart full x) := by
  apply Prod.ext
  · apply Subtype.ext
    change tail (complementLinear cElement (x : Coordinates)) =
      ((tailCycle full (tailMap full x)) : TailCoordinates)
    rw [linear_c]
    ext i
    fin_cases i <;> rfl
  · change ![complementLinear cElement (x : Coordinates) 0 +
        complementLinear cElement (x : Coordinates) 5,
        complementLinear cElement (x : Coordinates) 1] =
      localCycle ![(x : Coordinates) 0 + (x : Coordinates) 5, (x : Coordinates) 1]
    simp only [linear_c]
    ext i
    fin_cases i <;> simp [c, localCycle] <;> ring

end BinaryFourFullBlockCoordinates
end SymmetricSubgroupAsymptotics

end
