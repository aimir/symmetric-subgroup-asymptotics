import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterParabolicCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBlockConjugation
import SymmetricSubgroupAsymptotics.CFSGReeFFourInversionSuffixSignPilot
import SymmetricSubgroupAsymptotics.CFSGReeFFourAbelianImageCardinality

/-! The literal outer graded kernel contains the middle inversion block
and a middle-Weyl conjugate of the outer inversion block. Consequently it
has the full image of the fixed group under every abelian homomorphism.
Thus asserting this kernel lies in the derived group would assert full
perfectness, rather than merely an exceptional derived-index bound.
No containment in the derived group or bound on this image is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterKernelAbelianImage
open CFSGReeFFourOuterGradedQuotient CFSGReeFFourFixedPositiveAssociatedOuter
open CFSGReeFFourFixedBlockConjugation CFSGReeFFourInversionSuffixSignPilot
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourRelativePositiveSubgroups CFSGReeFFourRelativeSimpleWeyl
open CFSGReeFFourRelativeWeylRawWords CFSGReeFFourFieldParameters
open CFSGReeFFourOuterParabolicFlag CFSGReeFFourOuterFixedInversion
open CFSGReeFFourMiddleFixedInversion CFSGReeFFourOriginalInversionFactors
open CFSGReeFFourSimpleInversionBlocks CFSGReeFFourMinimalParabolics
open CFSGReeFFourAbelianImageCardinality CFSGReeFFourFixedBruhatCover
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra CFSGNormTwoRootPairing
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGFFourOriginalMiddleWords CFSGGradedMatrixSubgroups
open CFSGReeFFourOuterPositiveRemainderSupport
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private instance : DecidableEq (Roots A) := Classical.decEq _

def kernelImage (m : ℕ) : Subgroup (originalModelFixed m) :=
  (gradedKernel m).map (outerParabolic m).subtype

private theorem mem_kernelImage (m : ℕ) (g : originalModelFixed m)
    (hg : g ∈ fixedPositive m) (hstrict : fixedRawHom m g ∈ strictUnits outerWeight) :
    g ∈ kernelImage m := by
  refine ⟨⟨g, positive_le_parabolic m hg⟩, ?_, rfl⟩
  exact hstrict

private theorem raw_outer (m : ℕ) :
    fixedRawHom m (outerFixedWeyl m) =
      wordUnit A hs hp b₀ s₀ (Field m) [0,5,1] := by
  rw [fixedRawHom_apply]
  exact rawHom_outerRelativeWeyl m

private theorem raw_middle (m : ℕ) :
    fixedRawHom m (middleFixedWeyl m) =
      wordUnit A hs hp b₀ s₀ (Field m) [2,4,3,2,4,3] := by
  rw [fixedRawHom_apply]
  exact rawHom_middleRelativeWeyl m

theorem middle_inversion_le_kernelImage (m : ℕ) :
    fixedMiddleInversion m ≤ kernelImage m := by
  intro u hu
  have hraw : fixedRawHom m (outerFixedWeyl m) =
      wordUnit A hs hp b₀ s₀ (Field m) (conjugatingWord true 1) := raw_outer m
  have hmap := middle_block_conjugate_le m (outerFixedWeyl m)
    (conjugatingWord true 1) hraw (positiveBlockSigns_first_three true ⟨1, by decide⟩)
  have hpos : u ∈ fixedPositive m :=
    (show u.val ∈ modelInversion m (middleRelativeWeyl m) from hu).1
  exact mem_kernelImage m u hpos
    (fixedPositive_remainder_strict m u hpos (hmap ⟨u, hu, rfl⟩))

theorem outer_middle_conjugate_le_kernelImage (m : ℕ) :
    (fixedOuterInversion m).map (MulAut.conj (middleFixedWeyl m)).toMonoidHom ≤
      kernelImage m := by
  rintro _ ⟨u, hu, rfl⟩
  have hraw₁ : fixedRawHom m (middleFixedWeyl m) =
      wordUnit A hs hp b₀ s₀ (Field m) (conjugatingWord false 1) := raw_middle m
  have hmap₁ := outer_block_conjugate_le m (middleFixedWeyl m)
    (conjugatingWord false 1) hraw₁ (positiveBlockSigns_first_three false ⟨1, by decide⟩)
  have hraw₂ : fixedRawHom m (outerFixedWeyl m * middleFixedWeyl m) =
      wordUnit A hs hp b₀ s₀ (Field m) (conjugatingWord false 2) := by
    change fixedRawHom m (outerFixedWeyl m * middleFixedWeyl m) =
      wordUnit A hs hp b₀ s₀ (Field m) ([0,5,1] ++ [2,4,3,2,4,3])
    rw [map_mul, raw_outer, raw_middle, wordUnit_append]
    rfl
  have hmap₂ := outer_block_conjugate_le m (outerFixedWeyl m * middleFixedWeyl m)
    (conjugatingWord false 2) hraw₂ (positiveBlockSigns_first_three false ⟨2, by decide⟩)
  have hpos : middleFixedWeyl m * u * (middleFixedWeyl m)⁻¹ ∈ fixedPositive m :=
    hmap₁ ⟨u, hu, rfl⟩
  have hconj : outerFixedWeyl m * (middleFixedWeyl m * u * (middleFixedWeyl m)⁻¹) *
      (outerFixedWeyl m)⁻¹ ∈ fixedPositive m := by
    have he : outerFixedWeyl m * (middleFixedWeyl m * u * (middleFixedWeyl m)⁻¹) *
        (outerFixedWeyl m)⁻¹ =
        (outerFixedWeyl m * middleFixedWeyl m) * u *
          (outerFixedWeyl m * middleFixedWeyl m)⁻¹ := by group
    rw [he]
    exact hmap₂ ⟨u, hu, rfl⟩
  exact mem_kernelImage m _ hpos (fixedPositive_remainder_strict m _ hpos hconj)

theorem abelian_image_eq (m : ℕ) {B : Type*} [CommGroup B]
    (f : originalModelFixed m →* B) : (kernelImage m).map f = f.range := by
  apply le_antisymm
  · rintro _ ⟨g, _, rfl⟩
    exact ⟨g, rfl⟩
  · rw [range_eq_block_join]
    apply sup_le
    · rintro _ ⟨u, hu, rfl⟩
      rw [positiveBlock, simpleWeyl, simple_inversion_eq_block] at hu
      have hku : middleFixedWeyl m * u * (middleFixedWeyl m)⁻¹ ∈ kernelImage m :=
        outer_middle_conjugate_le_kernelImage m ⟨u, hu, rfl⟩
      refine ⟨middleFixedWeyl m * u * (middleFixedWeyl m)⁻¹, hku, ?_⟩
      rw [map_mul, map_mul, map_inv, mul_comm (f (middleFixedWeyl m)) (f u),
        mul_assoc, mul_inv_cancel, mul_one]
    · rintro _ ⟨u, hu, rfl⟩
      rw [positiveBlock, simpleWeyl, simple_inversion_eq_block] at hu
      exact ⟨u, middle_inversion_le_kernelImage m hu, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterKernelAbelianImage
