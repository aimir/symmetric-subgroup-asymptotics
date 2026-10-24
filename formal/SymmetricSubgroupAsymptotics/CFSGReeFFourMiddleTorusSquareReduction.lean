import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusGroup
import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeGenerationAssembly
import SymmetricSubgroupAsymptotics.NormalizerInversionSquareExtraction
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! The actual retained fixed diagonal group normalizes both original
opposite unipotent groups. Thus inversion by an already generated
middle Weyl word suffices for the entire middle torus family, by square
extraction. Actual Weyl membership and inversion remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTorusSquareReduction
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourFixedBruhatCover CFSGReeFFourOuterUnipotentGeneration
open CFSGReeFFourOppositeGenerationAssembly CFSGReeFFourFixedTorus
open CFSGReeFFourFixedTorusGroup CFSGReeFFourFixedDiagonalCardinality
open CFSGTwistedE6GeckNormalizerEnvelope NormalizerInversionSquareExtraction

theorem fixedDiagonal_le_normalizer_oppositeGenerated (m : ℕ) :
    fixedDiagonal m ≤ Subgroup.normalizer (oppositeGenerated m : Set (originalModelFixed m)) := by
  intro d hd
  have hraw : fixedRawHom m d ∈ diagonalNormalizer (Field m) := hd
  have hU : d ∈ Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m)) :=
    Subgroup.le_normalizer_comap (fixedRawHom m) hraw.1.1
  have hV : d ∈ Subgroup.normalizer (fixedNegative m : Set (originalModelFixed m)) :=
    Subgroup.le_normalizer_comap (fixedRawHom m) hraw.1.2
  exact (fixedPositive m).normalizer_inf_normalizer_le_normalizer_sup (fixedNegative m) ⟨hU,hV⟩

theorem middle_torus_mem_of_weyl_inversion (m : ℕ)
    (hW : fixedMiddleWeyl m ∈ oppositeGenerated m)
    (hi : ∀ b : (Field m)ˣ,
      fixedMiddleWeyl m * fixedTorus m 1 b * (fixedMiddleWeyl m)⁻¹ = (fixedTorus m 1 b)⁻¹)
    (b : (Field m)ˣ) : fixedTorus m 1 b ∈ oppositeGenerated m := by
  have hr : (middleTorusHom m).range ≤ oppositeGenerated m :=
    range_le_of_surjective_square (oppositeGenerated m) (middleTorusHom m)
      (unit_square_surjective m) (fixedMiddleWeyl m) hW
      (fun a => fixedDiagonal_le_normalizer_oppositeGenerated m (fixedTorus_mem_diagonal m 1 a)) hi
  exact hr ⟨b,rfl⟩

theorem oppositeGenerated_eq_top_of_middle_inversion (m : ℕ)
    (hW : fixedMiddleWeyl m ∈ oppositeGenerated m)
    (hi : ∀ b : (Field m)ˣ,
      fixedMiddleWeyl m * fixedTorus m 1 b * (fixedMiddleWeyl m)⁻¹ = (fixedTorus m 1 b)⁻¹) :
    oppositeGenerated m = ⊤ :=
  oppositeGenerated_eq_top_of_middle m hW (middle_torus_mem_of_weyl_inversion m hW hi)

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTorusSquareReduction
