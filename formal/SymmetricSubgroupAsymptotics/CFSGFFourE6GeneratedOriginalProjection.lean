import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalCentralKernel
import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedGeneratedGroup
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGE6GeckGeneratedParabolics

/-! Exact fixed-root-generated coordinates for the ORIGINAL F4 quotient.
The literal subgroup equality gives a surjective projection; the actual
positive Sylow map is identified and injective, and the proved central
kernel is retained in the literal upper normalizer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6GeneratedOriginalProjection
open CFSGFFourSerreMatrices CFSGFFourE6OriginalProjection
open CFSGFFourE6OriginalCentralKernel CFSGFFourE6FixedGeneratedGroup
open CFSGFFourE6OriginalOppositeAlignment CFSGFFourE6DiagramFixed
open CFSGFFourE6PositiveSylow CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGE6GeckGeneratedParabolics
open CFSGSerreQuadraticMatrix CFSG.Models.Chevalley

def foldedEquiv (K : Type) [Field K] [Finite K] :
    fixedRootGenerated K (RingEquiv.refl K) ≃* canonicalElementaryGroup realizationData K :=
  MulEquiv.subgroupCongr (fixedRootGenerated_eq_folded K)

def generatedToOriginal (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    fixedRootGenerated K (RingEquiv.refl K) →* Projective CartanMatrix.F₄ K :=
  (foldedToOriginal K).comp (foldedEquiv K).toMonoidHom

theorem generatedToOriginal_surjective (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] : Function.Surjective (generatedToOriginal K) :=
  (foldedToOriginal_surjective K).comp (foldedEquiv K).surjective

theorem rootPart_positive_folded_image (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (rootPart K (RingEquiv.refl K) false).map (foldedEquiv K).toMonoidHom =
      (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)) := by
  ext x
  rw [positiveSylow_coe]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj.1
  · intro hx
    refine ⟨(foldedEquiv K).symm x, ?_, (foldedEquiv K).apply_symm_apply x⟩
    exact ⟨hx, foldedModel_le_diagramFixed K x.property⟩

theorem rootPart_positive_original_injective (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    Function.Injective ((generatedToOriginal K).comp
      (rootPart K (RingEquiv.refl K) false).subtype) := by
  intro a b he
  let ea : positiveSylow K p := ⟨foldedEquiv K a.val, by
    change foldedEquiv K a.val ∈ (positiveSylow K p :
      Subgroup (canonicalElementaryGroup realizationData K))
    rw [positiveSylow_coe]
    exact a.property.1⟩
  let eb : positiveSylow K p := ⟨foldedEquiv K b.val, by
    change foldedEquiv K b.val ∈ (positiveSylow K p :
      Subgroup (canonicalElementaryGroup realizationData K))
    rw [positiveSylow_coe]
    exact b.property.1⟩
  have he' : foldedPositiveToOriginal K p ea = foldedPositiveToOriginal K p eb := he
  have hh := foldedPositiveToOriginal_injective K p he'
  apply Subtype.ext
  apply (foldedEquiv K).injective
  exact congrArg (fun z : positiveSylow K p => z.val) hh

theorem rootPart_positive_original_image (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (rootPart K (RingEquiv.refl K) false).map (generatedToOriginal K) =
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)) := by
  rw [generatedToOriginal, ← Subgroup.map_map, rootPart_positive_folded_image K p]
  exact positiveSylow_original_image K p

theorem generatedToOriginal_kernel_le_center (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (generatedToOriginal K).ker ≤ Subgroup.center (fixedRootGenerated K (RingEquiv.refl K)) := by
  intro j hj
  have hh : foldedEquiv K j ∈ (foldedToOriginal K).ker := hj
  have hc := foldedToOriginal_kernel_le_center K p hh
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply (foldedEquiv K).injective
  simpa only [map_mul] using Subgroup.mem_center_iff.mp hc (foldedEquiv K x)

theorem original_kernel_le_upperGenerated (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (generatedToOriginal K).ker ≤ upperGenerated K (RingEquiv.refl K) := by
  rw [upperGenerated_eq_normalizer]
  exact (generatedToOriginal_kernel_le_center K p).trans (Subgroup.center_le_normalizer _)

end SymmetricSubgroupAsymptotics.CFSGFFourE6GeneratedOriginalProjection
