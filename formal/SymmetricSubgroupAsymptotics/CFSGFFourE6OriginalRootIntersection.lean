import SymmetricSubgroupAsymptotics.CFSGFFourE6GeneratedOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGE6GeckGeneratedRootIntersection
import SymmetricSubgroupAsymptotics.CFSGKernelControlledIntersection

/-! The literal four positive root charts of ORIGINAL F4 are recovered
by intersecting its positive Sylow with the four actual opposite
parabolics. The proved central kernel controls the intersection image;
neither a lifted automorphism nor global source faithfulness is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootIntersection
open CFSGFFourE6GeneratedOriginalProjection CFSGFFourE6OriginalOppositeAlignment
open CFSGE6GeckGeneratedRootIntersection CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRootGeneratedPGroup CFSGKernelControlledIntersection
open CFSGSerreQuadraticMatrix CFSGFFourSerreMatrices CFSG.Models.Chevalley

def originalOppositeParabolic (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (a : Fin 4) :
    Subgroup (Projective CartanMatrix.F₄ K) :=
  (oppositeParabolicGenerated K (RingEquiv.refl K) a).map (generatedToOriginal K)

def originalOrbitRoot (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (a : Fin 4) :
    Subgroup (Projective CartanMatrix.F₄ K) :=
  (orbitRootGenerated K (RingEquiv.refl K) a).map (generatedToOriginal K)

theorem original_kernel_le_oppositeParabolicGenerated (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (a : Fin 4) : (generatedToOriginal K).ker ≤
      oppositeParabolicGenerated K (RingEquiv.refl K) a :=
  (generatedToOriginal_kernel_le_center K p).trans
    ((Subgroup.center_le_normalizer
      (rootPart K (RingEquiv.refl K) true : Set (fixedRootGenerated K (RingEquiv.refl K)))).trans
        (negative_normalizer_le_oppositeParabolicGenerated K (RingEquiv.refl K) a))

theorem original_positive_inf_oppositeParabolic (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (a : Fin 4) :
    (CFSGFFourE6OriginalProjection.originalPositiveSylow K p :
      Subgroup (Projective CartanMatrix.F₄ K)) ⊓ originalOppositeParabolic K a =
      originalOrbitRoot K a := by
  have hh := congrArg (fun S : Subgroup (fixedRootGenerated K (RingEquiv.refl K)) =>
    S.map (generatedToOriginal K))
    (rootPart_inf_oppositeParabolicGenerated K (RingEquiv.refl K) (fun _ => rfl) a)
  dsimp only at hh
  rw [map_inf_eq_of_kernel_le_right (generatedToOriginal K) _ _
    (original_kernel_le_oppositeParabolicGenerated K p a),
    rootPart_positive_original_image K p] at hh
  exact hh

theorem rootPart_negative_folded_image (K : Type) [Field K] [Finite K] :
    (rootPart K (RingEquiv.refl K) true).map (foldedEquiv K).toMonoidHom = negativeInFolded K := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hx
    exact ⟨(foldedEquiv K).symm x, hx, (foldedEquiv K).apply_symm_apply x⟩

theorem rootPart_negative_original_image (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (rootPart K (RingEquiv.refl K) true).map (generatedToOriginal K) = originalNegative K := by
  rw [generatedToOriginal, ← Subgroup.map_map, rootPart_negative_folded_image]
  rfl

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalRootIntersection
