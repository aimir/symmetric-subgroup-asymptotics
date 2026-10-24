import SymmetricSubgroupAsymptotics.CFSGFFourE6DiagonalOrbitFaithful
import SymmetricSubgroupAsymptotics.CFSGFFourE6PairNormalizerScalars
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalPositiveDiagramImage

/-! Four scalar actions of the retained diagonal subgroup of the same
original characteristic-two F4 Model. The scalar actions are faithful;
no identification with a torus or ordinary F4 simplicity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourOriginalDiagonalScalars
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalBruhatCells
open CFSGFFourOriginalGeneratedEquivalence CFSGFFourOriginalPositiveDiagramImage
open CFSGFFourE6PairNormalizerScalars CFSGE6GeckFixedPairNormalizer
open CFSGFFourE6DiagonalOrbitFaithful CFSGE6GeckRelativeSimpleHom
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckPositiveTwist
open CFSGCentralTwistedCommutatorLift
variable (K : Type) [Field K] [Finite K] [CharP K 2]

private theorem rawOrbit_id (neg : Bool) (i : Fin 4) (t : K) :
    rawOrbitHom K (RingEquiv.refl K) neg i (Multiplicative.ofAdd t)=
      orbitParameter K neg i t := by
  fin_cases i <;> rfl

theorem rawHom_diagonal_mem_pairNormalizer (d : Model CartanMatrix.F₄ K)
    (hdD : d∈modelDiagonalPart K) :
    rawHom K d∈pairNormalizer K (RingEquiv.refl K) := by
  have hfix : rawHom K d∈fixedSubgroup (unitTwist K (RingEquiv.refl K)) :=
    rawHom_diagram_fixed K d
  have hn := (fixedSubgroup (unitTwist K (RingEquiv.refl K))).le_normalizer hfix
  have hJ : rawHom K d∈fixedRootGenerated K (RingEquiv.refl K) := by
    rw [←modelEquivGenerated_val K d]
    exact (modelEquivGenerated K d).property
  refine ⟨⟨?_,?_⟩,hJ⟩
  · exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hdD.1.1,hn⟩
  · exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hdD.1.2,hn⟩

theorem exists_model_diagonal_scalars (d : Model CartanMatrix.F₄ K)
    (hdD : d∈modelDiagonalPart K) :
    ∃c : Fin 4→Kˣ,∀i t,
      d*modelRoot CartanMatrix.F₄ K false i t*d⁻¹=
        modelRoot CartanMatrix.F₄ K false i ((c i:K)*t) := by
  obtain ⟨c,hc⟩ := pairNormalizer_positive_scalars K (rawHom K d)
    (rawHom_diagonal_mem_pairNormalizer K d hdD)
  refine ⟨c,?_⟩
  intro i t
  apply rawHom_injective K
  simp only [map_mul,map_inv,rawHom_root,
    CFSGFFourE6FixedGeneratedGroup.folded_root_eq_orbitParameter]
  simpa only [rawOrbit_id] using hc i t

theorem model_diagonal_eq_one_of_simple_fixed (d : Model CartanMatrix.F₄ K)
    (hdD : d∈modelDiagonalPart K)
    (hfixed : ∀i t,d*modelRoot CartanMatrix.F₄ K false i t*d⁻¹=
      modelRoot CartanMatrix.F₄ K false i t) : d=1 := by
  have hraw : rawHom K d=1 := diagonal_eq_one_of_orbits_fixed K (rawHom K d) hdD
    (rawHom_diagram_fixed K d) (by
      intro i t
      have h := congrArg (rawHom K) (hfixed i t)
      simpa only [map_mul,map_inv,rawHom_root,
        CFSGFFourE6FixedGeneratedGroup.folded_root_eq_orbitParameter] using h)
  apply rawHom_injective K
  simpa only [map_one] using hraw

end SymmetricSubgroupAsymptotics.CFSGFFourOriginalDiagonalScalars
