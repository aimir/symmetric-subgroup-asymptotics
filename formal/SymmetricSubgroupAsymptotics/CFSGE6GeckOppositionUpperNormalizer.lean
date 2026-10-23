import SymmetricSubgroupAsymptotics.CFSGE6GeckOppositeOrbitParabolic
import SymmetricSubgroupAsymptotics.CFSGE6GeckIntermediateOvergroup
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality

/-! Actual relative opposition transports the whole positive fixed
normalizer onto the whole negative fixed normalizer inside J. Elements
of the simultaneous ambient normalizer that lie in J normalize both
fixed root parts, since J is pointwise fixed by the same twist. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOppositionUpperNormalizer
open CFSGE6GeckOppositeOrbitParabolic CFSGE6GeckIntermediateOvergroup
open CFSGTwistedE6GeckRelativeOpposition CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckNormalizerEnvelope
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckFixedRangePreimage CFSGSubgroupConjugateOrbitCardinality

theorem diagonal_generated_le_negativeNormalizer (K : Type) [Field K] (sigma : K≃+*K) :
    diagonalNormalizer K⊓fixedRootGenerated K sigma≤negativeGeneratedNormalizer K sigma := by
  intro d hdD
  refine ⟨?_,hdD.2⟩
  have hfix := fixedRootGenerated_le_fixed K sigma hdD.2
  have hfn := (CFSGCentralTwistedCommutatorLift.fixedSubgroup (unitTwist K sigma)).le_normalizer hfix
  have hn := Subgroup.inf_normalizer_le_normalizer_inf ⟨hdD.1.1.2,hfn⟩
  exact hn

theorem generated_opposition_map (K : Type) [Field K] (sigma : K≃+*K) :
    (fixedRootGenerated K sigma).map (MulAut.conj (relativeOpposition K)).toMonoidHom=
      fixedRootGenerated K sigma :=
  conjugate_eq_of_mem_normalizer _ _
    ((fixedRootGenerated K sigma).le_normalizer (relativeOpposition_mem_generated K sigma))

theorem upperIn_opposition_map (K : Type) [Field K] [Finite K] (sigma : K≃+*K) :
    (upperIn K (fixedRootGenerated K sigma)).map
      (MulAut.conj (relativeOpposition K)).toMonoidHom=negativeGeneratedNormalizer K sigma := by
  let e := MulAut.conj (relativeOpposition K)
  have hN : (Subgroup.normalizer
      (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ)).map e.toMonoidHom=
      Subgroup.normalizer (signedFixed K sigma true : Set (Matrix GeckIndex GeckIndex K)ˣ) :=
    (Subgroup.map_equiv_normalizer_eq (signedFixed K sigma false) e).trans
      (congrArg (fun S : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ)=>
        Subgroup.normalizer (S : Set ((Matrix GeckIndex GeckIndex K)ˣ)))
        (fixed_positive_image_eq_fixed_negative K sigma))
  rw [upperIn_eq_normalizer_inter K sigma (fixedRootGenerated K sigma)
    (fixedRootGenerated_le_preimage K sigma),Subgroup.map_inf _ _ _ e.injective]
  exact congrArg₂ (fun H L : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ)=>H⊓L)
    hN (generated_opposition_map K sigma)

end SymmetricSubgroupAsymptotics.CFSGE6GeckOppositionUpperNormalizer
