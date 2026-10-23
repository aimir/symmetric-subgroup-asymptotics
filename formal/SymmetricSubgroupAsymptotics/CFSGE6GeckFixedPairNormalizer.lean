import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedUpperNormalizer
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedRangePreimage
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeOpposition
import SymmetricSubgroupAsymptotics.CFSGE6GeckIntermediateOvergroup
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality

/-! The simultaneous normalizer of the genuine fixed opposed pair in
J consists of actual diagonal Geck matrices. The negative inclusion is
transferred by the same fixed relative opposition from proved positive
regularity. No whole-fixed-group recognition or generated-torus equality
is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckFixedPairNormalizer
open CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckRelativeRootGenerated CFSGE6GeckIntermediateOvergroup
open CFSGTwistedE6GeckRelativeOpposition CFSGE6GeckFixedUpperNormalizer
open CFSGTwistedE6GeckNormalizerEnvelope CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckFixedRangePreimage
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

theorem fixed_positive_normalizer_le_envelope (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) :
    Subgroup.normalizer (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ)⊓
      fixedRootGenerated K sigma≤normalizerEnvelope K := by
  rw [←upperIn_eq_normalizer_inter K sigma (fixedRootGenerated K sigma)
    (fixedRootGenerated_le_preimage K sigma)]
  exact inf_le_left

theorem fixed_negative_normalizer_le_ambient (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) :
    Subgroup.normalizer (signedFixed K sigma true : Set (Matrix GeckIndex GeckIndex K)ˣ)⊓
      fixedRootGenerated K sigma≤
        Subgroup.normalizer (Negative K : Set (Matrix GeckIndex GeckIndex K)ˣ)⊓MatrixGroup K := by
  intro d hdD
  let e := MulAut.conj (relativeOpposition K)
  have hsign : (signedFixed K sigma false).map e.toMonoidHom=signedFixed K sigma true :=
    fixed_positive_image_eq_fixed_negative K sigma
  have hN : (Subgroup.normalizer
      (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ)).map e.toMonoidHom=
        Subgroup.normalizer (signedFixed K sigma true : Set (Matrix GeckIndex GeckIndex K)ˣ) :=
    (Subgroup.map_equiv_normalizer_eq (signedFixed K sigma false) e).trans
      (congrArg (fun S : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ)=>
        Subgroup.normalizer (S : Set ((Matrix GeckIndex GeckIndex K)ˣ))) hsign)
  have hdN : d∈(Subgroup.normalizer
      (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ)).map e.toMonoidHom :=
    hN.symm ▸ hdD.1
  obtain ⟨c,hcN,he⟩ := hdN
  have hcJ : c∈fixedRootGenerated K sigma := by
    have hO := relativeOpposition_mem_generated K sigma
    have hh := (fixedRootGenerated K sigma).mul_mem
      ((fixedRootGenerated K sigma).mul_mem ((fixedRootGenerated K sigma).inv_mem hO) hdD.2) hO
    have hc : (relativeOpposition K)⁻¹*d*relativeOpposition K=c := by
      rw [←he]
      change (relativeOpposition K)⁻¹*(relativeOpposition K*c*(relativeOpposition K)⁻¹)*
        relativeOpposition K=c
      group
    exact hc ▸ hh
  have hcE := fixed_positive_normalizer_le_envelope K sigma ⟨hcN,hcJ⟩
  have hn := (Positive K).le_normalizer_map e.toMonoidHom
    (show d∈(Subgroup.normalizer (Positive K : Set (Matrix GeckIndex GeckIndex K)ˣ)).map
      e.toMonoidHom from ⟨c,hcE.1,he⟩)
  change d∈Subgroup.normalizer ((Positive K).map
    (MulAut.conj (relativeOpposition K)).toMonoidHom : Set (Matrix GeckIndex GeckIndex K)ˣ) at hn
  rw [positive_image_eq_negative] at hn
  exact ⟨hn,fixedRootGenerated_le_matrixGroup K sigma hdD.2⟩

def pairNormalizer (K : Type) [Field K] (sigma : K≃+*K) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  (Subgroup.normalizer (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ)⊓
    Subgroup.normalizer (signedFixed K sigma true : Set (Matrix GeckIndex GeckIndex K)ˣ))⊓
      fixedRootGenerated K sigma

theorem pairNormalizer_le_diagonalNormalizer (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) : pairNormalizer K sigma≤diagonalNormalizer K := by
  intro g hg
  have hpos := fixed_positive_normalizer_le_envelope K sigma ⟨hg.1.1,hg.2⟩
  have hneg := fixed_negative_normalizer_le_ambient K sigma ⟨hg.1.2,hg.2⟩
  exact ⟨⟨hpos.1,hneg.1⟩,hpos.2⟩

theorem pairNormalizer_isDiag (K : Type) [Field K] [Finite K] (sigma : K≃+*K)
    (g : (Matrix GeckIndex GeckIndex K)ˣ) (hg : g∈pairNormalizer K sigma) :
    (g : Matrix GeckIndex GeckIndex K).IsDiag :=
  diagonalNormalizer_isDiag K g (pairNormalizer_le_diagonalNormalizer K sigma hg)

end SymmetricSubgroupAsymptotics.CFSGE6GeckFixedPairNormalizer
