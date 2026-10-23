import SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalSimpleScalars
import SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleGeneratedParameters

/-! Four actual positive scalar actions of the identity-field E6 fixed
pair normalizer. Diagram fixedness equates each paired scalar; no torus
recognition or root-length claim about arbitrary automorphisms occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6PairNormalizerScalars
open CFSGE6GeckDiagonalSimpleScalars CFSGE6GeckFixedPairNormalizer
open CFSGE6GeckSignedSimpleParameters CFSGE6GeckRelativeSimpleHom
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6PairedFixedRoots
open CFSGTwistedE6FixedA2 CFSGSerreQuadraticMatrix

private theorem paired_scalar (K:Type) [Field K] [Finite K]
    (d:(Matrix GeckIndex GeckIndex K)ˣ) (hD:d∈pairNormalizer K (RingEquiv.refl K))
    (j:Fin 2) : ∃c:Kˣ,∀t:K,
    d*rawPairedHom K (RingEquiv.refl K) false j (Multiplicative.ofAdd t)*d⁻¹=
      rawPairedHom K (RingEquiv.refl K) false j (Multiplicative.ofAdd ((c:K)*t)) := by
  obtain ⟨c,hc⟩ := pairNormalizer_simple_scalar K (RingEquiv.refl K) d hD (pairedNode j)
  have hfix : unitTwist K (RingEquiv.refl K) d=d :=
    fixedRootGenerated_le_fixed K (RingEquiv.refl K) hD.2
  have hp (t:K) : d*canonicalRoot rawData K false (pairedPartner j) t*d⁻¹=
      canonicalRoot rawData K false (pairedPartner j) ((c:K)*t) := by
    have h := congrArg (unitTwist K (RingEquiv.refl K)) (hc t)
    simpa only [map_mul,map_inv,hfix,unitTwist_root,RingEquiv.refl_apply] using h
  refine ⟨c,?_⟩
  intro t
  change d*(canonicalRoot rawData K false (pairedNode j) t*
    canonicalRoot rawData K false (pairedPartner j) t)*d⁻¹=_
  calc
    _=(d*canonicalRoot rawData K false (pairedNode j) t*d⁻¹)*
        (d*canonicalRoot rawData K false (pairedPartner j) t*d⁻¹) := by group
    _=_ := by rw [hc,hp];rfl

private theorem singleton_scalar (K:Type) [Field K] [Finite K]
    (d:(Matrix GeckIndex GeckIndex K)ˣ) (hD:d∈pairNormalizer K (RingEquiv.refl K))
    (j:Fin 2) : ∃c:Kˣ,∀t:K,
    d*rawSingletonHom K false j (Multiplicative.ofAdd t)*d⁻¹=
      rawSingletonHom K false j (Multiplicative.ofAdd ((c:K)*t)) := by
  exact pairNormalizer_simple_scalar K (RingEquiv.refl K) d hD (node j)

theorem pairNormalizer_positive_scalars (K:Type) [Field K] [Finite K]
    (d:(Matrix GeckIndex GeckIndex K)ˣ) (hD:d∈pairNormalizer K (RingEquiv.refl K)) :
    ∃c:Fin 4→Kˣ,∀i t,
      d*rawOrbitHom K (RingEquiv.refl K) false i (Multiplicative.ofAdd t)*d⁻¹=
        rawOrbitHom K (RingEquiv.refl K) false i (Multiplicative.ofAdd ((c i:K)*t)) := by
  obtain ⟨c0,h0⟩ := paired_scalar K d hD 0
  obtain ⟨c1,h1⟩ := paired_scalar K d hD 1
  obtain ⟨c2,h2⟩ := singleton_scalar K d hD 1
  obtain ⟨c3,h3⟩ := singleton_scalar K d hD 0
  refine ⟨![c0,c1,c2,c3],?_⟩
  intro i t
  fin_cases i
  · exact h0 t
  · exact h1 t
  · exact h2 t
  · exact h3 t

end SymmetricSubgroupAsymptotics.CFSGFFourE6PairNormalizerScalars
