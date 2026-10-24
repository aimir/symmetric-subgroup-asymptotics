import SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalPositiveFaithful
import SymmetricSubgroupAsymptotics.CFSGE6GeckSignedSimpleParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeRootGenerated
import SymmetricSubgroupAsymptotics.CFSGTwistedE6FixedA2

/-! The four literal folded positive parameter actions faithfully
determine a diagram-fixed E6 diagonal-normalizer element in characteristic
two. Paired scalars agree by actual diagram covariance, and actual paired
parameter injectivity separates them. No ordinary F4 simplicity occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6DiagonalOrbitFaithful
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckNormalizerEnvelope
open CFSGE6GeckDiagonalSimpleScalars CFSGE6GeckDiagonalPositiveFaithful
open CFSGE6GeckSignedSimpleParameters CFSGTwistedE6PairedFixedRoots CFSGTwistedE6FixedA2
open CFSGSerreQuadraticMatrix

private theorem paired_positive_fixed (K : Type) [Field K]
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hD : d∈diagonalNormalizer K)
    (hfix : unitTwist K (RingEquiv.refl K) d=d)
    (hfixed : ∀a t,d*orbitParameter K false a t*d⁻¹=orbitParameter K false a t)
    (j : Fin 2) :
    (∀t,d*canonicalRoot rawData K false (pairedNode j) t*d⁻¹=
      canonicalRoot rawData K false (pairedNode j) t) ∧
    (∀t,d*canonicalRoot rawData K false (pairedPartner j) t*d⁻¹=
      canonicalRoot rawData K false (pairedPartner j) t) := by
  obtain ⟨c,hc⟩ := exists_simple_scalar K d hD (diagonalNormalizer_isDiag K d hD) (pairedNode j)
  have hp (t : K) : d*canonicalRoot rawData K false (pairedPartner j) t*d⁻¹=
      canonicalRoot rawData K false (pairedPartner j) ((c:K)*t) := by
    have h := congrArg (unitTwist K (RingEquiv.refl K)) (hc t)
    simpa only [map_mul,map_inv,hfix,unitTwist_root,RingEquiv.refl_apply] using h
  have hpair (t : K) :
      d*rawPairedHom K (RingEquiv.refl K) false j (Multiplicative.ofAdd t)*d⁻¹=
        rawPairedHom K (RingEquiv.refl K) false j (Multiplicative.ofAdd ((c:K)*t)) := by
    change d*(canonicalRoot rawData K false (pairedNode j) t*
      canonicalRoot rawData K false (pairedPartner j) t)*d⁻¹=_
    calc
      _=(d*canonicalRoot rawData K false (pairedNode j) t*d⁻¹)*
        (d*canonicalRoot rawData K false (pairedPartner j) t*d⁻¹) := by group
      _=_ := by rw [hc,hp];rfl
  have hpairfix (t : K) :
      d*rawPairedHom K (RingEquiv.refl K) false j (Multiplicative.ofAdd t)*d⁻¹=
        rawPairedHom K (RingEquiv.refl K) false j (Multiplicative.ofAdd t) := by
    fin_cases j
    · exact hfixed 0 t
    · exact hfixed 1 t
  have he := rawPaired_injective K (RingEquiv.refl K) false j ((hpairfix 1).symm.trans (hpair 1))
  have hval := congrArg Multiplicative.toAdd he
  have hc1 : c=1 := Units.ext (by simpa only [mul_one,Units.val_one] using hval.symm)
  subst c
  exact ⟨fun t=>by simpa only [Units.val_one,one_mul] using hc t,
    fun t=>by simpa only [Units.val_one,one_mul] using hp t⟩

theorem fixes_ambient_positive_of_fixes_orbits (K : Type) [Field K]
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hD : d∈diagonalNormalizer K)
    (hfix : unitTwist K (RingEquiv.refl K) d=d)
    (hfixed : ∀a t,d*orbitParameter K false a t*d⁻¹=orbitParameter K false a t) :
    ∀i t,d*canonicalRoot rawData K false i t*d⁻¹=canonicalRoot rawData K false i t := by
  have hp := paired_positive_fixed K d hD hfix hfixed
  intro i t
  fin_cases i
  · exact (hp 0).1 t
  · exact hfixed 3 t
  · exact (hp 1).1 t
  · exact hfixed 2 t
  · exact (hp 1).2 t
  · exact (hp 0).2 t

theorem diagonal_eq_one_of_orbits_fixed (K : Type) [Field K] [CharP K 2]
    (d : (Matrix GeckIndex GeckIndex K)ˣ) (hD : d∈diagonalNormalizer K)
    (hfix : unitTwist K (RingEquiv.refl K) d=d)
    (hfixed : ∀a t,d*orbitParameter K false a t*d⁻¹=orbitParameter K false a t) : d=1 :=
  diagonal_eq_one_of_positive_simple_fixed K d hD
    (fixes_ambient_positive_of_fixes_orbits K d hD hfix hfixed)

end SymmetricSubgroupAsymptotics.CFSGFFourE6DiagonalOrbitFaithful
