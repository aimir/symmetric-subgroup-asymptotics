import SymmetricSubgroupAsymptotics.CFSGFFourE6NormActionKernelUpper
import SymmetricSubgroupAsymptotics.CFSGE6GeckDiagonalSimpleScalars

/-! An actual norm26 kernel element centralizes every positive ambient
E6 simple parameter. Pair normalization provides the literal scalars;
injectivity of the folded norm charts forces them to be one. No original
F4 quotient, ordinary simplicity, or generated-torus recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormKernelPositiveScalars
open CFSGFFourSerreMatrices CFSGFFourE6NormActionKernelUpper CFSGFFourE6FixedGeneratedGroup
open CFSGFFourE6NormSimpleParameters CFSGFFourE6CharacteristicTwoNormImage
open CFSGE6GeckFixedPairNormalizer CFSGE6GeckDiagonalSimpleScalars
open CFSGE6GeckRelativeSimpleHom CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckFixedRangePreimage
open CFSGTwistedE6FixedA2 CFSGTwistedE6PairedFixedRoots CFSGSerreQuadraticMatrix
variable (K:Type) [Field K] [Finite K] [CharP K 2]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

omit [Finite K] [CharP K 2] in
private theorem rawOrbitHom_id_parameter (neg:Bool) (a:Fin 4) (t:K) :
    rawOrbitHom K (RingEquiv.refl K) neg a (Multiplicative.ofAdd t)=orbitParameter K neg a t := by
  fin_cases a <;> rfl

private theorem kernel_orbit_scalar_one (g:J) (hg:g∈(generatedNormAction K).ker)
    (a:Fin 4) (c:Kˣ)
    (hc:∀t:K,g.val*rawOrbitHom K (RingEquiv.refl K) false a (Multiplicative.ofAdd t)*g.val⁻¹=
      rawOrbitHom K (RingEquiv.refl K) false a (Multiplicative.ofAdd ((c:K)*t))) : c=1 := by
  have hconj:generatedToFolded K g*foldedRoot K false a 1*(generatedToFolded K g)⁻¹=
      foldedRoot K false a ((c:K)*1) := by
    apply Subtype.ext
    change g.val*canonicalRoot realizationData K false a 1*g.val⁻¹=
      canonicalRoot realizationData K false a ((c:K)*1)
    rw [folded_root_eq_orbitParameter K false a 1,
      folded_root_eq_orbitParameter K false a ((c:K)*1),
      ←rawOrbitHom_id_parameter K false a 1,←rawOrbitHom_id_parameter K false a ((c:K)*1)]
    exact hc 1
  have h:=congrArg (normAction K) hconj
  rw [map_mul,map_mul,map_inv] at h
  have hk:normAction K (generatedToFolded K g)=1:=hg
  rw [hk,one_mul,inv_one,mul_one] at h
  have ht:(1:K)=(c:K)*1:=norm_positive_parameter_injective K a h
  apply Units.ext
  simpa only [mul_one,Units.val_one] using ht.symm

private theorem kernel_paired_scalar_one (g:J) (hg:g∈(generatedNormAction K).ker)
    (j:Fin 2) (c:Kˣ)
    (hc:∀t:K,g.val*rawPairedHom K (RingEquiv.refl K) false j (Multiplicative.ofAdd t)*g.val⁻¹=
      rawPairedHom K (RingEquiv.refl K) false j (Multiplicative.ofAdd ((c:K)*t))) : c=1 := by
  fin_cases j
  · exact kernel_orbit_scalar_one K g hg 0 c hc
  · exact kernel_orbit_scalar_one K g hg 1 c hc

private theorem kernel_singleton_scalar_one (g:J) (hg:g∈(generatedNormAction K).ker)
    (j:Fin 2) (c:Kˣ)
    (hc:∀t:K,g.val*rawSingletonHom K false j (Multiplicative.ofAdd t)*g.val⁻¹=
      rawSingletonHom K false j (Multiplicative.ofAdd ((c:K)*t))) : c=1 := by
  fin_cases j
  · exact kernel_orbit_scalar_one K g hg 3 c hc
  · exact kernel_orbit_scalar_one K g hg 2 c hc

private theorem kernel_fixes_paired (g:J) (hg:g∈(generatedNormAction K).ker) (j:Fin 2) :
    (∀t:K,g.val*canonicalRoot rawData K false (pairedNode j) t*g.val⁻¹=
      canonicalRoot rawData K false (pairedNode j) t) ∧
    (∀t:K,g.val*canonicalRoot rawData K false (pairedPartner j) t*g.val⁻¹=
      canonicalRoot rawData K false (pairedPartner j) t) := by
  have hD:=kernel_mem_pairNormalizer K g hg
  obtain ⟨c,hc⟩:=pairNormalizer_simple_scalar K (RingEquiv.refl K) g.val hD (pairedNode j)
  have hfix:unitTwist K (RingEquiv.refl K) g.val=g.val:=
    fixedRootGenerated_le_fixed K (RingEquiv.refl K) g.property
  have hp (t:K):g.val*canonicalRoot rawData K false (pairedPartner j) t*g.val⁻¹=
      canonicalRoot rawData K false (pairedPartner j) ((c:K)*t) := by
    have h:=congrArg (unitTwist K (RingEquiv.refl K)) (hc t)
    simpa only [map_mul,map_inv,hfix,unitTwist_root,RingEquiv.refl_apply] using h
  have hpair (t:K):g.val*rawPairedHom K (RingEquiv.refl K) false j (Multiplicative.ofAdd t)*g.val⁻¹=
      rawPairedHom K (RingEquiv.refl K) false j (Multiplicative.ofAdd ((c:K)*t)) := by
    change g.val*(canonicalRoot rawData K false (pairedNode j) t*
      canonicalRoot rawData K false (pairedPartner j) t)*g.val⁻¹=_
    calc
      _=(g.val*canonicalRoot rawData K false (pairedNode j) t*g.val⁻¹)*
        (g.val*canonicalRoot rawData K false (pairedPartner j) t*g.val⁻¹) := by group
      _=_ := by rw [hc,hp];rfl
  have hc1:c=1:=kernel_paired_scalar_one K g hg j c hpair
  subst c
  exact ⟨fun t=>by simpa only [Units.val_one,one_mul] using hc t,
    fun t=>by simpa only [Units.val_one,one_mul] using hp t⟩

private theorem kernel_fixes_singleton (g:J) (hg:g∈(generatedNormAction K).ker) (j:Fin 2) :
    ∀t:K,g.val*canonicalRoot rawData K false (node j) t*g.val⁻¹=
      canonicalRoot rawData K false (node j) t := by
  obtain ⟨c,hc⟩:=pairNormalizer_simple_scalar K (RingEquiv.refl K) g.val
    (kernel_mem_pairNormalizer K g hg) (node j)
  have hc1:c=1:=kernel_singleton_scalar_one K g hg j c hc
  subst c
  intro t
  simpa only [Units.val_one,one_mul] using hc t

theorem kernel_fixes_ambient_positive (g:J) (hg:g∈(generatedNormAction K).ker)
    (i:Fin 6) (t:K) :
    g.val*canonicalRoot rawData K false i t*g.val⁻¹=canonicalRoot rawData K false i t := by
  have hp:=kernel_fixes_paired K g hg
  have hs:=kernel_fixes_singleton K g hg
  fin_cases i
  · exact (hp 0).1 t
  · exact hs 0 t
  · exact (hp 1).1 t
  · exact hs 1 t
  · exact (hp 1).2 t
  · exact (hp 0).2 t

theorem kernel_commutes_ambient_positive (g:J) (hg:g∈(generatedNormAction K).ker)
    (i:Fin 6) (t:K) : Commute g.val (canonicalRoot rawData K false i t) := by
  have h:=congrArg (fun u:(Matrix GeckIndex GeckIndex K)ˣ=>u*g.val)
    (kernel_fixes_ambient_positive K g hg i t)
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using h

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormKernelPositiveScalars
