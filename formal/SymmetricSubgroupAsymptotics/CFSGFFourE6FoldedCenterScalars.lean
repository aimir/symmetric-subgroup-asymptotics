import SymmetricSubgroupAsymptotics.CFSGFFourE6PairNormalizerScalars
import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedGeneratedGroup
import SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoNormImage
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! A central element of the actual folded group fixes all six ambient
positive simple parameters. Pair normalization and faithful folded
parameter charts supply the argument; no original F4 simplicity is used.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6FoldedCenterScalars
open CFSGFFourSerreMatrices CFSGFFourE6FixedGeneratedGroup CFSGFFourE6SignedFixedInclusion
open CFSGFFourE6CharacteristicTwoNormImage CFSGE6GeckFixedPairNormalizer
open CFSGE6GeckDiagonalSimpleScalars CFSGE6GeckSignedSimpleParameters
open CFSGE6GeckRelativeSimpleHom CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6PairedFixedRoots CFSGTwistedE6FixedA2 CFSGSerreQuadraticMatrix
variable (K:Type) [Field K] [Finite K]
local notation "F" => canonicalElementaryGroup realizationData K

theorem center_mem_pairNormalizer (g:F) (hg:g∈Subgroup.center F) :
    g.val∈pairNormalizer K (RingEquiv.refl K) := by
  have hn (neg:Bool) : g.val∈Subgroup.normalizer
      (signedFixed K (RingEquiv.refl K) neg:Set (Matrix GeckIndex GeckIndex K)ˣ) := by
    apply Subgroup.centralizer_le_normalizer
    apply Subgroup.mem_centralizer_iff.mpr
    intro u hu
    let v:F:=⟨u,signedFixed_mem_folded K neg ⟨u,hu⟩⟩
    exact congrArg (fun z:F=>z.val) (Subgroup.mem_center_iff.mp hg v)
  exact ⟨⟨hn false,hn true⟩,(fixedRootGenerated_eq_folded K).symm ▸ g.property⟩

private theorem rawOrbit_id (neg:Bool) (a:Fin 4) (t:K) :
    rawOrbitHom K (RingEquiv.refl K) neg a (Multiplicative.ofAdd t)=orbitParameter K neg a t := by
  fin_cases a <;> rfl

private theorem rawOrbit_injective (neg:Bool) (a:Fin 4) :
    Function.Injective (rawOrbitHom K (RingEquiv.refl K) neg a) := by
  fin_cases a
  · exact rawPaired_injective K (RingEquiv.refl K) neg 0
  · exact rawPaired_injective K (RingEquiv.refl K) neg 1
  · exact rawSingleton_injective K neg 1
  · exact rawSingleton_injective K neg 0

private theorem orbit_scalar_one (g:F) (hg:g∈Subgroup.center F) (a:Fin 4) (c:Kˣ)
    (hc:∀t:K,g.val*rawOrbitHom K (RingEquiv.refl K) false a (Multiplicative.ofAdd t)*g.val⁻¹=
      rawOrbitHom K (RingEquiv.refl K) false a (Multiplicative.ofAdd ((c:K)*t))) : c=1 := by
  have hcomm:g*foldedRoot K false a 1=foldedRoot K false a 1*g:=
    (Subgroup.mem_center_iff.mp hg (foldedRoot K false a 1)).symm
  have hconj:g.val*rawOrbitHom K (RingEquiv.refl K) false a (Multiplicative.ofAdd 1)*g.val⁻¹=
      rawOrbitHom K (RingEquiv.refl K) false a (Multiplicative.ofAdd 1) := by
    rw [rawOrbit_id,←folded_root_eq_orbitParameter]
    have he:=congrArg (fun z:F=>(z*g⁻¹).val) hcomm
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_assoc,mul_inv_cancel,mul_one] using he
  have hp:=rawOrbit_injective K false a (hconj.symm.trans (hc 1))
  have hval:=congrArg Multiplicative.toAdd hp
  apply Units.ext
  simpa only [mul_one,Units.val_one] using hval.symm

private theorem center_fixes_paired (g:F) (hg:g∈Subgroup.center F) (j:Fin 2) :
    (∀t:K,g.val*canonicalRoot rawData K false (pairedNode j) t*g.val⁻¹=
      canonicalRoot rawData K false (pairedNode j) t) ∧
    (∀t:K,g.val*canonicalRoot rawData K false (pairedPartner j) t*g.val⁻¹=
      canonicalRoot rawData K false (pairedPartner j) t) := by
  have hD:=center_mem_pairNormalizer K g hg
  obtain ⟨c,hc⟩:=pairNormalizer_simple_scalar K (RingEquiv.refl K) g.val hD (pairedNode j)
  have hfix:unitTwist K (RingEquiv.refl K) g.val=g.val:=
    fixedRootGenerated_le_fixed K (RingEquiv.refl K) hD.2
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
  have hc1:c=1 := by
    fin_cases j
    · exact orbit_scalar_one K g hg 0 c hpair
    · exact orbit_scalar_one K g hg 1 c hpair
  subst c
  exact ⟨fun t=>by simpa only [Units.val_one,one_mul] using hc t,
    fun t=>by simpa only [Units.val_one,one_mul] using hp t⟩

private theorem center_fixes_singleton (g:F) (hg:g∈Subgroup.center F) (j:Fin 2) :
    ∀t:K,g.val*canonicalRoot rawData K false (node j) t*g.val⁻¹=
      canonicalRoot rawData K false (node j) t := by
  obtain ⟨c,hc⟩:=pairNormalizer_simple_scalar K (RingEquiv.refl K) g.val
    (center_mem_pairNormalizer K g hg) (node j)
  have hc1:c=1 := by
    fin_cases j
    · exact orbit_scalar_one K g hg 3 c hc
    · exact orbit_scalar_one K g hg 2 c hc
  subst c
  intro t
  simpa only [Units.val_one,one_mul] using hc t

theorem center_fixes_ambient_positive (g:F) (hg:g∈Subgroup.center F) (i:Fin 6) (t:K) :
    g.val*canonicalRoot rawData K false i t*g.val⁻¹=canonicalRoot rawData K false i t := by
  have hp:=center_fixes_paired K g hg
  have hs:=center_fixes_singleton K g hg
  fin_cases i
  · exact (hp 0).1 t
  · exact hs 0 t
  · exact (hp 1).1 t
  · exact hs 1 t
  · exact (hp 1).2 t
  · exact (hp 0).2 t

theorem center_commutes_ambient_positive (g:F) (hg:g∈Subgroup.center F) (i:Fin 6) (t:K) :
    Commute g.val (canonicalRoot rawData K false i t) := by
  have h:=congrArg (fun u:(Matrix GeckIndex GeckIndex K)ˣ=>u*g.val)
    (center_fixes_ambient_positive K g hg i t)
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using h

end SymmetricSubgroupAsymptotics.CFSGFFourE6FoldedCenterScalars
