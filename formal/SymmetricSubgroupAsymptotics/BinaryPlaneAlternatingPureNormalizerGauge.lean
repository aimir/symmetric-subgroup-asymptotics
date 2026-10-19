import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalizerGauge

/-! After actual local cubic normalization, the normalizer acts by its
literal block permutation in the SAME regular-V4 chart. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingPureNormalizerGauge
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (R label regular)
open BinaryPlaneAlternatingRegularGauge (gauge)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

private theorem regular_apply (r s : R) : regular r (label s)=label (r*s) := by
  change label (r*label.symm (label s))=label (r*s)
  rw [label.symm_apply_apply]

theorem action (C : Subgroup Frame) (l : R →* C) [l.range.Normal]
    (ht : ∀ r, (l r : Frame).right=regular r)
    (g : C) (hb : (g : Frame).right (label 1)=label 1)
    (hlocal : (g : Frame).left (label 1)=1)
    (v : Fin 4 → Plane) (s : R) :
    gauge C l (BinaryPlaneCyclicWreathUniform.representation C g v) s =
      gauge C l v (label.symm ((g : Frame).right⁻¹ (label s))) := by
  let r := label.symm ((g : Frame).right⁻¹ (label s))
  obtain ⟨t,hc⟩ := BinaryPlaneAlternatingNormalRegularHom.conjugation_lift C l g r
  have hh : g*l r=l t*g := mul_inv_eq_iff_eq_mul.mp hc
  have he := congrArg (fun z : C => (z : Frame).right (label 1)) hh
  have hi : (g : Frame).right (label r)=label t := by
    simpa only [Subgroup.coe_mul,PermutationalWreathProduct.mul_right,
      ht,Equiv.Perm.mul_apply,regular_apply,mul_one,hb] using he
  have hlabel : (g : Frame).right (label r)=label s := by
    dsimp only [r]
    rw [label.apply_symm_apply]
    exact (g : Frame).right.apply_symm_apply (label s)
  have hts : t=s := label.injective (hi.symm.trans hlabel)
  subst t
  have hg := BinaryPlaneAlternatingNormalizerGauge.gauge_normalizer C l ht g r s hb hc v
  rw [hlocal] at hg
  exact hg

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingPureNormalizerGauge
