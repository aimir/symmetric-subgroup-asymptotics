import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRegularGauge
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalRegularHom

/-! A normalizer fixing the base block has one CONSTANT local operator
in the actual regular-V4 gauge. No claim is made about normalizers which
invert the cubic kernel being scalar-linear. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalizerGauge
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (R label regular)
open BinaryPlaneAlternatingRegularGauge (transport gauge)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

private theorem regular_apply (r s : R) : regular r (label s)=label (r*s) := by
  change label (r*label.symm (label s))=label (r*s)
  rw [label.symm_apply_apply]

variable (C : Subgroup Frame) (l : R →* C)
  (ht : ∀ r, (l r : Frame).right=regular r)

include ht in
/-- Exact transport identity for any actual conjugation equation. -/
theorem transport_normalizer (g : C) (r s : R)
    (hb : (g : Frame).right (label 1)=label 1)
    (hc : g*l r*g⁻¹=l s) :
    (g : Frame).left (label s)*transport C l r =
      transport C l s*(g : Frame).left (label 1) := by
  have hh : g*l r=l s*g := mul_inv_eq_iff_eq_mul.mp hc
  have htop := congrArg (fun z : C => (z : Frame).right) hh
  have hi : (g : Frame).right (label r)=label s := by
    have he := congrArg (fun p : Equiv.Perm (Fin 4) => p (label 1)) htop
    simpa only [Subgroup.coe_mul,PermutationalWreathProduct.mul_right,
      ht,Equiv.Perm.mul_apply,regular_apply,mul_one,hb] using he
  have hin : (g : Frame).right⁻¹ (label s)=label r := by
    rw [← hi]
    exact (g : Frame).right.symm_apply_apply (label r)
  have hs : (regular s)⁻¹ (label s)=label 1 := by
    have he : regular s (label 1)=label s := by
      simpa only [mul_one] using regular_apply s 1
    have hh := congrArg (regular s).symm he
    simpa only [Equiv.symm_apply_apply] using hh.symm
  have he := congrArg (fun z : C => (z : Frame).left (label s)) hh
  simp only [Subgroup.coe_mul,PermutationalWreathProduct.mul_left,Pi.mul_apply,ht] at he
  change (g : Frame).left (label s)*(l r : Frame).left ((g : Frame).right⁻¹ (label s))=
    (l s : Frame).left (label s)*(g : Frame).left ((regular s)⁻¹ (label s)) at he
  rw [hin,hs] at he
  exact he

include ht in
/-- The constant local factor is the genuine base-block operator of g.
Normality supplies the actual r-to-s conjugation used here. -/
theorem gauge_normalizer (g : C) (r s : R)
    (hb : (g : Frame).right (label 1)=label 1)
    (hc : g*l r*g⁻¹=l s) (v : Fin 4 → Plane) :
    gauge C l (BinaryPlaneCyclicWreathUniform.representation C g v) s =
      (g : Frame).left (label 1) (gauge C l v r) := by
  have hh : g*l r=l s*g := mul_inv_eq_iff_eq_mul.mp hc
  have he := congrArg (fun z : C => (z : Frame).right (label 1)) hh
  have hi : (g : Frame).right (label r)=label s := by
    simpa only [Subgroup.coe_mul,PermutationalWreathProduct.mul_right,
      ht,Equiv.Perm.mul_apply,regular_apply,mul_one,hb] using he
  have hin : (g : Frame).right⁻¹ (label s)=label r := by
    rw [← hi]
    exact (g : Frame).right.symm_apply_apply (label r)
  apply (transport C l s).injective
  change (transport C l s) ((transport C l s).symm
      ((g : Frame).left (label s) (v ((g : Frame).right⁻¹ (label s))))) =
    ((transport C l s)*(g : Frame).left (label 1))
      ((transport C l r).symm (v (label r)))
  rw [LinearEquiv.apply_symm_apply,hin,← transport_normalizer C l ht g r s hb hc]
  change _ = (g : Frame).left (label s)
    ((transport C l r) ((transport C l r).symm (v (label r))))
  rw [LinearEquiv.apply_symm_apply]

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalizerGauge
