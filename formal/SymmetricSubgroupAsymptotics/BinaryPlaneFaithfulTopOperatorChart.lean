import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopRegularLift
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingConstantNormalizerGauge
import SymmetricSubgroupAsymptotics.BinaryPlaneZeroOddDichotomy
import SymmetricSubgroupAsymptotics.AlternatingFourBinaryActualPolynomialUniform

/-! The actual faithful quartet top gives an actual order-three lift and
an actual regular flip. Their common binary chart retains the constant
local factor, whose cube is proved to be one. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopOperatorChart
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (R label regular top)
open BinaryPlaneAlternatingRegularGauge (gauge)
open AlternatingFourBinaryActualPolynomialUniform (cycle)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq
abbrev Space := Fin 4 → Plane

def representation (C : Subgroup Frame) (F : Space ≃ₗ[ZMod 2] Space) :
    Representation (ZMod 2) C Space :=
  F.conjRingEquiv.toMonoidHom.comp (BinaryPlaneCyclicWreathUniform.representation C)

private theorem regular_apply (r s : R) : regular r (label s)=label (r*s) := by
  change label (r*label.symm (label s))=label (r*s)
  rw [label.symm_apply_apply]
private theorem cycle_even : cycle∈alternatingGroup (Fin 4) := by
  change Equiv.Perm.sign cycle=1
  decide +kernel
private theorem cycle_cube : cycle^3=1 := by decide +kernel
private theorem cycle_base : cycle (label 1)=label 1 := by decide +kernel
private theorem base_zero : label 1=(0 : Fin 4) := by decide +kernel
private theorem flip_regular : ∃ r : R,
    regular r=AlternatingFourBinaryActualPolynomialUniform.flip := by decide +kernel

theorem exists_chart (C : Subgroup Frame) (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    ∃ (F : Space ≃ₗ[ZMod 2] Space) (a t : C) (L : Linear), L^3=1 ∧
      (∀ v i, representation C F a v i=L (v (cycle⁻¹ i))) ∧
      (∀ v i, representation C F t v i=
        v (AlternatingFourBinaryActualPolynomialUniform.flip⁻¹ i)) := by
  obtain ⟨l,hl,hn,ht⟩ := BinaryPlaneFaithfulTopRegularLift.exists_lift C hinj heven
  have htop : ∀ r, (l r : Frame).right=regular r := ht
  letI : l.range.Normal := hn
  let F : Space ≃ₗ[ZMod 2] Space :=
    (gauge C l).trans (LinearEquiv.funCongrLeft (ZMod 2) Plane label.symm)
  obtain ⟨g,hg⟩ := heven ⟨cycle,cycle_even⟩
  have hgc : g^3=1 := hinj (by
    rw [map_pow,map_one]
    change (g : Frame).right^3=1
    rw [hg]
    exact cycle_cube)
  have hgb : (g : Frame).right (label 1)=label 1 := by rw [hg]; exact cycle_base
  let L := (g : Frame).left (label 1)
  have hL : L^3=1 := by
    let q : BinaryPlaneZeroOddDichotomy.stabilizer C := ⟨g,by
      change (g : Frame).right 0=0
      simpa only [base_zero] using hgb⟩
    have hq : q^3=1 := Subtype.ext hgc
    have hh := congrArg (BinaryPlaneZeroOddDichotomy.localStabilizer C) hq
    simpa only [map_pow,map_one,BinaryPlaneZeroOddDichotomy.localStabilizer,
      q,L,base_zero] using hh
  obtain ⟨rflip,hrflip⟩ := flip_regular
  refine ⟨F,g,l rflip,L,hL,?_,?_⟩
  · intro v i
    let r := label.symm ((g : Frame).right⁻¹ i)
    let s := label.symm i
    obtain ⟨t,hc⟩ := BinaryPlaneAlternatingNormalRegularHom.conjugation_lift C l g r
    have hh : g*l r=l t*g := mul_inv_eq_iff_eq_mul.mp hc
    have he := congrArg (fun z : C => (z : Frame).right (label 1)) hh
    have hi : (g : Frame).right (label r)=label t := by
      simpa only [Subgroup.coe_mul,PermutationalWreathProduct.mul_right,
        htop,Equiv.Perm.mul_apply,regular_apply,mul_one,hgb] using he
    have hs : t=s := by
      apply label.injective
      rw [← hi]
      dsimp only [r,s]
      rw [label.apply_symm_apply,label.apply_symm_apply]
      exact (g : Frame).right.apply_symm_apply i
    subst t
    change gauge C l (BinaryPlaneCyclicWreathUniform.representation C g (F.symm v)) s=_
    rw [BinaryPlaneAlternatingNormalizerGauge.gauge_normalizer C l ht g r s hgb hc]
    change L (F (F.symm v) ((g : Frame).right⁻¹ i))=_
    rw [F.apply_symm_apply,hg]
  · intro v i
    change gauge C l
      (BinaryPlaneCyclicWreathUniform.representation C (l rflip) (F.symm v))
        (label.symm i)=_
    rw [BinaryPlaneAlternatingRegularGauge.gauge_lift C l ht]
    have hi : rflip⁻¹*label.symm i=
        label.symm (AlternatingFourBinaryActualPolynomialUniform.flip⁻¹ i) := by
      apply label.injective
      rw [label.apply_symm_apply,← regular_apply,label.apply_symm_apply,map_inv,hrflip]
    rw [hi]
    change F (F.symm v) (AlternatingFourBinaryActualPolynomialUniform.flip⁻¹ i)=_
    rw [F.apply_symm_apply]

end SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopOperatorChart
