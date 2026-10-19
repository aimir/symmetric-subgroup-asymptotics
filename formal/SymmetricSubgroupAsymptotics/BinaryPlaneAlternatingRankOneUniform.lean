import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalScalarGauge
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingPureNormalizerGauge
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalizedCubicLift
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingScalarCentralizer
import SymmetricSubgroupAsymptotics.BinaryCubicScalarGeneratorTransfer
import SymmetricSubgroupAsymptotics.AlternatingFourActualPolynomialUniform

/-! Actual rank-one odd kernels with A4/S4 block image have uniform ONE
translation generator. The scalar polynomial operator is assembled from
actual normal V4 and normalized top-three lifts; the original binary
subspaces and their retained sections are preserved throughout. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRankOneUniform
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneAlternatingCentralizerCommutators (R label regular top)
open BinaryPlaneAlternatingCentralizerKleinLift (alpha)
open BinaryPlaneAlternatingScalarCentralizer (H cubic centralizes_cubic)
open BinaryQuadraticField (Scalar omega)
open AlternatingFourActualPolynomialUniform (cycle)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

private theorem regular_apply (r s : R) : regular r (label s)=label (r*s) := by
  change label (r*label.symm (label s))=label (r*s)
  rw [label.symm_apply_apply]

private theorem cycle_even : cycle∈alternatingGroup (Fin 4) := by
  change Equiv.Perm.sign cycle=1
  decide +kernel
private theorem cycle_cube : cycle^3=1 := by decide +kernel
private theorem cycle_base : cycle (label 1)=label 1 := by decide +kernel
private theorem flip_regular : ∃ r : R, regular r=AlternatingFourActualPolynomialUniform.flip := by decide +kernel

private theorem mem_centralizer (C : Subgroup Frame) (g : C)
    (hc : ∀ o : oddKernel C, Commute g (o : C)) : g∈H C := by
  apply MulEquiv.ext
  intro o
  apply Subtype.ext
  change g*(o : C)*g⁻¹=(o : C)
  rw [(hc o).eq,mul_assoc,mul_inv_cancel,mul_one]

/-- No module-capacity premise is exposed by this actual endpoint. -/
theorem uniform (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    UniformSubrepresentationGeneratorBound
      (BinaryPlaneCyclicWreathUniform.representation C) 1 := by
  obtain ⟨l,E0,hl,hn,ht,hcomm,hE0,hregular,homega⟩ :=
    BinaryPlaneAlternatingNormalScalarGauge.exists_chart C e heven
  letI : l.range.Normal := hn
  let G := (BinaryPlaneAlternatingRegularGauge.gauge C l).trans
    (BinaryPlaneCubicScalarChart.functionChart (I := R) E0)
  let F : (Fin 4 → Plane) ≃ₗ[ZMod 2] (Fin 4 → Scalar) :=
    G.trans (LinearEquiv.funCongrLeft (ZMod 2) Scalar label.symm)
  obtain ⟨g,hg,hgc⟩ := BinaryPlaneAlternatingCubicCentralizingLift.exists_lift C e heven
    ⟨cycle,cycle_even⟩ (Subtype.ext cycle_cube)
  have hgb : (g : Frame).right (label 1)=label 1 := by rw [hg]; exact cycle_base
  obtain ⟨z,hzg,hzl,hzc⟩ :=
    BinaryPlaneAlternatingNormalizedCubicLift.normalize C e heven g hgb hgc
  have hz : (z : Frame).right=cycle := hzg.trans hg
  have hzb : (z : Frame).right (label 1)=label 1 := by rw [hz]; exact cycle_base
  obtain ⟨rflip,hrflip⟩ := flip_regular
  let aH : H C := ⟨z,mem_centralizer C z hzc⟩
  let tH : H C := ⟨l rflip,mem_centralizer C (l rflip) (hcomm rflip)⟩
  let rho2 : Representation (ZMod 2) (H C) (Fin 4 → Scalar) :=
    F.conjRingEquiv.toMonoidHom.comp
      ((BinaryPlaneCyclicWreathUniform.representation C).comp (H C).subtype)
  have hk : ∀ v, rho2 (cubic C e) v=omega • v := by
    intro v
    funext i
    change G (BinaryPlaneCyclicWreathUniform.representation C
      (BinaryPlaneRankOneOddGenerator.generator C e : C) (F.symm v)) (label.symm i)=omega*v i
    rw [homega]
    change omega*F (F.symm v) i=omega*v i
    rw [F.apply_symm_apply]
  let rho4 := BinaryCubicScalarLinearRepresentation.representation rho2
    (cubic C e) hk (centralizes_cubic C e)
  have ha : ∀ v i, rho4 aH v i=v (cycle⁻¹ i) := by
    intro v i
    change E0 (BinaryPlaneAlternatingRegularGauge.gauge C l
      (BinaryPlaneCyclicWreathUniform.representation C z (F.symm v)) (label.symm i))=_
    rw [BinaryPlaneAlternatingPureNormalizerGauge.action C l ht z hzb hzl]
    rw [label.apply_symm_apply,hz]
    change F (F.symm v) (cycle⁻¹ i)=v (cycle⁻¹ i)
    rw [F.apply_symm_apply]
  have htf : ∀ v i, rho4 tH v i=v (AlternatingFourActualPolynomialUniform.flip⁻¹ i) := by
    intro v i
    change E0 (BinaryPlaneAlternatingRegularGauge.gauge C l
      (BinaryPlaneCyclicWreathUniform.representation C (l rflip) (F.symm v))
        (label.symm i))=_
    rw [BinaryPlaneAlternatingRegularGauge.gauge_lift C l ht]
    have hi : rflip⁻¹*label.symm i=label.symm (AlternatingFourActualPolynomialUniform.flip⁻¹ i) := by
      apply label.injective
      rw [label.apply_symm_apply,← regular_apply,label.apply_symm_apply,map_inv,hrflip]
    rw [hi]
    change F (F.symm v) (AlternatingFourActualPolynomialUniform.flip⁻¹ i)=v (AlternatingFourActualPolynomialUniform.flip⁻¹ i)
    rw [F.apply_symm_apply]
  have hu4 := AlternatingFourActualPolynomialUniform.uniform rho4 aH tH ha htf
  have hu2 := BinaryCubicScalarGeneratorTransfer.uniform rho2 rho4
    (fun _ _ => rfl) (cubic C e) hk hu4
  let rhoH := (BinaryPlaneCyclicWreathUniform.representation C).comp (H C).subtype
  let inter : Representation.IntertwiningMap rhoH rho2 :=
    { toLinearMap := F.toLinearMap
      isIntertwining' h := by
        apply LinearMap.ext
        intro v
        change F (rhoH h v)=F (rhoH h (F.symm (F v)))
        rw [F.symm_apply_apply] }
  exact UniformSubrepresentationGeneratorBound.of_comp
    (BinaryPlaneCyclicWreathUniform.representation C) (H C).subtype
    (hu2.of_injective inter F.injective)

/-- Every literal retained subspace and its original quotient map retain
uniform one; no normal-subgroup inheritance or substitute N is used. -/
theorem section_uniform (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (S : Subrepresentation (BinaryPlaneCyclicWreathUniform.representation C))
    (sigma : Representation (ZMod 2) C V)
    (q : Representation.IntertwiningMap S.toRepresentation sigma)
    (hq : Function.Surjective q) : UniformSubrepresentationGeneratorBound sigma 1 := by
  let inter : Representation.IntertwiningMap S.toRepresentation
      (BinaryPlaneCyclicWreathUniform.representation C) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' _ := rfl }
  exact ((uniform C e heven).of_injective inter Subtype.val_injective).of_surjective q hq

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRankOneUniform
