import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalRegularHom
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRegularGauge
import SymmetricSubgroupAsymptotics.BinaryPlaneCubicScalarChart
import SymmetricSubgroupAsymptotics.BinaryPlaneRankOneOddGenerator

/-! One shared chart for the actual NORMAL V4 complement and actual cubic
kernel. This avoids independently choosing two incompatible gauge lifts. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalScalarGauge
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneAlternatingCentralizerCommutators (R label regular top)
open BinaryQuadraticField (Scalar omega)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

theorem exists_chart (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    ∃ (l : R →* C) (E0 : Plane ≃ₗ[ZMod 2] Scalar),
      Function.Injective l ∧ l.range.Normal ∧
      (∀ r, top C (l r)=regular r) ∧
      (∀ r (o : oddKernel C), Commute (l r) (o : C)) ∧
      (∀ v, E0 (localLinear C (label 1)
        (BinaryPlaneRankOneOddGenerator.generator C e) v)=omega*E0 v) ∧
      let E := (BinaryPlaneAlternatingRegularGauge.gauge C l).trans
        (BinaryPlaneCubicScalarChart.functionChart (I := R) E0)
      (∀ r (v : Fin 4 → Plane) s,
        E (BinaryPlaneCyclicWreathUniform.representation C (l r) v) s=E v (r⁻¹*s)) ∧
      ∀ (v : Fin 4 → Plane) r,
        E (BinaryPlaneCyclicWreathUniform.representation C
          (BinaryPlaneRankOneOddGenerator.generator C e : C) v) r=omega*E v r := by
  obtain ⟨l,hl,hn,ht,hc⟩ := BinaryPlaneAlternatingNormalRegularHom.exists_lift C e heven
  let k := BinaryPlaneRankOneOddGenerator.generator C e
  let L := localLinear C (label 1) k
  obtain ⟨E0,hE0⟩ := BinaryPlaneCubicScalarChart.exists_chart L
    (local_cubic C (label 1) k)
    (BinaryPlaneRankOneOddGenerator.local_fixedFree C e
      (BinaryPlaneAlternatingKernelPartition.transitive C heven) (label 1))
  refine ⟨l,E0,hl,hn,ht,hc,hE0,?_,?_⟩
  · intro r v s
    change E0 (BinaryPlaneAlternatingRegularGauge.gauge C l
      (BinaryPlaneCyclicWreathUniform.representation C (l r) v) s)=
        E0 (BinaryPlaneAlternatingRegularGauge.gauge C l v (r⁻¹*s))
    rw [BinaryPlaneAlternatingRegularGauge.gauge_lift C l ht]
  · intro v r
    change E0 (BinaryPlaneAlternatingRegularGauge.gauge C l
      (BinaryPlaneCyclicWreathUniform.representation C (k : C) v) r)=
        omega*E0 (BinaryPlaneAlternatingRegularGauge.gauge C l v r)
    rw [BinaryPlaneAlternatingRegularGauge.gauge_commuting C l ht (k : C)
      (top_one C k) (fun s => hc s k)]
    exact hE0 _

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNormalScalarGauge
