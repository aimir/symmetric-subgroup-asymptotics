import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRegularGauge
import SymmetricSubgroupAsymptotics.BinaryPlaneCubicScalarChart
import SymmetricSubgroupAsymptotics.BinaryPlaneRankOneOddGenerator

/-! The exact F4 chart for the actual regular Klein lift and the actual
rank-one odd generator. Full-normalizer elements may remain semilinear. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingScalarGauge
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathActualOddKernel
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)
open BinaryPlaneAlternatingCentralizerCommutators (R label regular)
open BinaryQuadraticField (Scalar omega)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

variable (C : Subgroup Frame) (e : oddKernel C ≃* Cubic)
  (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)

include heven in
/-- Both operators are tied to elements of the actual linear image.
There is no numerical capacity input and no splitting of an affine group. -/
theorem exists_scalar_gauge :
    ∃ (l : R →* C) (E : (Fin 4 → Plane) ≃ₗ[ZMod 2] (R → Scalar)),
      Function.Injective l ∧ (∀ r, (l r : Frame).right=regular r) ∧
      (∀ r (v : Fin 4 → Plane) s,
        E (BinaryPlaneCyclicWreathUniform.representation C (l r) v) s = E v (r⁻¹*s)) ∧
      ∀ (v : Fin 4 → Plane) r,
        E (BinaryPlaneCyclicWreathUniform.representation C
          (BinaryPlaneRankOneOddGenerator.generator C e : C) v) r = omega * E v r := by
  obtain ⟨l,hl,ht,hregular,hodd⟩ :=
    BinaryPlaneAlternatingRegularGauge.exists_actual_gauge C e heven
  let k := BinaryPlaneRankOneOddGenerator.generator C e
  let L : Linear := localLinear C (label 1) k
  have hc : L^3=1 := local_cubic C (label 1) k
  have hf : ∀ v, L v=v → v=0 :=
    BinaryPlaneRankOneOddGenerator.local_fixedFree C e
      (BinaryPlaneAlternatingKernelPartition.transitive C heven) (label 1)
  obtain ⟨E0,hE0⟩ := BinaryPlaneCubicScalarChart.exists_chart L hc hf
  let F := BinaryPlaneCubicScalarChart.functionChart (I := R) E0
  let E := (BinaryPlaneAlternatingRegularGauge.gauge C l).trans F
  refine ⟨l,E,hl,ht,?_,?_⟩
  · intro r v s
    change E0 (BinaryPlaneAlternatingRegularGauge.gauge C l
      (BinaryPlaneCyclicWreathUniform.representation C (l r) v) s) =
      E0 (BinaryPlaneAlternatingRegularGauge.gauge C l v (r⁻¹*s))
    rw [hregular]
  · intro v r
    change E0 (BinaryPlaneAlternatingRegularGauge.gauge C l
      (BinaryPlaneCyclicWreathUniform.representation C (k : C) v) r) =
      omega * E0 (BinaryPlaneAlternatingRegularGauge.gauge C l v r)
    rw [hodd]
    exact hE0 _

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingScalarGauge
