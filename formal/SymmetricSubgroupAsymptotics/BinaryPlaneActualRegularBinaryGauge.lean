import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingConstantNormalizerGauge
import SymmetricSubgroupAsymptotics.AlternatingFourBinaryActualPolynomialUniform

/-! The actual regular-Klein binary chart with its original block labels.
Normalizer and regular action formulas retain every actual local map. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneActualRegularBinaryGauge
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (R label regular)
open BinaryPlaneAlternatingRegularGauge (gauge)
open AlternatingFourBinaryActualPolynomialUniform (cycle)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq
abbrev Space := Fin 4 → Plane

def chart (C : Subgroup Frame) (l : R →* C) : Space ≃ₗ[ZMod 2] Space :=
  (gauge C l).trans (LinearEquiv.funCongrLeft (ZMod 2) Plane label.symm)

private theorem regular_apply (r s : R) : regular r (label s)=label (r*s) := by
  change label (r*label.symm (label s))=label (r*s)
  rw [label.symm_apply_apply]
private theorem cycle_base : cycle (label 1)=label 1 := by decide +kernel

theorem normalizer_action (C : Subgroup Frame) (l : R →* C) [l.range.Normal]
    (ht : ∀ r, (l r : Frame).right=regular r)
    (g : C) (hg : (g : Frame).right=cycle) (v : Space) (i : Fin 4) :
    chart C l (BinaryPlaneCyclicWreathUniform.representation C g v) i=
      (g : Frame).left (label 1) (chart C l v (cycle⁻¹ i)) := by
  have hb : (g : Frame).right (label 1)=label 1 := by rw [hg]; exact cycle_base
  change gauge C l (BinaryPlaneCyclicWreathUniform.representation C g v) (label.symm i)=_
  rw [BinaryPlaneAlternatingConstantNormalizerGauge.action C l ht g hb]
  rw [label.apply_symm_apply,hg]
  rfl

theorem regular_action (C : Subgroup Frame) (l : R →* C)
    (ht : ∀ r, (l r : Frame).right=regular r)
    (r : R) (v : Space) (i : Fin 4) :
    chart C l (BinaryPlaneCyclicWreathUniform.representation C (l r) v) i=
      chart C l v ((regular r)⁻¹ i) := by
  change gauge C l
    (BinaryPlaneCyclicWreathUniform.representation C (l r) v) (label.symm i)=_
  rw [BinaryPlaneAlternatingRegularGauge.gauge_lift C l ht]
  have hi : r⁻¹*label.symm i=label.symm ((regular r)⁻¹ i) := by
    apply label.injective
    rw [label.apply_symm_apply,← regular_apply,label.apply_symm_apply,map_inv]
  rw [hi]
  rfl

end SymmetricSubgroupAsymptotics.BinaryPlaneActualRegularBinaryGauge
