import SymmetricSubgroupAsymptotics.BinaryFourCanonicalSymmetricInducedChart
import SymmetricSubgroupAsymptotics.BinaryFourCyclicLayerRepresentations

/-! Literal source-image stability under the three concrete operators.
Surjectivity of the unchanged original quotient map supplies actual lifts
of the canonical generators. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourFullBlockCoordinates BinaryFourSymmetricBlockActions SemidirectProduct

abbrev canonicalFull := BinaryFourCanonicalSymmetricInducedChart.fullCoordinatesRepresentation

def canonicalU : SymmetricComplement := inl (inl (Multiplicative.ofAdd ![1, 0]))
def canonicalV : SymmetricComplement := inl (inl (Multiplicative.ofAdd ![0, 1]))
def canonicalC : SymmetricComplement := inl (inr (Multiplicative.ofAdd 1))

theorem fullChart_differenceU : ambientDifferenceULinear.comp fullChart.toLinearMap =
    fullChart.toLinearMap.comp (canonicalFull canonicalU - 1) := by
  apply (Pi.basisFun Scalar (Fin 8)).ext
  intro i
  rw [Pi.basisFun_apply]
  revert i
  decide +kernel

theorem fullChart_differenceV : ambientDifferenceVLinear.comp fullChart.toLinearMap =
    fullChart.toLinearMap.comp (canonicalFull canonicalV - 1) := by
  apply (Pi.basisFun Scalar (Fin 8)).ext
  intro i
  rw [Pi.basisFun_apply]
  revert i
  decide +kernel

theorem fullChart_cycle : ambientCycleEquiv.toLinearMap.comp fullChart.toLinearMap =
    fullChart.toLinearMap.comp (canonicalFull canonicalC) := by
  apply (Pi.basisFun Scalar (Fin 8)).ext
  intro i
  rw [Pi.basisFun_apply]
  revert i
  decide +kernel

variable {G : Type} [Group G] (gamma : G →* SymmetricComplement)
    (hgamma : ∀ r : Complement, ∃ g : G, gamma g = SemidirectProduct.inl r) (L : Subrepresentation (canonicalFull.comp gamma))

def originalAmbientSource : Submodule Scalar Module := L.toSubmodule.map fullChart.toLinearMap

include hgamma

theorem originalAmbientSource_differenceU (w : Module)
    (hw : w ∈ originalAmbientSource gamma L) :
    ambientDifferenceU w ∈ originalAmbientSource gamma L := by
  obtain ⟨x, hx, rfl⟩ := hw
  obtain ⟨g, hg⟩ := hgamma (SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0]))
  have hxg := L.apply_mem_toSubmodule g hx
  change canonicalFull (gamma g) x ∈ L at hxg
  rw [hg] at hxg
  refine ⟨canonicalFull canonicalU x - x, L.toSubmodule.sub_mem hxg hx, ?_⟩
  exact (LinearMap.congr_fun fullChart_differenceU x).symm

theorem originalAmbientSource_differenceV (w : Module)
    (hw : w ∈ originalAmbientSource gamma L) :
    ambientDifferenceV w ∈ originalAmbientSource gamma L := by
  obtain ⟨x, hx, rfl⟩ := hw
  obtain ⟨g, hg⟩ := hgamma (SemidirectProduct.inl (Multiplicative.ofAdd ![0, 1]))
  have hxg := L.apply_mem_toSubmodule g hx
  change canonicalFull (gamma g) x ∈ L at hxg
  rw [hg] at hxg
  refine ⟨canonicalFull canonicalV x - x, L.toSubmodule.sub_mem hxg hx, ?_⟩
  exact (LinearMap.congr_fun fullChart_differenceV x).symm

theorem originalAmbientSource_cycle (w : Module)
    (hw : w ∈ originalAmbientSource gamma L) :
    ambientCycle w ∈ originalAmbientSource gamma L := by
  obtain ⟨x, hx, rfl⟩ := hw
  obtain ⟨g, hg⟩ := hgamma (SemidirectProduct.inr (Multiplicative.ofAdd 1))
  have hxg := L.apply_mem_toSubmodule g hx
  change canonicalFull (gamma g) x ∈ L at hxg
  rw [hg] at hxg
  refine ⟨canonicalFull canonicalC x, hxg, ?_⟩
  exact (LinearMap.congr_fun fullChart_cycle x).symm

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
