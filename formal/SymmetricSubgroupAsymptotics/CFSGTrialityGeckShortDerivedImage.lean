import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortOrbitCommutator
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongDerivedImage
import SymmetricSubgroupAsymptotics.CFSGTrialityCubicFieldWitness

/-! Every extension-field short root acts as an element of the DERIVED
original fixed subgroup.  The actual cubic-field torus parameter exists
even at q=2; the extraction uses a²-1, never a Cartan denominator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortDerivedImage
open CFSGTrialityGeckShortOrbitCommutator CFSGTrialityGeckShortTorusConjugation
open CFSGTrialityGeckShortParameterWeyl CFSGTrialityGeckLongDerivedImage
open CFSGTrialityGeckOriginalFixedSections CFSGTrialityGeckSourceWordAction
open CFSGTrialityTripleFixedRoots CFSGTrialityCubicFieldWitness CFSGSerreOrdinaryTwists
open CFSGTrialityGeckSectionQuotientCoordinates CFSGTrialityGeckDiagramCovariance

def sourceShortTorus (q : CFSG.PrimePower) (a : (q.Extension 3)ˣ) : Fixed q :=
  sourceShortParameterWeyl q a * (sourceShortParameterWeyl q 1)⁻¹

def matrixShortTorus (K : Type) [Field K] (σ : K ≃+* K) (a : Kˣ) : MatrixGroup K :=
  matrixShortParameterWeyl K σ a * (matrixShortParameterWeyl K σ 1)⁻¹

theorem matrixShortTorus_val (K : Type) [Field K] (σ : K ≃+* K) (a : Kˣ) :
    (matrixShortTorus K σ a).val = shortTorusWord K σ a := rfl

theorem sourceShortTorus_action (q : CFSG.PrimePower) (a : (q.Extension 3)ˣ) :
    fixedImageAction q (sourceShortTorus q a) = matrixAction (q.Extension 3)
      (matrixShortTorus (q.Extension 3) (definingFieldAutomorphism q 3) a) := by
  simp only [sourceShortTorus,matrixShortTorus,map_mul,map_inv,sourceShortParameterWeyl_action]

theorem short_orbit_action_mem_derived (q : CFSG.PrimePower) (t : q.Extension 3) :
    fixedImageAction q (orbitRoot q false t) ∈ (derivedImageAction q).range := by
  obtain ⟨a,ha⟩ := exists_cubic_unit_square_ne_one q
  let b : q.Extension 3 := t/((a : q.Extension 3)^2-1)
  have hd : (a : q.Extension 3)^2-1 ≠ 0 := sub_ne_zero.mpr ha
  have hb : b*((a : q.Extension 3)^2-1) = t := div_mul_cancel₀ t hd
  let g := sourceShortTorus q a
  let h := orbitRoot q false b
  have hm := commutator_image_mem q g h
  have hword : ⁅matrixShortTorus (q.Extension 3) (definingFieldAutomorphism q 3) a,
      matrixShortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false b⁆ =
        matrixShortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t := by
    apply Subtype.ext
    change ⁅shortTorusWord (q.Extension 3) (definingFieldAutomorphism q 3) a,
      CFSGTrialityGeckFixedRootWords.shortOrbit (q.Extension 3)
        (definingFieldAutomorphism q 3) false b⁆ =
      CFSGTrialityGeckFixedRootWords.shortOrbit (q.Extension 3)
        (definingFieldAutomorphism q 3) false t
    rw [short_torus_commutator,hb]
  have he : ⁅fixedImageAction q g,fixedImageAction q h⁆ =
      fixedImageAction q (orbitRoot q false t) := by
    dsimp only [g,h]
    rw [sourceShortTorus_action,original_short_orbit_action,original_short_orbit_action,
      ← map_commutatorElement,hword]
  exact he ▸ hm

theorem short_source_action_mem_derived (q : CFSG.PrimePower) (s : Fin 3) (t : q.Extension 3) :
    fixedImageAction q (sourceShortSection q s false t) ∈ (derivedImageAction q).range :=
  conjugate_image_mem q (sourceShortTransport q s) (orbitRoot q false t)
    (short_orbit_action_mem_derived q t)

theorem short_positive_action_mem_derived (q : CFSG.PrimePower)
    (s : Fin 3) (t : Multiplicative (q.Extension 3)) :
    positiveAction (q.Extension 3)
      (shortPositiveSection (q.Extension 3) (definingFieldAutomorphism q 3) s t) ∈
        (derivedImageAction q).range := by
  have hm := short_source_action_mem_derived q s t.toAdd
  have he : fixedImageAction q (sourceShortSection q s false t.toAdd) =
      positiveAction (q.Extension 3)
        (shortPositiveSection (q.Extension 3) (definingFieldAutomorphism q 3) s t) := by
    rw [sourceShortSection_action]
    apply congrArg (matrixAction (q.Extension 3))
    apply Subtype.ext
    rw [matrixShortSection_val,positiveInclusion_val,shortPositiveSection_val]
  exact he ▸ hm

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortDerivedImage
