import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedCoordinates
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleInvariantPairing

/-! The actual four-coordinate alternating pairing for the diagram-fixed
D4 middle coefficient space. Nondegeneracy retains the explicit
characteristic-not-three hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedPairing

open CFSGTrialityGeckMiddleScalarPairing CFSGGTwoD4GeckMiddleFixedCoordinates
open CFSGGTwoD4GeckMiddleInvariantPairing

def pairing (K : Type) [Field K] : (Fin 4 → K) →ₗ[K] (Fin 4 → K) →ₗ[K] K :=
  (cubePairing K).compl₁₂ (fixedCubeEmbedding K) (fixedCubeEmbedding K)

theorem pairing_apply (K : Type) [Field K] (c d : Fin 4 → K) :
    pairing K c d = cubePairing K (fixedCubeEmbedding K c) (fixedCubeEmbedding K d) := rfl

theorem pairing_alternating (K : Type) [Field K] (c : Fin 4 → K) : pairing K c c = 0 :=
  cubePairing_alternating K (fixedCubeEmbedding K c)

theorem pairing_separating (K : Type) [Field K] (hthree : (3 : K) ≠ 0) (c : Fin 4 → K)
    (hz : ∀ d, pairing K c d = 0) : c = 0 := by
  have he : fixedCubeEmbedding K c = 0 := by
    apply fixed_cubePairing_separating K hthree _ (fixedCubeEmbedding_fixed K c)
    intro v hv
    obtain ⟨d,rfl⟩ := exists_fixedCubeEmbedding K v hv
    exact hz d
  apply fixedCubeEmbedding_injective K
  exact he.trans (map_zero (fixedCubeEmbedding K)).symm

theorem pairing_full (K : Type) [Field K] (hthree : (3 : K) ≠ 0) (c : Fin 4 → K) (hc : c ≠ 0) :
    Function.Surjective (pairing K c) := by
  have hn : ∃ d, pairing K c d ≠ 0 := by
    by_contra hn
    apply hc
    apply pairing_separating K hthree c
    intro d
    exact not_not.mp (fun hd => hn ⟨d,hd⟩)
  obtain ⟨d,hd⟩ := hn
  intro a
  refine ⟨(a/pairing K c d) • d,?_⟩
  rw [map_smul]
  change (a/pairing K c d)*pairing K c d = a
  exact div_mul_cancel₀ a hd

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFixedPairing
