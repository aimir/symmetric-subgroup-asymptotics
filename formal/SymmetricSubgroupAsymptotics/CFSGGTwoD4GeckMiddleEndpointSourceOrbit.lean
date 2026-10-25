import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleSourceEndpointAction
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddlePositiveShear
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointWeylAction
import SymmetricSubgroupAsymptotics.ScalarPlaneShearSwapOrbit
import SymmetricSubgroupAsymptotics.CentralExtensionLayerOrbitIndex
import Mathlib.Algebra.CharP.Reduced

/-! The nonzero endpoint orbit has exactly q^2-1 elements under the
actual source-normalizer intersection. Cube Frobenius supplies every
shear parameter; the actual normalizing Weyl word supplies the opposite
shears. All acting words lie in the original generated source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointSourceOrbit
open CFSGTrialityGeckFixedRootWords
open CFSGGTwoD4GeckMiddleFixedRadicalCoordinates CFSGGTwoD4GeckMiddleSourceNormalizer
open CFSGGTwoD4GeckMiddleEndpointProjection CFSGGTwoD4GeckMiddleEndpointNormalizerAction
open CFSGGTwoD4GeckMiddlePositiveShear CFSGGTwoD4GeckMiddleEndpointWeylAction
open CFSGGTwoD4GeckMiddleSourceEndpointAction
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
variable (K : Type) [Field K] [Finite K] [CharP K 3]

theorem source_lower_shears (hcard : 4 ≤ Nat.card K) (c : K) :
    ∃ g : sourceNormalizer K, ∀ v : Fin 2 → K,
      sourceAction K hcard g (Multiplicative.ofAdd v) = Multiplicative.ofAdd ![v 0,c*v 0+v 1] := by
  have hf : Function.Surjective (frobenius K 3) :=
    Finite.surjective_of_injective (frobenius_inj K 3)
  obtain ⟨a,ha⟩ := hf c
  change a^3 = c at ha
  let g : sourceNormalizer K := ⟨shortOrbit K (RingEquiv.refl K) false a,
    shortOrbit_mem_sourceNormalizer K a⟩
  refine ⟨g,?_⟩
  intro v
  obtain ⟨u,hu⟩ := endpointHom_surjective K hcard (Multiplicative.ofAdd v)
  have hact : sourceAction K hcard g (endpointHom K u) = endpointHom K (positiveConjugate K a u) := by
    have he : (fixedMiddle K).normalizerMonoidHom (toAmbientNormalizer K g) u =
        positiveConjugate K a u := by
      apply Subtype.ext
      rfl
    exact (endpointAction_apply K hcard (toAmbientNormalizer K g) u).trans (congrArg (endpointHom K) he)
  have hout := congrArg Multiplicative.ofAdd (endpoint_positiveConjugate K hcard a u)
  rw [hu,ha] at hout
  rw [←hu]
  exact hact.trans hout

theorem source_endpoint_transitive (hcard : 4 ≤ Nat.card K)
    (v w : Fin 2 → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : sourceNormalizer K, sourceAction K hcard g (Multiplicative.ofAdd v) = Multiplicative.ofAdd w := by
  obtain ⟨a,b,ha,hb,hW⟩ := endpoint_weyl_swap K hcard
  let w0 : sourceNormalizer K := ⟨shortWeyl K,shortWeyl_mem_sourceNormalizer K⟩
  have hswap (z : Fin 2 → K) : sourceAction K hcard w0 (Multiplicative.ofAdd z) =
      Multiplicative.ofAdd ![a*z 1,b*z 0] := hW z
  exact ScalarPlaneShearSwapOrbit.transitive (sourceAction K hcard)
    (source_lower_shears K hcard) w0 a b ha hb hswap v w hv hw

theorem source_endpoint_orbit_card (hcard : 4 ≤ Nat.card K)
    (v : Fin 2 → K) (hv : v ≠ 0) :
    Nat.card (CentralExtensionLayerOrbitIndex.layerOrbit (sourceAction K hcard) (Multiplicative.ofAdd v)) =
      Nat.card K^2-1 := by
  have hv1 : Multiplicative.ofAdd v ≠ (1 : Multiplicative (Fin 2 → K)) := hv
  have hs : CentralExtensionLayerOrbitIndex.layerOrbit (sourceAction K hcard) (Multiplicative.ofAdd v) =
      {w : Multiplicative (Fin 2 → K) | w ≠ 1} := by
    ext w
    constructor
    · rintro ⟨g,rfl⟩ hw
      apply hv1
      apply (sourceAction K hcard g).injective
      exact hw.trans (map_one (sourceAction K hcard g)).symm
    · intro hw
      exact source_endpoint_transitive K hcard v w.toAdd hv hw
  rw [hs]
  change Nat.card {w : Multiplicative (Fin 2 → K) // w ≠ 1} = Nat.card K^2-1
  rw [CentralExtensionLayerOrbitIndex.nonone_card]
  change Nat.card (Fin 2 → K)-1 = Nat.card K^2-1
  rw [Nat.card_fun,Nat.card_fin]

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointSourceOrbit
