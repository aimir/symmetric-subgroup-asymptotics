import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointPairing
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointProjection
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCentralExtensionData
import SymmetricSubgroupAsymptotics.CFSGScalarPlanePairing

/-! In characteristic three the entire endpoint kernel is the centre of
this same actual fixed radical. Its other two middle coordinates are
retained; the injected highest-root line is only one line in this centre. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointCentralKernel

open CFSGGTwoD4GeckMiddleFixedRadicalCoordinates
open CFSGGTwoD4GeckMiddleFixedPairing CFSGGTwoD4GeckMiddleInitialPairing
open CFSGGTwoD4GeckMiddleEndpointPairing CFSGGTwoD4GeckMiddleEndpointProjection
open CFSGGTwoD4GeckMiddleCentralExtensionData
open scoped commutatorElement

variable (K : Type) [Field K] [Finite K] [CharP K 3]

theorem pairing_endpoints (hcard : 4 ≤ Nat.card K) (u v : Fin 4 → K) :
    pairing K u v = CFSGScalarPlanePairing.pairing (initialPairingCoefficient K)
      (endpointLinear K u) (endpointLinear K v) := by
  rw [pairing_eq_endpoint_char_three K hcard]
  rfl

theorem endpoint_commutator (hcard : 4 ≤ Nat.card K) (u v : fixedMiddle K) :
    u*v*u⁻¹*v⁻¹ = central K (Multiplicative.ofAdd
      (CFSGScalarPlanePairing.pairing (initialPairingCoefficient K)
        (endpointHom K u).toAdd (endpointHom K v).toAdd)) := by
  rw [central_commutator, pairing_endpoints K hcard]
  rfl

theorem endpointKernel_le_center (hcard : 4 ≤ Nat.card K) :
    endpointKernel K ≤ Subgroup.center (fixedMiddle K) := by
  intro u hu
  have he : endpointHom K u = 1 := hu
  have hz : (endpointHom K u).toAdd = 0 := congrArg Multiplicative.toAdd he
  apply Subgroup.mem_center_iff.mpr
  intro v
  have hc : ⁅u,v⁆ = 1 := by
    change u*v*u⁻¹*v⁻¹ = 1
    rw [endpoint_commutator K hcard]
    have hp : CFSGScalarPlanePairing.pairing (initialPairingCoefficient K)
        (endpointHom K u).toAdd (endpointHom K v).toAdd = 0 := by
      simp only [hz, map_zero, LinearMap.zero_apply]
    rw [hp]
    exact map_one (central K)
  exact (commutatorElement_eq_one_iff_commute.mp hc).eq.symm

theorem center_eq_endpointKernel (hcard : 4 ≤ Nat.card K) :
    Subgroup.center (fixedMiddle K) = endpointKernel K := by
  apply le_antisymm
  · intro u hu
    have hz : (endpointHom K u).toAdd = 0 := by
      apply CFSGScalarPlanePairing.pairing_separating _ (initialPairingCoefficient_ne_zero K)
      intro w
      obtain ⟨v,hv⟩ := endpointHom_surjective K hcard (Multiplicative.ofAdd w)
      have hc : ⁅u,v⁆ = 1 := commutatorElement_eq_one_iff_commute.mpr
        (Subgroup.mem_center_iff.mp hu v).symm
      have he : central K (Multiplicative.ofAdd
          (CFSGScalarPlanePairing.pairing (initialPairingCoefficient K)
            (endpointHom K u).toAdd w)) = central K 1 := by
        calc
          _ = u*v*u⁻¹*v⁻¹ := by
            rw [endpoint_commutator K hcard, hv]
            rfl
          _ = 1 := hc
          _ = central K 1 := (map_one (central K)).symm
      exact congrArg Multiplicative.toAdd (central_injective K he)
    change endpointHom K u = 1
    exact congrArg Multiplicative.ofAdd hz
  · exact endpointKernel_le_center K hcard

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointCentralKernel
