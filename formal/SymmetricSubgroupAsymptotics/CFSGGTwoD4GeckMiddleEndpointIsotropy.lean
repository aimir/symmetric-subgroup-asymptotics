import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFullCentralLine
import SymmetricSubgroupAsymptotics.ScalarCentralLineIsotropicCardinality

/-! The endpoint image of any actual subgroup missing the primitive
highest-root parameter one has order at most q. Its intersection with
the entire q^3 centre is retained, including diagonal intersections. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointIsotropy
open CFSGGTwoD4GeckMiddleFixedRadicalCoordinates CFSGGTwoD4GeckMiddleEndpointProjection
open CFSGGTwoD4GeckMiddleEndpointCentralKernel CFSGGTwoD4GeckMiddleFullCentralLine
open CFSGGTwoD4GeckMiddleCentralExtensionData CFSGGTwoD4GeckMiddleInitialPairing
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem vector_image_card_le (K : Type) [Field K] [Finite K] [CharP K 3]
    (hcard : 4 ≤ Nat.card K) (J : Subgroup (fixedMiddle K))
    (hJ : central K (Multiplicative.ofAdd (1 : K)) ∉ J) :
    Nat.card (J.map (endpointHom K)) ≤ Nat.card K := by
  letI : CommGroup (Subgroup.center (fixedMiddle K)) :=
    { (inferInstance : Group (Subgroup.center (fixedMiddle K))) with
      mul_comm := fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp a.property) b.val).symm }
  let C : AddSubgroup (Additive (Subgroup.center (fixedMiddle K))) :=
    (J.comap (Subgroup.center (fixedMiddle K)).subtype).toAddSubgroup
  let W : AddSubgroup (Fin 2 → K) := (J.map (endpointHom K)).toAddSubgroup'
  let B := CFSGScalarPlanePairing.pairing (initialPairingCoefficient K)
  have hline : scalarLine K hcard 1 ∉ C := by
    change central K (Multiplicative.ofAdd (1 : K)) ∉ J
    exact hJ
  have hW : ∀ v ∈ W, ∀ w ∈ W, scalarLine K hcard (B v w) ∈ C := by
    intro v hv w hw
    change Multiplicative.ofAdd v ∈ J.map (endpointHom K) at hv
    change Multiplicative.ofAdd w ∈ J.map (endpointHom K) at hw
    obtain ⟨x,hx,hxv⟩ := hv
    obtain ⟨y,hy,hyw⟩ := hw
    have hxv' : (endpointHom K x).toAdd = v := congrArg Multiplicative.toAdd hxv
    have hyw' : (endpointHom K y).toAdd = w := congrArg Multiplicative.toAdd hyw
    change central K (Multiplicative.ofAdd (B v w)) ∈ J
    dsimp only [B]
    rw [←hxv',←hyw',←endpoint_commutator K hcard]
    exact J.mul_mem (J.mul_mem (J.mul_mem hx hy) (J.inv_mem hx)) (J.inv_mem hy)
  have hw : Nat.card W ≤ Nat.card K^1 :=
    ScalarCentralLineIsotropicCardinality.card_le_of_scalar_line_pairing
      (F := K) (V := Fin 2 → K) (Z := Additive (Subgroup.center (fixedMiddle K))) 3 1 B
      (CFSGScalarPlanePairing.pairing_alternating _)
      (CFSGScalarPlanePairing.pairing_full _ (initialPairingCoefficient_ne_zero K))
      (by simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin])
      (scalarLine K hcard) C hline W hW
  simpa only [pow_one] using hw

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointIsotropy
