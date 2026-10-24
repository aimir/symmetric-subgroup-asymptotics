import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleEndpointCentralKernel

/-! The primitive highest-root line lies inside the full actual endpoint
centre, whose order is q^3. The central line remains distinguished rather
than replacing the entire centre by a scalar field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFullCentralLine
open CFSGGTwoD4GeckMiddleFixedRadicalCoordinates
open CFSGGTwoD4GeckMiddleCentralExtensionData CFSGGTwoD4GeckMiddleEndpointProjection
open CFSGGTwoD4GeckMiddleEndpointCentralKernel

variable (K : Type) [Field K] [Finite K] [CharP K 3]

theorem endpointHom_central (t : Multiplicative K) : endpointHom K (central K t) = 1 := by
  have hp : projection K (central K t) = 1 := (central_range K).le ⟨t,rfl⟩
  have hc : coordinate K (central K t) = 0 := hp
  change endpointLinear K (coordinate K (central K t)) = 0
  rw [hc,map_zero]

def highInCenter (hcard : 4 ≤ Nat.card K) :
    Multiplicative K →* Subgroup.center (fixedMiddle K) :=
  (central K).codRestrict (Subgroup.center (fixedMiddle K)) (fun t =>
    endpointKernel_le_center K hcard (endpointHom_central K t))

theorem highInCenter_injective (hcard : 4 ≤ Nat.card K) :
    Function.Injective (highInCenter K hcard) := by
  intro a b he
  exact central_injective K (congrArg Subtype.val he)

def scalarLine (hcard : 4 ≤ Nat.card K) : K →+ Additive (Subgroup.center (fixedMiddle K)) where
  toFun a := Additive.ofMul (highInCenter K hcard (Multiplicative.ofAdd a))
  map_zero' := congrArg Additive.ofMul (map_one (highInCenter K hcard))
  map_add' a b := by
    change highInCenter K hcard (Multiplicative.ofAdd (a+b)) =
      highInCenter K hcard (Multiplicative.ofAdd a)*highInCenter K hcard (Multiplicative.ofAdd b)
    rw [ofAdd_add,map_mul]

theorem center_card (hcard : 4 ≤ Nat.card K) :
    Nat.card (Subgroup.center (fixedMiddle K)) = Nat.card K^3 := by
  rw [center_eq_endpointKernel K hcard]
  exact endpointKernel_card K hcard

theorem center_subtype_range (hcard : 4 ≤ Nat.card K) :
    (Subgroup.center (fixedMiddle K)).subtype.range = (endpointHom K).ker := by
  rw [Subgroup.range_subtype]
  exact center_eq_endpointKernel K hcard

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleFullCentralLine
