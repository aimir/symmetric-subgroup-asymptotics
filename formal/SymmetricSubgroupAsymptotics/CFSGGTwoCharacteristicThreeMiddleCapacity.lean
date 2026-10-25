import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCommutator
import SymmetricSubgroupAsymptotics.ScalarCentralLineIsotropicCardinality
import SymmetricSubgroupAsymptotics.CFSGScalarPlanePairing

/-! Arbitrary diagonal central intersections and endpoint images of ONE
literal subgroup. The full q^3 centre is kept; only prime-field additive
linearity is used for the isotropy and proper-centre capacities. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCapacity
open scoped commutatorElement
open CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
open CFSGGTwoCharacteristicThreeMiddleCentralCoordinates
open CFSGGTwoCharacteristicThreeMiddleCommutator
open CFSGGTwoCharacteristicThreeCentralGraph
variable (K : Type) [Field K] [Finite K] [CharP K 3]
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem commutator_pairing (u v : Middle K) :
    ⁅u,v⁆ = highHom K (Multiplicative.ofAdd (CFSGScalarPlanePairing.pairing (-1 : K)
      (endpointHom K u).toAdd (endpointHom K v).toAdd)) := by
  rw [commutator_eq]
  apply congrArg (highHom K)
  apply congrArg Multiplicative.ofAdd
  change coordinates K u 3*coordinates K v 0-coordinates K u 0*coordinates K v 3 =
    (-1 : K)*(coordinates K u 0*coordinates K v 3-coordinates K u 3*coordinates K v 0)
  ring

theorem central_preimage_card_mul_three_le (J : Subgroup (Middle K))
    (hJ : highHom K (Multiplicative.ofAdd (1 : K)) ∉ J) :
    3*Nat.card (J.comap (centralHom K)) ≤ Nat.card K^3 := by
  letI : Algebra (ZMod 3) K := ZMod.algebra K 3
  let C : AddSubgroup (Fin 3 → K) := (J.comap (centralHom K)).toAddSubgroup'
  have hC : C ≠ ⊤ := by
    intro he
    apply hJ
    change vertical K 1 ∈ C
    rw [he]
    trivial
  have hc := ScalarCentralLineIsotropicCardinality.proper_additive_card_mul_prime_le 3 C hC
  have hZ : Nat.card (Fin 3 → K) = Nat.card K^3 := by rw [Nat.card_fun,Nat.card_fin]
  rw [hZ] at hc
  exact hc

theorem vector_image_card_le (J : Subgroup (Middle K))
    (hJ : highHom K (Multiplicative.ofAdd (1 : K)) ∉ J) :
    Nat.card (J.map (endpointHom K)) ≤ Nat.card K := by
  let C : AddSubgroup (Fin 3 → K) := (J.comap (centralHom K)).toAddSubgroup'
  let W : AddSubgroup (Fin 2 → K) := (J.map (endpointHom K)).toAddSubgroup'
  let B := CFSGScalarPlanePairing.pairing (-1 : K)
  have hline : vertical K 1 ∉ C := hJ
  have hW : ∀ v ∈ W, ∀ w ∈ W, vertical K (B v w) ∈ C := by
    intro v hv w hw
    change Multiplicative.ofAdd v ∈ J.map (endpointHom K) at hv
    change Multiplicative.ofAdd w ∈ J.map (endpointHom K) at hw
    obtain ⟨x,hx,hxv⟩ := hv
    obtain ⟨y,hy,hyw⟩ := hw
    have hxv' : (endpointHom K x).toAdd = v := congrArg Multiplicative.toAdd hxv
    have hyw' : (endpointHom K y).toAdd = w := congrArg Multiplicative.toAdd hyw
    change highHom K (Multiplicative.ofAdd (B v w)) ∈ J
    dsimp only [B]
    rw [←hxv',←hyw',←commutator_pairing K x y]
    exact J.mul_mem (J.mul_mem (J.mul_mem hx hy) (J.inv_mem hx)) (J.inv_mem hy)
  have hw : Nat.card W ≤ Nat.card K^1 :=
    ScalarCentralLineIsotropicCardinality.card_le_of_scalar_line_pairing
      (F := K) (V := Fin 2 → K) (Z := Fin 3 → K) 3 1 B
      (CFSGScalarPlanePairing.pairing_alternating _)
      (CFSGScalarPlanePairing.pairing_full _ (neg_ne_zero.mpr one_ne_zero))
      (by simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin])
      (vertical K) C hline W hW
  simpa only [pow_one] using hw

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleCapacity
