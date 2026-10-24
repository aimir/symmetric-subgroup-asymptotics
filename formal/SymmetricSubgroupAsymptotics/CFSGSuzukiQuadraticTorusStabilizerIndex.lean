import SymmetricSubgroupAsymptotics.CFSGSuzukiSquareIsotropy
import SymmetricSubgroupAsymptotics.CFSGSuzukiCentralAnnihilatorIndex
import Mathlib.LinearAlgebra.Quotient.Card

/-! Exact division-free coupling for the SAME Suzuki semidirect
stabilizer. The central quotient pays the scalar dual orbit and the
actual quadratic square relation bounds its actual vector image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiQuadraticTorusStabilizerIndex
open CFSGSuzukiFieldParameters CFSGSuzukiUnipotent CFSGSuzukiCentralExtensionLayers
open CFSGSuzukiSubgroupPrimeFieldLayers CFSGSuzukiSquareIsotropy CFSGSuzukiCentralAnnihilatorIndex

theorem quadratic_torus_le_index (m : ℕ) (M : Subgroup (Borel m))
    (hM : ¬(centralHom m).range ≤ M.comap SemidirectProduct.inl) :
    (Nat.card (Field m) - 1) * 2^(m+1) ≤ M.index := by
  let q := Nat.card (Field m)
  let c := Nat.card (centralSubspace m (M.comap SemidirectProduct.inl))
  let w := Nat.card (vectorSubspace m (M.comap SemidirectProduct.inl))
  let d := Nat.card ((Field m) ⧸ centralSubspace m (M.comap SemidirectProduct.inl))
  let l := (M.map SemidirectProduct.rightHom).index
  have hc : q = c * d :=
    (centralSubspace m (M.comap SemidirectProduct.inl)).card_eq_card_quotient_mul_card
  have he : M.index * c * w = q * q * l := index_mul_actual_layer_cards m M
  have ho : q - 1 ≤ d * l := central_quotient_mul_projected_index_ge m M hM
  have hw : w ≤ 2^m := vectorSubspace_card_le m (M.comap SemidirectProduct.inl) hM
  have hcpos : 0 < c := Nat.card_pos
  have hex : M.index * w = q * d * l := by
    apply Nat.eq_of_mul_eq_mul_left hcpos
    calc
      c * (M.index * w) = M.index * c * w := by ring
      _ = q * q * l := he
      _ = c * (q * d * l) := by rw [hc]; ring
  have hlo : q * (q-1) ≤ M.index * w := by
    calc
      q * (q-1) ≤ q * (d*l) := Nat.mul_le_mul_left q ho
      _ = M.index * w := by rw [hex]; ring
  have hp : (2 : ℕ)^(m+1) * 2^m = q := by
    rw [← pow_add]
    dsimp only [q]
    rw [field_card]
    congr 1
    omega
  have hmul : ((q-1)*2^(m+1)) * 2^m ≤ M.index * 2^m := by
    calc
      ((q-1)*2^(m+1))*2^m = (q-1)*(2^(m+1)*2^m) := mul_assoc _ _ _
      _ = q*(q-1) := by rw [hp]; ring
      _ ≤ M.index*w := hlo
      _ ≤ M.index*2^m := Nat.mul_le_mul_left M.index hw
  exact Nat.le_of_mul_le_mul_right hmul (pow_pos (by decide : 0 < (2 : ℕ)) m)

end SymmetricSubgroupAsymptotics.CFSGSuzukiQuadraticTorusStabilizerIndex
